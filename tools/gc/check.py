#!/usr/bin/env python3
"""Portable team gate. Run from any directory; requires Python 3.9+ and Lake.

Static checks are hygiene only. The default also builds the actual Lean library
and its transitive axiom audit. Neither checks mathematical adequacy of
the endpoint specification; that requires the documented contract review.
"""
import argparse
import hashlib
import json
import pathlib
import re
import subprocess
import sys
import time
from module_layout import verify_layout

ROOT = pathlib.Path(__file__).resolve().parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lean_code(text):
    """Remove nested comments and string contents, keeping line boundaries."""
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            out.append(' ')
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            out.append('\n' if text[i] == '\n' else ' ')
            i += 1
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            out.append(' ')
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            out.append(text[i])
            i += 1
    return ''.join(out)


def static_checks(verify_promotion=False):
    assert (ROOT/'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.33.1'
    manifest = json.loads((ROOT/'lake-manifest.json').read_text())
    mathlib = next(p for p in manifest['packages'] if p['name'] == 'mathlib')
    assert mathlib['rev'] == '0df444a360eaa60ab8c11dca51a86af692955474'
    placement = verify_layout(proofs=verify_promotion)
    files = [ROOT/p for p in placement['module_paths']]
    modules = {str(p.relative_to(ROOT).with_suffix('')).replace('/', '.'): p for p in files}
    edges = {}
    for mod, path in modules.items():
        raw = path.read_text()
        assert not re.search(r'/(Users|home)/', raw), f'Absolute personal path: {path}'
        code = lean_code(raw)
        assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b', code), f'Unproved/unsafe source: {path}'
        assert not re.search(r'set_option\s+debug\.skipKernelTC\s+true', code), path
        imports = re.findall(r'^import\s+([\w.]+)', code, re.M)
        assert not any(m.startswith(('Geometrization', 'GeometrizationChecks')) for m in imports), path
        edges[mod] = [m for m in imports if m in modules]
        for imp in imports:
            if imp.startswith('DifferentialGeometry.'):
                assert (ROOT/(imp.replace('.', '/')+'.lean')).exists(), (path, imp)
        for imp in edges[mod]:
            assert imp in modules, f'Missing module {imp} imported by {mod}'
    seen, active = set(), set()

    def visit(mod):
        assert mod not in active, f'Import cycle at {mod}'
        if mod in seen:
            return
        active.add(mod)
        for dep in edges[mod]:
            visit(dep)
        active.remove(mod)
        seen.add(mod)

    audit_module = next(m for m in modules if m.endswith('.Checks.AxiomAudit'))
    visit(audit_module)
    assert seen == set(modules), f'Modules missing from gate: {set(modules)-seen}'
    provenance = json.loads((ROOT/'docs/geometrization/BASELINE_PROVENANCE.json').read_text())
    mapping = {m['original_module']: m['module'] for m in provenance['modules']}
    for m in provenance['modules']:
        source, receipt = ROOT/m['source'], ROOT/m['receipt']
        assert sha(source) == m['source_sha256'], source
        assert sha(receipt) == m['receipt_sha256'], receipt
        assert sha(ROOT/m['path']) == m['promoted_sha256'], m['path']
    tasks = [json.loads(p.read_text()) for p in sorted((ROOT/'docs/geometrization/tasks').glob('*.json'))]
    ids = {t['id'] for t in tasks}
    assert len(ids) == len(tasks) and tasks, 'Missing or duplicate task IDs'
    for task in tasks:
        assert set(task['depends_on']) <= ids, task['id']
        assert task['status'] in {'interface-review', 'ready', 'claimed', 'review', 'accepted'}
    task_map = {t['id']: t for t in tasks}
    task_seen, task_active = set(), set()

    def visit_task(tid):
        assert tid not in task_active, f'Scheduling cycle at {tid}'
        if tid in task_seen:
            return
        task_active.add(tid)
        for dep in task_map[tid]['depends_on']:
            visit_task(dep)
        task_active.remove(tid)
        task_seen.add(tid)

    for tid in ids:
        visit_task(tid)
    for i, first in enumerate(tasks):
        for second in tasks[i+1:]:
            for a in first['write_scope']:
                for b in second['write_scope']:
                    assert a != b and not (a.endswith('/') and b.startswith(a)) and not (
                        b.endswith('/') and a.startswith(b)), f'Overlapping write scopes: {first["id"]}, {second["id"]}'
    # This register schedules work; it does not replace the mathematical DAG.
    return dict(modules=len(modules), promoted_modules=len(provenance['modules']), tasks=len(tasks),
                source_sha256={str(p.relative_to(ROOT)): sha(p) for p in files})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--static', action='store_true', help='No Lean invocation; not proof validation')
    parser.add_argument('--verify-promotion', action='store_true', help='Check recorded module placement and proof-token preservation')
    parser.add_argument('--fresh-audit', action='store_true', help='Rerun the axiom command even when its Lake target is cached')
    parser.add_argument('--owned-modules', action='store_true', help='Build every owned leaf via its audit consumer; skip unrelated root modules')
    args = parser.parse_args()
    report = static_checks(args.verify_promotion)
    print(f'Static gate passed: {report["modules"]} Lean modules, {report["tasks"]} task cards.', flush=True)
    if args.static:
        return
    out = ROOT/'.lake/gc'
    out.mkdir(parents=True, exist_ok=True)
    report.update(started_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()), commands=[], success=False)
    target = ('DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.Checks.AxiomAudit'
              if args.owned_modules else 'DifferentialGeometry')
    report['build_scope'] = 'all-owned-modules' if args.owned_modules else 'whole-DifferentialGeometry-root'
    commands = [['lake', 'build', target]]
    if args.fresh_audit:
        commands.append(['lake', 'env', 'lean', 'DifferentialGeometry/Geometry/Flow/RicciFlow/Surgery/Geometrization/Checks/AxiomAudit.lean'])
    for cmd in commands:
        log = out/f'check-{len(report["commands"])+1}.log'
        print('Running '+' '.join(cmd), flush=True)
        with log.open('w') as stream:
            proc = subprocess.run(cmd, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
        report['commands'].append(dict(command=cmd, exit_code=proc.returncode,
                                       log=str(log.relative_to(ROOT)), log_sha256=sha(log)))
        print('\n'.join(log.read_text().splitlines()[-8:]), flush=True)
        if proc.returncode:
            (out/'verification.json').write_text(json.dumps(report, indent=2)+'\n')
            sys.exit(proc.returncode)
    report['success'] = True
    report['finished_utc'] = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
    report['git_commit'] = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    report['git_dirty'] = bool(subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT, text=True))
    report['toolchain'] = (ROOT/'lean-toolchain').read_text().strip()
    report['lake_manifest_sha256'] = sha(ROOT/'lake-manifest.json')
    (out/'verification.json').write_text(json.dumps(report, indent=2)+'\n')
    print('Lean build and axiom gate passed. Receipt: .lake/gc/verification.json')


if __name__ == '__main__':
    main()

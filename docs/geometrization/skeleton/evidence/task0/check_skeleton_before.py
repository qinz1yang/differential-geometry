"""Build and inventory the explicitly admitted blueprint skeleton, separately from baseline proof checks."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
DOC = ROOT / 'docs/geometrization/skeleton'
MANIFEST = DOC / 'manifest.json'
AUDIT = 'DifferentialGeometry/Topology/ThreeManifold/Geometrization/Checks/DeclarationAudit.lean'
BASELINE = '3167083409cd58f39742a7872dab504a65d24b56'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def declarations(path):
    source = path.read_text()
    lines = source.splitlines()
    stack, result = [], []
    for i, line in enumerate(lines):
        if line.startswith('namespace '):
            stack.append(line.split()[1])
        elif line.startswith('end ') and stack:
            assert stack[-1] == line.split()[1], (path, line, stack)
            stack.pop()
        m = re.match(r'(?:@\[[^]]+\]\s*)?(?:(private|protected|noncomputable) )?'
                     r'(def|abbrev|theorem|lemma|structure|inductive|class) ([\w.]+)', line)
        if m:
            result.append(dict(name='.'.join(stack + [m[3]]), kind=m[2], line=i + 1,
                               private=m[1] == 'private'))
    for i, item in enumerate(result):
        end = result[i + 1]['line'] - 1 if i + 1 < len(result) else len(lines)
        item['direct_sorry'] = bool(re.search(r'\bsorry\b', '\n'.join(lines[item['line']-1:end])))
        assert not item['direct_sorry'] or item['kind'] in ('theorem', 'lemma'), item
    assert len(re.findall(r'\bsorry\b', source)) == sum(d['direct_sorry'] for d in result), path
    return result


def new_math_paths():
    additions = subprocess.check_output(
        ['git', 'diff', '--name-only', '--diff-filter=A', BASELINE, '--', 'DifferentialGeometry'],
        cwd=ROOT, text=True).splitlines()
    additions += subprocess.check_output(
        ['git', 'ls-files', '--others', '--exclude-standard', '*.lean'],
        cwd=ROOT, text=True).splitlines()
    paths = sorted(set(p for p in additions if p.endswith('.lean') and p != AUDIT))
    assert paths and all(p.startswith('DifferentialGeometry/') for p in paths)
    return paths


def prepare():
    paths = new_math_paths()
    rec = dict(schema=1, blueprint_revision=207, baseline_commit=BASELINE,
               trust='User-authorized sorry skeleton; not a proof-complete library',
               audit_file=AUDIT, modules=[], direct_admissions=[])
    for p in paths:
        s = (ROOT/p).read_text()
        assert not re.search(r'\b(axiom|unsafe|admit)\b|\bopaque\b|/[-*]|--', s), p
        decls = declarations(ROOT/p)
        rec['modules'].append(dict(path=p, sha256=sha(ROOT/p), declarations=decls))
        rec['direct_admissions'] += [d['name'] for d in decls if d['direct_sorry']]
    rec['mathematical_modules'] = len(paths)
    rec['authored_declarations'] = sum(len(m['declarations']) for m in rec['modules'])
    rec['direct_sorry_count'] = len(rec['direct_admissions'])
    bp = ROOT/'docs/geometrization/blueprint'
    rec['blueprint_sha256'] = {p: sha(bp/p) for p in ('master207.tex', 'master207A.tex', 'master207B.tex')}
    rec['full_DAG_translation_claimed'] = False
    modules = [p[:-5].replace('/', '.') for p in paths]
    code = ''.join('import '+m+'\n' for m in modules)+'import Lean\n\n'
    code += '''open Lean Elab Command
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option pp.maxSteps 50000
set_option pp.universes true

run_cmd do
  let env ← getEnv
  let owned : List Name := [MODULES]
  let expected : List Name := [ADMISSIONS]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound, ``sorryAx]
  let mut count : Nat := 0
  let mut direct : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless owned.contains mod do continue
    unless (env.checked.get.find? name).isSome do
      throwError "Unchecked declaration {name}"
    if info.isAxiom || info.isUnsafe then
      throwError "Unexpected axiom or unsafe declaration {name}"
    if info.type.getUsedConstants.contains ``sorryAx then
      throwError "Admission in declaration type {name}"
    let axs ← collectAxioms name
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {name}"
    let valueUses := (info.value? (allowOpaque := true)).map Expr.getUsedConstants
    let isDirect := valueUses.any (fun ns => ns.contains ``sorryAx)
    if isDirect then
      unless info.isTheorem && expected.contains name do
        throwError "Unregistered direct admission {name}"
      direct := direct + 1
    let fmt ← liftTermElabM <| Meta.ppExpr info.type
    let row := Json.mkObj [
      ("name", toJson name.toString),
      ("module", toJson mod.toString),
      ("theorem", toJson info.isTheorem),
      ("direct_sorry", toJson isDirect),
      ("axioms", toJson (axs.toList.map Name.toString)),
      ("dependencies", toJson (info.getUsedConstantsAsSet.toList.map Name.toString)),
      ("type", toJson fmt.pretty)]
    logInfo m!"SKELETON_DECL {row.compress}"
    count := count + 1
  unless direct == expected.length do
    throwError "Expected {expected.length} direct admissions; observed {direct}"
  if count == 0 then throwError "Empty skeleton audit"
  logInfo m!"Skeleton declaration audit: {count} declarations, {direct} direct admissions."
'''.replace('MODULES', ', '.join('`'+m for m in modules)).replace(
        'ADMISSIONS', ', '.join('`'+n for n in rec['direct_admissions']))
    (ROOT/AUDIT).parent.mkdir(parents=True, exist_ok=True)
    (ROOT/AUDIT).write_text(code)
    rec['audit_sha256'] = sha(ROOT/AUDIT)
    MANIFEST.write_text(json.dumps(rec, indent=2)+'\n')
    root = ROOT/'DifferentialGeometry.lean'
    imports = root.read_text().splitlines()
    for p in paths+[AUDIT]:
        line = 'import '+p[:-5].replace('/', '.')
        if line not in imports:
            imports.append(line)
    root.write_text('\n'.join(imports)+'\n')
    print(f"Registered {len(paths)} mathematical modules; {rec['direct_sorry_count']} direct admissions.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepare', action='store_true', help='Refresh explicit manifest and audit imports')
    parser.add_argument('--full-root', action='store_true', help='Build the whole flat library root')
    args = parser.parse_args()
    DOC.mkdir(parents=True, exist_ok=True)
    if args.prepare:
        prepare()
        return
    rec = json.loads(MANIFEST.read_text())
    assert new_math_paths() == [m['path'] for m in rec['modules']], 'Stale module manifest'
    assert sha(ROOT/AUDIT) == rec['audit_sha256'], 'Generated audit changed after preparation'
    root_imports = (ROOT/'DifferentialGeometry.lean').read_text().splitlines()
    old_root = subprocess.check_output(['git', 'show', BASELINE+':DifferentialGeometry.lean'],
                                       cwd=ROOT, text=True).splitlines()
    assert root_imports[:len(old_root)] == old_root, 'Existing root imports changed'
    assert len(root_imports) == len(old_root)+len(rec['modules'])+1, 'Unexpected root additions'
    for p in [m['path'] for m in rec['modules']]+[AUDIT]:
        assert root_imports.count('import '+p[:-5].replace('/', '.')) == 1, p
    changed = subprocess.check_output([
        'git', 'diff', '--name-only', '--diff-filter=MDTR', BASELINE, '--',
        'DifferentialGeometry', 'lean-toolchain', 'lake-manifest.json',
        'tools/gc/check.py', 'tools/gc/module_layout.py'], cwd=ROOT, text=True)
    assert not changed.strip(), 'Existing foundation changed: '+changed
    for p, expected in rec['blueprint_sha256'].items():
        assert sha(ROOT/'docs/geometrization/blueprint'/p) == expected, p
    for m in rec['modules']:
        assert sha(ROOT/m['path']) == m['sha256'], m['path']
    crosswalks = ['collapse_review.json', 'finite_regularity_declarations.json',
                 'hyperbolic_crosswalk.json', 'topology_declarations.json',
                 'flow_declarations.json']
    links = [d for p in crosswalks for d in json.loads((DOC/p).read_text())['declarations']]
    by_name = {d['declaration']: d for d in links}
    authored = {d['name']: (m['path'], d['line'])
                for m in rec['modules'] for d in m['declarations']}
    assert set(authored) == set(by_name) and len(links) == len(authored), 'Crosswalk coverage'
    for name, (path, line) in authored.items():
        assert (by_name[name]['file'], by_name[name]['line']) == (path, line), name
    from module_layout import verify_layout
    baseline = verify_layout(proofs=True)
    for p in baseline['module_paths']:
        old = subprocess.check_output(['git','show', BASELINE+':'+p], cwd=ROOT)
        assert old == (ROOT/p).read_bytes(), p
    out = DOC/'evidence'
    out.mkdir(exist_ok=True)
    target = 'DifferentialGeometry' if args.full_root else AUDIT[:-5].replace('/', '.')
    log = out/'build.log'
    started = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
    with log.open('w') as stream:
        proc = subprocess.run(['lake','build',target], cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
    assert proc.returncode == 0, f'Build failed; read {log}'
    text = log.read_text()
    rows = [json.loads(line.split('SKELETON_DECL ',1)[1])
            for line in text.splitlines() if 'SKELETON_DECL ' in line]
    assert rows, 'Audit must emit declaration evidence (fresh or Lake-replayed)'
    names = {r['name'] for r in rows}
    for module in rec['modules']:
        for decl in module['declarations']:
            matches = [r for r in rows if r['name'] == decl['name'] or
                       (decl['private'] and r['name'].startswith('_private.') and
                        r['name'].endswith('.'+decl['name']))]
            assert len(matches) == 1, ('Authored declaration absent or ambiguous', decl)
            assert matches[0]['module'] == module['path'][:-5].replace('/', '.')
            matches[0]['authored_name'] = decl['name']
    for row in rows:
        row['skeleton_dependencies'] = sorted(set(row['dependencies']) & names)
    direct = {r['name'] for r in rows if r['direct_sorry']}
    assert direct == set(rec['direct_admissions'])
    endpoint = next(r for r in rows if r['name']=='GC.Endpoint.geometrization')
    assert 'sorryAx' in endpoint['axioms'], 'Endpoint unexpectedly absent from placeholder census'
    by_name = {r['name']: r for r in rows}
    reachable, pending = set(), [endpoint['name']]
    while pending:
        name = pending.pop()
        if name in reachable:
            continue
        reachable.add(name)
        pending.extend(by_name[name]['skeleton_dependencies'])
    (out/'declarations.json').write_text(json.dumps(rows,indent=2)+'\n')
    report = dict(success=True, started_utc=started,
        finished_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
        target=target, full_root=args.full_root, blueprint_revision=207,
        mathematical_modules=len(rec['modules']), authored_declarations=rec['authored_declarations'],
        elaborated_declarations=len(rows), direct_sorry_theorems=len(direct),
        sorry_dependent_declarations=sum('sorryAx' in r['axioms'] for r in rows),
        endpoint_reachable_direct_admissions=sorted(direct & reachable),
        other_direct_admissions=sorted(direct - reachable),
        baseline_modules_byte_identical=len(baseline['module_paths']),
        existing_foundation_unchanged=True,
        every_authored_declaration_elaborated=True,
        every_authored_declaration_cross_referenced=True,
        allowed_axioms=['propext','Classical.choice','Quot.sound','sorryAx'],
        endpoint_is_proved_without_sorry=False, manifest_sha256=sha(MANIFEST),
        audit_sha256=sha(ROOT/AUDIT), log_sha256=sha(log),
        toolchain=(ROOT/'lean-toolchain').read_text().strip(),
        lake_manifest_sha256=sha(ROOT/'lake-manifest.json'))
    (out/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()

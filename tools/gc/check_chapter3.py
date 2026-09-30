"""Scoped build and axiom audit of the independent metric migration work."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

from check import lean_code
from check_skeleton import declarations

ROOT = Path(__file__).resolve().parents[2]
DOC = ROOT / 'docs/geometrization/chapter3'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    manifest = json.loads((DOC / 'manifest.json').read_text())
    assert (ROOT / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0-rc3'
    packages = json.loads((ROOT / 'lake-manifest.json').read_text())['packages']
    assert next(p for p in packages if p['name'] == 'mathlib')['rev'] == manifest['mathlib_commit']
    changed = subprocess.check_output(['git', 'diff', '--no-renames', '--name-only', '--diff-filter=DMRTUXB',
        manifest['baseline_commit'], '--', 'DifferentialGeometry'], cwd=ROOT, text=True)
    assert not changed.strip(), 'Existing DifferentialGeometry leaves must remain unchanged: ' + changed
    added = subprocess.check_output(['git', 'diff', '--no-renames', '--name-only', '-z',
        '--diff-filter=A', manifest['baseline_commit'], '--', 'DifferentialGeometry'],
        cwd=ROOT, text=True).split('\0')
    untracked = subprocess.check_output(['git', 'ls-files', '--others', '--exclude-standard',
        '-z', '--', 'DifferentialGeometry'], cwd=ROOT, text=True).split('\0')
    new_leaves = {p for p in added + untracked if p.endswith('.lean')}
    listed = [entry['path'] for entry in manifest['modules']]
    assert len(set(listed)) == len(listed), 'Duplicate module in manifest'
    assert new_leaves == set(listed), \
        'Manifest and all added Lean leaves differ: ' + str(new_leaves.symmetric_difference(listed))
    modules = []
    sources = []
    root_imports = (ROOT / 'DifferentialGeometry.lean').read_text().splitlines()
    for entry in manifest['modules']:
        p = entry['path']
        assert p.startswith('DifferentialGeometry/') and p.endswith('.lean')
        assert (DOC / entry['contract_notes']).is_file(), entry['contract_notes']
        raw = (ROOT / p).read_text()
        code = lean_code(raw)
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|opaque)\b', code), p
        assert '/-' not in raw and '--' not in raw, p
        assert not re.search(r'skipKernelTC|debug\.', code), p
        module = p[:-5].replace('/', '.')
        assert 'import ' + module in root_imports, p
        modules.append(module)
        sources.append(dict(path=p, sha256=sha(ROOT / p), declarations=declarations(ROOT / p)))
    out = DOC / 'evidence'
    out.mkdir(parents=True, exist_ok=True)
    receipt = dict(scope=manifest.get('scope', 'named Chapter 3 leaves only; full PC root not built'),
        started_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
        toolchain=(ROOT / 'lean-toolchain').read_text().strip(),
        mathlib_commit=manifest['mathlib_commit'], sources=sources, success=False)
    command = ['lake', 'build', *modules]
    result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    (out / 'build.log').write_text(result.stdout)
    print(result.stdout, end='')
    receipt['build'] = dict(command=command, exit_code=result.returncode,
                            log_sha256=sha(out / 'build.log'))
    if result.returncode:
        (out / 'verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
        raise SystemExit(result.returncode)
    audit = ''.join('import ' + m + '\n' for m in modules) + 'import Lean\n\n'
    audit += '''open Lean Elab Command
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
run_cmd do
  let env ← getEnv
  let owned : List Name := [MODULES]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless owned.contains env.header.moduleNames[idx.toNat]! do continue
    unless (env.checked.get.find? name).isSome do
      throwError "Unchecked declaration {name}"
    if info.isAxiom || info.isUnsafe then
      throwError "Unexpected axiom or unsafe declaration {name}"
    let axs ← collectAxioms name
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {name}"
    count := count + 1
  if count = 0 then throwError "Empty declaration audit"
  logInfo m!"CHAPTER3_AUDIT_PASS {count} declarations"
'''.replace('MODULES', ', '.join('`' + m for m in modules))
    result = subprocess.run(['lake', 'env', 'lean', '--stdin'], input=audit,
        cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (out / 'axioms.log').write_text(result.stdout)
    print(result.stdout, end='')
    receipt['axiom_audit'] = dict(exit_code=result.returncode,
        log_sha256=sha(out / 'axioms.log'), script_sha256=hashlib.sha256(audit.encode()).hexdigest())
    assert all(sha(ROOT / s['path']) == s['sha256'] for s in sources), \
        'A source changed while the scoped build/audit was running; rerun the check.'
    receipt['success'] = result.returncode == 0 and 'CHAPTER3_AUDIT_PASS' in result.stdout
    receipt['finished_utc'] = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
    receipt['git_head_at_check'] = subprocess.check_output(
        ['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    (out / 'verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    if not receipt['success']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()

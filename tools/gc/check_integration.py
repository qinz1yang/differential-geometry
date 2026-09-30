"""Audit the joint GC forest against the user-accepted migrated upstream baseline."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

from check import lean_code
from check_skeleton import declarations, validate_source, validate_crosswalk_locators, admitted_names

ROOT = Path(__file__).resolve().parents[2]
DOC = ROOT / 'docs/geometrization/integration'
MANIFEST = DOC / 'manifest.json'
CROSSWALKS = ['collapse_review.json', 'finite_regularity_declarations.json',
              'hyperbolic_crosswalk.json', 'topology_declarations.json', 'flow_declarations.json']
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def read_json(p):
    return json.loads(p.read_text())


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True)


def static_check(rec, prepare=False):
    baseline = rec['upstream_commit']
    assert git('branch','--show-current').strip()==rec['branch']
    assert git('remote','get-url','origin').strip()==rec['development_repository']
    assert git('merge-base', '--is-ancestor', baseline, 'HEAD') == ''
    assert (ROOT/'lean-toolchain').read_text().strip() == rec['toolchain']
    mathlib = next(p for p in read_json(ROOT/'lake-manifest.json')['packages'] if p['name']=='mathlib')
    assert mathlib['rev'] == rec['mathlib_commit']
    for p in ['lean-toolchain', 'lake-manifest.json', 'lakefile.toml']:
        assert (ROOT/p).read_text() == git('show', baseline+':'+p), p
    changed = git('diff','--no-renames','--name-only','--diff-filter=DMRTUXB', baseline,
                  '--','DifferentialGeometry').splitlines()
    assert not changed, ('Upstream mathematical source changed', changed)
    additions = set(git('diff','--no-renames','--name-only','--diff-filter=A',baseline,
                        '--','DifferentialGeometry').splitlines())
    additions.update(git('ls-files','--others','--exclude-standard','--','DifferentialGeometry').splitlines())
    additions = {p for p in additions if p.endswith('.lean')}
    paths = [m['path'] for m in rec['modules']]
    assert len(paths) == len(set(paths))
    assert additions == set(paths), ('Unregistered or missing sources', additions.symmetric_difference(paths))
    upstream_paths = set(git('ls-tree', '-r', '--name-only', baseline,
                             '--', 'DifferentialGeometry').splitlines())
    actual_paths = {str(p.relative_to(ROOT)) for p in (ROOT/'DifferentialGeometry').rglob('*.lean')}
    expected_paths = {p for p in upstream_paths if p.endswith('.lean')} | set(paths)
    assert actual_paths == expected_paths, ('Unexpected production sources',
                                            actual_paths.symmetric_difference(expected_paths))
    original_root = git('show',baseline+':DifferentialGeometry.lean')
    assert hashlib.sha256(original_root.encode()).hexdigest() == rec['upstream_root_sha256']
    old_lines = original_root.splitlines()
    lines = (ROOT/'DifferentialGeometry.lean').read_text().splitlines()
    assert lines[:len(old_lines)] == old_lines
    assert set(lines[len(old_lines):]) == {'import '+p[:-5].replace('/','.') for p in paths}
    assert len(lines) == len(old_lines)+len(paths)
    sk = ROOT/'docs/geometrization/skeleton'
    skeleton = read_json(sk/'manifest.json')
    links = [x for f in CROSSWALKS for x in read_json(sk/f)['declarations']]
    validate_crosswalk_locators(links,skeleton['blueprint_sha256'])
    expected = set(skeleton['direct_admissions'])
    assert expected == admitted_names(links) and len(expected)==22
    historical = read_json(DOC/'historical/skeleton_67f27962/manifest.json')
    assert expected == set(historical['direct_admissions']), 'Admission registry changed during migration'
    observed = set()
    current_skeleton_declarations = {}
    skeleton_paths = {m['path'] for m in skeleton['modules']}
    independent_paths = {m['path'] for m in read_json(ROOT/'docs/geometrization/chapter3/manifest.json')['modules']}
    foundation_paths = set(read_json(ROOT/'docs/geometrization/MODULE_PLACEMENT.json')['module_paths'])
    roles = {m['path']: m['role'] for m in rec['modules']}
    original_options = {m['path']: m for m in read_json(DOC/'historical/original_options.json')}
    assert {p for p in paths if roles[p]=='skeleton'} == skeleton_paths
    assert {p for p in paths if roles[p]=='independent'} == independent_paths-skeleton_paths
    assert {p for p in paths if roles[p]=='geometrization_foundation'} == foundation_paths
    assert {p for p in paths if roles[p]=='skeleton_audit'} == {skeleton['audit_file']}
    for m in rec['modules']:
        p=ROOT/m['path'];raw=p.read_text();code=lean_code(raw)
        if m['role']=='skeleton':
            validate_source(raw,m['path'])
        else:
            assert not re.search(r'\b(sorry|admit|axiom|unsafe|opaque|native_decide|implemented_by)\b',code), m['path']
            assert not re.search(r'skipKernelTC|debug\.',code),m['path']
        if m['role']=='independent':
            assert '/-' not in raw and '--' not in raw,m['path']
            for opt in re.findall(r'\bset_option\b[^\n]*',code):
                assert re.fullmatch(r'set_option\s+autoImplicit\s+false\s*',opt),m['path']
        if m['role'] in ('geometrization_foundation', 'skeleton_audit'):
            original = original_options[m['path']]
            assert original['original_sha256'] == m['original_sha256']
            assert re.findall(r'\bset_option\b[^\n]*',code) == original['set_options'], \
                ('Changed inherited elaboration options', m['path'])
        ds=foundation_declarations(p) if m['role']=='geometrization_foundation' else declarations(p)
        if m['role']=='skeleton':
            for d in ds:
                current_skeleton_declarations[d['name']]=(m['path'],d['line'])
        direct={d['name'] for d in ds if d['direct_sorry']}
        assert not direct or m['role']=='skeleton'
        observed.update(direct)
        for imp in re.findall(r'^import +(\S+)',code,re.M):
            if imp.startswith('DifferentialGeometry.'):
                assert (ROOT/(imp.replace('.','/')+'.lean')).is_file(),(m['path'],imp)
        if prepare:
            m['sha256']=sha(p);m['declarations']=ds
        else:
            assert sha(p)==m['sha256'] and ds==m['declarations'],m['path']
    assert observed==expected
    assert len(links)==len(current_skeleton_declarations)
    assert {e['declaration']:(e['file'],e['line']) for e in links}==current_skeleton_declarations
    return skeleton,expected



def foundation_declarations(path):
    frames=[];result=[]
    for line_number,line in enumerate(lean_code(path.read_text()).splitlines(),1):
        line=line.strip()
        m=re.fullmatch(r'namespace +([^ ]+)',line)
        if m:
            frames.append(('namespace',m[1]));continue
        m=re.fullmatch(r'(?:noncomputable +)?section(?: +([^ ]+))?',line)
        if m:
            frames.append(('section',m[1]));continue
        m=re.fullmatch(r'end(?: +([^ ]+))?',line)
        if m:
            assert frames,(path,line_number,'Unmatched end')
            kind,name=frames.pop()
            assert m[1] is None or m[1]==name,(path,line_number,name,m[1])
            continue
        m=re.match(r'(?:@\[[^]]+\]\s*)?((?:(?:private|protected|noncomputable) )*)'
                   r'(def|abbrev|theorem|lemma|structure|inductive|class|alias) ([\w.]+)',line)
        if m:
            ns=[n for k,n in frames if k=='namespace']
            result.append(dict(name='.'.join(ns+[m[3]]),kind=m[2],line=line_number,
                               private='private' in m[1].split(),direct_sorry=False))
    assert all(k=='section' for k,_ in frames),(path,frames)
    return result


def audit_source(rec, expected):
    mods=[m['path'][:-5].replace('/','.') for m in rec['modules']]
    skeleton=[m['path'][:-5].replace('/','.') for m in rec['modules'] if m['role']=='skeleton']
    authored=[d['name'] for m in rec['modules'] for d in m['declarations'] if not d['private']]
    code=''.join('import '+m+'\n' for m in mods)+'import Lean\n\n'
    code+='''open Lean Elab Command
run_cmd do
  let env ← getEnv
  let owned : List Name := [OWNED]
  let skeleton : List Name := [SKELETON]
  let authored : List Name := [AUTHORED]
  let expected : List Name := [EXPECTED]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in authored do
    unless (env.checked.get.find? name).isSome do
      throwError "Unchecked authored declaration {name}"
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
      unless allowed.contains ax || (skeleton.contains mod && ax == ``sorryAx) do
        throwError "Unexpected transitive axiom {ax} in {name}"
    let directSorry := (info.value? (allowOpaque := true)).any
      (fun e => e.getUsedConstants.contains ``sorryAx)
    if directSorry then
      unless skeleton.contains mod && info.isTheorem && expected.contains name do
        throwError "Unregistered direct admission {name}"
      direct := direct + 1
    let fmt ← liftTermElabM <| Meta.ppExpr info.type
    let row := Json.mkObj [
      ("name", toJson name.toString), ("module", toJson mod.toString),
      ("direct_sorry", toJson directSorry),
      ("theorem", toJson info.isTheorem),
      ("type", toJson fmt.pretty),
      ("dependencies", toJson (info.getUsedConstantsAsSet.toList.map Name.toString)),
      ("axioms", toJson (axs.toList.map Name.toString))]
    logInfo m!"INTEGRATION_DECL {row.compress}"
    count := count + 1
  unless direct == expected.length do
    throwError "Expected {expected.length} direct admissions; observed {direct}"
  if count == 0 then throwError "Empty integration audit"
  logInfo m!"INTEGRATION_AUDIT_PASS {count} declarations, {direct} direct admissions"
'''
    names=lambda xs:', '.join('`'+x for x in xs)
    return code.replace('OWNED',names(mods)).replace('SKELETON',names(skeleton)).replace(
        'AUTHORED',names(authored)).replace('EXPECTED',names(sorted(expected)))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepare',action='store_true')
    parser.add_argument('--static',action='store_true')
    args=parser.parse_args()
    rec=read_json(MANIFEST)
    _,expected=static_check(rec,prepare=args.prepare)
    out=DOC/'evidence';out.mkdir(exist_ok=True)
    if args.prepare:
        rec['gate_sha256']=sha(Path(__file__))
        rec['direct_admissions']=sorted(expected)
        rec['registry_sha256'] = {str(p.relative_to(ROOT)): sha(p) for p in
            [ROOT/'docs/geometrization/skeleton/manifest.json',
             ROOT/'docs/geometrization/chapter3/manifest.json',
             ROOT/'docs/geometrization/MODULE_PLACEMENT.json',
             DOC/'historical/skeleton_67f27962/manifest.json',
             DOC/'historical/original_options.json',
             ROOT/'tools/gc/check.py', ROOT/'tools/gc/check_skeleton.py'] +
            [ROOT/'docs/geometrization/skeleton'/f for f in CROSSWALKS]}
        (out/'IntegrationAudit.lean').write_text(audit_source(rec,expected))
        rec['audit_sha256']=sha(out/'IntegrationAudit.lean')
        MANIFEST.write_text(json.dumps(rec,indent=2)+'\n')
        print('Prepared',len(rec['modules']),'modules and',len(expected),'registered admissions')
        return
    assert rec['gate_sha256']==sha(Path(__file__))
    assert all(sha(ROOT/p)==h for p,h in rec['registry_sha256'].items())
    assert rec['audit_sha256']==sha(out/'IntegrationAudit.lean')
    assert (out/'IntegrationAudit.lean').read_text()==audit_source(rec,expected)
    if args.static:
        print('Joint static checks passed; this is not a Lean proof check')
        return
    pin=sha(MANIFEST)
    receipt=dict(success=False,started_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),
        upstream_commit=rec['upstream_commit'],toolchain=rec['toolchain'],
        mathlib_commit=rec['mathlib_commit'],manifest_sha256=pin,commands=[])
    try:
        for command,label in [(['lake','build','DifferentialGeometry'],'verified_full_root'),
                (['lake','env','lean','-DmaxHeartbeats=16000000','-DmaxRecDepth=100000',
                  '-Dpp.maxSteps=50000','-Dpp.universes=true',
                  str(out/'IntegrationAudit.lean')],'fresh_integration_audit')]:
            log=out/(label+'.log')
            with log.open('w') as f:
                result=subprocess.run(command,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
            receipt['commands'].append(dict(command=command,exit_code=result.returncode,
                log=str(log.relative_to(ROOT)),log_sha256=sha(log)))
            assert result.returncode==0,('Check failed',str(log))
        rows=[json.loads(line.split('INTEGRATION_DECL ',1)[1]) for line in log.read_text().splitlines()
              if 'INTEGRATION_DECL ' in line]
        assert rows and {r['name'] for r in rows if r['direct_sorry']}==expected
        for m in rec['modules']:
            for d in m['declarations']:
                matches=[r for r in rows if r['module']==m['path'][:-5].replace('/','.') and
                    (r['name']==d['name'] or (d['private'] and
                     r['name'].startswith('_private.') and r['name'].endswith('.'+d['name'])))]
                assert len(matches)==1,(m['path'],d)
                assert matches[0]['module']==m['path'][:-5].replace('/','.')
        (out/'declarations.json').write_text(json.dumps(rows,indent=2)+'\n')
        assert sha(MANIFEST)==pin
        assert all(sha(ROOT/p)==h for p,h in rec['registry_sha256'].items())
        static_check(rec)
        receipt.update(success=True,modules=len(rec['modules']),declarations=len(rows),
            direct_admissions=len(expected),upstream_mathematical_sources_unchanged=True,
            endpoint_proved_without_sorry=False,audit_evidence='fresh elaboration')
    finally:
        receipt['finished_utc']=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())
        (out/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))


if __name__=='__main__':
    main()

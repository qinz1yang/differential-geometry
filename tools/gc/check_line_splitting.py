"""Audit the line-splitting supplement with the existing manifest and provenance API."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

from check_skeleton import declarations

ROOT = Path(__file__).resolve().parents[2]
DOC = ROOT / 'docs/geometrization/chapter3'
OUT = DOC / 'evidence'
NS = 'DifferentialGeometry.Geometry.Comparison.Toponogov.'
EDGES = [
    ('ConcaveOn.eq_of_nonneg_univ', 'DifferentialGeometry.eq_of_concaveOn_univ_of_bddBelow'),
    (NS + 'sq_dist_isometry_line', 'ConcaveOn.eq_affine_of_add_neg_nonneg'),
    (NS + 'exists_calibrated_ray', NS + 'lineCoordinate_affine_of_dist'),
    (NS + 'exists_calibrated_line', NS + 'exists_calibrated_ray'),
    (NS + 'lineTranslation', NS + 'exists_calibrated_line'),
    (NS + 'lineSplitting', NS + 'sq_dist_lineTranslation'),
    (NS + 'lineSplitting', NS + 'lineTranslation_add'),
    (NS + 'exists_isometryEquiv_real_prod', NS + 'lineSplitting'),
    ('GC.MetricGeometry.PointedGHConverges.exists_isometryEquiv_real_prod',
     'GC.MetricGeometry.PointedGHConverges.fourPointComparison_zero_of_eventual_comparison'),
    ('GC.MetricGeometry.PointedGHConverges.exists_isometryEquiv_real_prod', NS + 'exists_isometryEquiv_real_prod'),
    ('GC.MetricGeometry.exists_pointedGHConverges_with_line_splitting',
     'GC.MetricGeometry.exists_geodesic_pointedGHConverges_of_covering_and_comparison'),
    ('GC.MetricGeometry.exists_pointedGHConverges_with_line_splitting', NS + 'exists_isometryEquiv_real_prod'),
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    record = json.loads((OUT / 'line_splitting_sources.json').read_text())
    manifest = json.loads((DOC / 'manifest.json').read_text())
    assert sha(ROOT / record['dag']) == record['dag_sha256']
    dag = json.loads((ROOT / record['dag']).read_text())
    listed = {m['path'] for m in manifest['modules']}
    assert (ROOT / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0-rc3'
    packages = json.loads((ROOT / 'lake-manifest.json').read_text())['packages']
    assert next(p for p in packages if p['name'] == 'mathlib')['rev'] == manifest['mathlib_commit']
    expected, before, modules = set(), {}, []
    for item in record['modules']:
        path = item['file']
        assert path in listed
        assert declarations(ROOT / path) == item['declarations']
        assert item['blueprint'] == [dag['nodes'][n]['statement'] for n in item['nodes']]
        expected.update(d['name'] for d in item['declarations'])
        before[path] = sha(ROOT / path)
        modules.append(path[:-5].replace('/', '.'))
    receipt = dict(success=False, started_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
                   scope='ten new metric line-splitting modules and same-limit applications',
                   sources=before, source_record_sha256=sha(OUT / 'line_splitting_sources.json'))
    (OUT / 'line_splitting_verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    result = subprocess.run(['lake', 'build', *modules], cwd=ROOT, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (OUT / 'line_splitting_build.log').write_text(result.stdout)
    print(result.stdout, end='')
    assert result.returncode == 0
    audit = ''.join('import ' + m + '\n' for m in modules) + 'import Lean\n'
    audit += '''open Lean Elab Command
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option pp.maxSteps 50000
set_option pp.universes true
run_cmd do
  let env ← getEnv
  let owned : List Name := [MODULES]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless owned.contains env.header.moduleNames[idx.toNat]! do continue
    unless (env.checked.get.find? name).isSome do throwError "Unchecked {name}"
    if info.isAxiom || info.isUnsafe then throwError "Untrusted {name}"
    let axs ← collectAxioms name
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {name}"
    let fmt ← liftTermElabM <| Meta.ppExpr info.type
    let row := Json.mkObj [
      ("name", toJson name.toString),
      ("axioms", toJson (axs.toList.map Name.toString)),
      ("dependencies", toJson (info.getUsedConstantsAsSet.toList.map Name.toString)),
      ("type", toJson fmt.pretty)]
    logInfo m!"LINE_SPLITTING_DECL {row.compress}"
'''.replace('MODULES', ', '.join('`' + m for m in modules))
    result = subprocess.run(['lake', 'env', 'lean', '--stdin'], input=audit, cwd=ROOT,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (OUT / 'line_splitting_declaration_audit.log').write_text(result.stdout)
    assert result.returncode == 0, result.stdout
    rows = [json.loads(line.split('LINE_SPLITTING_DECL ', 1)[1])
            for line in result.stdout.splitlines() if line.startswith('LINE_SPLITTING_DECL ')]
    actual = {row['name'] for row in rows}
    assert expected <= actual
    generated_equations = {NS + 'metricComparisonAngle.eq_1'}
    assert all(name in generated_equations or any(name.startswith(parent + '.') for parent in expected)
               for name in actual - expected), actual - expected
    assert generated_equations <= actual
    by_name = {row['name']: row for row in rows}
    def dependency_path(consumer, supplier):
        pending, seen = [(consumer, [consumer])], {consumer}
        for current, path in pending:
            for dependency in by_name[current]['dependencies']:
                if dependency == supplier:
                    return path + [dependency]
                if dependency in by_name and dependency not in seen:
                    seen.add(dependency)
                    pending.append((dependency, path + [dependency]))
        raise AssertionError((consumer, supplier))
    checked_edges = [dict(consumer=c, supplier=s, dependency_path=dependency_path(c, s))
                     for c, s in EDGES]
    (OUT / 'line_splitting_declarations.json').write_text(json.dumps(rows, indent=2) + '\n')
    blocks = re.findall(r'```lean\n(.*?)```', (DOC / 'line_splitting_review.md').read_text(), re.S)
    assert len(blocks) == 1 and blocks[0].count('\nexample') == 5
    result = subprocess.run(['lake', 'env', 'lean', '--stdin'], input=blocks[0], cwd=ROOT,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (OUT / 'line_splitting_review.log').write_text(result.stdout)
    assert result.returncode == 0 and 'LINE_SPLITTING_REVIEW_PASS' in result.stdout, result.stdout
    assert before == {p: sha(ROOT / p) for p in before}
    assert sha(OUT / 'line_splitting_sources.json') == receipt['source_record_sha256']
    receipt.update(success=True, owned_declarations=len(rows), authored_declarations=len(expected),
                   checked_edges=checked_edges, applications=5,
                   generated_imported_equations=sorted(generated_equations),
                   applications_sha256=hashlib.sha256(blocks[0].encode()).hexdigest(),
                   declaration_audit_sha256=sha(OUT / 'line_splitting_declaration_audit.log'),
                   build_log_sha256=sha(OUT / 'line_splitting_build.log'),
                   full_root_built=False, human_approval_claimed=False,
                   finished_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()))
    (OUT / 'line_splitting_verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(f'LINE_SPLITTING_AUDIT_PASS: {len(rows)} owned declarations, {len(expected)} authored declarations, '
          f'{len(EDGES)} checked dependency edges, 5 applications')


if __name__ == '__main__':
    main()

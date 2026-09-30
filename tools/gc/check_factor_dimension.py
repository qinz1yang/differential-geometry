"""Audit the factor-dimension supplement with the existing manifest and provenance API."""
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
EDGES = [
    ('IsometryEquiv.exists_segment_l2_product_factor',
     'IsometryEquiv.l2_product_fst_eq_of_dist_add_eq'),
    ('IsometryEquiv.exists_finset_net_euclidean_factor',
     'EuclideanSpace.exists_separated_grid'),
    ('IsometryEquiv.exists_finset_net_euclidean_factor',
     'Metric.card_le_card_of_separated_net'),
    ('IsometryEquiv.exists_finset_net_euclidean_factor',
     'Metric.exists_finset_net_card_le_of_packing'),
    ('IsometryEquiv.dimH_euclidean_factor_le',
     'IsometryEquiv.exists_finset_net_euclidean_factor'),
    ('IsometryEquiv.dimH_euclidean_factor_le',
     'dimH_iUnion_le_of_polynomial_nets'),
    ('IsometryEquiv.subsingleton_euclidean_factor_of_polynomial_nets',
     'Metric.subsingleton_of_dimH_lt_one'),
    ('IsometryEquiv.subsingleton_euclidean_factor_of_polynomial_nets',
     'IsometryEquiv.dimH_euclidean_factor_le'),
    ('IsometryEquiv.exists_pointed_isometryEquiv_euclidean_of_splitting',
     'IsometryEquiv.subsingleton_euclidean_factor_of_polynomial_nets'),
    ('IsometryEquiv.dimH_real_factor_le',
     'IsometryEquiv.dimH_euclidean_factor_le'),
    ('GC.MetricGeometry.PointedGHConverges.exists_polynomial_nets_at',
     'GC.MetricGeometry.PointedGHConverges.exists_internal_finset_net_of_polynomial_covering'),
    ('GC.MetricGeometry.PointedGHConverges.exists_polynomial_nets_at',
     'Metric.exists_internal_finset_net_of_finite_centers'),
    ('GC.MetricGeometry.PointedGHConverges.dimH_euclidean_factor_le',
     'GC.MetricGeometry.PointedGHConverges.exists_polynomial_nets_at'),
    ('GC.MetricGeometry.PointedGHConverges.dimH_euclidean_factor_le',
     'IsometryEquiv.dimH_euclidean_factor_le'),
    ('GC.MetricGeometry.PointedGHConverges.exists_pointed_isometryEquiv_euclidean',
     'IsometryEquiv.exists_pointed_isometryEquiv_euclidean_of_splitting'),
    ('GC.MetricGeometry.PointedGHConverges.exists_isometryEquiv_real_prod_dimH_le',
     'DifferentialGeometry.Geometry.Comparison.Toponogov.exists_isometryEquiv_real_prod'),
    ('GC.MetricGeometry.PointedGHConverges.exists_isometryEquiv_real_prod_dimH_le',
     'GC.MetricGeometry.PointedGHConverges.dimH_real_factor_le'),
    ('GC.MetricGeometry.exists_pointedGHConverges_with_line_factor_dimension',
     'GC.MetricGeometry.exists_geodesic_pointedGHConverges_of_covering_and_comparison'),
    ('GC.MetricGeometry.exists_pointedGHConverges_with_line_factor_dimension',
     'GC.MetricGeometry.PointedGHConverges.exists_isometryEquiv_real_prod_dimH_le'),
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    record = json.loads((OUT / 'factor_dimension_sources.json').read_text())
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
                   scope='eight new factor-dimension modules and same-limit applications',
                   sources=before, source_record_sha256=sha(OUT / 'factor_dimension_sources.json'))
    (OUT / 'factor_dimension_verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    result = subprocess.run(['lake', 'build', *modules], cwd=ROOT, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (OUT / 'factor_dimension_build.log').write_text(result.stdout)
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
    logInfo m!"FACTOR_DIMENSION_DECL {row.compress}"
'''.replace('MODULES', ', '.join('`' + m for m in modules))
    result = subprocess.run(['lake', 'env', 'lean', '--stdin'], input=audit, cwd=ROOT,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (OUT / 'factor_dimension_declaration_audit.log').write_text(result.stdout)
    assert result.returncode == 0, result.stdout
    rows = [json.loads(line.split('FACTOR_DIMENSION_DECL ', 1)[1])
            for line in result.stdout.splitlines() if line.startswith('FACTOR_DIMENSION_DECL ')]
    actual = {row['name'] for row in rows}
    assert expected <= actual
    generated_equations = set()
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
    (OUT / 'factor_dimension_declarations.json').write_text(json.dumps(rows, indent=2) + '\n')
    blocks = re.findall(r'```lean\n(.*?)```', (DOC / 'factor_dimension_review.md').read_text(), re.S)
    assert len(blocks) == 1 and blocks[0].count('\nexample') == 6
    result = subprocess.run(['lake', 'env', 'lean', '--stdin'], input=blocks[0], cwd=ROOT,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (OUT / 'factor_dimension_review.log').write_text(result.stdout)
    assert result.returncode == 0 and 'FACTOR_DIMENSION_REVIEW_PASS' in result.stdout, result.stdout
    assert before == {p: sha(ROOT / p) for p in before}
    assert sha(OUT / 'factor_dimension_sources.json') == receipt['source_record_sha256']
    receipt.update(success=True, owned_declarations=len(rows), authored_declarations=len(expected),
                   checked_edges=checked_edges, applications=6,
                   generated_imported_equations=sorted(generated_equations),
                   applications_sha256=hashlib.sha256(blocks[0].encode()).hexdigest(),
                   declaration_audit_sha256=sha(OUT / 'factor_dimension_declaration_audit.log'),
                   build_log_sha256=sha(OUT / 'factor_dimension_build.log'),
                   full_root_built=False, human_approval_claimed=False,
                   finished_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()))
    (OUT / 'factor_dimension_verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(f'FACTOR_DIMENSION_AUDIT_PASS: {len(rows)} owned declarations, {len(expected)} authored declarations, '
          f'{len(EDGES)} checked dependency edges, 6 applications')


if __name__ == '__main__':
    main()

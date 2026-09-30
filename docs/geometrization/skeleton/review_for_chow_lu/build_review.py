"""Assemble the human review and check its declaration/source coverage.

This is a document consistency check, not a mathematical verifier or Lean build.
Run from any directory with Python 3. The Lean sources are never modified.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
SKELETON = HERE.parent
COMMIT = 'ea0fae60ee01ef8c8d9b57a51794c6538f679c5d'
URL = f'https://github.com/qinz1yang/differential-geometry-dev/blob/{COMMIT}/'
manifest = json.loads((SKELETON / 'manifest.json').read_text())
audit = json.loads((SKELETON / 'evidence/declarations.json').read_text())
receipt = json.loads((SKELETON / 'evidence/verification.json').read_text())
audit_by_name = {x['authored_name']: x for x in audit if x.get('authored_name')}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def write_json(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')

# Every authored root declaration receives a specific mathematical destination.
root_sections = {
    'cutPieceMap': 'f3-induced-cut-metric',
    'isInducedCutMetric': 'f3-induced-cut-metric',
    'HyperbolicOrCollapsed': 'f3-induced-cut-metric',
    'geometrizes_of_hyperbolicOrCollapsed': 'f3-induced-cut-metric',
    'hasCommonNeckAccuracy': 'f4-common-accuracy',
    'componentMetric': 'f2-slices',
    'hasExteriorAreaObstructionAfter': 'f5-area-obstruction',
    'hasLateSequenceTests': 'f6-sequence-tests',
    'exists_surgery_with_late_sequence_tests': 'f7-selected-flow',
    'components_geometrize_of_late_sequence_tests': 'f8-bad-sequence-proof',
    'geometrizes_of_metric': 'f9-capstone',
    'RegularSlice': 'f2-slices', 'history': 'f2-slices', 'stage': 'f2-slices',
    'metric': 'f2-slices', 'normalizedMetric': 'f2-slices',
    'curvatureOneMetric': 'f2-slices', 'initial': 'f2-slices',
    'hasArbitrarilyLateNonemptySlices': 'f2-slices',
    'exists_regular_slice_after': 'f2-slices',
    'empty_slice_or_arbitrarily_late': 'f2-slices',
    'exists_common_late_slice': 'f2-slices',
    'geometrizes_of_late_slice_supply': 'f2-slices',
    'geometrization': 'f9-capstone', 'geometrization_conjecture': 'f9-capstone',
    'smooth_geometrization_conjecture': 'f9-capstone',
}
root_paths = {
    'DifferentialGeometry/Geometry/Collapse/TorusDecomposition.lean',
    'DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/LateDecomposition.lean',
    'DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/RegularSlice.lean',
    'DifferentialGeometry/Topology/ThreeManifold/Geometrization/Theorem.lean',
}
root_rows = []
for m in manifest['modules']:
    if m['path'] not in root_paths:
        continue
    for d in m['declarations']:
        root_rows.append(dict(d, file=m['path'],
            section=root_sections[d['name'].rsplit('.', 1)[-1]],
            axioms=audit_by_name[d['name']]['axioms']))
assert len(root_rows) == 26
write_json(HERE / 'endpoint_flow_coverage.json', {
    'reviewed_commit': COMMIT, 'report': 'endpoint_and_flow.md',
    'report_sha256': sha((HERE / 'endpoint_and_flow.md').read_bytes()),
    'declarations': root_rows, 'declaration_count': len(root_rows),
    'lean_code_modified': False,
})

rows = []
def add(name, file, line, anchor, report):
    rows.append(dict(name=name, file=file, line=line, anchor=anchor, report=report))

for d in root_rows:
    add(d['name'], d['file'], d['line'], d['section'], 'endpoint_and_flow.md')
for d in json.loads((HERE / 'collapse_coverage.json').read_text())['declarations']:
    add(d['declaration'], d['file'], d['line'], d['section'].split('#')[1], 'collapse.md')
for d in json.loads((HERE / 'hyperbolic_area_coverage.json').read_text())['declarations']:
    add(d['declaration'], d['file'], d['line'], d['anchor'], 'hyperbolic_area.md')
for d in json.loads((HERE / 'topology_finite_regularity_coverage.json').read_text())['declarations']:
    add(d['name'], d['path'], d['line'], d['report_anchor'], 'topology_finite_regularity.md')

expected = {d['name']: dict(d, file=m['path']) for m in manifest['modules'] for d in m['declarations']}
assert len(rows) == len({x['name'] for x in rows}) == len(expected) == 121
assert {x['name'] for x in rows} == set(expected)
for d in rows:
    e = expected[d['name']]
    assert (d['file'], d['line']) == (e['file'], e['line'])
    prose = (HERE / d['report']).read_text()
    assert f'{{#{d["anchor"]}}}' in prose or f'id="{d["anchor"]}"' in prose
    d.update(kind=e['kind'], direct_sorry=e['direct_sorry'],
             axioms=audit_by_name[d['name']]['axioms'])
    if d['direct_sorry']:
        d['status'] = 'Admitted'
    elif d['kind'] == 'theorem':
        d['status'] = ('Written proof; admitted dependence' if 'sorryAx' in d['axioms']
                       else 'Written proof; no skeleton admission')
    else:
        d['status'] = ('Definition/construction; admitted dependence' if 'sorryAx' in d['axioms']
                       else 'Definition/construction')

assert sum(x['direct_sorry'] for x in rows) == 17
assert sum(x['kind'] == 'theorem' for x in rows) == 55
assert len(receipt['endpoint_reachable_direct_admissions']) == 6
assert all(expected[n]['direct_sorry'] for n in receipt['endpoint_reachable_direct_admissions'])
assert len(receipt['other_direct_admissions']) == 11

# Freeze exact source text, with .txt extension: no new Lean modules are created.
snap = []
source_hashes = []
for m in manifest['modules']:
    data = (REPO / m['path']).read_bytes()
    frozen = subprocess.check_output(['git', 'show', f'{COMMIT}:{m["path"]}'], cwd=REPO)
    assert data == frozen
    assert sha(data) == m['sha256']
    source_hashes.append(dict(path=m['path'], sha256=sha(data), role='skeleton module'))
    snap.append(f'\n{"=" * 78}\n{m["path"]}\ncommit: {COMMIT}\nsha256: {sha(data)}\n{"=" * 78}\n\n' + data.decode())
(HERE / 'exact_sources.txt').write_text('EXACT FROZEN SKELETON SOURCES (not a new Lean module)\n' + ''.join(snap))

parts = ['overview.md', 'endpoint_and_flow.md', 'collapse.md', 'hyperbolic_area.md',
         'topology_finite_regularity.md', 'review_decisions.md']
all_prose = '\n'.join((HERE / p).read_text() for p in parts)
linked_sources = set(re.findall(r'/GC_BASELINE_EXPORT/([^\s)]+?\.lean)(?::\d+)?\)', all_prose))
foundation_sources = [
 'Topology/ThreeManifold/Geometrization/' + f + '.lean'
 for f in ['Prime', 'Carrier', 'Statement', 'TorusGluing', 'SmoothTorusReconstruction']
] + ['Geometry/Thurston/' + f + '.lean' for f in ['Atlas', 'Models', 'ModelAtlas', 'ElementaryModels']]
foundation_sources += ['Geometry/Flow/RicciFlow/Surgery/' + s + '.lean' for s in [
 'History/RawSurgery', 'History/CoherentSurgeryTower', 'History/SurgeryEventControl',
 'Geometrization/RawHistory', 'Geometrization/ClassifiedHistory',
 'Topology/ObservationTower', 'Topology/EventData', 'Topology/GeometricCutoff']]
foundation_sources += ['Topology/Manifold/ClosedOriented.lean', 'Topology/ThreeManifold/ConnectedSum/Finite.lean']
linked_sources.update('DifferentialGeometry/' + p for p in foundation_sources)
already = {x['path'] for x in source_hashes}
for p in sorted(linked_sources - already):
    data = (REPO / p).read_bytes()
    assert data == subprocess.check_output(['git', 'show', f'{COMMIT}:{p}'], cwd=REPO)
    source_hashes.append(dict(path=p, sha256=sha(data), role='referenced inherited definition source; not a whole-file proof audit'))
write_json(HERE / 'source_snapshot.json', dict(reviewed_commit=COMMIT, sources=source_hashes))

write_json(HERE / 'declaration_coverage.json', dict(reviewed_commit=COMMIT,
    declaration_count=121, direct_admissions=17, declarations=rows))

register = ['# Complete declaration register {#declaration-register}',
    'This register is exhaustive for the 121 authored declarations. Each entry gives its status, '
    'a link to the mathematical explanation, and the exact source line at the frozen commit. '
    'All file paths are under `DifferentialGeometry/`. A proof without a skeleton admission '
    'still uses the inherited library; this label is not a new audit of that whole library.\n']
row_by_name = {x['name']: x for x in rows}
for module_index, m in enumerate(manifest['modules'], 1):
    short = m['path'].removeprefix('DifferentialGeometry/')
    register += ['```{=latex}\n\\Needspace{6\\baselineskip}\n```\n',
                 f'## M{module_index:02d}. {Path(short).name}\n', f'**File:** `{short}`\n']
    for e in m['declarations']:
        d = row_by_name[e['name']]
        label = re.sub(r'^(f\d+|e\d+).*', lambda x: x.group(1).upper(), d['anchor'])
        if d['anchor'].startswith('collapse-'):
            label = {'collapse-radius':'C2','collapse-tensor':'C1','collapse-cuspmodel':'C3',
                     'collapse-cuspembedding':'C4','collapse-boundarydistance':'C5',
                     'collapse-hypotheses':'C6','collapse-admitted':'C8',
                     'collapse-composition':'C9','collapse-uniform':'C10'}[d['anchor']]
        elif d['anchor'].startswith('ha-'):
            label = 'HA-' + d['anchor'][3:].replace('-', '.')
        elif d['report'] == 'topology_finite_regularity.md':
            label = d['anchor'].upper()
        register += [f'- `{d["name"]}`\\\n  {d["status"]}. '
                     f'[Explanation: {label}](#{d["anchor"]}); '
                     f'[source line {d["line"]}]({URL}{d["file"]}#L{d["line"]}).\n']
(HERE / 'declaration_register.md').write_text('\n'.join(register))

def normalize(text):
    # Preserve mathematical meaning; convert raw HTML anchors to Pandoc headers.
    text = re.sub(r'<a id="([^"]+)"></a>\s*\n(#{1,6} [^\n]+)', r'\2 {#\1}', text)
    # Private, immutable source links work for all collaborators with repository access.
    text = re.sub(r'\]\(/Users/[^\n)]+?/GC_BASELINE_EXPORT/([^\s)]+?\.lean)(?::(\d+))?\)',
                  lambda m: '](' + URL + m.group(1) + ('#L' + m.group(2) if m.group(2) else '') + ')', text)
    return text.replace('\u2011', '-').replace('\u2212', '-')

combined = []
for p in parts + ['declaration_register.md']:
    t = normalize((HERE / p).read_text())
    if p == 'overview.md':
        t = t.replace('# Geometrization skeleton: a mathematical reading for Bennett Chow and Peng Lu',
                      '# Reading guide and actual proof map {#overview}')
    combined.append(t)
out = '\n\n'.join(combined)
anchors = re.findall(r'\{#([^}]+)\}', out)
assert len(anchors) == len(set(anchors)), 'Duplicate document anchors'
assert all(d['anchor'] in anchors for d in rows)
(HERE / 'geometrization_skeleton_mathematical_review.md').write_text(out)

write_json(HERE / 'report_verification.json', {
    'reviewed_commit': COMMIT, 'blueprint_revision': 207,
    'source_hashes_match_frozen_commit': True,
    'all_121_authored_declarations_have_translation_destinations': True,
    'mathematical_module_count': len(manifest['modules']),
    'direct_admissions': 17, 'written_theorem_bodies': 38,
    'endpoint_reachable_direct_admissions': receipt['endpoint_reachable_direct_admissions'],
    'other_direct_admissions': receipt['other_direct_admissions'],
    'lean_sources_modified': False, 'new_lean_build_run_for_report': False,
    'prior_build_receipt': '../evidence/verification.json',
    'prior_build_receipt_sha256': sha((SKELETON / 'evidence/verification.json').read_bytes()),
    'complete_mathematical_proof_claimed': False,
    'combined_markdown_sha256': sha(out.encode()),
    'family_report_hashes': {p: sha((HERE / p).read_bytes()) for p in parts},
})
print('Verified 22 unchanged source modules, all 121 declaration translations, 17 admissions (6 on endpoint route).')

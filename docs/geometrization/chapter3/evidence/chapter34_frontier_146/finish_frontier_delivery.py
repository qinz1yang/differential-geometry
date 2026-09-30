from pathlib import Path
import argparse
import datetime
import hashlib
import json
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument('--static-exit-code', type=int, required=True)
args = parser.parse_args()
root = Path.cwd()
repo = root / 'GC_CHAPTER3_435_RC3'
doc = repo / 'docs/geometrization/chapter3'
ev = doc / 'evidence/chapter34_frontier_146'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip()
commit = '45111b9d91f50111658f0497be2320e750325ca6'
subprocess.run(['git', 'merge-base', '--is-ancestor', commit, head], cwd=repo, check=True)
assert not subprocess.check_output(['git', 'diff', commit, '--', 'DifferentialGeometry',
    'DifferentialGeometry.lean', 'docs/geometrization/chapter3/manifest.json'], cwd=repo)
assert sha(doc / 'chapter34_frontier.md') == '581861bd18cc4d793f721459ac71c3e303b64554c60c83e51acbbeb9b6cb4e58'
assert sha(ev / 'index.json') == 'd1ff6fffa87d1f26a7d7d4a3a18258ae82cd70ecc53d17876d1f1ab8614360d4'
audit_sha = 'a71b3b706ed68f757debfad4dbbbf4f80a243ed1db2f56fa5054d23dd54e2018'
assert sha(root / 'GEOMETRIZATION_BLUEPRINT/audit_blueprint.py') == audit_sha
blueprint_sha = '277359ee147d25184d4b38b20a91ee44a394fd6ea316cfc368fab74e06bef79b'
assert sha(root / 'GEOMETRIZATION_BLUEPRINT/master207A.tex') == blueprint_sha
raw = Path('/tmp/gc_frontier_blueprint_final_audit.log').read_bytes()
log = raw.decode()
assert ('Executing unchanged audit with complete-file reads; audit SHA256=' + audit_sha) in log
if args.static_exit_code == 0:
    assert 'BLUEPRINT_STATIC_OK' in log and 'Complete-file input validation:' in log
    status = 'passed'
    reason = 'The unchanged static auditor completed with its success marker and validated full input reads.'
else:
    assert args.static_exit_code > 0 and 'BLUEPRINT_STATIC_OK' not in log
    assert 'Traceback (most recent call last):' in log
    status = 'failed'
    reason = log.strip().splitlines()[-1]
copies = {
    'blueprint_final_audit.log': Path('/tmp/gc_frontier_blueprint_final_audit.log'),
    'blueprint_empty_direct_attempt.log': Path('/tmp/gc_frontier_blueprint_audit.log'),
    'blueprint_interrupted_preinstall_attempt.log': Path('/tmp/gc_frontier_blueprint_complete_audit.log'),
    'blueprint_complete_read_wrapper.py': Path('/tmp/gc_run_blueprint_complete_reads.py'),
    'final_bundle_freeze.json': Path('/tmp/gc_chapter34_frontier_final_bundle_freeze.json'),
    'bundle_finalization_record.json': Path('/tmp/gc_chapter34_frontier_final_after145/finalization_record.json'),
    'finish_frontier_delivery.py': Path(__file__),
}
for name, source in copies.items():
    target = ev / name
    assert not target.exists(), target
    target.write_bytes(source.read_bytes())
record = {
    'status': 'bounded_frontier_audit_delivered_at_inherited_interface_boundary',
    'recorded_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'accepted_mathematical_milestone': 145,
    'accepted_mathematical_commit': commit,
    'documentation_head_before_delivery': head,
    'audit_baseline_milestone': 144,
    'observed_modules': 513, 'observed_owned_declarations': 2362, 'observed_jobs': 3351,
    'new_production_theorems_in_this_audit': 0,
    'full_chapters_complete': False, 'full_migrated_root_built': False,
    'changing_pc_snapshot_probed': False,
    'blueprint_revision': 207, 'blueprint_sha256': blueprint_sha,
    'unchanged_audit_sha256': audit_sha,
    'blueprint_static_audit': {
        'status': status, 'success': status == 'passed',
        'latest_completed_exit_code': args.static_exit_code,
        'actual_session': 25354, 'running_session': None,
        'reason': reason, 'full_file_read_validation_enforced': True,
        'log': 'blueprint_final_audit.log',
        'log_sha256': sha(ev / 'blueprint_final_audit.log'),
        'original_entrypoint': ['python3', 'GEOMETRIZATION_BLUEPRINT/audit_blueprint.py'],
        'actual_execution': ['python3', '-u', '/tmp/gc_run_blueprint_complete_reads.py'],
        'earlier_attempts': [
            {'session': 51477, 'exit_code': 0, 'accepted_as_static_success': False,
             'reason': 'Empty output with no auditor completion marker; possible cloud short read.'},
            {'session': 95288, 'exit_code': 143, 'accepted_as_static_success': False,
             'reason': 'Stopped cloud-stalled pre-install attempt after scripts were downloaded; rerun unchanged after installation.'},
        ],
    },
    'frontier_index_sha256': sha(ev / 'index.json'),
    'frontier_report_sha256': sha(doc / 'chapter34_frontier.md'),
    'additional_files': {name: sha(ev / name) for name in copies},
}
(ev / 'delivery_status.json').write_text(json.dumps(record, indent=2) + '\n')
summary = f'''# Chapter 3–4 delivery and remaining migration boundary

The [final chapter report](chapter34_frontier.md) and its hash-checked evidence bundle are complete. The last mathematical milestone is **145**, published at `{commit}` on the existing private branch. Its shared Lean gate passed for **513 modules, 2362 owned declarations and 3351 jobs**, with eleven new regressions, nineteen canonical-import axiom reports and silent selected lint. This documentation audit adds no production theorem and changes no existing mathematical leaf or manifest.

The bounded review found no further required independent producer among the frozen MC, AC, ALG, ALS and ALR obligations. An exact unnumbered compact-target net export was compiled and checked; a final challenge confirmed that the pure first-exit and buffered intrinsic-to-ambient kernels already exist. The remaining actual smooth length, curvature, angle, compactness and exhaustion/coverage bindings are still work. MC17/20, AC05/06 and the smooth ALG08 applications await the completed PC release or an explicitly stabilized interface, under the standing instruction preserved in the report. The chapters and migrated root are **not** declared complete.

The fresh, separate blueprint static audit **{status}** with actual exit code **{args.static_exit_code}**. Its final diagnostic is:

```
{reason}
```

The [actual complete-read audit log](evidence/chapter34_frontier_146/blueprint_final_audit.log) and [delivery record](evidence/chapter34_frontier_146/delivery_status.json) retain the executable hash, exact result, and earlier empty/interrupted attempts. An empty-output exit-zero invocation was not accepted as a pass. The final attempt executes the unchanged auditor with full-size/hash checks on its executable and complete-file reads for cloud-backed inputs. It ran after the report installation. This is a document-consistency check, separate from the successful Lean proof audit.

Blueprint **207A** and the accepted144/145 historical receipts are unchanged. The final audit bundle preserves the accepted144 contract-review snapshot and adds the actual145 delivery evidence separately. No changing PC snapshot was probed, no inherited foundation was rebuilt, and no new mathematical axiom was introduced.
'''
(doc / 'chapter34_frontier_delivery.md').write_text(summary)
print(json.dumps({'static_status': status, 'static_exit_code': args.static_exit_code,
    'diagnostic': reason, 'delivery_record': str(ev / 'delivery_status.json')}, indent=2))

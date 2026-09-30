#!/usr/bin/env python3
"""Validate the frozen report/evidence plan; copy only on explicit --apply."""
import argparse
import hashlib
import json
from pathlib import Path

PREFIX = Path('GC_CHAPTER3_435_RC3/docs/geometrization/chapter3')
EV = PREFIX / 'evidence/chapter34_frontier_146'
INDEX = EV / 'index.json'


def digest(data):
    return hashlib.sha256(data).hexdigest()



def validate_accepted145(plan, get_bytes):
    import re
    m = plan['milestone145']
    assert m['status'] == 'accepted_and_remote_verified'
    commit = m['accepted_commit']
    assert re.fullmatch(r'[0-9a-f]{40}', commit)
    def evidence(role):
        row = m['evidence'][role]
        data = get_bytes(row['destination'])
        assert digest(data) == row['sha256'], role
        return data
    receipt_raw = evidence('milestone_receipt')
    shared_raw = evidence('shared_receipt')
    receipt, shared = json.loads(receipt_raw), json.loads(shared_raw)
    manifest = json.loads(evidence('manifest'))
    checks = json.loads(evidence('canonical_checks'))
    remote = json.loads(evidence('remote_verification'))
    assert receipt['success'] is True and receipt['milestone'] == 145
    assert receipt['full_migrated_root_built'] is False
    assert shared['success'] is True
    assert shared['build']['exit_code'] == shared['axiom_audit']['exit_code'] == 0
    assert receipt['shared_gate_receipt_sha256'] == digest(shared_raw)
    assert m['verification_sha256'] == digest(receipt_raw)
    assert m['verification_receipt'] == m['evidence']['milestone_receipt']['destination']
    assert shared['git_head_at_check'] == receipt['git_head_at_check'] == checks['git_head_at_check']
    source_map = {s['path']: s['sha256'] for s in shared['sources']}
    assert len(source_map) == len(shared['sources'])
    manifest_paths = [item['path'] for item in manifest['modules']]
    assert len(manifest_paths) == len(set(manifest_paths))
    assert set(manifest_paths) == set(source_map)
    assert all(re.fullmatch(r'[0-9a-f]{64}', h) for h in source_map.values())
    assert receipt['sources'] and all(source_map.get(p) == h for p, h in receipt['sources'].items())
    assert checks['success'] is True and checks['review_exit_code'] == 0
    assert checks['source_copy_checks'] and all(c['exit_code'] == 0 for c in checks['source_copy_checks'])
    assert checks['production_sources'] == receipt['sources']
    assert digest(evidence('canonical_checks')) == receipt['checks_receipt_sha256']
    review = evidence('canonical_review_log')
    lint = evidence('canonical_lint_log')
    assert lint == b'' and digest(lint) == checks['lint_log_sha256']
    assert digest(review) == checks['review_log_sha256']
    parsed = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", review.decode(), re.S)
    assert [name for name, _ in parsed] == checks['review_reports']
    assert len(parsed) == receipt['expected_review_reports']
    assert not any(t in review.decode() for t in ('error:', 'warning:', 'sorryAx'))
    assert all({a.strip() for a in axioms.split(',') if a.strip()} <=
               {'propext', 'Classical.choice', 'Quot.sound'} for _, axioms in parsed)
    build, axioms = evidence('build_log'), evidence('axioms_log')
    assert digest(build) == shared['build']['log_sha256']
    assert digest(axioms) == shared['axiom_audit']['log_sha256']
    jobs = re.findall(r'Build completed successfully \((\d+) jobs\)\.', build.decode())
    owned = re.findall(r'^CHAPTER3_AUDIT_PASS (\d+) declarations\s*$', axioms.decode(), re.M)
    assert jobs and len(set(jobs)) == 1 and owned and len(set(owned)) == 1
    observed = (len(source_map), int(owned[0]), int(jobs[0]))
    assert observed == (receipt['combined_modules'], receipt['combined_owned_declarations'], receipt['combined_jobs'])
    assert observed == (m['observed_modules'], m['observed_owned_declarations'], m['observed_jobs'])
    baseline = get_bytes(str(EV / 'accepted144_milestone_verification.json'))
    assert receipt['previous_milestone_receipt_sha256'] == digest(baseline)
    assert json.loads(baseline)['milestone'] == plan['accepted_baseline']['milestone'] == 144
    assert receipt['new_concrete_regressions'] >= 0
    assert remote['exact_match'] is True
    assert remote['push_exit_code'] == remote['remote_verification_exit_code'] == 0
    assert remote['accepted_commit'] == remote['remote_head'] == commit
    assert m['remote_push_confirmation']['record_sha256'] == digest(evidence('remote_verification'))
    assert remote['remote_url'] and remote['verified_at_utc'] and remote['branch']
    ref = 'refs/heads/' + remote['branch']
    command = remote['verification_command']
    assert isinstance(command, list) and command and all(isinstance(v, str) for v in command)
    assert command[0] == 'git' and 'ls-remote' in command
    assert command[-2] == m['remote_push_confirmation']['remote_name'] and command[-1] == ref
    lines = [line.split() for line in remote['verification_stdout'].splitlines() if line.strip()]
    assert lines == [[commit, ref]]
    assert m['remote_push_confirmation']['ref'] == ref
    static = receipt['blueprint_static_audit']
    assert static['status'] in ('passed', 'failed', 'pending')
    if static['status'] == 'passed':
        assert static.get('success') is True and static.get('latest_completed_exit_code') == 0
    else:
        assert static.get('success') is False
        code = static.get('latest_completed_exit_code')
        assert isinstance(code, int) and not isinstance(code, bool) and code != 0
    return receipt, shared, remote

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--plan', type=Path,
                        default=Path(__file__).with_name('index.json'))
    parser.add_argument('--apply', action='store_true')
    parser.add_argument('--destination-root', type=Path)
    parser.add_argument('--verify-destination-root', type=Path)
    parser.add_argument('--validation-output', type=Path)
    args = parser.parse_args()
    if args.verify_destination_root is not None and (args.apply or args.destination_root is not None):
        parser.error('--verify-destination-root is read-only and cannot be combined with --apply')
    if args.verify_destination_root is not None:
        args.verify_destination_root = args.verify_destination_root.resolve()
    raw = args.plan.read_bytes()
    plan = json.loads(raw)
    assert plan['accepted_baseline']['commit'] == '9f5f8d2c624110d0bc79d3ddebfb655112d57100'
    assert plan['milestone145']['status'] == 'accepted_and_remote_verified'
    assert plan['full_chapters_complete'] is False
    assert plan['new_registered_production_theorems'] == 0
    rows = []
    seen = set()
    for item in plan['copies']:
        relative = Path(item['destination'])
        source = (args.verify_destination_root / relative if args.verify_destination_root is not None
                  else Path(item['source']))
        assert source.is_absolute() and source.is_file(), str(source)
        assert not relative.is_absolute() and '..' not in relative.parts
        assert (relative == PREFIX / 'chapter34_frontier.md' or
                relative.is_relative_to(PREFIX / 'evidence/chapter34_frontier_146')), str(relative)
        assert relative not in seen, str(relative)
        seen.add(relative)
        data = source.read_bytes()
        assert digest(data) == item['sha256'], f'Changed source: {source}'
        rows.append((relative, data))
    copied = {str(relative): content for relative, content in rows}
    validate_accepted145(plan, copied.__getitem__)
    assert INDEX not in seen
    rows.append((INDEX, raw))
    if args.verify_destination_root is not None:
        assert (args.verify_destination_root / INDEX).read_bytes() == raw
    if args.apply:
        if args.destination_root is None:
            parser.error('--apply requires --destination-root')
        root = args.destination_root.resolve()
        for relative, data in rows:
            target = root / relative
            assert target.resolve().is_relative_to(root), str(target)
            if target.exists():
                assert target.is_file() and target.read_bytes() == data, \
                    f'Refusing to replace different existing bytes: {target}'
        for relative, data in rows:
            target = root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            if not target.exists():
                target.write_bytes(data)
            assert target.read_bytes() == data
    elif args.destination_root is not None:
        parser.error('--destination-root requires --apply')
    result = {'status': 'passed', 'mode': ('copy' if args.apply else 'verify_copied_destination'
                       if args.verify_destination_root is not None else 'validate_only'),
              'plan_sha256': digest(raw), 'copied_or_validated_files': len(rows),
              'total_bytes': sum(len(data) for _, data in rows),
              'destination_root': str(args.destination_root) if args.apply else
                                  str(args.verify_destination_root) if args.verify_destination_root else None,
              'production_or_live_manifest_paths': False,
              'build_commands_executed': False,
              'sources_unchanged': True}
    if args.validation_output is not None:
        args.validation_output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()

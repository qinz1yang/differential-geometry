"""Exercise the joint static gate against in-memory corruptions; do not edit build inputs."""
from contextlib import redirect_stdout
import copy
import io
import json
from pathlib import Path
from unittest.mock import patch

import check_integration as gate


def main():
    rec = gate.read_json(gate.MANIFEST)
    independent = next(m['path'] for m in rec['modules'] if m['role'] == 'independent')
    foundation = next(m['path'] for m in rec['modules'] if m['role'] == 'geometrization_foundation')
    skeleton = next(m['path'] for m in rec['modules'] if m['role'] == 'skeleton')
    crosswalk = 'docs/geometrization/skeleton/' + gate.CROSSWALKS[0]
    original_read = Path.read_text

    def moved_locator(raw):
        data = json.loads(raw)
        data['declarations'][0]['blueprint'][0]['label_line'] += 1
        return json.dumps(data)

    cases = [
        ('independent_kernel_bypass', independent, lambda s: s+'\nset_option debug.skipKernelTC true\n'),
        ('skeleton_extra_option', skeleton, lambda s: s+'\nset_option maxHeartbeats 0\n'),
        ('foundation_new_option', foundation, lambda s: s+'\nset_option maxHeartbeats 0\n'),
        ('unregistered_admission', independent, lambda s: s+'\ntheorem hidden : True := by sorry\n'),
        ('incorrect_source_label', crosswalk, moved_locator),
    ]
    rows = []
    with redirect_stdout(io.StringIO()):
        gate.static_check(copy.deepcopy(rec), prepare=True)
    for label, relative, corrupt in cases:
        target = gate.ROOT / relative

        def fixture_read(path, *args, **kwargs):
            text = original_read(path, *args, **kwargs)
            return corrupt(text) if path == target else text

        rejected = False
        with patch.object(Path, 'read_text', fixture_read), redirect_stdout(io.StringIO()):
            try:
                gate.static_check(copy.deepcopy(rec), prepare=True)
            except AssertionError as exc:
                rejected = True
                reason = str(exc)
        assert rejected, 'Joint gate accepted negative fixture '+label
        rows.append(dict(fixture=label, rejected=True, reason=reason))
    with redirect_stdout(io.StringIO()):
        gate.static_check(rec)
    receipt = dict(success=True, scope='in-memory source/locator corruption; full joint static gate',
        manifest_sha256=gate.sha(gate.MANIFEST), gate_sha256=gate.sha(Path(gate.__file__)),
        test_sha256=gate.sha(Path(__file__)), fixtures=rows)
    (gate.DOC/'evidence/negative_fixtures.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print('Joint static gate rejected all',len(rows),'negative fixtures; live sources unchanged')


if __name__ == '__main__':
    main()

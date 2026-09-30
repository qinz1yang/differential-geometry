"""Verify the subject-placement migration and proof-token preservation."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
RECORD = ROOT/'docs/geometrization/MODULE_PLACEMENT.json'


def uncomment(s):
    out, i, depth = [], 0, 0
    while i < len(s):
        if depth:
            if s.startswith('/-', i):
                depth += 1
                i += 2
            elif s.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                if s[i] == '\n':
                    out.append('\n')
                i += 1
        elif s.startswith('/-', i):
            out.append(' ')
            depth = 1
            i += 2
        elif s.startswith('--', i):
            j = s.find('\n', i)
            i = len(s) if j < 0 else j
        elif s[i] == '"':
            out.append(s[i])
            i += 1
            while i < len(s):
                c = s[i]
                out.append(c)
                i += 1
                if c == '\\' and i < len(s):
                    out.append(s[i])
                    i += 1
                elif c == '"':
                    break
        else:
            out.append(s[i])
            i += 1
    assert depth == 0, 'Unclosed source comment'
    return ''.join(out)


def body_tokens(s):
    # Token equality after erasing imports/comments; strings remain intact.
    s = re.sub(r'^import [^\n]+\n', '', uncomment(s), flags=re.M)
    return re.findall(r'"(?:\\.|[^"\\])*"|[^\s]+', s)


def verify_layout(proofs=False):
    rec = json.loads(RECORD.read_text())
    paths = rec['module_paths']
    assert len(paths) == len(set(paths)) == rec['expected_new_modules']
    root = (ROOT/'DifferentialGeometry.lean').read_text()
    for p in paths:
        assert p.startswith('DifferentialGeometry/'), p
        assert (ROOT/p).is_file(), p
        assert 'import '+p[:-5].replace('/', '.')+'\n' in root, p
        assert not re.search(r'^import (?:Geometrization|DifferentialGeometry)\s*$',
                             (ROOT/p).read_text(), re.M), p
    for p in rec['retired_aggregates']:
        assert not (ROOT/p).exists(), p
    for folder in ('Geometrization', 'GeometrizationChecks'):
        assert not (ROOT/folder).exists(), folder
    for p in ROOT.rglob('*.lean'):
        rel = p.relative_to(ROOT)
        if rel.parts[0] in ('.lake', '.git'):
            continue
        assert rel.parts[0] == 'DifferentialGeometry' or str(rel) == 'DifferentialGeometry.lean', rel
    for e in rec['archived_sources']:
        assert not (ROOT/e['old_path']).exists(), e['old_path']
        assert hashlib.sha256((ROOT/e['path']).read_bytes()).hexdigest() == e['sha256'], e['path']
    audit_path = next(p for p in paths if p.endswith('/Checks/AxiomAudit.lean'))
    audit = (ROOT/audit_path).read_text()
    guarded = re.search(r'unless \(\[(.*?)\] : List Name\).contains mod do', audit, re.S)
    assert guarded
    assert set(re.findall(r'`([\w.]+)', guarded[1])) == {p[:-5].replace('/', '.') for p in paths}
    for e in rec['modules'] + rec['split_outputs']:
        raw = (ROOT/e['path']).read_bytes()
        assert hashlib.sha256(raw).hexdigest() == e['sha256'], e['path']
        if not e.get('vendor'):
            assert not re.search(r'/[-*]|--', uncomment(raw.decode())), e['path']
            # Comment removal must leave the source unchanged except whitespace.
            assert re.sub(r'\s+', '', raw.decode()) == re.sub(r'\s+', '', uncomment(raw.decode())), e['path']
    if proofs:
        for e in rec['modules']:
            old = subprocess.check_output(['git', 'show', rec['source_commit']+':'+e['old_path']],
                                          cwd=ROOT, text=True)
            assert hashlib.sha256(old.encode()).hexdigest() == e['source_sha256']
            new = (ROOT/e['path']).read_text()
            if e['old_path'].endswith('/CompactFundamentalGroup.lean'):
                split = next(x['path'] for x in rec['split_outputs'] if x['original'] == e['old_path'])
                for ns, target in [('GC.Topology', new), ('GC.GeneralFlow', (ROOT/split).read_text())]:
                    pattern = r'namespace '+re.escape(ns)+r'\b.*?end '+re.escape(ns)
                    assert body_tokens(re.search(pattern, old, re.S)[0]) == body_tokens(re.search(pattern, target, re.S)[0]), ns
            elif e['old_path'].endswith('/StandardPrimes.lean'):
                split = next(x['path'] for x in rec['split_outputs'] if x['original'] == e['old_path'])
                for ns, target in [('GC.Endpoint', new), ('GC.Group', (ROOT/split).read_text())]:
                    pattern = r'namespace '+re.escape(ns)+r'\b.*?end '+re.escape(ns)
                    assert body_tokens(re.search(pattern, old, re.S)[0]) == body_tokens(re.search(pattern, target, re.S)[0]), ns
            elif e['old_path'].endswith('/Axioms.lean'):
                old = old.replace('unless (`Geometrization).isPrefixOf mod || (`GeometrizationChecks).isPrefixOf mod do', guarded[0])
                assert body_tokens(old) == body_tokens(new), e['path']
            else:
                assert body_tokens(old) == body_tokens(new), e['path']
    return rec


if __name__ == '__main__':
    r = verify_layout(proofs=True)
    print(f"Placement and proof preservation passed: {len(r['module_paths'])} leaves, {len(r['archived_sources'])} archived sources.")

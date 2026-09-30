#!/usr/bin/env python3
"""Negative integration test for the Lean axiom gate, in an isolated directory.

Run after the normal build. The fixture is never added to the accepted library.
Both a new mathematical axiom and a proof placeholder must be rejected. Uses the
same audit command as the production gate, without importing the large library.
"""
import json
import os
import pathlib
import re
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]


def main():
    lean = subprocess.check_output(['lake', 'env', 'which', 'lean'], cwd=ROOT, text=True).strip()
    env = dict(os.environ)
    env['LEAN_PATH'] = subprocess.check_output(
        ['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=ROOT, text=True).strip()
    audit = (ROOT/'DifferentialGeometry/Geometry/Flow/RicciFlow/Surgery/Geometrization/Checks/AxiomAudit.lean').read_text()
    audit = audit[audit.index('open Lean Elab Command'):]
    audit = re.sub(r'unless \(\[.*?\] : List Name\).contains mod do',
                   'unless mod == `DifferentialGeometry.NegativeFixture do', audit, flags=re.S)
    results = []
    with tempfile.TemporaryDirectory(prefix='gc-axiom-gate-') as tmp:
        base = pathlib.Path(tmp)
        folder = base/'DifferentialGeometry'
        folder.mkdir(parents=True)
        fixture = folder/'NegativeFixture.lean'
        target = fixture.with_suffix('.olean')
        driver = base/'Check.lean'
        driver.write_text('import DifferentialGeometry.NegativeFixture\nimport Lean\n\n'+audit)
        env['LEAN_PATH'] = str(base)+os.pathsep+env['LEAN_PATH']
        fixtures = [
            ('standard', 'theorem GC.testGateTrue : True := True.intro\n', True),
            ('new-axiom', 'axiom GC.testGateFalse : False\n', False),
            ('placeholder', 'theorem GC.testGateFalse : False := by sorry\n', False),
        ]
        for name, source, should_pass in fixtures:
            fixture.write_text(source)
            built = subprocess.run([lean, '-R', str(base), '-o', str(target), str(fixture)],
                                   env=env, cwd=base, text=True, capture_output=True)
            assert built.returncode == 0, built.stdout+built.stderr
            checked = subprocess.run([lean, '-R', str(base), str(driver)], env=env,
                                     cwd=base, text=True, capture_output=True)
            output = checked.stdout+checked.stderr
            if should_pass:
                assert checked.returncode == 0 and 'Team axiom audit passed' in output, output
            else:
                assert checked.returncode != 0 and 'Unapproved axiom' in output, output
                expected = 'sorryAx' if name == 'placeholder' else 'GC.testGateFalse'
                assert expected in output, output
            results.append(dict(case=name, expected_pass=should_pass,
                                audit_exit_code=checked.returncode, output=output))
            print(f'{name}: expected result observed', flush=True)
    out = ROOT/'.lake/gc'
    out.mkdir(parents=True, exist_ok=True)
    (out/'gate-negative-tests.json').write_text(json.dumps(results, indent=2)+'\n')


if __name__ == '__main__':
    main()

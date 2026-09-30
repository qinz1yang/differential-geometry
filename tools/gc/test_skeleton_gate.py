#!/usr/bin/env python3
"""Compile isolated fixtures against the actual generated skeleton audit and source gate."""
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from check_skeleton import ROOT, AUDIT, validate_source


def main():
    lean = subprocess.check_output(['lake', 'env', 'which', 'lean'], cwd=ROOT, text=True).strip()
    env = dict(os.environ)
    env['LEAN_PATH'] = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'],
                                              cwd=ROOT, text=True).strip()
    audit = (ROOT / AUDIT).read_text()
    audit = audit[audit.index('open Lean Elab Command'):]
    results = []
    with tempfile.TemporaryDirectory(prefix='gc-skeleton-negative-') as tmp:
        base = Path(tmp)
        (base / 'GateFixture').mkdir()
        env['LEAN_PATH'] = str(base) + os.pathsep + env['LEAN_PATH']

        def compile_file(path, source, output=None):
            path.write_text(source)
            cmd = [lean, '-R', str(base)]
            if output is not None:
                cmd += ['-o', str(output)]
            return subprocess.run(cmd + [str(path)], cwd=base, env=env,
                                  text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

        dependency = base / 'GateFixture/Dependency.lean'
        built = compile_file(dependency, 'axiom ExternalSeed.seed : False\n', dependency.with_suffix('.olean'))
        assert built.returncode == 0, built.stdout
        fixtures = [
            ('standard', 'theorem GateFixture.good : True := True.intro\n', [], ['GateFixture.good'], None),
            ('unchecked-name', 'theorem GateFixture.good : True := True.intro\n', [], ['GateFixture.missing'], 'Unchecked declaration'),
            ('axiom', 'axiom GateFixture.bad : False\n', [], [], 'Unexpected axiom or unsafe declaration'),
            ('unsafe', 'unsafe def GateFixture.bad : Nat := 0\n', [], [], 'Unexpected axiom or unsafe declaration'),
            ('type-admission', 'theorem GateFixture.bad : (sorry : Prop) := by sorry\n', [], [], 'Admission in declaration type'),
            ('external-axiom', 'import GateFixture.Dependency\ntheorem GateFixture.bad : False := ExternalSeed.seed\n', [], [], 'Unexpected axiom ExternalSeed.seed'),
            ('unregistered', 'theorem GateFixture.bad : False := by sorry\n', [], [], 'Unregistered direct admission'),
            ('registered', 'theorem GateFixture.bad : False := by sorry\n', ['GateFixture.bad'], ['GateFixture.bad'], None),
            ('count', 'theorem GateFixture.good : True := True.intro\n', ['GateFixture.good'], [], 'Expected 1 direct admissions'),
            ('empty', 'theorem GateFixture.good : True := True.intro\n', [], [], 'Empty skeleton audit'),
            ('skip-kernel', 'set_option debug.skipKernelTC true in\ntheorem GateFixture.skipped : 1 + 1 = 2 := rfl\ntheorem GateFixture.normal : 1 + 1 = 2 := rfl\n', [], [], None),
        ]
        for case, source, expected, authored, message in fixtures:
            fixture = base / 'GateFixture/Test.lean'
            built = compile_file(fixture, source, fixture.with_suffix('.olean'))
            assert built.returncode == 0, (case, built.stdout)
            code = audit
            for variable, names in [('owned', ['GateFixture.Absent'] if case == 'empty' else ['GateFixture.Test']),
                                    ('expected', expected), ('authored', authored)]:
                code, count = re.subn(r'let ' + variable + r' : List Name := \[[^\n]*\]',
                    'let ' + variable + ' : List Name := [' + ', '.join('`' + n for n in names) + ']', code)
                assert count == 1, (variable, count)
            driver = base / 'Driver.lean'
            checked = compile_file(driver, 'import GateFixture.Test\nimport Lean\n' + code)
            if message is None:
                assert checked.returncode == 0 and 'Skeleton declaration audit:' in checked.stdout, (case, checked.stdout)
            else:
                assert checked.returncode != 0 and message in checked.stdout, (case, checked.stdout)
            static_rejection = None
            if case == 'skip-kernel':
                try:
                    validate_source(source, fixture)
                except AssertionError as error:
                    static_rejection = str(error)
                assert static_rejection and 'Forbidden set_option' in static_rejection
            results.append(dict(case=case, fixture_exit=built.returncode, audit_exit=checked.returncode,
                                expected_error=message, fixture_output=built.stdout,
                                audit_output=checked.stdout, static_rejection=static_rejection))
            print(f'{case}: PASS' + (f' ({message})' if message else '') +
                  (' (compiled fixture rejected by static set_option gate)' if static_rejection else ''), flush=True)
    out = ROOT / 'docs/geometrization/skeleton/evidence/negative_tests.json'
    out.write_text(json.dumps(results, indent=2) + '\n')
    print(f'SKELETON_NEGATIVE_TESTS_PASS: {len(results)} cases', flush=True)


if __name__ == '__main__':
    main()

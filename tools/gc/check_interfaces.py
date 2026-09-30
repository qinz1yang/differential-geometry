#!/usr/bin/env python3
"""Check actual applications of the area barrier in the unified skeleton environment."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
from check_skeleton import ROOT, MANIFEST, verify_pins


def main():
    rec = json.loads(MANIFEST.read_text())
    verify_pins(rec)
    doc = ROOT / 'docs/geometrization/skeleton/interface_applications.md'
    blocks = re.findall(r'```lean\n(.*?)```', doc.read_text(), re.S)
    assert len(blocks) == 1
    names = []

    def name_example(_):
        name = 'interface_application_' + str(len(names) + 1)
        names.append(name)
        return 'theorem ' + name + ' '

    code = re.sub(r'^example\s+', name_example, blocks[0], flags=re.M)
    assert names and not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b', code)
    code = 'import Lean\n' + code
    code += '\nopen Lean Elab Command\n'
    for name in names:
        code += f'\n#print axioms {name}\nrun_cmd do\n'
        code += f'  let axs ← collectAxioms `{name}\n'
        code += '  for ax in axs do\n'
        code += '    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do\n'
        code += '      throwError "Untrusted interface application axiom {ax}"\n'
        code += f'  logInfo "INTERFACE_APPLICATION {name}"\n'
    code += '''
run_cmd do
  let old ← getConstInfo ``DifferentialGeometry.Analysis.not_nonnegative_area_upper_barriers_shift
  let proved ← getConstInfo ``DifferentialGeometry.Analysis.false_of_area_upper_barriers
  unless ← liftTermElabM <| Meta.isDefEq old.type proved.type do
    throwError "Area contracts differ"
  logInfo "AREA_CONTRACT_DEFINITIONALLY_EQUAL"
'''
    out = ROOT / 'docs/geometrization/skeleton/evidence/interfaces'
    out.mkdir(parents=True, exist_ok=True)
    result = subprocess.run(['lake', 'env', 'lean', '--stdin'], input=code,
                            cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (out / 'applications.log').write_text(result.stdout)
    assert result.returncode == 0, result.stdout
    markers = re.findall(r'^INTERFACE_APPLICATION (\S+)$', result.stdout, re.M)
    assert markers == names, (markers, names)
    assert 'AREA_CONTRACT_DEFINITIONALLY_EQUAL' in result.stdout
    receipt = dict(success=True, applications=len(markers), application_names=markers,
                   exact_contract_definitionally_equal=True,
                   toolchain=rec['toolchain'], mathlib_commit=rec['mathlib_commit'],
                   applications_sha256=hashlib.sha256(code.encode()).hexdigest(),
                   log_sha256=hashlib.sha256(result.stdout.encode()).hexdigest(),
                   scope='Freshly elaborated scalar endpoint, varying-target induced-map, and empty-family examples')
    (out / 'verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(f'INTERFACE_AUDIT_PASS: {len(markers)} positive application markers; standard axioms; exact contract')


if __name__ == '__main__':
    main()

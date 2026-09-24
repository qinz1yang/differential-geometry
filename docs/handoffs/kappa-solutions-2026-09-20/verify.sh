#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../../.."
evidence=$(mktemp -d /private/tmp/wt17-kappa-verification.XXXXXX)
printf 'Verification directory: %s\n' "$evidence"
lean_options=(-Dpp.unicode.fun=true -DmaxSynthPendingDepth=3 -DautoImplicit=false
  -Dweak.linter.mathlibStandardSet=true -Dlinter.style.header=false -Dlinter.style.longLine=false)
modules=(
  DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Cylinder
  DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CylinderPreservation
  DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.AncientRankOne
  DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticShrinker
  DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticShrinkerNormalization
  DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalCurvatureTrichotomy
  DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSplitting
)
git rev-parse HEAD > "$evidence/commit.txt"
git status --porcelain=v1 > "$evidence/status.txt"
lake env lean --version > "$evidence/lean-version.txt"
lake --version > "$evidence/lake-version.txt"
lake build "${modules[@]}" > "$evidence/modules-build.log" 2>&1
for module in "${modules[@]}"; do
  source_file=${module//.//}.lean
  lake env lean "${lean_options[@]}" "$source_file" > "$evidence/${module##*.}.log" 2>&1
  test ! -s "$evidence/${module##*.}.log"
done
lake build DifferentialGeometry > "$evidence/root-build.log" 2>&1
cat > "$evidence/audit.lean" <<'LEAN_AUDIT'
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticShrinker
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticShrinkerNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalCurvatureTrichotomy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSplitting
open Lean Elab Command Batteries.Tactic.Lint in
run_cmd liftCoreM do
  let decls := #[`DifferentialGeometry.PDE.RicciFlow.laplacian_height_eq_zero_of_initial_cylinder, `DifferentialGeometry.PDE.RicciFlow.normGradSqFun_height_eq_one_of_initial_cylinder, `DifferentialGeometry.PDE.RicciFlow.covariantDerivative_gradFun_height_eq_zero_of_initial_cylinder, `DifferentialGeometry.PDE.RicciFlow.curvatureOperatorImageAt_finrank_le_one_of_initial_cylinder, `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_backward_slice_asymptotic_shrinker, `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_samePole_normalized_asymptotic_shrinker, `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.klim_terminal_curvature_trichotomy, `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_fixed_universal_cover_product_of_null_plane, `DifferentialGeometry.PDE.RicciFlow.curvatureOperatorImageAt_finrank_eq_one_of_complete_ancient_rank_one]
  let linters := (← getChecks true none none).filter fun l => l.name != `docBlame && l.name != `docBlameThm
  let results ← lintCore decls linters
  if results.any (!·.2.isEmpty) then
    throwError (← formatLinterResults results decls false "Four kappa headlines and ancient rank" true .low linters.size)
  IO.println s!"Checked {decls.size} declarations and {linters.size} linters."
#print axioms DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_backward_slice_asymptotic_shrinker
#check @DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_backward_slice_asymptotic_shrinker
#print axioms DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_samePole_normalized_asymptotic_shrinker
#check @DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_samePole_normalized_asymptotic_shrinker
#print axioms DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.klim_terminal_curvature_trichotomy
#check @DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.klim_terminal_curvature_trichotomy
#print axioms DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_fixed_universal_cover_product_of_null_plane
#check @DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_fixed_universal_cover_product_of_null_plane
#print axioms DifferentialGeometry.PDE.RicciFlow.curvatureOperatorImageAt_finrank_eq_one_of_complete_ancient_rank_one
#check @DifferentialGeometry.PDE.RicciFlow.curvatureOperatorImageAt_finrank_eq_one_of_complete_ancient_rank_one
#print axioms DifferentialGeometry.PDE.RicciFlow.laplacian_height_eq_zero_of_initial_cylinder
#check @DifferentialGeometry.PDE.RicciFlow.laplacian_height_eq_zero_of_initial_cylinder
#print axioms DifferentialGeometry.PDE.RicciFlow.normGradSqFun_height_eq_one_of_initial_cylinder
#check @DifferentialGeometry.PDE.RicciFlow.normGradSqFun_height_eq_one_of_initial_cylinder
#print axioms DifferentialGeometry.PDE.RicciFlow.covariantDerivative_gradFun_height_eq_zero_of_initial_cylinder
#check @DifferentialGeometry.PDE.RicciFlow.covariantDerivative_gradFun_height_eq_zero_of_initial_cylinder
#print axioms DifferentialGeometry.PDE.RicciFlow.curvatureOperatorImageAt_finrank_le_one_of_initial_cylinder
#check @DifferentialGeometry.PDE.RicciFlow.curvatureOperatorImageAt_finrank_le_one_of_initial_cylinder
LEAN_AUDIT
cat > "$evidence/debt.lean" <<'LEAN_DEBT'
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureBlowup
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientExtensionLimitInputs
import Lean.Util.FoldConsts
open Lean Elab Command in
run_cmd liftCoreM do
  let env ← getEnv
  let mut pending := #[`DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.arbitrary_high_curvature_blowup]
  let mut seen : NameSet := {}
  let mut debt : Array Name := #[]
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if !seen.contains n then
      seen := seen.insert n
      if let some c := env.find? n then
        let deps := c.getUsedConstantsAsSet
        if deps.contains `sorryAx then
          debt := debt.push n
        for d in deps do
          pending := pending.push d
  for n in debt do
    IO.println s!"REACHABLE_SORRY {n}"
#print axioms DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.arbitrary_high_curvature_blowup
#print axioms DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.good_point_derivatives
#print axioms DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.first_backward_slab
#print axioms DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.local_propagation
#print axioms DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ancientExtension_nonempty_of_halfLineAncientLimitFrontier
LEAN_DEBT
python3 - "$evidence" <<'PY_COMPAT'
from pathlib import Path
import re
import subprocess
import sys
out = Path(sys.argv[1])
base = '7c2e6848cb8678a932191bc810a64ecd803627ba'
prefix = 'DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/KappaSolutions/'
pairs = [
 ('AsymptoticShrinker', 'exists_backward_slice_asymptotic_shrinker', 'F hF tau htau hescape'),
 ('AsymptoticShrinkerNormalization', 'exists_samePole_normalized_asymptotic_shrinker', 'F hF p tau htau hescape'),
 ('TerminalCurvatureTrichotomy', 'klim_terminal_curvature_trichotomy', ''),
 ('AncientSplitting', 'ancient_fixed_universal_cover_product_of_null_plane', ''),
]
imports = ''.join('import ' + (prefix + stem).replace('/', '.') + '\n' for stem, _, _ in pairs[:2])
parts = [imports]
checks = []
for i, (stem, name, args) in enumerate(pairs):
 path = prefix + stem + '.lean'
 current = Path(path).read_text()
 original = subprocess.check_output(['git', 'show', base + ':' + path], text=True)
 marker = 'theorem ' + name
 def statement(text):
  return text[text.index(marker):text.index(':= by', text.index(marker))]
 old, new = statement(original), statement(current)
 if i < 2:
  expected = old.replace('(hdim : 2 ≤ Module.finrank ℝ E)', '')
  assert re.sub(r'\s+', ' ', expected).strip() == re.sub(r'\s+', ' ', new).strip(), name
  preamble = current[:current.index(marker)].split('noncomputable section', 1)[1]
  ns = 'DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions'
  nested = ns + '.OriginalContract' + str(i)
  preamble = preamble.replace('namespace ' + ns, 'namespace ' + nested, 1)
  parts.append('noncomputable section\n' + preamble + old.replace(marker, 'example', 1)
    + ':= by\n  let _ := hdim\n  exact ' + name + ' ' + args + '\n\nend ' + nested + '\n')
  checks.append(name + ': only the dimension lower-bound binder was removed; original corollary generated.')
 else:
  assert old == new, name
  checks.append(name + ': original declaration text unchanged.')
(out / 'original-statements.lean').write_text('\n'.join(parts))
(out / 'statement-comparison.txt').write_text('\n'.join(checks) + '\n')
PY_COMPAT
lake env lean "${lean_options[@]}" "$evidence/original-statements.lean" > "$evidence/original-statements.log" 2>&1
test ! -s "$evidence/original-statements.log"
lake env lean "${lean_options[@]}" "$evidence/audit.lean" > "$evidence/audit.log" 2>&1
lake env lean "${lean_options[@]}" "$evidence/debt.lean" > "$evidence/debt.log" 2>&1
rg -n '^\s*sorry\s*$' DifferentialGeometry | LC_ALL=C sort > "$evidence/sorry-inventory.txt"
python3 - "$evidence" <<'PY_RESULTS'
from pathlib import Path
import re
import sys
p = Path(sys.argv[1])
for filename in ['modules-build.log', 'root-build.log']:
 text = (p / filename).read_text()
 assert 'Build completed successfully' in text, filename
 for line in text.splitlines():
  if re.search(r'(^|\s)(error:|warning:|info:|trace:)|Try this', line):
   assert line.startswith('warning: ') and line.endswith('declaration uses `sorry`'), line
root_warnings = [line for line in (p / 'root-build.log').read_text().splitlines() if line.startswith('warning: ')]
assert len(root_warnings) == 21, root_warnings
text = (p / 'audit.log').read_text()
assert 'Checked 9 declarations and 13 linters.' in text
assert not re.search(r'warning:|error:|Try this', text)
closures = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", text)
assert len(closures) == 9, len(closures)
for name, axioms in closures:
 assert {a.strip() for a in axioms.split(',')} == {'propext', 'Classical.choice', 'Quot.sound'}, (name, axioms)
text = (p / 'debt.log').read_text()
assert not re.search(r'warning:|error:|Try this', text)
reached = {line.rsplit('.', 1)[-1] for line in text.splitlines() if line.startswith('REACHABLE_SORRY ')}
assert reached == {'bounded_curvature_at_distance', 'terminal_limit_global_bound', 'ancient_extension'}, reached
inventory = (p / 'sorry-inventory.txt').read_text().splitlines()
assert len(inventory) == 21 and len({line.split(':')[0] for line in inventory}) == 11
assert not any('/KappaSolutions/' in line for line in inventory)
print('PASS: root build; seven freshly elaborated sources; 9 declarations x 13 linters; standard axioms only.')
print('PASS: original statement compatibility; 21 retained sorries in 11 files; exactly 3 reachable blowup blockers.')
PY_RESULTS
git diff --check
printf 'Evidence retained outside the repository at %s\n' "$evidence"

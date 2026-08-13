import DifferentialGeometry.Tensor.Auxiliary.Perm
import DifferentialGeometry.Tensor.Auxiliary.Shuffle.Placement
import DifferentialGeometry.Tensor.Auxiliary.Shuffle.Decomposition
import DifferentialGeometry.Tensor.Alternating.Wedge
import DifferentialGeometry.Tensor.Exterior.Defs
import DifferentialGeometry.Tensor.Exterior.Basic
import DifferentialGeometry.Tensor.Exterior.Pullback
import DifferentialGeometry.Tensor.Exterior.Cochain
import DifferentialGeometry.Tensor.Exterior.Leibniz
import DifferentialGeometry.Tensor.Exterior.ModelDifferentialForm
import DifferentialGeometry.Analysis.Calculus.AnalyticTransfer
import DifferentialGeometry.Tensor.Alternating.Comp

open Batteries.Tactic.Lint Lean Elab Command

run_cmd do
  let env ← getEnv
  let targetModules : Array Name := #[
  `DifferentialGeometry.Tensor.Auxiliary.Perm,
  `DifferentialGeometry.Tensor.Auxiliary.Shuffle.Placement,
  `DifferentialGeometry.Tensor.Auxiliary.Shuffle.Decomposition,
  `DifferentialGeometry.Tensor.Alternating.Wedge,
  `DifferentialGeometry.Tensor.Exterior.Defs,
  `DifferentialGeometry.Tensor.Exterior.Basic,
  `DifferentialGeometry.Tensor.Exterior.Pullback,
  `DifferentialGeometry.Tensor.Exterior.Cochain,
  `DifferentialGeometry.Tensor.Exterior.Leibniz,
  `DifferentialGeometry.Tensor.Exterior.ModelDifferentialForm,
  `DifferentialGeometry.Analysis.Calculus.AnalyticTransfer,
  `DifferentialGeometry.Tensor.Alternating.Comp]
  let checks ← liftCoreM <| getChecks (slow := true) (runOnly := none) (runAlways := none)
  let excluded := #[`docBlame, `docBlameThm]
  let mut found := false
  let mut covered := 0
  for (decl, _) in env.constants.toList do
    let mod := env.getModuleFor? decl
    if let some m := mod then
      if targetModules.contains m then
        covered := covered + 1
        for linter in checks do
          if excluded.contains linter.name then
            continue
          if ← liftCoreM <| shouldBeLinted linter.name decl then
            let msg ← liftTermElabM <| linter.test decl
            if let some msg := msg then
              found := true
              logError m!"LINT_FAIL {decl}\n{msg}"
  if found then
    throwError "linter failures found in de Rham foundation modules"

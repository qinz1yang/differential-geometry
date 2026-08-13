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

open Lean Elab Command Batteries.Tactic.Lint

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
  let mut actual : Array String := #[]
  for (n, _) in env.constants.toList do
    if let some m := env.getModuleFor? n then
      if targetModules.contains m then
        if !(← liftCoreM (isAutoDecl n)) then
          actual := actual.push n.toString
  let actualSorted := actual.qsort (· < ·)
  let manifestPath := "Scripts/api.manifest"
  let manifest ← IO.FS.readFile manifestPath
  let expected := (manifest.splitOn "\n").filter (· != "")
  let missing := expected.filter fun e => !actualSorted.contains e
  let extra := actualSorted.filter fun a => !expected.contains a
  let mut failed := false
  if !missing.isEmpty then
    failed := true
    for m in missing do
      logError m!"MISSING PUBLIC API: {m}"
  if !extra.isEmpty then
    failed := true
    for e in extra do
      logError m!"UNEXPECTED PUBLIC API: {e}"
  let forbidden := ["canonL", "canonR", "twoShuffleThreeShuffle", "rightShuffleTwoShuffle",
    "sign_canonL_canonR"]
  for f in forbidden do
    if actualSorted.any (fun a => a.contains f) then
      failed := true
      logError m!"FORBIDDEN OLD NAME PRESENT: {f}"
  if failed then
    throwError "public API inventory mismatch"

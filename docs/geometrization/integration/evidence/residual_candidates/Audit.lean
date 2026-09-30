import DifferentialGeometry.Geometry.Metric.Approximation.ProductResidualBound
import DifferentialGeometry.Geometry.Metric.Approximation.VanishingProductResidual
import DifferentialGeometry.Geometry.Metric.Approximation.TestedResidualParameter
import Lean

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let owned : List Name := [`DifferentialGeometry.Geometry.Metric.Approximation.ProductResidualBound, `DifferentialGeometry.Geometry.Metric.Approximation.VanishingProductResidual, `DifferentialGeometry.Geometry.Metric.Approximation.TestedResidualParameter]
  let skeleton : List Name := []
  let authored : List Name := [`WithLp.snd_dist_sq_le_of_fst_dist_gap, `GC.MetricGeometry.KleinerLottApprox.snd_dist_sq_le_of_coordinate_control, `GC.MetricGeometry.eventually_residual_lt_of_coordinate_control, `GC.MetricGeometry.PointedGHConverges.exists_subsequence_with_vanishing_tested_residual, `GC.MetricGeometry.exists_tested_residual_parameter_of_nonnegative_models]
  let expected : List Name := []
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in authored do
    unless (env.checked.get.find? name).isSome do
      throwError "Unchecked authored declaration {name}"
  let mut count : Nat := 0
  let mut direct : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless owned.contains mod do continue
    unless (env.checked.get.find? name).isSome do
      throwError "Unchecked declaration {name}"
    if info.isAxiom || info.isUnsafe then
      throwError "Unexpected axiom or unsafe declaration {name}"
    if info.type.getUsedConstants.contains ``sorryAx then
      throwError "Admission in declaration type {name}"
    let axs ← collectAxioms name
    for ax in axs do
      unless allowed.contains ax || (skeleton.contains mod && ax == ``sorryAx) do
        throwError "Unexpected transitive axiom {ax} in {name}"
    let directSorry := (info.value? (allowOpaque := true)).any
      (fun e => e.getUsedConstants.contains ``sorryAx)
    if directSorry then
      unless skeleton.contains mod && info.isTheorem && expected.contains name do
        throwError "Unregistered direct admission {name}"
      direct := direct + 1
    let fmt ← liftTermElabM <| Meta.ppExpr info.type
    let row := Json.mkObj [
      ("name", toJson name.toString), ("module", toJson mod.toString),
      ("direct_sorry", toJson directSorry),
      ("theorem", toJson info.isTheorem),
      ("type", toJson fmt.pretty),
      ("dependencies", toJson (info.getUsedConstantsAsSet.toList.map Name.toString)),
      ("axioms", toJson (axs.toList.map Name.toString))]
    logInfo m!"INTEGRATION_DECL {row.compress}"
    count := count + 1
  unless direct == expected.length do
    throwError "Expected {expected.length} direct admissions; observed {direct}"
  if count == 0 then throwError "Empty integration audit"
  logInfo m!"INTEGRATION_AUDIT_PASS {count} declarations, {direct} direct admissions"

import DifferentialGeometry.Analysis.Integration.Integral.Circle
import DifferentialGeometry.Analysis.Calculus.CircleResolvent
import DifferentialGeometry.Analysis.InnerProductSpace.SpectralProjection
import DifferentialGeometry.Analysis.InnerProductSpace.ProjectionRankStability
import DifferentialGeometry.Analysis.Integration.Integral.Resolvent
import DifferentialGeometry.Analysis.InnerProductSpace.SpectralProjectionBounds
import DifferentialGeometry.Analysis.InnerProductSpace.SpectralProjectionRegularity
import Lean

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let owned : List Name := [`DifferentialGeometry.Analysis.Integration.Integral.Circle, `DifferentialGeometry.Analysis.Calculus.CircleResolvent, `DifferentialGeometry.Analysis.InnerProductSpace.SpectralProjection, `DifferentialGeometry.Analysis.InnerProductSpace.ProjectionRankStability, `DifferentialGeometry.Analysis.Integration.Integral.Resolvent, `DifferentialGeometry.Analysis.InnerProductSpace.SpectralProjectionBounds, `DifferentialGeometry.Analysis.InnerProductSpace.SpectralProjectionRegularity]
  let skeleton : List Name := []
  let authored : List Name := [`ContinuousMap.circleIntegralCLM, `ContinuousMap.circleIntegralCLM_apply, `ContinuousMap.norm_circleIntegralCLM_le, `contDiffOn_circleIntegral_resolvent, `ContDiffOn.circleIntegral_resolvent, `ContinuousLinearMap.circleIntegral_resolvent_eq_starProjection, `Submodule.iSup_eigenspace_starProjection_eq, `Submodule.injective_orthogonalProjectionOnto_restrict_of_norm_sub_lt_one, `Submodule.finrank_eq_of_norm_starProjection_sub_lt_one, `spectrum.norm_normalized_circleIntegral_resolvent_sub_le, `ContinuousLinearMap.norm_starProjection_eigenspace_ball_sub_le, `ContinuousLinearMap.finrank_eigenspace_ball_eq_of_norm_sub_starProjection_lt, `ContDiffOn.starProjection_eigenspace_ball]
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

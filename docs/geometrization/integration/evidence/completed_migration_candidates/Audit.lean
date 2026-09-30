import DifferentialGeometry.Geometry.Comparison.Volume.ScaledBallComparison
import DifferentialGeometry.Geometry.Comparison.Volume.RicciScaleMultiplicity
import DifferentialGeometry.Analysis.InnerProductSpace.PrunedGraphRank
import DifferentialGeometry.Analysis.Calculus.PrunedGraph
import DifferentialGeometry.Geometry.Metric.RetainedMarkerLocality
import DifferentialGeometry.Analysis.NormedSpace.ScaleVanishing
import Lean

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let owned : List Name := [`DifferentialGeometry.Geometry.Comparison.Volume.ScaledBallComparison, `DifferentialGeometry.Geometry.Comparison.Volume.RicciScaleMultiplicity, `DifferentialGeometry.Analysis.InnerProductSpace.PrunedGraphRank, `DifferentialGeometry.Analysis.Calculus.PrunedGraph, `DifferentialGeometry.Geometry.Metric.RetainedMarkerLocality, `DifferentialGeometry.Analysis.NormedSpace.ScaleVanishing]
  let skeleton : List Name := []
  let authored : List Name := [`DifferentialGeometry.Geometry.Riemannian.VolumeComparison.ballVolume_mul_scale_le_model_ratio, `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.exists_finite_scale_cover_of_ricci_bound, `ContinuousLinearMap.pruned_graph_range_surjective_of_approximation, `DifferentialGeometry.Analysis.pruned_graph_derivative_surjective_of_approximation, `GC.MetricGeometry.nearby_scale_comparison_of_retained_markers, `GC.MetricGeometry.small_radius_lt_half_reference_of_contributing_support, `ContinuousLinearMap.norm_on_segment_le_of_vanishing_at_small_scale]
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

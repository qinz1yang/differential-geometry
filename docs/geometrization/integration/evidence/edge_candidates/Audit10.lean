import DifferentialGeometry.Geometry.Metric.Approximation.EdgePoint
import DifferentialGeometry.Geometry.Metric.Approximation.StripChart
import DifferentialGeometry.Geometry.Metric.Approximation.EdgeHalfPlaneModel
import DifferentialGeometry.Geometry.Metric.Approximation.EdgeBorderLifts
import DifferentialGeometry.Geometry.Metric.Approximation.EdgeHeight
import DifferentialGeometry.Geometry.Metric.Approximation.EdgeCoarseBorder
import DifferentialGeometry.Geometry.Metric.Approximation.StrongEdgePoint
import DifferentialGeometry.Geometry.Metric.Approximation.EndpointProductLifts
import DifferentialGeometry.Geometry.Metric.Approximation.StrongEdgeLifts
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleComposition
import Lean

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let owned : List Name := [`DifferentialGeometry.Geometry.Metric.Approximation.EdgePoint, `DifferentialGeometry.Geometry.Metric.Approximation.StripChart, `DifferentialGeometry.Geometry.Metric.Approximation.EdgeHalfPlaneModel, `DifferentialGeometry.Geometry.Metric.Approximation.EdgeBorderLifts, `DifferentialGeometry.Geometry.Metric.Approximation.EdgeHeight, `DifferentialGeometry.Geometry.Metric.Approximation.EdgeCoarseBorder, `DifferentialGeometry.Geometry.Metric.Approximation.StrongEdgePoint, `DifferentialGeometry.Geometry.Metric.Approximation.EndpointProductLifts, `DifferentialGeometry.Geometry.Metric.Approximation.StrongEdgeLifts, `DifferentialGeometry.Geometry.Metric.Scaling.RescaleComposition]
  let skeleton : List Name := []
  let authored : List Name := [`GC.MetricGeometry.isEdgePoint, `GC.MetricGeometry.isEdgePoint_of_recentered_interval, `GC.MetricGeometry.isEdgePoint_of_lipschitz_scale, `GC.MetricGeometry.KleinerLottApprox.stripMap, `GC.MetricGeometry.KleinerLottApprox.stripMap_basepoint, `GC.MetricGeometry.KleinerLottApprox.stripMap_height, `GC.MetricGeometry.KleinerLottApprox.stripMap_estimates, `GC.MetricGeometry.isEdgePoint.exists_local_half_plane_model, `GC.MetricGeometry.isEdgePoint.exists_local_half_plane_model_rescale, `GC.MetricGeometry.KleinerLottApprox.exists_strip_border_lift, `GC.MetricGeometry.KleinerLottApprox.exists_weak_edge_strip_border_lift, `GC.MetricGeometry.KleinerLottApprox.strip_height_lt_of_rescaled_edgePoint, `GC.MetricGeometry.KleinerLottApprox.strip_height_lt_of_weak_edge, `GC.MetricGeometry.KleinerLottApprox.coarse_border_of_lipschitz_scale, `GC.MetricGeometry.isEdgePoint_of_marked_interval_model, `GC.MetricGeometry.isEdgePoint_of_ray_model, `GC.MetricGeometry.KleinerLottApprox.coverage_witness_radius, `GC.MetricGeometry.KleinerLottApprox.exists_product_lift_radius, `GC.MetricGeometry.KleinerLottApprox.exists_nearby_product_lift, `GC.MetricGeometry.exists_strong_edge_interval_lift, `GC.MetricGeometry.exists_strong_edge_ray_lift, `MetricSpace.rescale_one, `MetricSpace.rescale_mul, `MetricSpace.rescale_inv_ratio, `GC.MetricGeometry.lipschitzWith_normalized_scale]
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

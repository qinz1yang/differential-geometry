import DifferentialGeometry.Geometry.Comparison.PairedPacketAnchors
import DifferentialGeometry.Geometry.Comparison.FullRankPacket
import DifferentialGeometry.Geometry.Comparison.UniformPacketPerturbation
import DifferentialGeometry.Geometry.Comparison.UniformLiftedPacket
import DifferentialGeometry.Geometry.Comparison.UniformImageCube
import DifferentialGeometry.Analysis.Integration.Measure.NormalizedHausdorffMeasure
import DifferentialGeometry.Analysis.Integration.Measure.CubeMeasureBound
import DifferentialGeometry.Geometry.Metric.Approximation.LimitVolumeLowerBound
import DifferentialGeometry.Analysis.Order.EventualTestBounds
import Lean

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let owned : List Name := [`DifferentialGeometry.Geometry.Comparison.PairedPacketAnchors, `DifferentialGeometry.Geometry.Comparison.FullRankPacket, `DifferentialGeometry.Geometry.Comparison.UniformPacketPerturbation, `DifferentialGeometry.Geometry.Comparison.UniformLiftedPacket, `DifferentialGeometry.Geometry.Comparison.UniformImageCube, `DifferentialGeometry.Analysis.Integration.Measure.NormalizedHausdorffMeasure, `DifferentialGeometry.Analysis.Integration.Measure.CubeMeasureBound, `DifferentialGeometry.Geometry.Metric.Approximation.LimitVolumeLowerBound, `DifferentialGeometry.Analysis.Order.EventualTestBounds]
  let skeleton : List Name := []
  let authored : List Name := [`DifferentialGeometry.Geometry.Comparison.Toponogov.PairedComparisonPacket.injective_anchors, `DifferentialGeometry.Geometry.Comparison.Toponogov.PairedComparisonPacket.exists_positive_anchor_bounds, `DifferentialGeometry.Geometry.Comparison.Toponogov.exists_rank_three_packet_near_of_dimH_gt_two, `DifferentialGeometry.Geometry.Comparison.Toponogov.PairedComparisonPacket.exists_uniform_metric_perturbation, `DifferentialGeometry.Geometry.Comparison.Toponogov.PairedComparisonPacket.eventually_uniform_lift, `DifferentialGeometry.Geometry.Comparison.Toponogov.PairedComparisonPacket.cube_subset_distanceCoordinates_image_three, `MeasureTheory.euclideanHausdorffFactor, `MeasureTheory.euclideanHausdorffFactor_pos, `MeasureTheory.normalizedHausdorffMeasure, `MeasureTheory.normalizedHausdorffMeasure_euclidean, `MeasureTheory.normalizedHausdorffMeasure_image_le, `MeasureTheory.volume_euclidean_coordinate_cube, `MeasureTheory.cube_le_normalizedHausdorffMeasure, `MeasureTheory.cube_le_normalizedHausdorffMeasure_three, `GC.MetricGeometry.PointedGHConverges.eventually_normalizedHausdorffMeasure_ball_lower_bound, `Filter.exists_positive_test_bound_of_pointwise_eventual_bounds]
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

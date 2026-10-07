import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceCurvatureControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ParabolicCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.PostSurgeryMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventCanonicalWindowData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicBall.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryNoncollapse.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.AnalyticAdmissibility.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.RegularSlice.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry.SpatialData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.LocalPropagation.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.CostDefs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCutoffRecordFamily
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ConeAccuracy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventCapCapture.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingSlabCanonicalBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingSlabDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStageMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingSlabGradientBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedRecordPrefix

set_option autoImplicit false
noncomputable section

/-!
# S-CH11-SHIM G1 consumer (`_C11X`)

Imports the 20 split-out shims and type-checks every public declaration of the
corresponding astra files by its full name: `example : type_of% @D := @D`.  A name that
were not visible under the shim path (or whose host signature disagreed with its use
here) would be an elaboration error.  The last example opens the two `private` helpers
of the `HistoryNoncollapse.Basic` shim exactly as astra users do.  Own file, no new
declarations.
-/

-- Surgery.Topology.BackwardTraceCurvatureControl
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace
example : type_of% @isRmControlled := @isRmControlled
example : type_of% @isRmControlled.restrictFirst := @isRmControlled.restrictFirst
end

-- LongTime.ParabolicCurvature
section
open GC.LongTime
example : type_of% @hasSmallParabolicCurvature := @hasSmallParabolicCurvature
end

-- LongTime.PostSurgeryMetric
section
open GC.LongTime
example : type_of% @postStage := @postStage
example : type_of% @postMetric := @postMetric
end

-- Surgery.Topology.EventCanonicalWindowData
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent
example : type_of% @PresentedStaticCap.window := @PresentedStaticCap.window
example : type_of% @PresentedStaticCap.window_smooth := @PresentedStaticCap.window_smooth
example : type_of% @PresentedStaticCap.hasCanonicalWindow := @PresentedStaticCap.hasCanonicalWindow
example : type_of% @retainedBoundary_of_presentation_cap_eq_inl :=
  @retainedBoundary_of_presentation_cap_eq_inl
end

-- Surgery.Topology.HistoryParabolicBall.Defs
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
example : type_of% @isParabolicallyRmControlledBall := @isParabolicallyRmControlledBall
example : type_of% @isParabolicallyRmControlledBall.radius_sq_le_time :=
  @isParabolicallyRmControlledBall.radius_sq_le_time
end

-- Surgery.Topology.HistoryNoncollapse.Basic
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory
example : type_of% @NoncollapsedBefore := @NoncollapsedBefore
example : type_of% @noncollapsedBefore_mono := @noncollapsedBefore_mono
example : type_of% @noncollapsedBefore_zero := @noncollapsedBefore_zero
end

-- LongTime.AnalyticAdmissibility.Defs
section
open GC.LongTime
example : type_of% @hasCommonNeckAccuracy := @hasCommonNeckAccuracy
example : type_of% @hasCommonNeckAccuracy.bounds := @hasCommonNeckAccuracy.bounds
example : type_of% @AnalyticSurgeryProfile := @AnalyticSurgeryProfile
example : type_of% @hasAnalyticAdmissibility := @hasAnalyticAdmissibility
example : type_of% @AnalyticSurgeryProfile.commonNeckAccuracy :=
  @AnalyticSurgeryProfile.commonNeckAccuracy
example : type_of% @AnalyticSurgeryProfile.largerBallAccuracy_on_late_half_interval :=
  @AnalyticSurgeryProfile.largerBallAccuracy_on_late_half_interval
end

-- LongTime.RegularSlice.Defs
section
open GC.LongTime
example : type_of% @RegularSlice := @RegularSlice
example : type_of% @RegularSlice.history := @RegularSlice.history
example : type_of% @RegularSlice.stage := @RegularSlice.stage
example : type_of% @RegularSlice.metric := @RegularSlice.metric
example : type_of% @RegularSlice.normalizedMetric := @RegularSlice.normalizedMetric
example : type_of% @RegularSlice.curvatureOneMetric := @RegularSlice.curvatureOneMetric
example : type_of% @RegularSlice.initial := @RegularSlice.initial
end

-- Perelman.CanonicalNeighborhood.FiniteHornGeometry.SpatialData
section
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
example : type_of% @I3 := @I3
example : type_of% @I2 := @I2
example : type_of% @Cylinder := @Cylinder
example : type_of% @IC := @IC
example : type_of% @metricDistance := @metricDistance
example : type_of% @CompactDomain := @CompactDomain
example : type_of% @MetricComparisonOn := @MetricComparisonOn
example : type_of% @CylinderReference := @CylinderReference
example : type_of% @ProjectivePresentation := @ProjectivePresentation
example : type_of% @CapCore := @CapCore
example : type_of% @SecLower := @SecLower
example : type_of% @PositiveComponent := @PositiveComponent
example : type_of% @SecLower.mono := @SecLower.mono
end

-- Perelman.CanonicalNeighborhood.LocalPropagation.Basic
section
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
example : type_of% @forall_le_of_no_crossing := @forall_le_of_no_crossing
example : type_of% @hasDerivAt_inv_sqrt := @hasDerivAt_inv_sqrt
example : type_of% @abs_deriv_inv_sqrt_le := @abs_deriv_inv_sqrt_le
example : type_of% @hasDerivAt_inv_of := @hasDerivAt_inv_of
example : type_of% @abs_deriv_inv_le := @abs_deriv_inv_le
example : type_of% @one_div_ten_lt_inv_sqrt_two_sub_inv_sqrt_three :=
  @one_div_ten_lt_inv_sqrt_two_sub_inv_sqrt_three
example : type_of% @abs_sub_le_of_hasDerivAt_of_lintegral_le :=
  @abs_sub_le_of_hasDerivAt_of_lintegral_le
example : type_of% @exists_path_lintegral_speed_lt_of_mem_closedBall :=
  @exists_path_lintegral_speed_lt_of_mem_closedBall
end

-- Surgery.LGeometry.Action.CostDefs
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
example : type_of% @stageEndTime := @stageEndTime
example : type_of% @regularizedStageStart := @regularizedStageStart
example : type_of% @regularizedStageEnd := @regularizedStageEnd
example : type_of% @StageInterval := @StageInterval
example : type_of% @stageEndTime_castSucc := @stageEndTime_castSucc
example : type_of% @stageEndTime_last := @stageEndTime_last
example : type_of% @time_le_stageEndTime := @time_le_stageEndTime
example : type_of% @stageEndTime_le_horizon := @stageEndTime_le_horizon
example : type_of% @stageEndTime_mono := @stageEndTime_mono
example : type_of% @time_le_of_mem_stageDomain := @time_le_of_mem_stageDomain
example : type_of% @le_stageEndTime_of_mem_stageDomain := @le_stageEndTime_of_mem_stageDomain
example : type_of% @mem_stageDomain_of_mem_Ioo := @mem_stageDomain_of_mem_Ioo
example : type_of% @regularizedStageStart_eq_of_mem_Icc := @regularizedStageStart_eq_of_mem_Icc
example : type_of% @regularizedStageEnd_eq_of_mem_stageDomain :=
  @regularizedStageEnd_eq_of_mem_stageDomain
example : type_of% @regularizedStage_bounds := @regularizedStage_bounds
example : type_of% @regularizedStage_endpoint_clocks := @regularizedStage_endpoint_clocks
example : type_of% @mapsTo_regularizedStage_Ioo := @mapsTo_regularizedStage_Ioo
example : type_of% @regularizedStageStart_castSucc_eq_event_clock :=
  @regularizedStageStart_castSucc_eq_event_clock
example : type_of% @regularizedStageEnd_succ_eq_event_clock :=
  @regularizedStageEnd_succ_eq_event_clock
example : type_of% @stageRegularizedLagrangian := @stageRegularizedLagrangian
example : type_of% @stageRegularizedAction := @stageRegularizedAction
example : type_of% @regularizedC1ActionValues := @regularizedC1ActionValues
example : type_of% @regularizedC1Cost := @regularizedC1Cost
example : type_of% @regularizedC1Cost_eq_top_of_no_competitor :=
  @regularizedC1Cost_eq_top_of_no_competitor
example : type_of% @stageRegularizedLagrangian_castSucc := @stageRegularizedLagrangian_castSucc
example : type_of% @stageRegularizedAction_castSucc := @stageRegularizedAction_castSucc
example : type_of% @stageRegularizedLagrangian_last := @stageRegularizedLagrangian_last
example : type_of% @stageRegularizedAction_last := @stageRegularizedAction_last
example : type_of% @stageRegularizedExtendedAction := @stageRegularizedExtendedAction
example : type_of% @regularizedExtendedAction := @regularizedExtendedAction
example : type_of% @regularizedActionValues := @regularizedActionValues
example : type_of% @regularizedCost := @regularizedCost
example : type_of% @regularizedCost_eq_top_of_no_competitor :=
  @regularizedCost_eq_top_of_no_competitor
end

-- Surgery.Topology.CanonicalCutoffRecordFamily
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory
example : type_of% @IsCanonicalCutoffRecordFamily := @IsCanonicalCutoffRecordFamily
example : type_of% @hasCanonicalCutoffRecords_iff_exists_isCanonicalCutoffRecordFamily :=
  @hasCanonicalCutoffRecords_iff_exists_isCanonicalCutoffRecordFamily
example : type_of% @IsCanonicalCutoffRecordFamily.inv_two_mul_sq_lt_static_scale :=
  @IsCanonicalCutoffRecordFamily.inv_two_mul_sq_lt_static_scale
end

-- Surgery.Topology.ConeAccuracy
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
example : type_of% @coneAccuracy := @coneAccuracy
example : type_of% @coneAccuracy_pos := @coneAccuracy_pos
end

-- Surgery.Topology.EventCapCapture.Basic
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
example : type_of% @MetricCutCapEvent.exists_retained_cap_of_not_regularCrossing :=
  @MetricCutCapEvent.exists_retained_cap_of_not_regularCrossing
example : type_of% @ObservedHistory.exists_latest_event_without_regularCrossing :=
  @ObservedHistory.exists_latest_event_without_regularCrossing
end

-- Surgery.Topology.HistoryPinching
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory
example : type_of% @EventSlabsPinched := @EventSlabsPinched
end

-- Surgery.Topology.IncomingSlabCanonicalBounds
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
example : type_of% @CanonicalBefore := @CanonicalBefore
example : type_of% @SpatiallyCanonicalBefore := @SpatiallyCanonicalBefore
example : type_of% @CanonicalOn := @CanonicalOn
example : type_of% @SpatiallyCanonicalOn := @SpatiallyCanonicalOn
example : type_of% @canonicalBefore_mono := @canonicalBefore_mono
example : type_of% @spatiallyCanonicalBefore_mono := @spatiallyCanonicalBefore_mono
example : type_of% @canonicalBefore_start := @canonicalBefore_start
example : type_of% @spatiallyCanonicalBefore_start := @spatiallyCanonicalBefore_start
end

-- Surgery.Topology.IncomingSlabDerivativeBounds
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
example : type_of% @DerivativeBoundBefore := @DerivativeBoundBefore
example : type_of% @GradientBoundBefore := @GradientBoundBefore
example : type_of% @DerivativeBoundOn := @DerivativeBoundOn
example : type_of% @GradientBoundOn := @GradientBoundOn
example : type_of% @derivativeBoundBefore_mono := @derivativeBoundBefore_mono
example : type_of% @gradientBoundBefore_mono := @gradientBoundBefore_mono
example : type_of% @derivativeBoundBefore_start := @derivativeBoundBefore_start
example : type_of% @gradientBoundBefore_start := @gradientBoundBefore_start
end

-- Surgery.Topology.HistoryStageMetric
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
example : type_of% @stageMetric_castSucc_apply := @stageMetric_castSucc_apply
example : type_of% @stageMetric_last_of_lt := @stageMetric_last_of_lt
example : type_of% @stageMetric_last_of_le := @stageMetric_last_of_le
example : type_of% @mem_stageDomain_last := @mem_stageDomain_last
end

-- Surgery.Topology.IncomingSlabGradientBounds
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
example : type_of% @scalarDifferential_eq_inner_gradientFun :=
  @scalarDifferential_eq_inner_gradientFun
example : type_of% @inner_gradientFun_scalar_le_sq_of_abs_scalarDifferential_le :=
  @inner_gradientFun_scalar_le_sq_of_abs_scalarDifferential_le
example : type_of% @abs_scalarDifferential_le_of_inner_gradientFun_le_sq :=
  @abs_scalarDifferential_le_of_inner_gradientFun_le_sq
end

-- Surgery.Topology.RetainedRecordPrefix
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory
example : type_of% @prefixAt := @prefixAt
example : type_of% @prefixAt_time_last := @prefixAt_time_last
example : type_of% @backwardPointTraceOfPrefix := @backwardPointTraceOfPrefix
example : type_of% @geometricCutoffRecordOfPrefix := @geometricCutoffRecordOfPrefix
example : type_of% @prefixRecords := @prefixRecords
end

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
namespace RetainedCoreHistory

open private rm_bound_of_stage_eq volume_lower_bound_of_stage_index from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryNoncollapse.Basic

example : type_of% @rm_bound_of_stage_eq := @rm_bound_of_stage_eq

example : type_of% @volume_lower_bound_of_stage_index :=
  @volume_lower_bound_of_stage_index

end RetainedCoreHistory

-- the host has one extra (unused) `variable {P₀ : OrientedThreeStage}`: same elaborated type
universe u in
example : type_of% @RetainedCoreHistory.EventSlabsPinched.{u} =
    (RetainedCoreHistory.{u} → (ℝ → ℝ) → Prop) := rfl
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

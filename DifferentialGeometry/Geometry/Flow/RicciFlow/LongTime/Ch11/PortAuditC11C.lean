import DifferentialGeometry.Analysis.Calculus.Cutoff.SingularBarrier
import DifferentialGeometry.Analysis.Calculus.UpperSupport.WithTop
import DifferentialGeometry.Analysis.Calculus.UpperSupport.WithTopPortC11P
import DifferentialGeometry.Analysis.Integration.Measure.Jacobian.LipschitzImageIntegral
import DifferentialGeometry.Analysis.Integration.Measure.Parametric.DensityComparisonC11X
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.LipschitzImagePortC11X
import DifferentialGeometry.Analysis.Order.CommonProfileComparison
import DifferentialGeometry.Analysis.Order.CommonProfileDecay
import DifferentialGeometry.Analysis.Order.CommonProfileFamily
import DifferentialGeometry.Geometry.Collapse.CurvatureRadiusNormBound
import DifferentialGeometry.Geometry.Collapse.CurvatureScaleNearbyVolume
import DifferentialGeometry.Geometry.Collapse.TestedBallVolumeSeed
import DifferentialGeometry.Geometry.Collapse.VolumeTriggerBounds
import DifferentialGeometry.Geometry.Comparison.Variation.EndpointAccelerationChain
import DifferentialGeometry.Geometry.Comparison.Variation.Field.CompactExponential
import DifferentialGeometry.Geometry.Comparison.Variation.Field.FiniteJointFrames
import DifferentialGeometry.Geometry.Comparison.Variation.Field.FiniteJointRealization
import DifferentialGeometry.Geometry.Comparison.Variation.Field.JointRealization
import DifferentialGeometry.Geometry.Comparison.Variation.Field.LocalJointRealization
import DifferentialGeometry.Geometry.Comparison.Variation.Field.ParameterEndpointCorrection
import DifferentialGeometry.Geometry.Connection.Hessian.FiniteScalarTrace
import DifferentialGeometry.Geometry.Connection.Hessian.FiniteScalarTracePortC11P
import DifferentialGeometry.Geometry.Curvature.DimensionThree.SectionalScalarBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.FixedEndpoints
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.FixedTerminalOpenBuffer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.LocalDistanceContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.ScalarTimeComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.TerminalBallProtection
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.AnalyticAdmissibility.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CurvatureBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ParabolicCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.PostSurgeryMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.RegularSlice.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.SmallEnlargementScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry.SpatialData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.LocalPropagation.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SphereChordConnector
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.FiniteJointAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.JointRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.FiniteTraceEnergy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.CountableClosedStripGluing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.PowerNormalizedVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornCutoffRecordC11X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornFineCutoffRecordC11X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PoincareHornCutoffRecordOfFineCutNecksC11X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.FiniteObservationContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.MatchedRawScale
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.ScaffoldData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.ClosedTimeACSplice
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.CollarCompetitors
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.CostDefs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.InterleavedJoins
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.InterleavedJointAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.PhysicalClockSupport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.PhysicalCollarReserve
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.RecentScalarCost
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.SmallPrefixTrace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.SmoothCollarCompetitors
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.SmoothCollarContact
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.SmoothStageRepresentatives
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.SmoothSurvivorJoins
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.SmoothSurvivorRepresentatives
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.StageSolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.ZeroPoleComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.GeometricObservationStep
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.GeometricObservationStepPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.SpatialWitnessTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.ReducedVolume.RegularEndpointBlock
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CanonicalStaticCoordinates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientLimitSurvivorCanonicalWitnessC11X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceCurvatureControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceScalarControl.TimeLocal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceAfterEventC11X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCutoffRecordFamily
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCutoffRecordSplicing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalTimeControlPointSelection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapAnnulusCoordinates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapAnnulusCoordinatesPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapBoundaryChord
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowActionC11X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowEllipticity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowLocalInverse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowLocalInversePortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedSliceScalarEscape
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ConeAccuracy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ControlledBallTerminalJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingAncientLimitSpatialC11X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffParameterGluing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordAccuracy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordSplicing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordSplicingPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventCanonicalWindowData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventCapCapture.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventDistanceScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventDistanceScalarPresentation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventDistanceScalarTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventDistanceScalarTransportPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventRetainedVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FinalSlabNoncollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FinalSlabNoncollapsePortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FinitePresentedStaticCapC11X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FirstCurvatureContactVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FirstCurvatureContactVolumePortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoffCollapseBands
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoffRawScale
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoffVolumeNonincrease
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyCurvatureScale
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryNoncollapse.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryNoncollapseRadius
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicBall.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicSeedRicci
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicSeedRicciPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStageMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IdentifiedHistoryPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingSlabCanonicalBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingSlabDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingSlabGradientBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialLayerBallVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialScalarUpperBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckAnnulusControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckAnnulusControlPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckBoundaryChord
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PresentedStaticCapRadialCoordinates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PresentedStaticCapRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PresentedStaticCapRestrictionPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.QuantitativeStageWindowProtection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RecentCaptureScale
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RecentCutoffRadius
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedRecordPrefix
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabGradientScalarControlC11X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabGradientScalarControlC11XPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCapCoordinates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalDistanceUpperLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionRecenter
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniformCapWindowContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniformCapWindowSpatialCanonicalWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniformObservationEstimatePacket
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniformSlabStartDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniformSpatialCrossingContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniversalCanonicalContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniversalSpatialCanonicalContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.WholeCanonicalComponentSeedVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.WholeCanonicalComponentSeedVolumePortC11P
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.FiniteParameterGraph
import DifferentialGeometry.Topology.MetricSpace.TruncatedDistanceLevel

set_option autoImplicit false
noncomputable section

/-!
# S-CH11-CONS G2 consumer 汇总（`_C11C`）

一次 `import` 全部已落地的 ch11 donor 派生模块（B1 verbatim、B2/B3/EXT verbatim、20 个 split shim、
FIX 的 `PortC11P` 与 extension `C11X`），对其中每个**用户写的 public 声明**（theorem / def / inductive）
做 `example : type_of% @D := @D` 的型检查。顺带证明这些模块可以同时 import（无重名冲突）。
只含 `example`，不引入任何声明；生成脚本 `build-logs/scratch/S-CH11-CONS/mkconsumer.py`。
-/

-- DG.Analysis.Calculus.Cutoff.SingularBarrier
section
example : type_of% @DifferentialGeometry.Analysis.SingularBarrier.value :=
  @DifferentialGeometry.Analysis.SingularBarrier.value
example : type_of% @DifferentialGeometry.Analysis.SingularBarrier.bound :=
  @DifferentialGeometry.Analysis.SingularBarrier.bound
example : type_of% @DifferentialGeometry.Analysis.SingularBarrier.contDiffOn :=
  @DifferentialGeometry.Analysis.SingularBarrier.contDiffOn
example : type_of% @DifferentialGeometry.Analysis.SingularBarrier.one_le :=
  @DifferentialGeometry.Analysis.SingularBarrier.one_le
example : type_of% @DifferentialGeometry.Analysis.SingularBarrier.pos :=
  @DifferentialGeometry.Analysis.SingularBarrier.pos
example : type_of% @DifferentialGeometry.Analysis.SingularBarrier.monotoneOn :=
  @DifferentialGeometry.Analysis.SingularBarrier.monotoneOn
example : type_of% @DifferentialGeometry.Analysis.SingularBarrier.one_of_le :=
  @DifferentialGeometry.Analysis.SingularBarrier.one_of_le
example : type_of% @DifferentialGeometry.Analysis.SingularBarrier.deriv_nonneg :=
  @DifferentialGeometry.Analysis.SingularBarrier.deriv_nonneg
example : type_of% @DifferentialGeometry.Analysis.SingularBarrier.deriv_pos :=
  @DifferentialGeometry.Analysis.SingularBarrier.deriv_pos
example : type_of% @DifferentialGeometry.Analysis.SingularBarrier.deriv_zero_of_le :=
  @DifferentialGeometry.Analysis.SingularBarrier.deriv_zero_of_le
example : type_of% @DifferentialGeometry.Analysis.SingularBarrier.deriv2_zero_of_le :=
  @DifferentialGeometry.Analysis.SingularBarrier.deriv2_zero_of_le
example : type_of% @DifferentialGeometry.Analysis.SingularBarrier.deriv2_zero_of_deriv_zero :=
  @DifferentialGeometry.Analysis.SingularBarrier.deriv2_zero_of_deriv_zero
example : type_of% @DifferentialGeometry.Analysis.SingularBarrier.tendsto_at_pole :=
  @DifferentialGeometry.Analysis.SingularBarrier.tendsto_at_pole
example : type_of% @DifferentialGeometry.Analysis.SingularBarrier.bound_nonneg :=
  @DifferentialGeometry.Analysis.SingularBarrier.bound_nonneg
example : type_of% @DifferentialGeometry.Analysis.SingularBarrier.differential_bound :=
  @DifferentialGeometry.Analysis.SingularBarrier.differential_bound
example : type_of% @DifferentialGeometry.Analysis.SingularBarrier.exists_constant :=
  @DifferentialGeometry.Analysis.SingularBarrier.exists_constant
end

-- DG.Analysis.Calculus.UpperSupport.WithTop  （无用户声明：shim / re-export）

-- DG.Analysis.Calculus.UpperSupport.WithTopPortC11P
section
example : type_of% @WithTop.antitoneOn_of_lowerSemicontinuousOn_of_upper_support_below :=
  @WithTop.antitoneOn_of_lowerSemicontinuousOn_of_upper_support_below
end

-- DG.Analysis.Integration.Measure.Jacobian.LipschitzImageIntegral
section
example : type_of% @MeasureTheory.image_lintegral_le_of_locallyLipschitzOn :=
  @MeasureTheory.image_lintegral_le_of_locallyLipschitzOn
end

-- DG.Analysis.Integration.Measure.Parametric.DensityComparisonC11X
section
example : type_of% @DifferentialGeometry.Integral.Measure.paramDensity_le_of_inner_mfderiv_le :=
  @DifferentialGeometry.Integral.Measure.paramDensity_le_of_inner_mfderiv_le
end

-- DG.Analysis.Integration.Measure.Riemannian.LipschitzImagePortC11X
section
open DifferentialGeometry.Integral.Measure in
example : type_of% @riemannianVolumeMeasure_image_le_of_locally_nonexpanding :=
  @riemannianVolumeMeasure_image_le_of_locally_nonexpanding
end

-- DG.Analysis.Order.CommonProfileComparison
section
example : type_of% @GC.GeneralFlow.exists_decaying_commonProfile_sq_mul_lt :=
  @GC.GeneralFlow.exists_decaying_commonProfile_sq_mul_lt
end

-- DG.Analysis.Order.CommonProfileDecay
section
example : type_of% @GC.GeneralFlow.commonProfile_tendsto_zero :=
  @GC.GeneralFlow.commonProfile_tendsto_zero
example : type_of% @GC.GeneralFlow.exists_decaying_commonProfile :=
  @GC.GeneralFlow.exists_decaying_commonProfile
end

-- DG.Analysis.Order.CommonProfileFamily
section
example : type_of% @GC.GeneralFlow.prefixBudget_mono := @GC.GeneralFlow.prefixBudget_mono
example : type_of% @GC.GeneralFlow.commonProfile_mono := @GC.GeneralFlow.commonProfile_mono
example : type_of% @GC.GeneralFlow.exists_antitone_family_minorant :=
  @GC.GeneralFlow.exists_antitone_family_minorant
example : type_of% @GC.GeneralFlow.exists_decaying_commonProfile_sq_mul_lt_and_diagonal :=
  @GC.GeneralFlow.exists_decaying_commonProfile_sq_mul_lt_and_diagonal
end

-- DG.Geometry.Collapse.CurvatureRadiusNormBound
section
open DifferentialGeometry.Geometry.Collapse in
example : type_of% @exists_uniform_whole_radius_curvature_bound_of_tested_bounds :=
  @exists_uniform_whole_radius_curvature_bound_of_tested_bounds
example :
    type_of% @DifferentialGeometry.Geometry.Collapse.exists_uniform_whole_radius_curvature_bound :=
  @DifferentialGeometry.Geometry.Collapse.exists_uniform_whole_radius_curvature_bound
end

-- DG.Geometry.Collapse.CurvatureScaleNearbyVolume
section
example : type_of% @DifferentialGeometry.Geometry.Collapse.ballVolume_lower_near_curvature_scale :=
  @DifferentialGeometry.Geometry.Collapse.ballVolume_lower_near_curvature_scale
end

-- DG.Geometry.Collapse.TestedBallVolumeSeed
section
example :
    type_of% @DifferentialGeometry.Geometry.Collapse.sectional_and_volume_lower_of_tested_ball :=
  @DifferentialGeometry.Geometry.Collapse.sectional_and_volume_lower_of_tested_ball
end

-- DG.Geometry.Collapse.VolumeTriggerBounds
section
open DifferentialGeometry.Geometry.Collapse in
example : type_of% @ballVolume_le_of_volumeCollapsedAtCurvatureScale :=
  @ballVolume_le_of_volumeCollapsedAtCurvatureScale
example :
    type_of% @DifferentialGeometry.Geometry.Collapse.radius_lt_of_volumeCollapsedAtCurvatureScale :=
  @DifferentialGeometry.Geometry.Collapse.radius_lt_of_volumeCollapsedAtCurvatureScale
end

-- DG.Geometry.Comparison.Variation.EndpointAccelerationChain
section
open DifferentialGeometry.Geometry.Riemannian.Variation in
example : type_of% @sum_variation_acceleration_boundary_eq_endpoints :=
  @sum_variation_acceleration_boundary_eq_endpoints
open DifferentialGeometry.Geometry.Riemannian.Variation in
example : type_of% @centralVariationAcceleration_eq_zero_of_exp_germ :=
  @centralVariationAcceleration_eq_zero_of_exp_germ
open DifferentialGeometry.Geometry.Riemannian.Variation in
example : type_of% @sum_variation_acceleration_boundary_eq_zero_of_terminal_exp :=
  @sum_variation_acceleration_boundary_eq_zero_of_terminal_exp
end

-- DG.Geometry.Comparison.Variation.Field.CompactExponential
section
example : type_of% @DifferentialGeometry.Geometry.Riemannian.Variation.exists_compact_exponential :=
  @DifferentialGeometry.Geometry.Riemannian.Variation.exists_compact_exponential
end

-- DG.Geometry.Comparison.Variation.Field.FiniteJointFrames
section
example : type_of% @DifferentialGeometry.Geometry.Riemannian.Variation.frameParameter :=
  @DifferentialGeometry.Geometry.Riemannian.Variation.frameParameter
example : type_of% @DifferentialGeometry.Geometry.Riemannian.Variation.frameParameter_apply :=
  @DifferentialGeometry.Geometry.Riemannian.Variation.frameParameter_apply
example : type_of% @DifferentialGeometry.Geometry.Riemannian.Variation.frameParameter_single :=
  @DifferentialGeometry.Geometry.Riemannian.Variation.frameParameter_single
open DifferentialGeometry.Geometry.Riemannian.Variation in
example : type_of% @exists_compatible_joint_variation_of_fields :=
  @exists_compatible_joint_variation_of_fields
end

-- DG.Geometry.Comparison.Variation.Field.FiniteJointRealization
section
open DifferentialGeometry.Geometry.Riemannian.Variation in
example : type_of% @exists_compatible_joint_variation_of_linear_fields :=
  @exists_compatible_joint_variation_of_linear_fields
end

-- DG.Geometry.Comparison.Variation.Field.JointRealization
section
open DifferentialGeometry.Geometry.Riemannian.Variation in
example : type_of% @exists_joint_variation_of_linear_fields :=
  @exists_joint_variation_of_linear_fields
end

-- DG.Geometry.Comparison.Variation.Field.LocalJointRealization
section
open DifferentialGeometry.Geometry.Riemannian.Variation in
example : type_of% @exists_joint_variation_of_linear_fields_on :=
  @exists_joint_variation_of_linear_fields_on
end

-- DG.Geometry.Comparison.Variation.Field.ParameterEndpointCorrection
section
open DifferentialGeometry.Geometry.Riemannian.Variation in
example : type_of% @correct_parameter_variation_endpoint := @correct_parameter_variation_endpoint
end

-- DG.Geometry.Connection.Hessian.FiniteScalarTrace  （无用户声明：shim / re-export）

-- DG.Geometry.Connection.Hessian.FiniteScalarTracePortC11P
section
open DifferentialGeometry.Geometry.Connection in
example : type_of% @abstractHessian_eq_inner_cov_gradientFun_of_contMDiffAt_two :=
  @abstractHessian_eq_inner_cov_gradientFun_of_contMDiffAt_two
open DifferentialGeometry.Geometry.Connection in
example : type_of% @laplacian_eq_sum_abstractHessian_of_contMDiffAt_two :=
  @laplacian_eq_sum_abstractHessian_of_contMDiffAt_two
open DifferentialGeometry.Geometry.Connection in
example : type_of% @abstractHessian_eq_deriv_deriv_expMap_of_contMDiffAt_two :=
  @abstractHessian_eq_deriv_deriv_expMap_of_contMDiffAt_two
end

-- DG.Geometry.Curvature.DimensionThree.SectionalScalarBounds
section
open DifferentialGeometry.Geometry.Curvature.DimensionThree in
example : type_of% @sqrt_normSq0S_le_of_sectional_lower_scalar_upper :=
  @sqrt_normSq0S_le_of_sectional_lower_scalar_upper
end

-- RF.Estimates.Distance.FixedEndpoints
section
open DifferentialGeometry.PDE.RicciFlow in
example : type_of% @riemannianEDistOf_le_add_of_endpoint_ricci_on_interval :=
  @riemannianEDistOf_le_add_of_endpoint_ricci_on_interval
end

-- RF.Estimates.FixedTerminalOpenBuffer
section
example : type_of% @DifferentialGeometry.PDE.RicciFlow.exists_fixed_open_terminal_buffer :=
  @DifferentialGeometry.PDE.RicciFlow.exists_fixed_open_terminal_buffer
end

-- RF.Estimates.LocalDistanceContinuity
section
open DifferentialGeometry.PDE.RicciFlow in
example : type_of% @continuousOn_min_edist_of_compact_protected_domain :=
  @continuousOn_min_edist_of_compact_protected_domain
open DifferentialGeometry.PDE.RicciFlow in
example : type_of% @continuousOn_min_edist_toReal_of_compact_protected_domain :=
  @continuousOn_min_edist_toReal_of_compact_protected_domain
end

-- RF.Estimates.ScalarTimeComparison
section
example :
    type_of% @DifferentialGeometry.PDE.RicciFlow.IsSolutionOn.lipschitzOnWith_inv_max_scalar_Icc :=
  @DifferentialGeometry.PDE.RicciFlow.IsSolutionOn.lipschitzOnWith_inv_max_scalar_Icc
example :
    type_of% @DifferentialGeometry.PDE.RicciFlow.IsSolutionOn.scalar_le_of_quadratic_time_bound :=
  @DifferentialGeometry.PDE.RicciFlow.IsSolutionOn.scalar_le_of_quadratic_time_bound
open DifferentialGeometry.PDE.RicciFlow.IsSolutionOn in
example : type_of% @scalar_le_two_mul_of_quadratic_time_bound :=
  @scalar_le_two_mul_of_quadratic_time_bound
end

-- RF.Estimates.TerminalBallProtection
section
open DifferentialGeometry.PDE.RicciFlow in
example : type_of% @exists_pos_moving_closedBall_subset_terminal_ball :=
  @exists_pos_moving_closedBall_subset_terminal_ball
end

-- RF.LongTime.AnalyticAdmissibility.Defs  （无用户声明：shim / re-export）

-- RF.LongTime.CurvatureBounds
section
example : type_of% @GC.LongTime.exists_postMetric_curvature_bounds_of_cutoff_records :=
  @GC.LongTime.exists_postMetric_curvature_bounds_of_cutoff_records
end

-- RF.LongTime.ParabolicCurvature  （无用户声明：shim / re-export）

-- RF.LongTime.PostSurgeryMetric  （无用户声明：shim / re-export）

-- RF.LongTime.RegularSlice.Defs  （无用户声明：shim / re-export）

-- RF.LongTime.SmallEnlargementScalar
section
example : type_of% @GC.LongTime.hasSmallParabolicCurvature.scalar_abs_le :=
  @GC.LongTime.hasSmallParabolicCurvature.scalar_abs_le
end

-- RF.Perelman.CanonicalNeighborhood.FiniteHornGeometry.SpatialData  （无用户声明：shim / re-export）

-- RF.Perelman.CanonicalNeighborhood.LocalPropagation.Basic  （无用户声明：shim / re-export）

-- RF.Perelman.KappaSolutions.SphereChordConnector
section
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions in
example : type_of% @sphere2_exists_chord_controlled_curve := @sphere2_exists_chord_controlled_curve
end

-- RF.Perelman.LGeometry.Action.Regularized.FiniteJointAction
section
example : type_of% @DifferentialGeometry.PDE.RicciFlow.Perelman.finiteJointAction :=
  @DifferentialGeometry.PDE.RicciFlow.Perelman.finiteJointAction
example : type_of% @DifferentialGeometry.PDE.RicciFlow.Perelman.contDiffOn_finiteJointAction :=
  @DifferentialGeometry.PDE.RicciFlow.Perelman.contDiffOn_finiteJointAction
open DifferentialGeometry.PDE.RicciFlow.Perelman in
example : type_of% @exists_finiteJointAction_endpoint_branch :=
  @exists_finiteJointAction_endpoint_branch
end

-- RF.Perelman.LGeometry.Action.Regularized.JointRegularity
section
example :
    type_of% @DifferentialGeometry.PDE.RicciFlow.Perelman.contDiffOn_lRegularizedAction_joint :=
  @DifferentialGeometry.PDE.RicciFlow.Perelman.contDiffOn_lRegularizedAction_joint
end

-- RF.Perelman.LGeometry.Index.FiniteTraceEnergy
section
open DifferentialGeometry.PDE.RicciFlow.Perelman in
example : type_of% @sum_lRegularizedIndex_trace_linear_cutoff_eq_energy :=
  @sum_lRegularizedIndex_trace_linear_cutoff_eq_energy
end

-- RF.Solution.CountableClosedStripGluing
section
example : type_of% @DifferentialGeometry.PDE.RicciFlow.exists_solution_of_coherent_closed_strips :=
  @DifferentialGeometry.PDE.RicciFlow.exists_solution_of_coherent_closed_strips
open DifferentialGeometry.PDE.RicciFlow in
example : type_of% @exists_complete_solution_of_coherent_closed_strips :=
  @exists_complete_solution_of_coherent_closed_strips
end

-- RF.Solution.PowerNormalizedVolume
section
example : type_of% @DifferentialGeometry.PDE.RicciFlow.SolutionOn.hasDerivAt_rpow_mul_volume :=
  @DifferentialGeometry.PDE.RicciFlow.SolutionOn.hasDerivAt_rpow_mul_volume
example : type_of% @DifferentialGeometry.PDE.RicciFlow.SolutionOn.antitoneOn_rpow_mul_volume :=
  @DifferentialGeometry.PDE.RicciFlow.SolutionOn.antitoneOn_rpow_mul_volume
end

-- RF.Surgery.Contract.HornCutoffRecordC11X  （无用户声明：shim / re-export）

-- RF.Surgery.Contract.HornFineCutoffRecordC11X
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  renaming
exists_horn_cutoff_history_extension_with_canonical_windows_of_fineCutNecks_with_radial_coordinates
  → cons_c11c in
example : type_of% @cons_c11c := @cons_c11c
end

-- RF.Surgery.Contract.PoincareHornCutoffRecordOfFineCutNecksC11X
section
-- (name > 100 cols; see DeclarationAuditC11C): exists_horn_cutoff_record_with…
end

-- RF.Surgery.History.FiniteObservationContinuation
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory in
example : type_of% @exists_closedSlab_extension_of_eventCount_bounded :=
  @exists_closedSlab_extension_of_eventCount_bounded
end

-- RF.Surgery.History.MatchedRawScale  （无用户声明：shim / re-export）

-- RF.Surgery.History.ScaffoldData
section
example : type_of% @GC.GeneralFlow.ScaffoldState := @GC.GeneralFlow.ScaffoldState
example : type_of% @GC.GeneralFlow.ScaffoldSuccessor := @GC.GeneralFlow.ScaffoldSuccessor
example : type_of% @GC.GeneralFlow.all_record_fields_of_successors :=
  @GC.GeneralFlow.all_record_fields_of_successors
example : type_of% @GC.GeneralFlow.all_parameter_values_of_successors :=
  @GC.GeneralFlow.all_parameter_values_of_successors
end

-- RF.Surgery.LGeometry.Action.ClosedTimeACSplice  （无用户声明：shim / re-export）

-- RF.Surgery.LGeometry.Action.CollarCompetitors
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @exists_three_piece_stage_curve := @exists_three_piece_stage_curve
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @sum_stage_parts_eq_endpoints_add_events :=
  @sum_stage_parts_eq_endpoints_add_events
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @exists_stage_family_of_collar_pieces := @exists_stage_family_of_collar_pieces
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @extend_stage_family_by_zero_pole_stage :=
  @extend_stage_family_by_zero_pole_stage
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @regularizedCost_le_collar_piece_action :=
  @regularizedCost_le_collar_piece_action
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @regularizedCost_le_of_zero_pole_stage_extension :=
  @regularizedCost_le_of_zero_pole_stage_extension
end

-- RF.Surgery.LGeometry.Action.CostDefs  （无用户声明：shim / re-export）

-- RF.Surgery.LGeometry.Action.InterleavedJoins
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @interleavedJoinEquiv := @interleavedJoinEquiv
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @interleavedJoinEquiv_values := @interleavedJoinEquiv_values
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @exists_interleaved_actual_joins := @exists_interleaved_actual_joins
end

-- RF.Surgery.LGeometry.Action.InterleavedJointAction
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @interleavedPieceEquiv := @interleavedPieceEquiv
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @interleavedPieceEquiv_values := @interleavedPieceEquiv_values
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @ActualPieceCarrier := @ActualPieceCarrier
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @interleaved_actual_flow_joint_families :=
  @interleaved_actual_flow_joint_families
end

-- RF.Surgery.LGeometry.Action.PhysicalClockSupport
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @physical_clock_support_of_same_history_jets :=
  @physical_clock_support_of_same_history_jets
end

-- RF.Surgery.LGeometry.Action.PhysicalCollarReserve
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @exists_physical_collar_reserve_of_attained_action :=
  @exists_physical_collar_reserve_of_attained_action
end

-- RF.Surgery.LGeometry.Action.RecentScalarCost
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @regularizedCost_ge_recent_half_time_of_cutoff_records :=
  @regularizedCost_ge_recent_half_time_of_cutoff_records
end

-- RF.Surgery.LGeometry.Action.SmallPrefixTrace
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @regularizedStageStart_eq_max_zero := @regularizedStageStart_eq_max_zero
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @sum_stage_action_eq_of_collapsed_suffix :=
  @sum_stage_action_eq_of_collapsed_suffix
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @tendsto_regularizedWeightedStageAction_of_collapsed_suffix :=
  @tendsto_regularizedWeightedStageAction_of_collapsed_suffix
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @tendsto_regularizedStage_trace_energy := @tendsto_regularizedStage_trace_energy
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @exists_small_prefix_trace_energy_lt := @exists_small_prefix_trace_energy_lt
end

-- RF.Surgery.LGeometry.Action.SmoothCollarCompetitors
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @smooth_curve_projected_action := @smooth_curve_projected_action
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @smooth_survivor_curve_projected_actions :=
  @smooth_survivor_curve_projected_actions
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @regularizedCost_le_smooth_collar_action :=
  @regularizedCost_le_smooth_collar_action
end

-- RF.Surgery.LGeometry.Action.SmoothCollarContact
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @smooth_collar_action_eq_sum_stage_action :=
  @smooth_collar_action_eq_sum_stage_action
end

-- RF.Surgery.LGeometry.Action.SmoothStageRepresentatives
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @exists_smooth_prefix_stage_representatives :=
  @exists_smooth_prefix_stage_representatives
end

-- RF.Surgery.LGeometry.Action.SmoothSurvivorJoins
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @exists_smooth_survivor_directed_joins := @exists_smooth_survivor_directed_joins
end

-- RF.Surgery.LGeometry.Action.SmoothSurvivorRepresentatives
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @exists_smooth_prefix_survivor_representatives :=
  @exists_smooth_prefix_survivor_representatives
end

-- RF.Surgery.LGeometry.Action.StageSolution
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @exists_stage_incomingSlab_metric := @exists_stage_incomingSlab_metric
end

-- RF.Surgery.LGeometry.Action.ZeroPoleComparison
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @zero_mem_regularizedActionValues_self := @zero_mem_regularizedActionValues_self
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @regularizedActionValues_subset_of_zero_pole :=
  @regularizedActionValues_subset_of_zero_pole
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @regularizedCost_le_of_zero_pole := @regularizedCost_le_of_zero_pole
end

-- RF.Surgery.Noncollapsing.GeometricObservationStep  （无用户声明：shim / re-export）

-- RF.Surgery.Noncollapsing.GeometricObservationStepPortC11P
section
example : type_of% @GC.GeneralFlow.exists_geometric_observation_step :=
  @GC.GeneralFlow.exists_geometric_observation_step
end

-- RF.Surgery.Noncollapsing.SpatialWitnessTransport  （无用户声明：shim / re-export）

-- RF.Surgery.ReducedVolume.RegularEndpointBlock
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
example : type_of% @exists_test_volume_lower_of_regular_endpoint_block :=
  @exists_test_volume_lower_of_regular_endpoint_block
end

-- RF.Surgery.StandardCap.CanonicalStaticCoordinates
section
open DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness in
example : type_of% @window_eq_retainedMap := @window_eq_retainedMap
open DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness in
example : type_of% @toStaticCapWitness_hasRadialCoordinates :=
  @toStaticCapWitness_hasRadialCoordinates
end

-- RF.Surgery.Topology.AncientLimitSurvivorCanonicalWitnessC11X
section
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn in
example : type_of% @eventually_exists_canonicalWitness_survivor_of_normalized_local_flow_limit :=
  @eventually_exists_canonicalWitness_survivor_of_normalized_local_flow_limit
end

-- RF.Surgery.Topology.BackwardTraceCurvatureControl  （无用户声明：shim / re-export）

-- RF.Surgery.Topology.BackwardTraceScalarControl.TimeLocal
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace in
example : type_of% @scalar_le_two_mul_of_time_local_derivative_control :=
  @scalar_le_two_mul_of_time_local_derivative_control
end

-- RF.Surgery.Topology.BoundedCurvatureAtDistanceAfterEventC11X
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory in
example :
    type_of% @exists_scalar_bound_at_distance_of_not_capWindowPoint_of_birth_metric_comparison :=
  @exists_scalar_bound_at_distance_of_not_capWindowPoint_of_birth_metric_comparison
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory in
example : type_of% @exists_scalar_bound_at_distance_of_not_capWindowPoint_at_birth :=
  @exists_scalar_bound_at_distance_of_not_capWindowPoint_at_birth
end

-- RF.Surgery.Topology.CanonicalCutoffRecordFamily  （无用户声明：shim / re-export）

-- RF.Surgery.Topology.CanonicalCutoffRecordSplicing
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory in
example : type_of% @exists_isCanonicalCutoffRecordFamily_appendEvent_spliceAfter :=
  @exists_isCanonicalCutoffRecordFamily_appendEvent_spliceAfter
end

-- RF.Surgery.Topology.CanonicalTimeControlPointSelection
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @HasSpatialCanonicalTimeControl := @HasSpatialCanonicalTimeControl
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @exists_localized_canonical_time_control_point_selection :=
  @exists_localized_canonical_time_control_point_selection
end

-- RF.Surgery.Topology.CapAnnulusCoordinates  （无用户声明：shim / re-export）

-- RF.Surgery.Topology.CapAnnulusCoordinatesPortC11P
section
example : type_of% @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capSeamWidth :=
  @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capSeamWidth
example : type_of% @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capSeamWidth_pos :=
  @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capSeamWidth_pos
example : type_of% @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capSeamWidth_le_radius :=
  @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capSeamWidth_le_radius
example : type_of% @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capSeamWidth_le_one :=
  @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capSeamWidth_le_one
example : type_of% @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capSeamAnnulus :=
  @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capSeamAnnulus
example : type_of% @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capRadialCoordinates :=
  @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capRadialCoordinates
example :
    type_of% @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capRadialCoordinates_pos_smul :=
  @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capRadialCoordinates_pos_smul
example : type_of% @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capSeamAnnulus_ne_zero :=
  @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capSeamAnnulus_ne_zero
example : type_of% @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCompact_capSeamAnnulus :=
  @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCompact_capSeamAnnulus
example :
    type_of% @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capRadialCoordinates_smooth :=
  @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capRadialCoordinates_smooth
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
example : type_of% @exists_capRadialCoordinates_bound := @exists_capRadialCoordinates_bound
end

-- RF.Surgery.Topology.CapBoundaryChord
section
example : type_of% @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capBoundaryCoordinate :=
  @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capBoundaryCoordinate
example :
    type_of% @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capBoundaryCoordinate_injective :=
  @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capBoundaryCoordinate_injective
example : type_of% @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capBoundaryCorePoint :=
  @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capBoundaryCorePoint
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap in
example : type_of% @boundaryOldPoint := @boundaryOldPoint
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap in
example : type_of% @oldTerminal_boundaryOldPoint := @oldTerminal_boundaryOldPoint
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap in
example : type_of% @oldOutput_boundaryOldPoint := @oldOutput_boundaryOldPoint
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap in
example : type_of% @exists_actual_boundary_curve := @exists_actual_boundary_curve
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap in
example : type_of% @boundaryExtensionConstant := @boundaryExtensionConstant
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap in
example : type_of% @exists_boundary_distance_extension := @exists_boundary_distance_extension
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap in
example : type_of% @exists_actual_cap_distance_extension := @exists_actual_cap_distance_extension
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord in
example : type_of% @exists_cap_boundary_distance_extension :=
  @exists_cap_boundary_distance_extension
end

-- RF.Surgery.Topology.CapWindowActionC11X
section
-- (name > 100 cols; see DeclarationAuditC11C): exists_uniform_prepared_cap_bi…
end

-- RF.Surgery.Topology.CapWindowEllipticity
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
example : type_of% @exists_uniform_presented_window_ellipticity :=
  @exists_uniform_presented_window_ellipticity
end

-- RF.Surgery.Topology.CapWindowLocalInverse  （无用户声明：shim / re-export）

-- RF.Surgery.Topology.CapWindowLocalInversePortC11P
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
example : type_of% @exists_uniform_local_window_inverse_on_closed_core :=
  @exists_uniform_local_window_inverse_on_closed_core
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
example : type_of% @exists_uniform_local_window_inverse := @exists_uniform_local_window_inverse
end

-- RF.Surgery.Topology.ClosedSliceScalarEscape  （无用户声明：shim / re-export）

-- RF.Surgery.Topology.ConeAccuracy  （无用户声明：shim / re-export）

-- RF.Surgery.Topology.ControlledBallTerminalJets  （无用户声明：shim / re-export）

-- RF.Surgery.Topology.CrossingAncientLimitSpatialC11X
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @exists_eventually_canonicalWitness_survivor_of_isTracedRegion_at_closed_time :=
  @exists_eventually_canonicalWitness_survivor_of_isTracedRegion_at_closed_time
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @exists_eventually_spatialCanonicalWitness_of_isTracedRegion_at_closed_time :=
  @exists_eventually_spatialCanonicalWitness_of_isTracedRegion_at_closed_time
end

-- RF.Surgery.Topology.CutoffParameterGluing
section
example : type_of% @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutoffParameters.diagonal :=
  @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutoffParameters.diagonal
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutoffParameters in
example : type_of% @diagonal_eq_on_prefix := @diagonal_eq_on_prefix
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutoffParameters in
example : type_of% @diagonal_eval_of_nonpos := @diagonal_eval_of_nonpos
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutoffParameters in
example : type_of% @diagonal_delta_eq := @diagonal_delta_eq
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutoffParameters in
example : type_of% @diagonal_neckRadius_antitone := @diagonal_neckRadius_antitone
example :
    type_of% @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutoffParameters.spliceAfter :=
  @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutoffParameters.spliceAfter
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutoffParameters in
example : type_of% @spliceAfter_eval_of_le := @spliceAfter_eval_of_le
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutoffParameters in
example : type_of% @spliceAfter_eval_of_lt := @spliceAfter_eval_of_lt
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutoffParameters in
example : type_of% @spliceAfter_neckRadius_antitone := @spliceAfter_neckRadius_antitone
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord in
example : type_of% @diagonalParameters := @diagonalParameters
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord in
example : type_of% @diagonalParameters_preserves := @diagonalParameters_preserves
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord in
example : type_of% @spliceAfterParametersOfLE := @spliceAfterParametersOfLE
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord in
example : type_of% @spliceAfterParametersOfLE_preserves := @spliceAfterParametersOfLE_preserves
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord in
example : type_of% @spliceAfterParametersOfLT := @spliceAfterParametersOfLT
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord in
example : type_of% @spliceAfterParametersOfLT_preserves := @spliceAfterParametersOfLT_preserves
end

-- RF.Surgery.Topology.CutoffRecordAccuracy
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord in
example : type_of% @exists_of_delta_le_of_neckRadius_le := @exists_of_delta_le_of_neckRadius_le
end

-- RF.Surgery.Topology.CutoffRecordSplicing  （无用户声明：shim / re-export）

-- RF.Surgery.Topology.CutoffRecordSplicingPortC11P
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord in
example : type_of% @appendEvent_nominalRadius_heq := @appendEvent_nominalRadius_heq
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory in
example : type_of% @exists_cutoff_records_at_appendEvent_spliceAfter :=
  @exists_cutoff_records_at_appendEvent_spliceAfter
end

-- RF.Surgery.Topology.EventCanonicalWindowData  （无用户声明：shim / re-export）

-- RF.Surgery.Topology.EventCapCapture.Basic  （无用户声明：shim / re-export）

-- RF.Surgery.Topology.EventDistanceScalar
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent in
example : type_of% @HasUniformDistanceScalar := @HasUniformDistanceScalar
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent in
example : type_of% @HasUniformDistanceScalar.of_coreEvent_heq :=
  @HasUniformDistanceScalar.of_coreEvent_heq
end

-- RF.Surgery.Topology.EventDistanceScalarPresentation
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent in
example : type_of% @HasUniformDistanceScalar.oldTerminal_edist_le :=
  @HasUniformDistanceScalar.oldTerminal_edist_le
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.SamePresentation in
example : type_of% @hasUniformDistanceScalar := @hasUniformDistanceScalar
end

-- RF.Surgery.Topology.EventDistanceScalarTransport  （无用户声明：shim / re-export）

-- RF.Surgery.Topology.EventDistanceScalarTransportPortC11P
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf in
example : type_of% @hasUniformDistanceScalar_event := @hasUniformDistanceScalar_event
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory in
example : type_of% @hasUniformDistanceScalar_restrict := @hasUniformDistanceScalar_restrict
end

-- RF.Surgery.Topology.EventRetainedVolume
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent in
example : type_of% @oldOutput_volume_eq_oldTerminal_volume :=
  @oldOutput_volume_eq_oldTerminal_volume
end

-- RF.Surgery.Topology.FinalSlabNoncollapse  （无用户声明：shim / re-export）

-- RF.Surgery.Topology.FinalSlabNoncollapsePortC11P
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory in
example : type_of% @terminalNoncollapsedBefore_finalSlab := @terminalNoncollapsedBefore_finalSlab
end

-- RF.Surgery.Topology.FinitePresentedStaticCapC11X
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
example : type_of% @exists_presentedStaticCap_neck_heq_window_eq_coordinates_of_finiteMetricEvent :=
  @exists_presentedStaticCap_neck_heq_window_eq_coordinates_of_finiteMetricEvent
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  renaming
  exists_presentedStaticCap_neck_heq_window_eq_coordinates_of_finiteMetricEvent_terminal
  → cons_c11c in
example : type_of% @cons_c11c := @cons_c11c
example :
    type_of% @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.finitePresentedStaticCaps_C11X :=
  @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.finitePresentedStaticCaps_C11X
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
example : type_of% @finitePresentedStaticCaps_hasRadialCoordinates :=
  @finitePresentedStaticCaps_hasRadialCoordinates
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
example : type_of% @finitePresentedStaticCapsOfTerminal_C11X :=
  @finitePresentedStaticCapsOfTerminal_C11X
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
example : type_of% @finitePresentedStaticCapsOfTerminal_hasRadialCoordinates :=
  @finitePresentedStaticCapsOfTerminal_hasRadialCoordinates
end

-- RF.Surgery.Topology.FirstCurvatureContactVolume  （无用户声明：shim / re-export）

-- RF.Surgery.Topology.FirstCurvatureContactVolumePortC11P
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
example : type_of% @exists_ball_volume_lower_of_seed_and_canonical_first_contacts :=
  @exists_ball_volume_lower_of_seed_and_canonical_first_contacts
end

-- RF.Surgery.Topology.GeometricCutoffCollapseBands
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StaticCapWitness in
example : type_of% @tipCoordinate_neg := @tipCoordinate_neg
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StaticCapWitness in
example : type_of% @CollapseBandDomain := @CollapseBandDomain
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StaticCapWitness in
example : type_of% @collapseBandParameter := @collapseBandParameter
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StaticCapWitness in
example : type_of% @collapseBandParameter_coe := @collapseBandParameter_coe
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StaticCapWitness in
example : type_of% @collapseBandSource := @collapseBandSource
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StaticCapWitness in
example : type_of% @negativeBandParameters := @negativeBandParameters
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StaticCapWitness in
example : type_of% @negativeCollapseBand := @negativeCollapseBand
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StaticCapWitness in
example : type_of% @compactBandParameters := @compactBandParameters
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StaticCapWitness in
example : type_of% @isCompact_compactBandParameters := @isCompact_compactBandParameters
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StaticCapWitness in
example : type_of% @compactBandParameters_mono := @compactBandParameters_mono
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StaticCapWitness in
example : type_of% @iUnion_compactBandParameters := @iUnion_compactBandParameters
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StaticCapWitness in
example : type_of% @isCompact_collapseBandSource_range := @isCompact_collapseBandSource_range
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StaticCapWitness in
example : type_of% @isCompact_collapseBandSource_piece := @isCompact_collapseBandSource_piece
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StaticCapWitness in
example : type_of% @negativeCollapseBand_eq_iUnion := @negativeCollapseBand_eq_iUnion
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StaticCapWitness in
example : type_of% @exists_collapseBandParameter_collapse_eq_cap :=
  @exists_collapseBandParameter_collapse_eq_cap
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord in
example : type_of% @collapseBandOutput := @collapseBandOutput
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord in
example : type_of% @negativeCollapseImage := @negativeCollapseImage
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord in
example : type_of% @isCompact_collapseBandOutput_piece := @isCompact_collapseBandOutput_piece
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord in
example : type_of% @negativeCollapseImage_eq_iUnion := @negativeCollapseImage_eq_iUnion
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord in
example : type_of% @cap_range_subset_oldOutput_union_negativeCollapseImage :=
  @cap_range_subset_oldOutput_union_negativeCollapseImage
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord in
example : type_of% @disjoint_negativeCollapseBand_oldTerminal :=
  @disjoint_negativeCollapseBand_oldTerminal
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord in
example : type_of% @pairwise_disjoint_negativeCollapseBand :=
  @pairwise_disjoint_negativeCollapseBand
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord in
example : type_of% @collapseBandHull := @collapseBandHull
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord in
example : type_of% @isCompact_collapseBandHull := @isCompact_collapseBandHull
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord in
example : type_of% @oldTerminal_subset_collapseBandHull := @oldTerminal_subset_collapseBandHull
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord in
example : type_of% @negativeCollapseBand_subset_collapseBandHull :=
  @negativeCollapseBand_subset_collapseBandHull
end

-- RF.Surgery.Topology.GeometricCutoffRawScale
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord in
example : type_of% @raw_scale_gt_of_recent_nominal_bound := @raw_scale_gt_of_recent_nominal_bound
end

-- RF.Surgery.Topology.GeometricCutoffVolumeNonincrease
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord in
example : type_of% @volume_le_collapseBandHull := @volume_le_collapseBandHull
end

-- RF.Surgery.Topology.HamiltonIveyCurvatureScale
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
example : type_of% @exists_uniform_curvature_bound_of_scaled_fixedHamiltonIveyRegion :=
  @exists_uniform_curvature_bound_of_scaled_fixedHamiltonIveyRegion
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
example : type_of% @exists_uniform_curvature_bound_on_history_slices :=
  @exists_uniform_curvature_bound_on_history_slices
end

-- RF.Surgery.Topology.HistoryNoncollapse.Basic  （无用户声明：shim / re-export）

-- RF.Surgery.Topology.HistoryNoncollapseRadius
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
example : type_of% @exists_noncollapsedBefore_radius_enlargement :=
  @exists_noncollapsedBefore_radius_enlargement
end

-- RF.Surgery.Topology.HistoryParabolicBall.Defs  （无用户声明：shim / re-export）

-- RF.Surgery.Topology.HistoryParabolicSeedRicci  （无用户声明：shim / re-export）

-- RF.Surgery.Topology.HistoryParabolicSeedRicciPortC11P
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @isParabolicallyRmControlledBall.ricci_le_on_past_seed_ball :=
  @isParabolicallyRmControlledBall.ricci_le_on_past_seed_ball
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @isParabolicallyRmControlledBall.ricci_le_on_past_seed_core_on_half_clock :=
  @isParabolicallyRmControlledBall.ricci_le_on_past_seed_core_on_half_clock
end

-- RF.Surgery.Topology.HistoryPinching  （无用户声明：shim / re-export）

-- RF.Surgery.Topology.HistoryStageMetric  （无用户声明：shim / re-export）

-- RF.Surgery.Topology.IdentifiedHistoryPinching
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
example : type_of% @exists_pinching_certificates_for_identified_histories :=
  @exists_pinching_certificates_for_identified_histories
end

-- RF.Surgery.Topology.IncomingSlabCanonicalBounds  （无用户声明：shim / re-export）

-- RF.Surgery.Topology.IncomingSlabDerivativeBounds  （无用户声明：shim / re-export）

-- RF.Surgery.Topology.IncomingSlabGradientBounds  （无用户声明：shim / re-export）

-- RF.Surgery.Topology.InitialLayerBallVolume
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
example : type_of% @exists_initial_layer_all_ball_volume_lower_bound :=
  @exists_initial_layer_all_ball_volume_lower_bound
end

-- RF.Surgery.Topology.InitialScalarUpperBound
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
example : type_of% @exists_scalar_lt_at_initial_metric := @exists_scalar_lt_at_initial_metric
example :
    type_of% @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_scalar_lt_at_time_zero :=
  @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_scalar_lt_at_time_zero
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
example : type_of% @exists_time_zero_high_threshold_vacuity :=
  @exists_time_zero_high_threshold_vacuity
end

-- RF.Surgery.Topology.NeckAnnulusControl  （无用户声明：shim / re-export）

-- RF.Surgery.Topology.NeckAnnulusControlPortC11P
section
example :
    type_of% @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capRadialDerivativeConstant :=
  @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capRadialDerivativeConstant
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
example : type_of% @capRadialDerivativeConstant_bound := @capRadialDerivativeConstant_bound
example : type_of% @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capSeamOpen :=
  @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capSeamOpen
example :
    type_of% @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capSeamOpen_subset_annulus :=
  @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capSeamOpen_subset_annulus
example : type_of% @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capSeamBall_subset :=
  @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capSeamBall_subset
example :
    type_of% @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.annulusLift :=
  @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.annulusLift
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck in
example : type_of% @annulusLift_smooth := @annulusLift_smooth
example :
    type_of% @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.annulusPoint :=
  @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.annulusPoint
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck in
example : type_of% @annulusPoint_apply := @annulusPoint_apply
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck in
example : type_of% @annulusPoint_boundary := @annulusPoint_boundary
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck in
example : type_of% @annulusPoint_retained := @annulusPoint_retained
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck in
example : type_of% @annulusPoint_smooth := @annulusPoint_smooth
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck in
example : type_of% @annulusDerivativeConstant := @annulusDerivativeConstant
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck in
example : type_of% @annulusPoint_speed_le := @annulusPoint_speed_le
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck in
example : type_of% @annulusPoint_edist_le := @annulusPoint_edist_le
end

-- RF.Surgery.Topology.NeckBoundaryChord
section
example :
    type_of% @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.boundaryPoint :=
  @DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.boundaryPoint
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck in
example : type_of% @boundaryPoint_smooth := @boundaryPoint_smooth
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck in
example : type_of% @exists_boundary_curve := @exists_boundary_curve
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck in
example : type_of% @edist_boundaryPoint_le_chord := @edist_boundaryPoint_le_chord
end

-- RF.Surgery.Topology.PresentedStaticCapRadialCoordinates
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap in
example : type_of% @hasRadialCoordinates_of_family_heq := @hasRadialCoordinates_of_family_heq
end

-- RF.Surgery.Topology.PresentedStaticCapRestriction  （无用户声明：shim / re-export）

-- RF.Surgery.Topology.PresentedStaticCapRestrictionPortC11P
section
open DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness in
example : type_of% @weakenOrderAccuracy := @weakenOrderAccuracy
open DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness in
example : type_of% @weakenOrderAccuracy_data := @weakenOrderAccuracy_data
open DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness in
example : type_of% @weakenOrderAccuracy_windowMetric := @weakenOrderAccuracy_windowMetric
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap in
example : type_of% @restrictCanonicalWindow := @restrictCanonicalWindow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap in
example : type_of% @restrictCanonicalWindow_delta := @restrictCanonicalWindow_delta
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap in
example : type_of% @restrictCanonicalWindow_order := @restrictCanonicalWindow_order
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap in
example : type_of% @restrictCanonicalWindow_neck := @restrictCanonicalWindow_neck
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap in
example : type_of% @restrictCanonicalWindow_Output := @restrictCanonicalWindow_Output
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap in
example : type_of% @restrictCanonicalWindow_metric := @restrictCanonicalWindow_metric
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap in
example : type_of% @restrictCanonicalWindow_inclusion := @restrictCanonicalWindow_inclusion
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap in
example : type_of% @restrictCanonicalWindow_cap := @restrictCanonicalWindow_cap
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap in
example : type_of% @restrictCanonicalWindow_retained := @restrictCanonicalWindow_retained
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap in
example : type_of% @restrictCanonicalWindow_collapse := @restrictCanonicalWindow_collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap in
example : type_of% @restrictCanonicalWindow_tip := @restrictCanonicalWindow_tip
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap in
example : type_of% @restrictCanonicalWindow_capChart := @restrictCanonicalWindow_capChart
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap in
example : type_of% @restrictCanonicalWindow_retainedPoint := @restrictCanonicalWindow_retainedPoint
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap in
example : type_of% @restrictCanonicalWindow_window := @restrictCanonicalWindow_window
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap in
example : type_of% @restrictCanonicalWindow_windowMetric := @restrictCanonicalWindow_windowMetric
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap in
example : type_of% @hasCanonicalWindow_restrictCanonicalWindow :=
  @hasCanonicalWindow_restrictCanonicalWindow
end

-- RF.Surgery.Topology.QuantitativeStageWindowProtection
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @exists_uniform_stage_window_protection :=
  @exists_uniform_stage_window_protection
end

-- RF.Surgery.Topology.RecentCaptureScale
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory in
example : type_of% @exists_recent_cap_capture_scale_of_isEmpty_backwardPointTrace :=
  @exists_recent_cap_capture_scale_of_isEmpty_backwardPointTrace
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory in
example : type_of% @isParabolicallyRmControlledBall_of_recent_cap_scale_separation :=
  @isParabolicallyRmControlledBall_of_recent_cap_scale_separation
end

-- RF.Surgery.Topology.RecentCutoffRadius
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord in
example : type_of% @nominalRadius_lt_mul_of_accuracy_bound :=
  @nominalRadius_lt_mul_of_accuracy_bound
end

-- RF.Surgery.Topology.RetainedRecordPrefix  （无用户声明：shim / re-export）

-- RF.Surgery.Topology.SlabGradientScalarControlC11X  （无用户声明：shim / re-export）

-- RF.Surgery.Topology.SlabGradientScalarControlC11XPortC11P
section
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood in
example : type_of% @scalar_le_four_mul_max_of_gradient_bound_of_max_pos :=
  @scalar_le_four_mul_max_of_gradient_bound_of_max_pos
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab in
example : type_of% @scalar_le_four_mul_max_of_gradient_bound_at_time_of_max_pos :=
  @scalar_le_four_mul_max_of_gradient_bound_at_time_of_max_pos
end

-- RF.Surgery.Topology.StaticCapCoordinates
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StaticCapWitness in
example : type_of% @HasRadialCoordinates := @HasRadialCoordinates
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StaticCapWitness.HasRadialCoordinates in
example : type_of% @reparametrizeCapOfLinearIsometry := @reparametrizeCapOfLinearIsometry
end

-- RF.Surgery.Topology.TerminalDistanceUpperLimit
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab in
example : type_of% @TerminalLimitMetric.eventually_ambient_edist_le :=
  @TerminalLimitMetric.eventually_ambient_edist_le
end

-- RF.Surgery.Topology.TracedRegionRecenter
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.isTracedRegion in
example : type_of% @recenter := @recenter
end

-- RF.Surgery.Topology.UniformCapWindowContinuation
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory in
example : type_of% @exists_uniform_capWindowPoint_bounds := @exists_uniform_capWindowPoint_bounds
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory in
example : type_of% @exists_uniform_capWindow_canonicalBoundsOn :=
  @exists_uniform_capWindow_canonicalBoundsOn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
example : type_of% @exists_uniform_capWindowContinuation := @exists_uniform_capWindowContinuation
end

-- RF.Surgery.Topology.UniformCapWindowSpatialCanonicalWitness
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory in
example : type_of% @exists_uniform_capWindowPoint_spatialCanonicalWitness :=
  @exists_uniform_capWindowPoint_spatialCanonicalWitness
end

-- RF.Surgery.Topology.UniformObservationEstimatePacket
section
example : type_of% @GC.GeneralFlow.exists_uniform_observation_estimate_packet :=
  @GC.GeneralFlow.exists_uniform_observation_estimate_packet
end

-- RF.Surgery.Topology.UniformSlabStartDerivativeBounds
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory in
example : type_of% @exists_uniform_slice_bounds_at_slab_start :=
  @exists_uniform_slice_bounds_at_slab_start
end

-- RF.Surgery.Topology.UniformSpatialCrossingContinuation
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
example : type_of% @exists_uniform_spatialCrossingContinuation :=
  @exists_uniform_spatialCrossingContinuation
end

-- RF.Surgery.Topology.UniversalCanonicalContinuation
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
example : type_of% @exists_universal_canonicalNeighborhoodContinuation :=
  @exists_universal_canonicalNeighborhoodContinuation
end

-- RF.Surgery.Topology.UniversalSpatialCanonicalContinuation
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
example : type_of% @exists_universal_spatialCanonicalContinuation :=
  @exists_universal_spatialCanonicalContinuation
end

-- RF.Surgery.Topology.WholeCanonicalComponentSeedVolume  （无用户声明：shim / re-export）

-- RF.Surgery.Topology.WholeCanonicalComponentSeedVolumePortC11P
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
example : type_of% @exists_ball_volume_lower_of_whole_canonical_component_and_seed :=
  @exists_ball_volume_lower_of_whole_canonical_component_and_seed
end

-- DG.Topology.Manifold.InverseFunctionTheorem.FiniteParameterGraph
section
open DifferentialGeometry.Coordinates in
example : type_of% @isLocalDiffeomorphAt_parameter_graph_of_slice_bijective_two :=
  @isLocalDiffeomorphAt_parameter_graph_of_slice_bijective_two
open DifferentialGeometry.Coordinates in
example : type_of% @isLocalDiffeomorphAt_parameter_graph_of_exponential_germ_two :=
  @isLocalDiffeomorphAt_parameter_graph_of_exponential_germ_two
end

-- DG.Topology.MetricSpace.TruncatedDistanceLevel
section
example : type_of% @EMetric.lipschitzWith_truncated_edist_level :=
  @EMetric.lipschitzWith_truncated_edist_level
example : type_of% @EMetric.truncated_edist_level_mem_Icc := @EMetric.truncated_edist_level_mem_Icc
end

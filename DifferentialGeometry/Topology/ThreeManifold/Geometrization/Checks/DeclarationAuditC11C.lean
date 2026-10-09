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
import Lean

set_option autoImplicit false

/-!
# ch11 搬入模块的 declaration audit（`_C11C`，S-CH11-CONS G2）

照 `DeclarationAudit.lean` 的格式，但 ch11 搬入模块全部**无任何 admission**：`expected` 为空，任何
`sorryAx`（类型里、值里、公理依赖里）、unsafe、自带 `axiomInfo` 都报错。`owned` = 被审计模块；
`authored` = 其中用户写的 public theorem 名（必须存在于环境）。生成脚本
`build-logs/scratch/S-CH11-CONS/mkconsumer.py`。不改已跟踪的 `DeclarationAudit.lean`。
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let owned : List String := [
    "DifferentialGeometry.Analysis.Calculus.Cutoff.SingularBarrier",
    "DifferentialGeometry.Analysis.Calculus.UpperSupport.WithTop",
    "DifferentialGeometry.Analysis.Calculus.UpperSupport.WithTopPortC11P",
    "DifferentialGeometry.Analysis.Integration.Measure.Jacobian.LipschitzImageIntegral",
    "DifferentialGeometry.Analysis.Integration.Measure.Parametric.DensityComparisonC11X",
    "DifferentialGeometry.Analysis.Integration.Measure.Riemannian.LipschitzImagePortC11X",
    "DifferentialGeometry.Analysis.Order.CommonProfileComparison",
    "DifferentialGeometry.Analysis.Order.CommonProfileDecay",
    "DifferentialGeometry.Analysis.Order.CommonProfileFamily",
    "DifferentialGeometry.Geometry.Collapse.CurvatureRadiusNormBound",
    "DifferentialGeometry.Geometry.Collapse.CurvatureScaleNearbyVolume",
    "DifferentialGeometry.Geometry.Collapse.TestedBallVolumeSeed",
    "DifferentialGeometry.Geometry.Collapse.VolumeTriggerBounds",
    "DifferentialGeometry.Geometry.Comparison.Variation.EndpointAccelerationChain",
    "DifferentialGeometry.Geometry.Comparison.Variation.Field.CompactExponential",
    "DifferentialGeometry.Geometry.Comparison.Variation.Field.FiniteJointFrames",
    "DifferentialGeometry.Geometry.Comparison.Variation.Field.FiniteJointRealization",
    "DifferentialGeometry.Geometry.Comparison.Variation.Field.JointRealization",
    "DifferentialGeometry.Geometry.Comparison.Variation.Field.LocalJointRealization",
    "DifferentialGeometry.Geometry.Comparison.Variation.Field.ParameterEndpointCorrection",
    "DifferentialGeometry.Geometry.Connection.Hessian.FiniteScalarTrace",
    "DifferentialGeometry.Geometry.Connection.Hessian.FiniteScalarTracePortC11P",
    "DifferentialGeometry.Geometry.Curvature.DimensionThree.SectionalScalarBounds",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.FixedEndpoints",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.FixedTerminalOpenBuffer",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.LocalDistanceContinuity",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.ScalarTimeComparison",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.TerminalBallProtection",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.AnalyticAdmissibility.Defs",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CurvatureBounds",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ParabolicCurvature",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.PostSurgeryMetric",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.RegularSlice.Defs",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.SmallEnlargementScalar",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.\
      FiniteHornGeometry.SpatialData",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.\
      LocalPropagation.Basic",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.\
      SphereChordConnector",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.\
      FiniteJointAction",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.\
      JointRegularity",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.\
      FiniteTraceEnergy",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.CountableClosedStripGluing",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.PowerNormalizedVolume",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornCutoffRecordC11X",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.\
      HornFineCutoffRecordC11X",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.\
      PoincareHornCutoffRecordOfFineCutNecksC11X",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.\
      FiniteObservationContinuation",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.MatchedRawScale",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.ScaffoldData",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.\
      ClosedTimeACSplice",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.\
      CollarCompetitors",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.CostDefs",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.\
      InterleavedJoins",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.\
      InterleavedJointAction",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.\
      PhysicalClockSupport",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.\
      PhysicalCollarReserve",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.\
      RecentScalarCost",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.\
      SmallPrefixTrace",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.\
      SmoothCollarCompetitors",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.\
      SmoothCollarContact",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.\
      SmoothStageRepresentatives",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.\
      SmoothSurvivorJoins",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.\
      SmoothSurvivorRepresentatives",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.StageSolution",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.\
      ZeroPoleComparison",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.\
      GeometricObservationStep",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.\
      GeometricObservationStepPortC11P",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.\
      SpatialWitnessTransport",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.ReducedVolume.\
      RegularEndpointBlock",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.\
      CanonicalStaticCoordinates",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      AncientLimitSurvivorCanonicalWitnessC11X",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      BackwardTraceCurvatureControl",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      BackwardTraceScalarControl.TimeLocal",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      BoundedCurvatureAtDistanceAfterEventC11X",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      CanonicalCutoffRecordFamily",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      CanonicalCutoffRecordSplicing",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      CanonicalTimeControlPointSelection",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapAnnulusCoordinates",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      CapAnnulusCoordinatesPortC11P",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapBoundaryChord",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowActionC11X",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowEllipticity",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowLocalInverse",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      CapWindowLocalInversePortC11P",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      ClosedSliceScalarEscape",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ConeAccuracy",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      ControlledBallTerminalJets",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      CrossingAncientLimitSpatialC11X",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffParameterGluing",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordAccuracy",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordSplicing",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      CutoffRecordSplicingPortC11P",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      EventCanonicalWindowData",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventCapCapture.Basic",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventDistanceScalar",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      EventDistanceScalarPresentation",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      EventDistanceScalarTransport",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      EventDistanceScalarTransportPortC11P",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventRetainedVolume",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FinalSlabNoncollapse",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      FinalSlabNoncollapsePortC11P",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      FinitePresentedStaticCapC11X",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      FirstCurvatureContactVolume",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      FirstCurvatureContactVolumePortC11P",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      GeometricCutoffCollapseBands",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      GeometricCutoffRawScale",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      GeometricCutoffVolumeNonincrease",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      HamiltonIveyCurvatureScale",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryNoncollapse.\
      Basic",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      HistoryNoncollapseRadius",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicBall.\
      Defs",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      HistoryParabolicSeedRicci",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      HistoryParabolicSeedRicciPortC11P",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryPinching",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStageMetric",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      IdentifiedHistoryPinching",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      IncomingSlabCanonicalBounds",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      IncomingSlabDerivativeBounds",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      IncomingSlabGradientBounds",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialLayerBallVolume",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      InitialScalarUpperBound",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckAnnulusControl",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      NeckAnnulusControlPortC11P",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckBoundaryChord",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      PresentedStaticCapRadialCoordinates",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      PresentedStaticCapRestriction",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      PresentedStaticCapRestrictionPortC11P",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      QuantitativeStageWindowProtection",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RecentCaptureScale",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RecentCutoffRadius",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedRecordPrefix",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      SlabGradientScalarControlC11X",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      SlabGradientScalarControlC11XPortC11P",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCapCoordinates",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      TerminalDistanceUpperLimit",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionRecenter",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      UniformCapWindowContinuation",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      UniformCapWindowSpatialCanonicalWitness",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      UniformObservationEstimatePacket",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      UniformSlabStartDerivativeBounds",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      UniformSpatialCrossingContinuation",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      UniversalCanonicalContinuation",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      UniversalSpatialCanonicalContinuation",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      WholeCanonicalComponentSeedVolume",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      WholeCanonicalComponentSeedVolumePortC11P",
    "DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.FiniteParameterGraph",
    "DifferentialGeometry.Topology.MetricSpace.TruncatedDistanceLevel"]
  let authored : List String := [
    "DifferentialGeometry.Analysis.SingularBarrier.contDiffOn",
    "DifferentialGeometry.Analysis.SingularBarrier.one_le",
    "DifferentialGeometry.Analysis.SingularBarrier.pos",
    "DifferentialGeometry.Analysis.SingularBarrier.monotoneOn",
    "DifferentialGeometry.Analysis.SingularBarrier.one_of_le",
    "DifferentialGeometry.Analysis.SingularBarrier.deriv_nonneg",
    "DifferentialGeometry.Analysis.SingularBarrier.deriv_pos",
    "DifferentialGeometry.Analysis.SingularBarrier.deriv_zero_of_le",
    "DifferentialGeometry.Analysis.SingularBarrier.deriv2_zero_of_le",
    "DifferentialGeometry.Analysis.SingularBarrier.deriv2_zero_of_deriv_zero",
    "DifferentialGeometry.Analysis.SingularBarrier.tendsto_at_pole",
    "DifferentialGeometry.Analysis.SingularBarrier.bound_nonneg",
    "DifferentialGeometry.Analysis.SingularBarrier.differential_bound",
    "DifferentialGeometry.Analysis.SingularBarrier.exists_constant",
    "WithTop.antitoneOn_of_lowerSemicontinuousOn_of_upper_support_below",
    "MeasureTheory.image_lintegral_le_of_locallyLipschitzOn",
    "DifferentialGeometry.Integral.Measure.paramDensity_le_of_inner_mfderiv_le",
    "DifferentialGeometry.Integral.Measure.\
      riemannianVolumeMeasure_image_le_of_locally_nonexpanding",
    "GC.GeneralFlow.exists_decaying_commonProfile_sq_mul_lt",
    "GC.GeneralFlow.commonProfile_tendsto_zero",
    "GC.GeneralFlow.exists_decaying_commonProfile",
    "GC.GeneralFlow.prefixBudget_mono",
    "GC.GeneralFlow.commonProfile_mono",
    "GC.GeneralFlow.exists_antitone_family_minorant",
    "GC.GeneralFlow.exists_decaying_commonProfile_sq_mul_lt_and_diagonal",
    "DifferentialGeometry.Geometry.Collapse.\
      exists_uniform_whole_radius_curvature_bound_of_tested_bounds",
    "DifferentialGeometry.Geometry.Collapse.exists_uniform_whole_radius_curvature_bound",
    "DifferentialGeometry.Geometry.Collapse.ballVolume_lower_near_curvature_scale",
    "DifferentialGeometry.Geometry.Collapse.sectional_and_volume_lower_of_tested_ball",
    "DifferentialGeometry.Geometry.Collapse.\
      ballVolume_le_of_volumeCollapsedAtCurvatureScale",
    "DifferentialGeometry.Geometry.Collapse.radius_lt_of_volumeCollapsedAtCurvatureScale",
    "DifferentialGeometry.Geometry.Riemannian.Variation.\
      sum_variation_acceleration_boundary_eq_endpoints",
    "DifferentialGeometry.Geometry.Riemannian.Variation.\
      centralVariationAcceleration_eq_zero_of_exp_germ",
    "DifferentialGeometry.Geometry.Riemannian.Variation.\
      sum_variation_acceleration_boundary_eq_zero_of_terminal_exp",
    "DifferentialGeometry.Geometry.Riemannian.Variation.exists_compact_exponential",
    "DifferentialGeometry.Geometry.Riemannian.Variation.frameParameter_apply",
    "DifferentialGeometry.Geometry.Riemannian.Variation.frameParameter_single",
    "DifferentialGeometry.Geometry.Riemannian.Variation.\
      exists_compatible_joint_variation_of_fields",
    "DifferentialGeometry.Geometry.Riemannian.Variation.\
      exists_compatible_joint_variation_of_linear_fields",
    "DifferentialGeometry.Geometry.Riemannian.Variation.\
      exists_joint_variation_of_linear_fields",
    "DifferentialGeometry.Geometry.Riemannian.Variation.\
      exists_joint_variation_of_linear_fields_on",
    "DifferentialGeometry.Geometry.Riemannian.Variation.\
      correct_parameter_variation_endpoint",
    "DifferentialGeometry.Geometry.Connection.\
      abstractHessian_eq_inner_cov_gradientFun_of_contMDiffAt_two",
    "DifferentialGeometry.Geometry.Connection.\
      laplacian_eq_sum_abstractHessian_of_contMDiffAt_two",
    "DifferentialGeometry.Geometry.Connection.\
      abstractHessian_eq_deriv_deriv_expMap_of_contMDiffAt_two",
    "DifferentialGeometry.Geometry.Curvature.DimensionThree.\
      sqrt_normSq0S_le_of_sectional_lower_scalar_upper",
    "DifferentialGeometry.PDE.RicciFlow.\
      riemannianEDistOf_le_add_of_endpoint_ricci_on_interval",
    "DifferentialGeometry.PDE.RicciFlow.exists_fixed_open_terminal_buffer",
    "DifferentialGeometry.PDE.RicciFlow.\
      continuousOn_min_edist_of_compact_protected_domain",
    "DifferentialGeometry.PDE.RicciFlow.\
      continuousOn_min_edist_toReal_of_compact_protected_domain",
    "DifferentialGeometry.PDE.RicciFlow.IsSolutionOn.lipschitzOnWith_inv_max_scalar_Icc",
    "DifferentialGeometry.PDE.RicciFlow.IsSolutionOn.scalar_le_of_quadratic_time_bound",
    "DifferentialGeometry.PDE.RicciFlow.IsSolutionOn.\
      scalar_le_two_mul_of_quadratic_time_bound",
    "DifferentialGeometry.PDE.RicciFlow.exists_pos_moving_closedBall_subset_terminal_ball",
    "GC.LongTime.exists_postMetric_curvature_bounds_of_cutoff_records",
    "GC.LongTime.hasSmallParabolicCurvature.scalar_abs_le",
    "DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.\
      sphere2_exists_chord_controlled_curve",
    "DifferentialGeometry.PDE.RicciFlow.Perelman.contDiffOn_finiteJointAction",
    "DifferentialGeometry.PDE.RicciFlow.Perelman.exists_finiteJointAction_endpoint_branch",
    "DifferentialGeometry.PDE.RicciFlow.Perelman.contDiffOn_lRegularizedAction_joint",
    "DifferentialGeometry.PDE.RicciFlow.Perelman.\
      sum_lRegularizedIndex_trace_linear_cutoff_eq_energy",
    "DifferentialGeometry.PDE.RicciFlow.exists_solution_of_coherent_closed_strips",
    "DifferentialGeometry.PDE.RicciFlow.\
      exists_complete_solution_of_coherent_closed_strips",
    "DifferentialGeometry.PDE.RicciFlow.SolutionOn.hasDerivAt_rpow_mul_volume",
    "DifferentialGeometry.PDE.RicciFlow.SolutionOn.antitoneOn_rpow_mul_volume",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.\
      exists_horn_cutoff_history_extension_with_canonical_windows_of_fineCutNecks_with_radi\
      al_coordinates",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.\
      exists_horn_cutoff_record_with_uniform_volume_debit_of_spatiallyCanonical_of_fineCutN\
      ecks_with_radial_coordinates",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.\
      exists_closedSlab_extension_of_eventCount_bounded",
    "GC.GeneralFlow.all_record_fields_of_successors",
    "GC.GeneralFlow.all_parameter_values_of_successors",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      exists_three_piece_stage_curve",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      sum_stage_parts_eq_endpoints_add_events",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      exists_stage_family_of_collar_pieces",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      extend_stage_family_by_zero_pole_stage",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      regularizedCost_le_collar_piece_action",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      regularizedCost_le_of_zero_pole_stage_extension",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      interleavedJoinEquiv_values",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      exists_interleaved_actual_joins",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      interleavedPieceEquiv_values",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      interleaved_actual_flow_joint_families",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      physical_clock_support_of_same_history_jets",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      exists_physical_collar_reserve_of_attained_action",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      regularizedCost_ge_recent_half_time_of_cutoff_records",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      regularizedStageStart_eq_max_zero",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      sum_stage_action_eq_of_collapsed_suffix",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      tendsto_regularizedWeightedStageAction_of_collapsed_suffix",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      tendsto_regularizedStage_trace_energy",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      exists_small_prefix_trace_energy_lt",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      smooth_curve_projected_action",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      smooth_survivor_curve_projected_actions",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      regularizedCost_le_smooth_collar_action",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      smooth_collar_action_eq_sum_stage_action",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      exists_smooth_prefix_stage_representatives",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      exists_smooth_survivor_directed_joins",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      exists_smooth_prefix_survivor_representatives",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      exists_stage_incomingSlab_metric",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      zero_mem_regularizedActionValues_self",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      regularizedActionValues_subset_of_zero_pole",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      regularizedCost_le_of_zero_pole",
    "GC.GeneralFlow.exists_geometric_observation_step",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.\
      exists_test_volume_lower_of_regular_endpoint_block",
    "DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.\
      window_eq_retainedMap",
    "DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.\
      toStaticCapWitness_hasRadialCoordinates",
    "DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.\
      eventually_exists_canonicalWitness_survivor_of_normalized_local_flow_limit",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace.\
      scalar_le_two_mul_of_time_local_derivative_control",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.\
      exists_scalar_bound_at_distance_of_not_capWindowPoint_of_birth_metric_comparison",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.\
      exists_scalar_bound_at_distance_of_not_capWindowPoint_at_birth",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.\
      exists_isCanonicalCutoffRecordFamily_appendEvent_spliceAfter",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      exists_localized_canonical_time_control_point_selection",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capSeamWidth_pos",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capSeamWidth_le_radius",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capSeamWidth_le_one",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capRadialCoordinates_pos_smul",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capSeamAnnulus_ne_zero",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCompact_capSeamAnnulus",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capRadialCoordinates_smooth",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.\
      exists_capRadialCoordinates_bound",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capBoundaryCoordinate_injective",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.\
      PresentedStaticCap.oldTerminal_boundaryOldPoint",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.\
      PresentedStaticCap.oldOutput_boundaryOldPoint",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.\
      PresentedStaticCap.exists_actual_boundary_curve",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.\
      PresentedStaticCap.exists_boundary_distance_extension",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.\
      PresentedStaticCap.exists_actual_cap_distance_extension",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.\
      exists_cap_boundary_distance_extension",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      exists_uniform_prepared_cap_birth_action_lower_bound_of_parabolicallyRmControlledBall\
      _with_window_scale_bound",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.\
      exists_uniform_presented_window_ellipticity",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.\
      exists_uniform_local_window_inverse_on_closed_core",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.\
      exists_uniform_local_window_inverse",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      exists_eventually_canonicalWitness_survivor_of_isTracedRegion_at_closed_time",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      exists_eventually_spatialCanonicalWitness_of_isTracedRegion_at_closed_time",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutoffParameters.\
      diagonal_eq_on_prefix",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutoffParameters.\
      diagonal_eval_of_nonpos",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutoffParameters.\
      diagonal_delta_eq",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutoffParameters.\
      diagonal_neckRadius_antitone",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutoffParameters.\
      spliceAfter_eval_of_le",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutoffParameters.\
      spliceAfter_eval_of_lt",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutoffParameters.\
      spliceAfter_neckRadius_antitone",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.\
      diagonalParameters_preserves",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.\
      spliceAfterParametersOfLE_preserves",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.\
      spliceAfterParametersOfLT_preserves",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.\
      exists_of_delta_le_of_neckRadius_le",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.\
      appendEvent_nominalRadius_heq",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.\
      exists_cutoff_records_at_appendEvent_spliceAfter",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.\
      HasUniformDistanceScalar.of_coreEvent_heq",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.\
      HasUniformDistanceScalar.oldTerminal_edist_le",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.\
      SamePresentation.hasUniformDistanceScalar",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.\
      hasUniformDistanceScalar_event",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.\
      hasUniformDistanceScalar_restrict",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.\
      oldOutput_volume_eq_oldTerminal_volume",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.\
      terminalNoncollapsedBefore_finalSlab",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.\
      exists_presentedStaticCap_neck_heq_window_eq_coordinates_of_finiteMetricEvent",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.\
      exists_presentedStaticCap_neck_heq_window_eq_coordinates_of_finiteMetricEvent_termina\
      l",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.\
      finitePresentedStaticCaps_hasRadialCoordinates",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.\
      finitePresentedStaticCapsOfTerminal_hasRadialCoordinates",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.\
      exists_ball_volume_lower_of_seed_and_canonical_first_contacts",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StaticCapWitness.\
      tipCoordinate_neg",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StaticCapWitness.\
      collapseBandParameter_coe",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StaticCapWitness.\
      isCompact_compactBandParameters",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StaticCapWitness.\
      compactBandParameters_mono",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StaticCapWitness.\
      iUnion_compactBandParameters",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StaticCapWitness.\
      isCompact_collapseBandSource_range",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StaticCapWitness.\
      isCompact_collapseBandSource_piece",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StaticCapWitness.\
      negativeCollapseBand_eq_iUnion",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StaticCapWitness.\
      exists_collapseBandParameter_collapse_eq_cap",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.\
      isCompact_collapseBandOutput_piece",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.\
      negativeCollapseImage_eq_iUnion",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.\
      cap_range_subset_oldOutput_union_negativeCollapseImage",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.\
      disjoint_negativeCollapseBand_oldTerminal",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.\
      pairwise_disjoint_negativeCollapseBand",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.\
      isCompact_collapseBandHull",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.\
      oldTerminal_subset_collapseBandHull",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.\
      negativeCollapseBand_subset_collapseBandHull",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.\
      raw_scale_gt_of_recent_nominal_bound",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.\
      volume_le_collapseBandHull",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.\
      exists_uniform_curvature_bound_of_scaled_fixedHamiltonIveyRegion",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.\
      exists_uniform_curvature_bound_on_history_slices",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.\
      exists_noncollapsedBefore_radius_enlargement",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      isParabolicallyRmControlledBall.ricci_le_on_past_seed_ball",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      isParabolicallyRmControlledBall.ricci_le_on_past_seed_core_on_half_clock",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.\
      exists_pinching_certificates_for_identified_histories",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.\
      exists_initial_layer_all_ball_volume_lower_bound",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.\
      exists_scalar_lt_at_initial_metric",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_scalar_lt_at_time_zero",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.\
      exists_time_zero_high_threshold_vacuity",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.\
      capRadialDerivativeConstant_bound",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capSeamOpen_subset_annulus",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capSeamBall_subset",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.\
      annulusLift_smooth",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.\
      annulusPoint_apply",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.\
      annulusPoint_boundary",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.\
      annulusPoint_retained",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.\
      annulusPoint_smooth",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.\
      annulusPoint_speed_le",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.\
      annulusPoint_edist_le",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.\
      boundaryPoint_smooth",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.\
      exists_boundary_curve",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.\
      edist_boundaryPoint_le_chord",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.\
      PresentedStaticCap.hasRadialCoordinates_of_family_heq",
    "DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.\
      weakenOrderAccuracy_data",
    "DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.\
      weakenOrderAccuracy_windowMetric",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.\
      PresentedStaticCap.restrictCanonicalWindow_delta",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.\
      PresentedStaticCap.restrictCanonicalWindow_order",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.\
      PresentedStaticCap.restrictCanonicalWindow_neck",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.\
      PresentedStaticCap.restrictCanonicalWindow_Output",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.\
      PresentedStaticCap.restrictCanonicalWindow_metric",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.\
      PresentedStaticCap.restrictCanonicalWindow_inclusion",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.\
      PresentedStaticCap.restrictCanonicalWindow_cap",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.\
      PresentedStaticCap.restrictCanonicalWindow_retained",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.\
      PresentedStaticCap.restrictCanonicalWindow_collapse",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.\
      PresentedStaticCap.restrictCanonicalWindow_tip",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.\
      PresentedStaticCap.restrictCanonicalWindow_capChart",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.\
      PresentedStaticCap.restrictCanonicalWindow_retainedPoint",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.\
      PresentedStaticCap.restrictCanonicalWindow_window",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.\
      PresentedStaticCap.restrictCanonicalWindow_windowMetric",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.\
      PresentedStaticCap.hasCanonicalWindow_restrictCanonicalWindow",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      exists_uniform_stage_window_protection",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.\
      exists_recent_cap_capture_scale_of_isEmpty_backwardPointTrace",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.\
      isParabolicallyRmControlledBall_of_recent_cap_scale_separation",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.\
      nominalRadius_lt_mul_of_accuracy_bound",
    "DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.\
      scalar_le_four_mul_max_of_gradient_bound_of_max_pos",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.\
      scalar_le_four_mul_max_of_gradient_bound_at_time_of_max_pos",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StaticCapWitness.\
      HasRadialCoordinates.reparametrizeCapOfLinearIsometry",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.\
      TerminalLimitMetric.eventually_ambient_edist_le",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.isTracedRegion.\
      recenter",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.\
      exists_uniform_capWindowPoint_bounds",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.\
      exists_uniform_capWindow_canonicalBoundsOn",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.\
      exists_uniform_capWindowContinuation",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.\
      exists_uniform_capWindowPoint_spatialCanonicalWitness",
    "GC.GeneralFlow.exists_uniform_observation_estimate_packet",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.\
      exists_uniform_slice_bounds_at_slab_start",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.\
      exists_uniform_spatialCrossingContinuation",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.\
      exists_universal_canonicalNeighborhoodContinuation",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.\
      exists_universal_spatialCanonicalContinuation",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.\
      exists_ball_volume_lower_of_whole_canonical_component_and_seed",
    "DifferentialGeometry.Coordinates.\
      isLocalDiffeomorphAt_parameter_graph_of_slice_bijective_two",
    "DifferentialGeometry.Coordinates.\
      isLocalDiffeomorphAt_parameter_graph_of_exponential_germ_two",
    "EMetric.lipschitzWith_truncated_edist_level",
    "EMetric.truncated_edist_level_mem_Icc"]
  for s in authored do
    unless (env.find? s.toName).isSome do throwError "Missing declaration {s}"
  let expected : List Name := []
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for modS in owned do
    let mod := modS.toName
    let some idx := env.getModuleIdx? mod | throwError "Missing module {mod}"
    for name in env.header.moduleData[idx.toNat]!.constNames do
      let some info := env.find? name | throwError "Unchecked declaration {name}"
      if info.isAxiom || info.isUnsafe then
        throwError "Unexpected axiomInfo or unsafe declaration {name}"
      if info.type.getUsedConstants.contains ``sorryAx then
        throwError "Admission in declaration type {name}"
      let valueUses := (info.value? (allowOpaque := true)).map Expr.getUsedConstants
      if valueUses.any (fun ns => ns.contains ``sorryAx) then
        unless expected.contains name do throwError "Unregistered direct admission {name}"
      for ax in (← collectAxioms name) do
        unless allowed.contains ax do throwError "Unexpected axioms {ax} in {name}"
      count := count + 1
  let msg : String := s!"ch11 declaration audit: {owned.length} modules, {count} declarations, "
    ++ s!"{authored.length} authored theorems present, 0 admissions."
  logInfo msg

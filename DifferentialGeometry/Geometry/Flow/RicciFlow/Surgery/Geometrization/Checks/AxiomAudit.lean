import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.Checks.MetricAndSeamExamples
import DifferentialGeometry.Analysis.Order.CommonProfile
import DifferentialGeometry.External.GraphCoveringTheory.Kurosh
import DifferentialGeometry.External.GraphCoveringTheory.KuroshActive
import DifferentialGeometry.External.GraphCoveringTheory.KuroshCover
import DifferentialGeometry.External.GraphCoveringTheory.KuroshCoverAction
import DifferentialGeometry.External.GraphCoveringTheory.KuroshCoverConnected
import DifferentialGeometry.External.GraphCoveringTheory.KuroshCoverLift
import DifferentialGeometry.External.GraphCoveringTheory.KuroshCoverLocal
import DifferentialGeometry.External.GraphCoveringTheory.KuroshCoverStar
import DifferentialGeometry.External.GraphCoveringTheory.KuroshFreeCorollary
import DifferentialGeometry.External.GraphCoveringTheory.KuroshFreeFiber
import DifferentialGeometry.External.GraphCoveringTheory.KuroshFreePart
import DifferentialGeometry.External.GraphCoveringTheory.KuroshKernel
import DifferentialGeometry.External.GraphCoveringTheory.KuroshPathEndpoint
import DifferentialGeometry.External.GraphCoveringTheory.KuroshPathInjective
import DifferentialGeometry.External.GraphCoveringTheory.KuroshPathRelation
import DifferentialGeometry.External.GraphCoveringTheory.KuroshPathRelationInvariant
import DifferentialGeometry.External.GraphCoveringTheory.KuroshRawPathValue
import DifferentialGeometry.External.GraphCoveringTheory.KuroshTheorem
import DifferentialGeometry.External.GraphCoveringTheory.KuroshTree
import DifferentialGeometry.External.GrushkoNeumannTheorem.MarshallHall.Grushko
import DifferentialGeometry.External.GrushkoNeumannTheorem.MarshallHall.GrushkoEdge
import DifferentialGeometry.External.GrushkoNeumannTheorem.MarshallHall.GrushkoFold
import DifferentialGeometry.External.GrushkoNeumannTheorem.MarshallHall.GrushkoFoldStep
import DifferentialGeometry.External.GrushkoNeumannTheorem.MarshallHall.GrushkoFull
import DifferentialGeometry.External.GrushkoNeumannTheorem.MarshallHall.GrushkoGeneral
import DifferentialGeometry.External.GrushkoNeumannTheorem.MarshallHall.GrushkoGraph
import DifferentialGeometry.External.GrushkoNeumannTheorem.MarshallHall.GrushkoInvariant
import DifferentialGeometry.External.GrushkoNeumannTheorem.MarshallHall.GrushkoReduction
import DifferentialGeometry.External.GrushkoNeumannTheorem.MarshallHall.GrushkoReductionChain
import DifferentialGeometry.External.GrushkoNeumannTheorem.MarshallHall.GrushkoRemove
import DifferentialGeometry.External.GrushkoNeumannTheorem.MarshallHall.GrushkoRose
import DifferentialGeometry.External.GrushkoNeumannTheorem.MarshallHall.GrushkoUnfold
import DifferentialGeometry.External.GrushkoNeumannTheorem.MarshallHall.GrushkoUnsafe
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComponentVolumeBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.KappaLoss
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.KappaModelVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelBallVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ReservedCanonical
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RoundCoverVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RoundImageVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RoundReservedWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialRoundFiniteDegree
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.ClassifiedHistory
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.ObservedHistory
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.OrientedReconstruction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.RawHistory
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.SmoothReconstruction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.ActualEventGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.CoherentSurgeryTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.CoherentTowerConsequences
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.ConcatenationHorizon
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.EventTimeTranslation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.FiniteConcatenation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.GeneralPrefixExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.LateOrEmpty
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.MarkedContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.RawSurgery
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.SlabCompatibility
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.SurgeryEventControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.TerminalTimeTranslation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.TowerFinitePrefixes
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.CompletedHistoryDegree
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.CutoffProfiles
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.DegreeBoundCanonical
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.DegreeGeometricHorizon
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.FiniteGeometricHorizon
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.FiniteInitialDegree
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.GeneralCanonicalFromSmallScale
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.GeneralCanonicalProduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.GeneralInitialBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.GeometricHorizons
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.HistoryDegreeBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.HistoryFreeFactors
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.InitialDecomposition
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.JointCutoffProfiles
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.ProfileQuantifiers
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.ReserveContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.SmallScaleFromDegree
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.SmallScaleGeometricHorizon
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCapGroups
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCapFreeFactor
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCapReconstruction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedComponentGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialFundamentalGroup
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MarkedDiscardedGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MarkedReconstruction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ReconstructionSlots
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedDiscardedLabels
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TubeFreeFactors
import DifferentialGeometry.Geometry.Metric.Approximation.PointedBallApproximation
import DifferentialGeometry.Geometry.Metric.Approximation.RealBallExamples
import DifferentialGeometry.Geometry.Metric.Scaling.EuclideanBalls
import DifferentialGeometry.Geometry.Metric.Scaling.RiemannianBalls
import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.AntipodalQuotient
import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.SphericalMetric
import DifferentialGeometry.Geometry.Thurston.Atlas
import DifferentialGeometry.Geometry.Thurston.ElementaryModels
import DifferentialGeometry.Geometry.Thurston.ModelAtlas
import DifferentialGeometry.Geometry.Thurston.Models
import DifferentialGeometry.Geometry.Thurston.Models.CoordinateHomogeneity
import DifferentialGeometry.Geometry.Thurston.Models.CoordinateMetrics
import DifferentialGeometry.Geometry.Thurston.Models.HomogeneousCompleteness
import DifferentialGeometry.Geometry.Thurston.NonemptyGeometricPresentation
import DifferentialGeometry.Geometry.Thurston.SphericalProductPiece
import DifferentialGeometry.Geometry.Thurston.StandardFactorGeometry
import DifferentialGeometry.Geometry.Thurston.Transport
import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.Commutative
import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.FiniteCoprodSupport
import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.FiniteFreeFactors
import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.FiniteIndecomposable
import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.FiniteKurosh
import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.FiniteProductPresentation
import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.FixedFactorComparison
import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.FreeFactor
import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.InheritedFreeFactor
import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.KuroshFreeFactors
import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.LargeFreeFactor
import DifferentialGeometry.Topology.FundamentalGroup.FiniteGeneration.CompactFundamentalGroup
import DifferentialGeometry.Topology.FundamentalGroup.FiniteGeneration.CoverConnectors
import DifferentialGeometry.Topology.FundamentalGroup.FiniteGeneration.CoverSubdivision
import DifferentialGeometry.Topology.FundamentalGroup.FiniteGeneration.FiniteCoverGroups
import DifferentialGeometry.Topology.FundamentalGroup.FiniteGeneration.FiniteLocalCover
import DifferentialGeometry.Topology.FundamentalGroup.MarkedFundamentalGroup
import DifferentialGeometry.Topology.FundamentalGroup.SigmaFundamentalGroup
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedPresentation
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.Carrier
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.FiniteConnectedSum
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.NoCuts
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.OrientationTransport
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.Prime
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.SmoothTorusReconstruction
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.SphereExample
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.StandardCertificates
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.StandardPrimes
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.Statement
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.TorusGluing
import DifferentialGeometry.Topology.ThreeManifold.TorusCut.MarkedSeams
import DifferentialGeometry.Topology.ThreeManifold.TorusCut.SeamExamples
import DifferentialGeometry.Topology.ThreeManifold.TorusCut.TorusCylinder
import DifferentialGeometry.Topology.VanKampen.FreeFactors.CollarFreeFactor
import DifferentialGeometry.Topology.VanKampen.FreeFactors.FiniteCollarFreeFactors
import DifferentialGeometry.Topology.VanKampen.FreeFactors.OpenCoverFreeFactors
import DifferentialGeometry.Topology.VanKampen.FreeFactors.SeparatedCollarGroups
import DifferentialGeometry.Topology.VanKampen.FreeFactors.StarCoverGroups
import DifferentialGeometry.Topology.VanKampen.FreeFactors.ThinOverlapGroups
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.Checks.RawSurgeryExamples
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.Checks.CertificateExamples
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.Checks.ConnectedSumExamples
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.Checks.ObservedHistoryExamples
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.Checks.SmoothHistoryExamples
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.Checks.StandardFactorExamples
import Lean

open Lean Elab Command
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless ([
      `DifferentialGeometry.Analysis.Order.CommonProfile,
      `DifferentialGeometry.External.GraphCoveringTheory.Kurosh,
      `DifferentialGeometry.External.GraphCoveringTheory.KuroshActive,
      `DifferentialGeometry.External.GraphCoveringTheory.KuroshCover,
      `DifferentialGeometry.External.GraphCoveringTheory.KuroshCoverAction,
      `DifferentialGeometry.External.GraphCoveringTheory.KuroshCoverConnected,
      `DifferentialGeometry.External.GraphCoveringTheory.KuroshCoverLift,
      `DifferentialGeometry.External.GraphCoveringTheory.KuroshCoverLocal,
      `DifferentialGeometry.External.GraphCoveringTheory.KuroshCoverStar,
      `DifferentialGeometry.External.GraphCoveringTheory.KuroshFreeCorollary,
      `DifferentialGeometry.External.GraphCoveringTheory.KuroshFreeFiber,
      `DifferentialGeometry.External.GraphCoveringTheory.KuroshFreePart,
      `DifferentialGeometry.External.GraphCoveringTheory.KuroshKernel,
      `DifferentialGeometry.External.GraphCoveringTheory.KuroshPathEndpoint,
      `DifferentialGeometry.External.GraphCoveringTheory.KuroshPathInjective,
      `DifferentialGeometry.External.GraphCoveringTheory.KuroshPathRelation,
      `DifferentialGeometry.External.GraphCoveringTheory.KuroshPathRelationInvariant,
      `DifferentialGeometry.External.GraphCoveringTheory.KuroshRawPathValue,
      `DifferentialGeometry.External.GraphCoveringTheory.KuroshTheorem,
      `DifferentialGeometry.External.GraphCoveringTheory.KuroshTree,
      `DifferentialGeometry.External.GrushkoNeumannTheorem.MarshallHall.Grushko,
      `DifferentialGeometry.External.GrushkoNeumannTheorem.MarshallHall.GrushkoEdge,
      `DifferentialGeometry.External.GrushkoNeumannTheorem.MarshallHall.GrushkoFold,
      `DifferentialGeometry.External.GrushkoNeumannTheorem.MarshallHall.GrushkoFoldStep,
      `DifferentialGeometry.External.GrushkoNeumannTheorem.MarshallHall.GrushkoFull,
      `DifferentialGeometry.External.GrushkoNeumannTheorem.MarshallHall.GrushkoGeneral,
      `DifferentialGeometry.External.GrushkoNeumannTheorem.MarshallHall.GrushkoGraph,
      `DifferentialGeometry.External.GrushkoNeumannTheorem.MarshallHall.GrushkoInvariant,
      `DifferentialGeometry.External.GrushkoNeumannTheorem.MarshallHall.GrushkoReduction,
      `DifferentialGeometry.External.GrushkoNeumannTheorem.MarshallHall.GrushkoReductionChain,
      `DifferentialGeometry.External.GrushkoNeumannTheorem.MarshallHall.GrushkoRemove,
      `DifferentialGeometry.External.GrushkoNeumannTheorem.MarshallHall.GrushkoRose,
      `DifferentialGeometry.External.GrushkoNeumannTheorem.MarshallHall.GrushkoUnfold,
      `DifferentialGeometry.External.GrushkoNeumannTheorem.MarshallHall.GrushkoUnsafe,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComponentVolumeBridge,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.KappaLoss,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.KappaModelVolume,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelBallVolume,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ReservedCanonical,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RoundCoverVolume,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RoundImageVolume,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RoundReservedWitness,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialRoundFiniteDegree,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedVolume,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.Checks.AxiomAudit,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.Checks.CertificateExamples,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.Checks.ConnectedSumExamples,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.Checks.MetricAndSeamExamples,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.Checks.ObservedHistoryExamples,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.Checks.RawSurgeryExamples,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.Checks.SmoothHistoryExamples,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.Checks.StandardFactorExamples,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.ClassifiedHistory,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.ObservedHistory,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.OrientedReconstruction,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.RawHistory,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.SmoothReconstruction,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.ActualEventGeometry,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.CoherentSurgeryTower,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.CoherentTowerConsequences,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.ConcatenationHorizon,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.EventTimeTranslation,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.FiniteConcatenation,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.GeneralPrefixExtension,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.LateOrEmpty,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.MarkedContinuation,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.RawSurgery,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.SlabCompatibility,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.SurgeryEventControl,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.TerminalTimeTranslation,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.TowerFinitePrefixes,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.CompletedHistoryDegree,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.CutoffProfiles,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.DegreeBoundCanonical,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.DegreeGeometricHorizon,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.FiniteGeometricHorizon,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.FiniteInitialDegree,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.GeneralCanonicalFromSmallScale,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.GeneralCanonicalProduction,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.GeneralInitialBound,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.GeometricHorizons,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.HistoryDegreeBound,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.HistoryFreeFactors,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.InitialDecomposition,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.JointCutoffProfiles,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.ProfileQuantifiers,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.ReserveContinuation,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.SmallScaleFromDegree,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.SmallScaleGeometricHorizon,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCapGroups,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCapFreeFactor,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCapReconstruction,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedComponentGeometry,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialFundamentalGroup,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MarkedDiscardedGeometry,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MarkedReconstruction,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ReconstructionSlots,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedDiscardedLabels,
      `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TubeFreeFactors,
      `DifferentialGeometry.Geometry.Metric.Approximation.PointedBallApproximation,
      `DifferentialGeometry.Geometry.Metric.Approximation.RealBallExamples,
      `DifferentialGeometry.Geometry.Metric.Scaling.EuclideanBalls,
      `DifferentialGeometry.Geometry.Metric.Scaling.RiemannianBalls,
      `DifferentialGeometry.Geometry.Metric.Sphere.Quotient.AntipodalQuotient,
      `DifferentialGeometry.Geometry.Metric.Sphere.Quotient.SphericalMetric,
      `DifferentialGeometry.Geometry.Thurston.Atlas,
      `DifferentialGeometry.Geometry.Thurston.ElementaryModels,
      `DifferentialGeometry.Geometry.Thurston.ModelAtlas,
      `DifferentialGeometry.Geometry.Thurston.Models,
      `DifferentialGeometry.Geometry.Thurston.Models.CoordinateHomogeneity,
      `DifferentialGeometry.Geometry.Thurston.Models.CoordinateMetrics,
      `DifferentialGeometry.Geometry.Thurston.Models.HomogeneousCompleteness,
      `DifferentialGeometry.Geometry.Thurston.NonemptyGeometricPresentation,
      `DifferentialGeometry.Geometry.Thurston.SphericalProductPiece,
      `DifferentialGeometry.Geometry.Thurston.StandardFactorGeometry,
      `DifferentialGeometry.Geometry.Thurston.Transport,
      `DifferentialGeometry.Topology.Algebra.Group.FreeProduct.Commutative,
      `DifferentialGeometry.Topology.Algebra.Group.FreeProduct.FiniteCoprodSupport,
      `DifferentialGeometry.Topology.Algebra.Group.FreeProduct.FiniteFreeFactors,
      `DifferentialGeometry.Topology.Algebra.Group.FreeProduct.FiniteIndecomposable,
      `DifferentialGeometry.Topology.Algebra.Group.FreeProduct.FiniteKurosh,
      `DifferentialGeometry.Topology.Algebra.Group.FreeProduct.FiniteProductPresentation,
      `DifferentialGeometry.Topology.Algebra.Group.FreeProduct.FixedFactorComparison,
      `DifferentialGeometry.Topology.Algebra.Group.FreeProduct.FreeFactor,
      `DifferentialGeometry.Topology.Algebra.Group.FreeProduct.InheritedFreeFactor,
      `DifferentialGeometry.Topology.Algebra.Group.FreeProduct.KuroshFreeFactors,
      `DifferentialGeometry.Topology.Algebra.Group.FreeProduct.LargeFreeFactor,
      `DifferentialGeometry.Topology.FundamentalGroup.FiniteGeneration.CompactFundamentalGroup,
      `DifferentialGeometry.Topology.FundamentalGroup.FiniteGeneration.CoverConnectors,
      `DifferentialGeometry.Topology.FundamentalGroup.FiniteGeneration.CoverSubdivision,
      `DifferentialGeometry.Topology.FundamentalGroup.FiniteGeneration.FiniteCoverGroups,
      `DifferentialGeometry.Topology.FundamentalGroup.FiniteGeneration.FiniteLocalCover,
      `DifferentialGeometry.Topology.FundamentalGroup.MarkedFundamentalGroup,
      `DifferentialGeometry.Topology.FundamentalGroup.SigmaFundamentalGroup,
      `DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedPresentation,
      `DifferentialGeometry.Topology.ThreeManifold.Geometrization.Carrier,
      `DifferentialGeometry.Topology.ThreeManifold.Geometrization.FiniteConnectedSum,
      `DifferentialGeometry.Topology.ThreeManifold.Geometrization.NoCuts,
      `DifferentialGeometry.Topology.ThreeManifold.Geometrization.OrientationTransport,
      `DifferentialGeometry.Topology.ThreeManifold.Geometrization.Prime,
      `DifferentialGeometry.Topology.ThreeManifold.Geometrization.SmoothTorusReconstruction,
      `DifferentialGeometry.Topology.ThreeManifold.Geometrization.SphereExample,
      `DifferentialGeometry.Topology.ThreeManifold.Geometrization.StandardCertificates,
      `DifferentialGeometry.Topology.ThreeManifold.Geometrization.StandardPrimes,
      `DifferentialGeometry.Topology.ThreeManifold.Geometrization.Statement,
      `DifferentialGeometry.Topology.ThreeManifold.Geometrization.TorusGluing,
      `DifferentialGeometry.Topology.ThreeManifold.TorusCut.MarkedSeams,
      `DifferentialGeometry.Topology.ThreeManifold.TorusCut.SeamExamples,
      `DifferentialGeometry.Topology.ThreeManifold.TorusCut.TorusCylinder,
      `DifferentialGeometry.Topology.VanKampen.FreeFactors.CollarFreeFactor,
      `DifferentialGeometry.Topology.VanKampen.FreeFactors.FiniteCollarFreeFactors,
      `DifferentialGeometry.Topology.VanKampen.FreeFactors.OpenCoverFreeFactors,
      `DifferentialGeometry.Topology.VanKampen.FreeFactors.SeparatedCollarGroups,
      `DifferentialGeometry.Topology.VanKampen.FreeFactors.StarCoverGroups,
      `DifferentialGeometry.Topology.VanKampen.FreeFactors.ThinOverlapGroups
    ] : List Name).contains mod do
      continue
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration is not in the checked environment: {name}"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unapproved axiom {ax} in {name} (module {mod})"
    count := count + 1
  if count == 0 then throwError "Empty team axiom audit"
  logInfo m!"Team axiom audit passed for {count} declarations."

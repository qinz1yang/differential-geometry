import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Metric.UniversalCover.Metric
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.Integral.Measure
open CanonicalNeighborhood
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M] [Inhabited M]

theorem universalCover_image_ball_liftedMetric
    (g : SmoothRiemannianMetric I M) (x : UniversalCover M)
    (r : ℝ) (hr : 0 < r) :
    (UniversalCover.proj : UniversalCover M → M) ''
        riemannianBallOf (I := I) (UniversalCover.liftedMetric (I := I) g) x r =
      riemannianBallOf (I := I) g (UniversalCover.proj x) r := by
  sorry

variable [SecondCountableTopology M]

private local instance upstreamCoverVolumeMeasurable : MeasurableSpace M := borel M
private local instance upstreamCoverVolumeBorel : BorelSpace M := ⟨rfl⟩
private local instance upstreamCoverVolumeLiftMeasurable :
    MeasurableSpace (UniversalCover M) := borel (UniversalCover M)
private local instance upstreamCoverVolumeLiftBorel :
    BorelSpace (UniversalCover M) := ⟨rfl⟩
private local instance upstreamCoverVolumeC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance upstreamCoverVolumeLiftC1 :
    IsManifold I 1 (UniversalCover M) := IsManifold.of_le (n := ∞) (by decide)

theorem universalCover_volume_image_le
    (g : SmoothRiemannianMetric I M) (U : Set (UniversalCover M)) (hU : IsOpen U) :
    riemannianVolumeMeasure (I := I) (M := M) g
        ((UniversalCover.proj : UniversalCover M → M) '' U) ≤
      riemannianVolumeMeasure (I := I) (M := UniversalCover M)
        (UniversalCover.liftedMetric (I := I) g) U := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

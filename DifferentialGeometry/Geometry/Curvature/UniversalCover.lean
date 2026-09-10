import DifferentialGeometry.Geometry.Curvature.Positive
import DifferentialGeometry.Geometry.Metric.UniversalCover.Completeness
import DifferentialGeometry.Geometry.Metric.UniversalCover.Curvature
import DifferentialGeometry.Topology.Covering.Smooth.LocalDiffeomorph
import DifferentialGeometry.Geometry.Metric.Pullback.Local
import DifferentialGeometry.Geometry.Metric.Basic



noncomputable section
open Bundle Manifold
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M] [Inhabited M]

omit [SigmaCompactSpace M] [ConnectedSpace M] in
theorem universalCover_liftedMetric_eq_localPull (g : SmoothRiemannianMetric I M) :
    UniversalCover.liftedMetric g = localPullMetric g UniversalCover.proj
      (UniversalCover.proj_localDiffeo (I := I)) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [localPullMetric_inner, (UniversalCover.hasMFDerivAt_proj (I := I) x).mfderiv]
  rfl

omit [SigmaCompactSpace M] [ConnectedSpace M] in
theorem HasPositiveSectionalCurvature.universalCoverMetric
    {g : SmoothRiemannianMetric I M} (hg : HasPositiveSectionalCurvature g) :
    HasPositiveSectionalCurvature (UniversalCover.liftedMetric (I := I) g) := by
  intro x v w hvw
  exact lt_of_lt_of_eq (hg (UniversalCover.proj x) v w hvw)
    (UniversalCover.metricRm_lifted (I := I) g x v w w v).symm

omit [SigmaCompactSpace M] [ConnectedSpace M] in
theorem universalCover_orthonormal_sectional_bound (g : SmoothRiemannianMetric I M) {k : ℝ}
    (hsec : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v v = 1 → g.inner x w w = 1 → g.inner x v w = 0 →
        k ≤ metricRm04StandardAt g x v w w v) :
    ∀ (x : UniversalCover M) (v w : TangentSpace I x),
      (UniversalCover.liftedMetric g).inner x v v = 1 →
      (UniversalCover.liftedMetric g).inner x w w = 1 →
      (UniversalCover.liftedMetric g).inner x v w = 0 →
        k ≤ metricRm04StandardAt (UniversalCover.liftedMetric g) x v w w v := by
  intro x v w hv hw hvw
  exact le_trans (hsec (UniversalCover.proj x) v w hv hw hvw)
    (UniversalCover.metricRm_lifted (I := I) g x v w w v).symm.le

end DifferentialGeometry.Geometry

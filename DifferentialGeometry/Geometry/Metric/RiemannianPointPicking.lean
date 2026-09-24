import DifferentialGeometry.Geometry.Metric.PointPicking
import DifferentialGeometry.Geometry.Metric.Distance.Topology
import DifferentialGeometry.Geometry.Metric.Distance.Ball

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.SmoothRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RegularSpace M] [PreconnectedSpace M]

theorem exists_weighted_point_selection (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} {p y : M} {R eta : ℝ}
    (hcompact : IsCompact (riemannianClosedBallOf g p R))
    (hf : ContinuousOn f (riemannianClosedBallOf g p R))
    (hy : (riemannianEDistOf g p y).toReal < R) (hfy : 0 < f y) (heta : eta < 1) :
    let d := fun a b : M => (riemannianEDistOf g a b).toReal
    ∃ x : M, d p x < R ∧ 0 < f x ∧
      f y * (R - d p y) ^ 2 ≤ f x * (R - d p x) ^ 2 ∧
      ∀ z : M, d x z ≤ eta * (R - d p x) →
        d p z < R ∧ f z ≤ ((1 - eta)⁻¹) ^ 2 * f x := by
  let _ : PseudoMetricSpace M := g.toPseudoMetricSpace
  have hd (a b : M) : dist a b = (riemannianEDistOf g a b).toReal := rfl
  have hR : 0 ≤ R := ENNReal.toReal_nonneg.trans hy.le
  have hball : Metric.closedBall p R = riemannianClosedBallOf g p R := by
    ext z
    rw [Metric.mem_closedBall, dist_comm, hd]
    exact (ENNReal.le_ofReal_iff_toReal_le (riemannianEDistOf_ne_top g p z) hR).symm
  have hcp : IsCompact (Metric.closedBall p R) := by rwa [hball]
  have hcont : ContinuousOn f (Metric.closedBall p R) := by rwa [hball]
  simpa only [hd] using Metric.exists_weighted_point_selection hcp hcont hy hfy heta

end DifferentialGeometry.SmoothRiemannianMetric

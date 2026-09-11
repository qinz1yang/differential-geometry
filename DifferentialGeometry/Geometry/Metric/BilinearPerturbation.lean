import DifferentialGeometry.Geometry.Metric.DerivativeENorm
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds

set_option autoImplicit false
noncomputable section
open Bundle Set DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Analysis.Laplacian
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem inner_bounds_of_metricDerivNorm_le
    (g h : SmoothRiemannianMetric I M) (x : M) {δ : ℝ}
    (herr : metricDerivNorm 0 h g g x ≤ δ) (v : TangentSpace I x) :
    (1 - δ) * g.inner x v v ≤ h.inner x v v ∧
      h.inner x v v ≤ (1 + δ) * g.inner x v v := by
  have hb := metricDifference_abs_le h g g x v v
  rw [mul_assoc, Real.mul_self_sqrt (metric_inner_self_nonneg g x v)] at hb
  have he := hb.trans (mul_le_mul_of_nonneg_right herr (metric_inner_self_nonneg g x v))
  obtain ⟨hl, hu⟩ := abs_le.mp he
  constructor <;> linarith

theorem inner_bounds_of_metricDerivENormSupOn_lt
    (g h : SmoothRiemannianMetric I M) {K : Set M} {k : ℕ} {δ : ℝ}
    (herr : metricDerivENormSupOn K k h g g < ENNReal.ofReal δ)
    {x : M} (hx : x ∈ K) (v : TangentSpace I x) :
    (1 - δ) * g.inner x v v ≤ h.inner x v v ∧
      h.inner x v v ≤ (1 + δ) * g.inner x v v :=
  inner_bounds_of_metricDerivNorm_le g h x
    (metricDerivNorm_lt_of_sup_lt K k h g g herr (Nat.zero_le k) hx).le v

end DifferentialGeometry.Geometry.Metric

import DifferentialGeometry.Geometry.Metric.Approximation.FiniteOrder
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PartialDiffeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H N] [T2Space N] [IsManifold I ∞ N]

local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem isMetricApproximationOn.inner_sub_abs_le
    {Φ : PartialDiffeomorph I I M N ∞} {K : Set M} {p : ℕ} {ε : ℝ}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (hΦ : isMetricApproximationOn Φ K p ε g h) {x : M} (hx : x ∈ K)
    (v : TangentSpace I x) :
    |h.inner (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x v) - g.inner x v v| ≤
      ε * g.inner x v v := by
  let U : TopologicalSpace.Opens M := ⟨Φ.source, Φ.open_source⟩
  let y : U := ⟨x, hΦ.1 hx⟩
  have hnn : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le
  have hb := CheegerGromovCompactness.metricDifference_abs_le
    (pullbackMetricOn Φ U Set.Subset.rfl h) (g.restrictOpen U) (g.restrictOpen U) y v v
  rw [pullbackMetricOn_inner Φ U Set.Subset.rfl h y v v] at hb
  change |h.inner (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x v) - g.inner x v v| ≤
      CheegerGromovCompactness.metricDerivNorm 0 (pullbackMetricOn Φ U Set.Subset.rfl h)
        (g.restrictOpen U) (g.restrictOpen U) y *
          Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x v v) at hb
  rw [mul_assoc, Real.mul_self_sqrt hnn] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right (hΦ.metricDerivNorm_zero_lt hx).le hnn)

theorem isMetricApproximationOn.quadratic_bounds
    {Φ : PartialDiffeomorph I I M N ∞} {K : Set M} {p : ℕ} {ε : ℝ}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (hΦ : isMetricApproximationOn Φ K p ε g h) {x : M} (hx : x ∈ K)
    (v : TangentSpace I x) :
    (1 - ε) * g.inner x v v ≤
      h.inner (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x v) ∧
    h.inner (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x v) ≤
      (1 + ε) * g.inner x v v := by
  obtain ⟨hl, hu⟩ := abs_le.mp (hΦ.inner_sub_abs_le hx v)
  constructor <;> nlinarith only [hl, hu]

end DifferentialGeometry.PartialDiffeomorph

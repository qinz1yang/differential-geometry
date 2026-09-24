import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.Scalar
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Self

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open scoped Manifold ContDiff Topology BigOperators

open CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]

theorem exists_abs_metricScalarAt_sub_lt
    (gRef : SmoothRiemannianMetric I M) {K : Set M} (hK : IsCompact K)
    {c : ℝ} (hc : 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ h : SmoothRiemannianMetric I M,
        (∀ x ∈ K, ∀ j : ℕ, j ≤ 2 →
          metricDerivNorm (I := I) j h gRef gRef x ≤ ε) →
        ∀ x ∈ K, |metricScalarAt (I := I) h x - metricScalarAt gRef x| < c := by
  obtain ⟨C₀, hC₀⟩ := metricCovDerivNorm_bddOn (I := I) hK 0 gRef gRef
  let C₀' : ℝ := max C₀ 0
  let B : ℝ := C₀' + 1
  have hC₀' : 0 ≤ C₀' := by
    dsimp [C₀']
    exact le_max_right _ _
  have hB0 : 0 ≤ B := by
    dsimp [B]
    linarith
  obtain ⟨C, hC, hscalarDiff⟩ :=
    exists_abs_metricScalarAt_sub_le (I := I) gRef hK (1 / 2 : ℝ) B (by norm_num)
  let ε : ℝ := min (1 / 2 : ℝ) (c / (6 * C))
  have hfracpos : 0 < c / (6 * C) := by positivity
  have hεpos : 0 < ε := by
    dsimp [ε]
    exact lt_min (by norm_num) hfracpos
  refine ⟨ε, hεpos, ?_⟩
  intro h hderiv x hx
  have hεhalf : ε ≤ (1 / 2 : ℝ) := by
    dsimp [ε]
    exact min_le_left _ _
  have hεone : ε ≤ 1 := hεhalf.trans (by norm_num)
  have hεfrac : ε ≤ c / (6 * C) := by
    dsimp [ε]
    exact min_le_right _ _
  have hlowh : ∀ y ∈ K, ∀ ξ : TangentSpace I y,
      (1 / 2 : ℝ) * gRef.inner y ξ ξ ≤ h.inner y ξ ξ := by
    intro y hy ξ
    have hdiff := metricDifference_abs_le h gRef gRef y ξ ξ
    rw [mul_assoc, Real.mul_self_sqrt (metric_inner_self_nonneg gRef y ξ)] at hdiff
    have hn := metric_inner_self_nonneg gRef y ξ
    have hb := hdiff.trans (mul_le_mul_of_nonneg_right
      ((hderiv y hy 0 (by norm_num)).trans hεhalf) hn)
    linarith [(abs_le.mp hb).1]
  have hlowRef : ∀ y ∈ K, ∀ ξ : TangentSpace I y,
      (1 / 2 : ℝ) * gRef.inner y ξ ξ ≤ gRef.inner y ξ ξ := by
    intro y hy ξ
    nlinarith [metric_inner_self_nonneg gRef y ξ]
  have hcovh : ∀ y ∈ K, ∀ j : ℕ, j ≤ 2 →
      metricCovDerivNorm (I := I) j h gRef y ≤ B := by
    intro y hy j hj
    have htri := covNorm_le_add (I := I) j h gRef gRef y
    have hdj := hderiv y hy j hj
    cases j with
    | zero =>
      have h0 := (hC₀ y hy).trans (le_max_left C₀ 0)
      dsimp [B]
      linarith
    | succ j =>
      rw [covNorm_self_succ] at htri
      dsimp [B]
      linarith
  have hcovRef : ∀ y ∈ K, ∀ j : ℕ, j ≤ 2 →
      metricCovDerivNorm (I := I) j gRef gRef y ≤ B := by
    intro y hy j hj
    cases j with
    | zero =>
      have h0 := (hC₀ y hy).trans (le_max_left C₀ 0)
      dsimp [B]
      linarith
    | succ j =>
      rw [covNorm_self_succ]
      exact hB0
  have hdiffscalar := hscalarDiff h gRef hlowh hlowRef hcovh hcovRef x hx
  have hsum : (∑ j ∈ Finset.range 3,
      metricDerivNorm (I := I) j h gRef gRef x) ≤ 3 * ε := by
    calc
      (∑ j ∈ Finset.range 3, metricDerivNorm (I := I) j h gRef gRef x)
          ≤ ∑ _j ∈ Finset.range 3, ε := by
            exact Finset.sum_le_sum fun j hj =>
              hderiv x hx j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
      _ = 3 * ε := by norm_num
  have hmul : ε * (6 * C) ≤ c := (le_div_iff₀ (by positivity)).mp hεfrac
  have hfinal : C * (3 * ε) < c := by nlinarith
  exact hdiffscalar.trans_lt ((mul_le_mul_of_nonneg_left hsum hC.le).trans_lt hfinal)

theorem exists_scalar_lower_bound_of_small_metric_derivatives
    (gRef : SmoothRiemannianMetric I M) {K : Set M} (hK : IsCompact K)
    {c : ℝ} (hc : 0 < c)
    (hscalar : ∀ x ∈ K, c ≤ metricScalarAt (I := I) gRef x) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ h : SmoothRiemannianMetric I M,
        (∀ x ∈ K, ∀ j : ℕ, j ≤ 2 →
          metricDerivNorm (I := I) j h gRef gRef x ≤ ε) →
        ∀ x ∈ K, c / 2 ≤ metricScalarAt (I := I) h x := by
  obtain ⟨ε, hε, hbound⟩ :=
    exists_abs_metricScalarAt_sub_lt gRef hK (c := c / 2) (by positivity)
  refine ⟨ε, hε, fun h hderiv x hx => ?_⟩
  have hdiff := (abs_lt.mp (hbound h hderiv x hx)).1
  have href := hscalar x hx
  linarith

end DifferentialGeometry.Geometry.Curvature

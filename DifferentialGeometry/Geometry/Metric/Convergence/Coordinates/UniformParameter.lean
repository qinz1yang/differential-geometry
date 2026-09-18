import DifferentialGeometry.Geometry.Metric.Convergence.Compactness.Precompactness

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology BigOperators
namespace DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator
variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
theorem chartGram_jets_uniform_of_metric_convergence
    (g : ℕ → P → SmoothRiemannianMetric I M) (g₀ : P → SmoothRiemannianMetric I M)
    (R : SmoothRiemannianMetric I M) {J : Set P}
    (hconv : ∀ K : Set M, IsCompact K → ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, metricDerivNormSupOn K p (g n t) (g₀ t) R < epsilon)
    (x₀ : M) (i j : Fin (Module.finrank ℝ E)) {K : Set E} (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt I x₀).target) (r : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ r (chartGramOnE (I := I) (g n t) x₀ i j) y -
        iteratedFDeriv ℝ r (chartGramOnE (I := I) (g₀ t) x₀ i j) y‖ ≤ epsilon := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let Kc : Set M := (extChartAt I x₀).symm '' K
  have hKc : IsCompact Kc := hK.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := I) x₀).mono hKt)
  have hKchart : Kc ⊆ (chartAt H x₀).source := by
    rintro y ⟨w, hw, rfl⟩
    rw [← extChartAt_source_eq_chartAt_source (I := I)]
    exact (extChartAt I x₀).map_target (hKt hw)
  obtain ⟨C, hC, hjet⟩ := chartJet_sub_le R x₀ hKc hKchart r
  let delta := epsilon / ((C + 1) * (r + 1))
  have hC1 : 0 < C + 1 := by linarith
  have hr : (0 : ℝ) < r + 1 := by positivity
  have hdelta : 0 < delta := div_pos hepsilon (mul_pos hC1 hr)
  obtain ⟨N, hN⟩ := hconv Kc hKc r delta hdelta
  refine ⟨N, fun n hn t ht y hy => ?_⟩
  let x := (extChartAt I x₀).symm y
  have hx : x ∈ Kc := ⟨y, hy, rfl⟩
  have hxy : extChartAt I x₀ x = y := (extChartAt I x₀).right_inv (hKt hy)
  have hsum : (∑ q ∈ Finset.range (r + 1), metricDerivNorm q (g n t) (g₀ t) R x) ≤
      (r + 1) * delta := by
    calc
      _ ≤ ∑ _q ∈ Finset.range (r + 1), delta := by
        apply Finset.sum_le_sum
        intro q hq
        exact (derivNorm_le_sup hKc (Nat.lt_succ_iff.mp (Finset.mem_range.mp hq))
          (g n t) (g₀ t) R hx).trans (hN n hn t ht).le
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  have hb := (hjet (g n t) (g₀ t) x hx i j).trans (mul_le_mul_of_nonneg_left hsum hC)
  rw [hxy] at hb
  calc
    _ ≤ C * ((r + 1) * delta) := hb
    _ ≤ (C + 1) * ((r + 1) * delta) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hr.le hdelta.le)
    _ = epsilon := by
      rw [← mul_assoc]
      exact mul_div_cancel₀ epsilon (ne_of_gt (mul_pos hC1 hr))
end DifferentialGeometry.CheegerGromovCompactness

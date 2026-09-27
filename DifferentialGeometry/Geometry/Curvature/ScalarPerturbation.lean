import DifferentialGeometry.Geometry.Curvature.RicciSharpUniformPerturbation
import DifferentialGeometry.Geometry.Curvature.ScalarTrace
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

noncomputable section
open scoped Manifold ContDiff BigOperators
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] in
theorem abs_scalar_curvature_sub_le_of_ricci_operator_difference
    (g h gRef : SmoothRiemannianMetric I M) (x : M) (C : ℝ)
    (hRicci : ∀ v : TangentSpace I x,
      let d := ricciSharp g x v - ricciSharp h x v
      Real.sqrt (gRef.inner x d d) ≤ C * Real.sqrt (gRef.inner x v v)) :
    |metricScalarAt g x - metricScalarAt h x| ≤ (Module.finrank ℝ E : ℝ) * C := by
  classical
  obtain ⟨b, hb⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis gRef x
  have hinv := metricInverseInBasis_of_orthonormal gRef b hb
  let A := (ricciSharp g x).toLinearMap - (ricciSharp h x).toLinearMap
  have htrace : metricScalarAt g x - metricScalarAt h x =
      ∑ i, b.repr (A (b i)) i := by
    rw [metricScalar_eq_trace_ricciSharp, metricScalar_eq_trace_ricciSharp,
      ← map_sub, LinearMap.trace_eq_matrix_trace ℝ b]
    simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
    rfl
  rw [htrace]
  calc
    _ ≤ ∑ i, |b.repr (A (b i)) i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace I x)), C := by
      apply Finset.sum_le_sum
      intro i _
      have hu : gRef.inner x (b i) (b i) = 1 := by simpa only [ite_true] using hb i i
      have hrepr : b.repr (A (b i)) i = gRef.inner x (A (b i)) (b i) := by
        rw [basis_repr_eq_sum_inv_inner gRef x b _ hinv]
        simp [identityInvMetric, diagonalInvMetric]
      rw [hrepr]
      have hcs := DifferentialGeometry.Analysis.Laplacian.abs_metric_inner_le_sqrt_metric_quadratic
        gRef x (A (b i)) (b i)
      rw [hu, Real.sqrt_one, mul_one] at hcs
      apply hcs.trans
      have h := hRicci (b i)
      rw [hu, Real.sqrt_one, mul_one] at h
      exact h
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem abs_scalar_curvature_sub_le_of_small_metric_derivatives
    (g gRef : SmoothRiemannianMetric I M) (x : M) (ε : ℝ) (hε : ε ≤ 1 / 2)
    (hsmall : ∀ k : ℕ, k ≤ 2 → metricDerivNorm k g gRef gRef x ≤ ε)
    (K : ℝ) (hRicci : ∀ v : TangentSpace I x,
      Real.sqrt (gRef.inner x (ricciSharp gRef x v) (ricciSharp gRef x v)) ≤
        K * Real.sqrt (gRef.inner x v v)) :
    |metricScalarAt g x - metricScalarAt gRef x| ≤
      (Module.finrank ℝ E : ℝ) *
        ((240 * (Module.finrank ℝ E : ℝ) * ε + ε * K) / (1 - ε)) := by
  apply abs_scalar_curvature_sub_le_of_ricci_operator_difference g gRef gRef x
  intro v
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  have hdenom : 0 < 1 - ε := by linarith
  have h := ricciSharp_difference_bound_of_small_metric_derivatives g gRef x ε hε hsmall v
  dsimp only at h ⊢
  apply h.trans
  calc
    _ ≤ (240 * (Module.finrank ℝ E : ℝ) * ε * Real.sqrt (gRef.inner x v v) +
        ε * (K * Real.sqrt (gRef.inner x v v))) / (1 - ε) :=
      div_le_div_of_nonneg_right
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hRicci v) hε0)) hdenom.le
    _ = _ := by ring

end DifferentialGeometry.Geometry.Curvature

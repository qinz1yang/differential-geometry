import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Ricci.Basic
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds

noncomputable section
open scoped Manifold ContDiff BigOperators
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature

namespace Poincare.Geometry.Curvature

theorem abs_ricci_difference_le_of_riemann_difference
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [BoundarylessManifold I M]
    (g h gRef : SmoothRiemannianMetric I M) (x : M) (C : ℝ)
    (hR : ∀ u v w : TangentSpace I x,
      let d := riemannOp (LeviCivita g) x u v w - riemannOp (LeviCivita h) x u v w
      Real.sqrt (gRef.inner x d d) ≤
        C * Real.sqrt (gRef.inner x u u) * Real.sqrt (gRef.inner x v v) *
          Real.sqrt (gRef.inner x w w)) (v w : TangentSpace I x) :
    |ricciTensor g x v w - ricciTensor h x v w| ≤
      (Module.finrank ℝ E : ℝ) * C *
        Real.sqrt (gRef.inner x v v) * Real.sqrt (gRef.inner x w w) := by
  classical
  obtain ⟨b, hb⟩ := exists_orthonormal_basis gRef x
  have hinv := metricInverseInBasis_of_orthonormal gRef b hb
  let A := ricciEndo g x v w - ricciEndo h x v w
  have htrace : ricciTensor g x v w - ricciTensor h x v w =
      ∑ i, b.repr (A (b i)) i := by
    rw [ricciTensor_apply, ricciTensor_apply, ← map_sub,
      LinearMap.trace_eq_matrix_trace ℝ b]
    simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
    rfl
  rw [htrace]
  calc
    _ ≤ ∑ i, |b.repr (A (b i)) i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace I x)),
        C * Real.sqrt (gRef.inner x v v) * Real.sqrt (gRef.inner x w w) := by
      apply Finset.sum_le_sum
      intro i _
      have hu : gRef.inner x (b i) (b i) = 1 := by simpa only [ite_true] using hb i i
      have hrepr : b.repr (A (b i)) i = gRef.inner x (A (b i)) (b i) := by
        rw [basis_repr_eq_sum_inv_inner gRef x b _ hinv]
        simp [identityInvMetric, diagonalInvMetric]
      rw [hrepr]
      have hcs := DifferentialGeometry.Analysis.Laplacian.abs_metric_inner_le_sqrt_metric_quadratic gRef x (A (b i)) (b i)
      rw [hu, Real.sqrt_one, mul_one] at hcs
      apply hcs.trans
      have hd := hR (b i) v w
      rw [hu, Real.sqrt_one, mul_one] at hd
      exact hd
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [show Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E from rfl]
      ring

end Poincare.Geometry.Curvature

import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Product.Scalar

section

noncomputable section
open MeasureTheory
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem norm_scalarSmul_le
    (q : SmoothRiemannianMetric I M) (r s : ℕ) (ζ : C^∞⟮I, M; Real⟯)
    {C : Real} (hC : 0 ≤ C) (hζ : ∀ x : M, |(ζ : M → Real) x| ≤ C)
    (S : SmoothCcTensor q r s) :
    ‖scalarSmul (I := I) (M := M) q r s ζ S‖ ≤ C * ‖S‖ := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) q
  let base : M → Real := fun x =>
    tensorInnerPointwise (I := I) (M := M) q r s x (S.toFun x) (S.toFun x)
  let weighted : M → Real := fun x =>
    tensorInnerPointwise (I := I) (M := M) q r s x
      ((scalarSmul (I := I) (M := M) q r s ζ S).toFun x)
      ((scalarSmul (I := I) (M := M) q r s ζ S).toFun x)
  have hpoint : ∀ x : M, weighted x ≤ C ^ 2 * base x := by
    intro x
    have hsq : ((ζ : M → Real) x) ^ 2 ≤ C ^ 2 := by
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) hC).2 (hζ x)
    have hbase : 0 ≤ base x :=
      tensorInnerPointwise_nonneg (I := I) (M := M) q r s x (S.toFun x)
    dsimp only [weighted, base]
    rw [scalarSmul_toFun_apply, tensorInnerPointwise_smul_left,
      tensorInnerPointwise_smul_right]
    nlinarith [mul_le_mul_of_nonneg_right hsq hbase]
  have hweighted : Integrable weighted μ := by
    exact (SmoothCcTensor.memL2_toFun
      (scalarSmul (I := I) (M := M) q r s ζ S)).integrable_inner_self
  have hbase : Integrable base μ := by
    exact (SmoothCcTensor.memL2_toFun S).integrable_inner_self
  have hint : (∫ x, weighted x ∂μ) ≤ ∫ x, C ^ 2 * base x ∂μ :=
    integral_mono_ae hweighted (hbase.const_mul (C ^ 2))
      (Filter.Eventually.of_forall hpoint)
  rw [integral_const_mul] at hint
  have hsq :
      ‖scalarSmul (I := I) (M := M) q r s ζ S‖ ^ 2 ≤
        (C * ‖S‖) ^ 2 := by
    simpa only [← real_inner_self_eq_norm_sq,
      SmoothCcTensor.inner_def, tensorL2Inner, weighted, base, μ, mul_pow] using hint
  have hrhs : 0 ≤ C * ‖S‖ := mul_nonneg hC (norm_nonneg S)
  nlinarith [norm_nonneg
    (scalarSmul (I := I) (M := M) q r s ζ S)]

end DifferentialGeometry.Analysis.Parabolic.TensorSpectral
end

end

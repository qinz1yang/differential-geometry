import DifferentialGeometry.Topology.VectorField.GradientLinearization
import DifferentialGeometry.Topology.VectorField.IndexLinearization

set_option autoImplicit false
noncomputable section
open Bundle
open scoped Manifold ContDiff
namespace DifferentialGeometry.VectorField
variable {d : ℕ} {g : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
  {a : EuclideanSpace ℝ (Fin (d + 1))}


theorem hasContinuousIsolatedZero_gradient_of_hessian_nondegenerate
    (hg : ContDiffAt ℝ 2 g a) (hcrit : fderiv ℝ g a = 0)
    (hnd : (QuadraticMap.associated
      (DifferentialGeometry.Topology.Morse.chartHessianAt g a)).SeparatingLeft) :
    HasContinuousIsolatedZero 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) (gradient g) a := by
  apply hasContinuousIsolatedZero_of_contMDiffAt_det_ne_zero
    𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) (contMDiffAt_gradient_section hg)
    ((gradient_eq_zero_iff (f := g) (x := a)).mpr hcrit)
  erw [linearizationAtZero_modelSpace_eq_fderiv]
  exact det_fderiv_gradient_ne_zero hg hnd


theorem index_gradient_eq_neg_one_pow_sigNeg
    (hg : ContDiffAt ℝ 2 g a)
    (hnd : (QuadraticMap.associated
      (DifferentialGeometry.Topology.Morse.chartHessianAt g a)).SeparatingLeft)
    (hV : HasContinuousIsolatedZero 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) (gradient g) a) :
    index 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) (gradient g) a hV =
      (-1 : ℤ) ^ sigNeg (DifferentialGeometry.Topology.Morse.chartHessianAt g a) := by
  have hdet : LinearMap.det (linearizationAtZero
      ((contMDiffAt_gradient_section hg).mdifferentiableAt one_ne_zero) hV.zero).toLinearMap ≠ 0 := by
    erw [linearizationAtZero_modelSpace_eq_fderiv]
    exact det_fderiv_gradient_ne_zero hg hnd
  rw [index_eq_sign_det_linearizationAtZero _ hV
    ((contMDiffAt_gradient_section hg).mdifferentiableAt one_ne_zero) hdet]
  erw [linearizationAtZero_modelSpace_eq_fderiv]
  exact sign_det_fderiv_gradient hg hnd


theorem exists_index_gradient_eq_neg_one_pow_sigNeg
    (hg : ContDiffAt ℝ 2 g a) (hcrit : fderiv ℝ g a = 0)
    (hnd : (QuadraticMap.associated
      (DifferentialGeometry.Topology.Morse.chartHessianAt g a)).SeparatingLeft) :
    ∃ hV : HasContinuousIsolatedZero 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) (gradient g) a,
      index 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) (gradient g) a hV =
        (-1 : ℤ) ^ sigNeg (DifferentialGeometry.Topology.Morse.chartHessianAt g a) :=
  ⟨hasContinuousIsolatedZero_gradient_of_hessian_nondegenerate hg hcrit hnd,
    index_gradient_eq_neg_one_pow_sigNeg hg hnd _⟩


theorem exists_index_gradient_of_isNondegenerateCriticalPointAt
    (hg : ContDiffAt ℝ 2 g a)
    (hcrit : DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt
      𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) g a) :
    ∃ hV : HasContinuousIsolatedZero 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) (gradient g) a,
      index 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) (gradient g) a hV =
        (-1 : ℤ) ^ sigNeg (DifferentialGeometry.Topology.Morse.chartHessianAt g a) := by
  apply exists_index_gradient_eq_neg_one_pow_sigNeg hg
  · simpa only [DifferentialGeometry.Topology.Morse.IsCriticalPointAt,
      mfderiv_eq_fderiv] using! hcrit.1
  · simpa only [mfld_simps, chartAt_self_eq] using! hcrit.2

end DifferentialGeometry.VectorField

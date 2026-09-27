import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.OriginalVolumeSplit
import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernel.Convolution.Lp

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set
open DifferentialGeometry.Analysis.Parabolic.Euclidean
open scoped ENNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow

def reducedSourceGaussianTailRate (n : ℕ) : ℝ :=
  100 * (1 + ∫ y : EuclideanSpace ℝ (Fin n),
    ‖y‖ ^ 2 * (((Real.pi : ℝ) ^ ((n : ℝ) / 2))⁻¹ * Real.exp (-‖y‖ ^ 2)))

theorem reducedSourceGaussianTailRate_pos (n : ℕ) :
    0 < reducedSourceGaussianTailRate n := by
  have hmoment : 0 ≤ ∫ y : EuclideanSpace ℝ (Fin n),
      ‖y‖ ^ 2 * (((Real.pi : ℝ) ^ ((n : ℝ) / 2))⁻¹ * Real.exp (-‖y‖ ^ 2)) :=
    integral_nonneg (fun y ↦ mul_nonneg (sq_nonneg ‖y‖)
      (mul_nonneg (inv_nonneg.mpr (Real.rpow_nonneg Real.pi_pos.le _))
        (Real.exp_pos _).le))
  unfold reducedSourceGaussianTailRate
  linarith only [hmoment]

private theorem reducedSourceGaussian_secondMoment_integrable (n : ℕ) [NeZero n] :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) ↦
      ‖y‖ ^ 2 * (((Real.pi : ℝ) ^ ((n : ℝ) / 2))⁻¹ * Real.exp (-‖y‖ ^ 2))) := by
  have h := gaussMoment_int (V := EuclideanSpace ℝ (Fin n)) 2 (a := 1) zero_lt_one
  apply (h.const_mul (((Real.pi : ℝ) ^ ((n : ℝ) / 2))⁻¹)).congr
  filter_upwards [] with y
  simp only [neg_one_mul]
  ring

theorem reducedSourceGaussianTail_le_rate_mul (n : ℕ) [NeZero n]
    (eps : ℝ) (heps : 0 < eps) :
    reducedSourceGaussianTail n (1 / (10 * Real.sqrt eps)) ≤
      ENNReal.ofReal (reducedSourceGaussianTailRate n * eps) := by
  let V := EuclideanSpace ℝ (Fin n)
  let d : V → ℝ := fun y ↦
    ((Real.pi : ℝ) ^ ((n : ℝ) / 2))⁻¹ * Real.exp (-‖y‖ ^ 2)
  let f : V → ℝ := fun y ↦ ‖y‖ ^ 2 * d y
  let A : Set V := {y | 1 / (10 * Real.sqrt eps) < ‖y‖}
  have hd : ∀ y : V, 0 ≤ d y := fun y ↦
    mul_nonneg (inv_nonneg.mpr (Real.rpow_nonneg Real.pi_pos.le _))
      (Real.exp_pos _).le
  have hf : ∀ y : V, 0 ≤ f y := fun y ↦ mul_nonneg (sq_nonneg ‖y‖) (hd y)
  have hfint : Integrable f := reducedSourceGaussian_secondMoment_integrable n
  have hscaled : Integrable (fun y : V ↦ (100 * eps) * f y) :=
    hfint.const_mul (100 * eps)
  have hA : MeasurableSet A :=
    measurableSet_lt measurable_const continuous_norm.measurable
  have hpoint : ∀ y ∈ A, d y ≤ (100 * eps) * f y := by
    intro y hy
    have hden : 0 < 10 * Real.sqrt eps := by positivity
    have hprod : 1 < ‖y‖ * (10 * Real.sqrt eps) := (div_lt_iff₀ hden).mp hy
    have hunit : 1 ≤ 100 * eps * ‖y‖ ^ 2 := by
      calc
        1 ≤ (‖y‖ * (10 * Real.sqrt eps)) ^ 2 := by
          simpa only [one_pow] using
            (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1)
              (mul_nonneg (norm_nonneg y) hden.le)).mpr hprod.le
        _ = 100 * eps * ‖y‖ ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt heps.le]
          ring
    calc
      d y = 1 * d y := (one_mul _).symm
      _ ≤ (100 * eps * ‖y‖ ^ 2) * d y := mul_le_mul_of_nonneg_right hunit (hd y)
      _ = (100 * eps) * f y := by dsimp only [f]; ring
  have htail : reducedSourceGaussianTail n (1 / (10 * Real.sqrt eps)) ≤
      ENNReal.ofReal ((100 * eps) * ∫ y : V, f y) := by
    calc
      reducedSourceGaussianTail n (1 / (10 * Real.sqrt eps)) =
          ∫⁻ y : V in A, ENNReal.ofReal (d y) := rfl
      _ ≤ ∫⁻ y : V in A, ENNReal.ofReal ((100 * eps) * f y) :=
        setLIntegral_mono' hA (fun y hy ↦ ENNReal.ofReal_le_ofReal (hpoint y hy))
      _ ≤ ∫⁻ y : V, ENNReal.ofReal ((100 * eps) * f y) := by
        simpa using lintegral_mono_set (subset_univ A)
      _ = ENNReal.ofReal (∫ y : V, (100 * eps) * f y) :=
        (ofReal_integral_eq_lintegral_ofReal hscaled
          (ae_of_all _ (fun y ↦ mul_nonneg (by positivity) (hf y)))).symm
      _ = ENNReal.ofReal ((100 * eps) * ∫ y : V, f y) := by
        rw [integral_const_mul]
  apply htail.trans
  apply ENNReal.ofReal_le_ofReal
  change (100 * eps) * (∫ y : V, f y) ≤
    (100 * (1 + ∫ y : V, f y)) * eps
  nlinarith only [heps]

end DifferentialGeometry.PDE.RicciFlow

end

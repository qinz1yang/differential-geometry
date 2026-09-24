import DifferentialGeometry.Analysis.Calculus.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section

open Set MeasureTheory

namespace DifferentialGeometry.Analysis

theorem integral_sq_le_measure_mul_integral_sq
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] {g : X → ℝ}
    (hg : MemLp g 2 μ) :
    (∫ x, g x ∂μ) ^ 2 ≤ (μ.real univ) * (∫ x, g x ^ 2 ∂μ) := by
  have hg' : MemLp (fun x => ‖g x‖) (ENNReal.ofReal 2) μ := by simpa using hg.norm
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := μ) (f := fun x => ‖g x‖) (g := fun _ : X => (1 : ℝ))
    Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun x => norm_nonneg (g x))
    (Filter.Eventually.of_forall fun _ => (by norm_num : (0 : ℝ) ≤ (1 : ℝ)))
    hg' (memLp_const _)
  simp only [mul_one, Real.rpow_two, one_pow, integral_const, smul_eq_mul,
    mul_one, ← Real.sqrt_eq_rpow] at hholder
  have hgi : 0 ≤ ∫ x, ‖g x‖ ∂μ := integral_nonneg fun x => norm_nonneg (g x)
  have hgs : 0 ≤ ∫ x, ‖g x‖ ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg ‖g x‖
  have hμ : 0 ≤ μ.real univ := measureReal_nonneg
  have hh := (sq_le_sq₀ hgi (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2
    hholder
  have hcs : (∫ x, ‖g x‖ ∂μ) ^ 2 ≤ μ.real univ * ∫ x, ‖g x‖ ^ 2 ∂μ := by
    simpa only [mul_pow, Real.sq_sqrt hgs, Real.sq_sqrt hμ, mul_comm] using hh
  have hi := (sq_le_sq₀ (norm_nonneg _) hgi).2 (norm_integral_le_integral_norm g)
  simpa only [Real.norm_eq_abs, sq_abs] using hi.trans hcs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem norm_sub_le_integral_norm_deriv_of_absolutelyContinuousOnInterval
    {f : ℝ → E} {a b x y : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    ‖f x - f y‖ ≤ ∫ t in a..b, ‖deriv f t‖ := by
  have hab : a ≤ b := hx.1.trans hx.2
  have hordered {u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) (huv : u ≤ v) :
      ‖f v - f u‖ ≤ ∫ t in a..b, ‖deriv f t‖ := by
    have hfuv : AbsolutelyContinuousOnInterval f u v := hf.mono (by
      rw [uIcc_of_le huv, uIcc_of_le hab]
      exact Icc_subset_Icc hu.1 hv.2)
    calc
      ‖f v - f u‖ = ‖∫ t in u..v, deriv f t‖ := by
        rw [hfuv.integral_deriv_eq_sub_vector]
      _ ≤ ∫ t in u..v, ‖deriv f t‖ :=
        intervalIntegral.norm_integral_le_integral_norm huv
      _ ≤ ∫ t in a..b, ‖deriv f t‖ :=
        intervalIntegral.integral_mono_interval hu.1 huv hv.2
          (Filter.Eventually.of_forall fun t => norm_nonneg (deriv f t))
          hf.intervalIntegrable_deriv_vector.norm
  rcases le_total x y with hxy | hyx
  · rw [norm_sub_rev]
    exact hordered hx hy hxy
  · exact hordered hy hx hyx

theorem norm_sub_sq_le_mul_integral_norm_deriv_sq_of_absolutelyContinuousOnInterval
    {f : ℝ → E} {a b x y : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hderiv : MemLp (deriv f) 2 (volume.restrict (Icc a b)))
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    ‖f x - f y‖ ^ 2 ≤ (b - a) * (∫ t in a..b, ‖deriv f t‖ ^ 2) := by
  have hab : a ≤ b := hx.1.trans hx.2
  have hdisp := norm_sub_le_integral_norm_deriv_of_absolutelyContinuousOnInterval hf hx hy
  have hcs := integral_sq_le_measure_mul_integral_sq hderiv.norm
  have hmeasure : (volume.restrict (Icc a b)).real univ = b - a := by
    rw [measureReal_restrict_apply_univ, Measure.real, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  rw [hmeasure] at hcs
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc] at hdisp ⊢
  exact ((sq_le_sq₀ (norm_nonneg _) (integral_nonneg fun t => norm_nonneg (deriv f t))).2
    hdisp).trans hcs

end DifferentialGeometry.Analysis

end

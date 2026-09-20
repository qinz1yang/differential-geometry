import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import DifferentialGeometry.Analysis.Integration.PolarDisk
import DifferentialGeometry.Analysis.Fourier.PeriodicVariations
import Mathlib.Analysis.Complex.TaylorSeries

section

namespace DifferentialGeometry.Analysis

theorem integral_circleMap_mul_pow_eq_zero {h : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DiffContOnCl ℂ h (Metric.ball 0 r)) (k : ℕ) :
    (∫ θ in 0..2 * Real.pi, h (circleMap 0 r θ) * (circleMap 0 1 θ) ^ (k + 1)) = 0 := by
  have hg : DiffContOnCl ℂ (fun z : ℂ => z ^ k * h z) (Metric.ball 0 r) := by
    simpa only [smul_eq_mul, Pi.pow_apply, id_eq] using (differentiable_id.pow k).diffContOnCl.smul hf
  have hz := hg.circleIntegral_eq_zero hr.le
  have hfactor : (∮ z in C(0, r), z ^ k * h z) =
      ((r : ℂ) ^ (k + 1) * Complex.I) *
        ∫ θ in 0..2 * Real.pi, h (circleMap 0 r θ) * (circleMap 0 1 θ) ^ (k + 1) := by
    rw [circleIntegral, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ hθ
    simp only [deriv_circleMap, smul_eq_mul]
    have hcircle : circleMap 0 r θ = (r : ℂ) * circleMap 0 1 θ := by
      simp [circleMap_zero]
    simp only [hcircle, mul_pow, pow_succ]
    ring
  rw [hfactor] at hz
  exact (mul_eq_zero.mp hz).resolve_left
    (mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hr.ne')) Complex.I_ne_zero)

end DifferentialGeometry.Analysis

end

section

open MeasureTheory Set
open scoped ComplexConjugate

namespace DifferentialGeometry.Analysis

theorem integral_circleMap_mul_conj_pow {h : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DiffContOnCl ℂ h (Metric.ball 0 r)) (n : ℕ) :
    (∫ θ in 0..2 * Real.pi, h (circleMap 0 r θ) * conj (circleMap 0 1 θ) ^ n) =
      (2 * (Real.pi : ℂ) * (r : ℂ) ^ n / (n.factorial : ℂ)) * iteratedDeriv n h 0 := by
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hkernel (θ : ℝ) :
      deriv (circleMap 0 r) θ *
          ((1 / circleMap 0 r θ ^ (n + 1)) * h (circleMap 0 r θ)) =
        (Complex.I / (r : ℂ) ^ n) *
          (h (circleMap 0 r θ) * conj (circleMap 0 1 θ) ^ n) := by
    have he : circleMap 0 1 θ ≠ 0 := circleMap_ne_center (by norm_num : (1 : ℝ) ≠ 0)
    have hconj : conj (circleMap 0 1 θ) = (circleMap 0 1 θ)⁻¹ :=
      (Complex.inv_eq_conj (by simp)).symm
    have hcircle : circleMap 0 r θ = (r : ℂ) * circleMap 0 1 θ := by
      simp [circleMap_zero]
    rw [deriv_circleMap, hconj, hcircle]
    simp only [mul_pow, pow_succ, inv_pow]
    field_simp [hrC, he]
  have hcauchy := DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul hr n hf
  simp only [circleIntegral, sub_zero, smul_eq_mul] at hcauchy
  simp_rw [hkernel] at hcauchy
  rw [intervalIntegral.integral_const_mul] at hcauchy
  apply mul_left_cancel₀ (div_ne_zero Complex.I_ne_zero (pow_ne_zero n hrC))
  calc
    _ = (2 * (Real.pi : ℂ) * Complex.I / (n.factorial : ℂ)) *
        iteratedDeriv n h 0 := hcauchy
    _ = _ := by field_simp [hrC, hfac]

end DifferentialGeometry.Analysis

end

section

open MeasureTheory Set
open scoped ComplexConjugate

namespace DifferentialGeometry.Analysis

theorem integral_re_circleMap_mul_sq_mul_conj_pow
    {h : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DiffContOnCl ℂ h (Metric.ball 0 r)) (n : ℕ) :
    (∫ θ in 0..2 * Real.pi,
      (((h (circleMap 0 r θ) * (circleMap 0 1 θ) ^ 2).re : ℝ) : ℂ) *
        conj (circleMap 0 1 θ) ^ (n + 2)) =
      ((Real.pi : ℂ) * (r : ℂ) ^ n / (n.factorial : ℂ)) * iteratedDeriv n h 0 := by
  have hcont : Continuous (fun θ => h (circleMap 0 r θ)) :=
    hf.continuousOn_ball.comp_continuous (continuous_circleMap 0 r)
      (fun θ => circleMap_mem_closedBall 0 hr.le θ)
  have hneg : IntervalIntegrable (fun θ =>
      h (circleMap 0 r θ) * conj (circleMap 0 1 θ) ^ n) volume 0 (2 * Real.pi) :=
    (hcont.mul ((Complex.continuous_conj.comp (continuous_circleMap 0 1)).pow n)).intervalIntegrable _ _
  have hpos : IntervalIntegrable (fun θ =>
      conj (h (circleMap 0 r θ) * (circleMap 0 1 θ) ^ (n + 4)))
      volume 0 (2 * Real.pi) :=
    (Complex.continuous_conj.comp (hcont.mul ((continuous_circleMap 0 1).pow (n + 4)))).intervalIntegrable _ _
  have hsplit (θ : ℝ) :
      (((h (circleMap 0 r θ) * (circleMap 0 1 θ) ^ 2).re : ℝ) : ℂ) *
          conj (circleMap 0 1 θ) ^ (n + 2) =
        (h (circleMap 0 r θ) * conj (circleMap 0 1 θ) ^ n +
          conj (h (circleMap 0 r θ) * (circleMap 0 1 θ) ^ (n + 4))) / 2 := by
    have he : circleMap 0 1 θ ≠ 0 := circleMap_ne_center (by norm_num : (1 : ℝ) ≠ 0)
    have hconj : conj (circleMap 0 1 θ) = (circleMap 0 1 θ)⁻¹ :=
      (Complex.inv_eq_conj (by simp)).symm
    rw [Complex.re_eq_add_conj]
    simp only [map_mul, map_pow, hconj, pow_add, inv_pow]
    field_simp [he]
  have hzero : (∫ θ in 0..2 * Real.pi,
      conj (h (circleMap 0 r θ) * (circleMap 0 1 θ) ^ (n + 4))) = 0 := by
    rw [intervalIntegral.integral_of_le Real.two_pi_pos.le, integral_conj,
      ← intervalIntegral.integral_of_le Real.two_pi_pos.le]
    have hz := integral_circleMap_mul_pow_eq_zero hr
      hf (n + 3)
    simpa only [Nat.add_assoc, Nat.reduceAdd, map_zero] using congrArg conj hz
  simp_rw [hsplit]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add hneg hpos,
    integral_circleMap_mul_conj_pow hr hf n, hzero]
  ring


theorem setIntegral_re_circleMap_mul_sq_mul_conj_pow
    {h : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DiffContOnCl ℂ h (Metric.ball 0 r)) (n : ℕ) :
    (∫ θ in Ioo (-Real.pi) Real.pi,
      (((h (circleMap 0 r θ) * (circleMap 0 1 θ) ^ 2).re : ℝ) : ℂ) *
        conj (circleMap 0 1 θ) ^ (n + 2)) =
      ((Real.pi : ℂ) * (r : ℂ) ^ n / (n.factorial : ℂ)) * iteratedDeriv n h 0 := by
  let f : ℝ → ℂ := fun θ =>
    (((h (circleMap 0 r θ) * (circleMap 0 1 θ) ^ 2).re : ℝ) : ℂ) *
      conj (circleMap 0 1 θ) ^ (n + 2)
  have hp : Function.Periodic f (2 * Real.pi) := by
    intro θ
    dsimp only [f]
    rw [periodic_circleMap 0 r θ, periodic_circleMap 0 1 θ]
  have hshift := hp.intervalIntegral_add_eq (-Real.pi) 0
  simp only [zero_add] at hshift
  have hend : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rw [hend, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    integral_Ioc_eq_integral_Ioo] at hshift
  exact hshift.trans (integral_re_circleMap_mul_sq_mul_conj_pow hr hf n)

theorem setIntegral_re_circleMap_exp_arg_sq_mul_conj_pow
    {h : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DiffContOnCl ℂ h (Metric.ball 0 r)) (n : ℕ) :
    (∫ θ in Ioo (-Real.pi) Real.pi,
      (((h (circleMap 0 r θ) *
        Complex.exp ((Complex.arg (circleMap 0 r θ) : ℂ) * Complex.I) ^ 2).re : ℝ) : ℂ) *
        conj (Complex.exp ((Complex.arg (circleMap 0 r θ) : ℂ) * Complex.I)) ^ (n + 2)) =
      (((Real.pi : ℂ) / (n.factorial : ℂ)) * iteratedDeriv n h 0) * (r : ℂ) ^ n := by
  calc
    _ = ∫ θ in Ioo (-Real.pi) Real.pi,
        (((h (circleMap 0 r θ) * (circleMap 0 1 θ) ^ 2).re : ℝ) : ℂ) *
          conj (circleMap 0 1 θ) ^ (n + 2) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro θ hθ
      have harg : Complex.arg (circleMap 0 r θ) = θ := by
        rw [circleMap_zero, Complex.exp_mul_I]
        exact Complex.arg_mul_cos_add_sin_mul_I hr ⟨hθ.1, hθ.2.le⟩
      dsimp only
      rw [harg]
      simp [circleMap_zero]
    _ = _ := by
      rw [setIntegral_re_circleMap_mul_sq_mul_conj_pow hr hf n]
      ring

end DifferentialGeometry.Analysis

end

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ComplexConjugate NNReal

namespace DifferentialGeometry.Analysis

theorem integral_re_holomorphic_radial_moment
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Metric.ball (0 : ℂ) 1))
    (hi : IntegrableOn h (Metric.ball (0 : ℂ) 1)) (n : ℕ) :
    (∫ z in Metric.ball (0 : ℂ) 1,
      (((h z * Complex.exp ((Complex.arg z : ℂ) * Complex.I) ^ 2).re : ℝ) : ℂ) *
        conj (Complex.exp ((Complex.arg z : ℂ) * Complex.I)) ^ (n + 2)) =
      (((Real.pi : ℂ) / (n.factorial : ℂ)) * iteratedDeriv n h 0) / ((n : ℂ) + 2) := by
  apply integral_unit_disk_eq_of_complex_circle_integral
    (integrable_radial_fourier_moment hi (n + 2)) n
  intro r hr
  exact setIntegral_re_circleMap_exp_arg_sq_mul_conj_pow hr.1
    ((hh.mono (Metric.closedBall_subset_ball hr.2)).diffContOnCl_ball subset_rfl) n

theorem eq_zero_on_unit_disk_of_holomorphic_radial_variations
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Metric.ball (0 : ℂ) 1))
    (hi : IntegrableOn h (Metric.ball (0 : ℂ) 1))
    (hvariation : ∀ ψ : ℝ → ℝ, Differentiable ℝ ψ →
      (∃ C : ℝ≥0, LipschitzWith C ψ) → Function.Periodic ψ 1 →
      (∫ z in Metric.ball (0 : ℂ) 1, deriv ψ (Complex.arg z / (2 * Real.pi)) *
        (h z * Complex.exp ((Complex.arg z : ℂ) * Complex.I) ^ 2).re) = 0) :
    EqOn h 0 (Metric.ball (0 : ℂ) 1) := by
  have hderiv (n : ℕ) : iteratedDeriv n h 0 = 0 := by
    have hmoment := integral_radial_fourier_eq_zero_of_periodic_variations hi hvariation n
    rw [integral_re_holomorphic_radial_moment hh hi n] at hmoment
    have hden : (n : ℂ) + 2 ≠ 0 := by
      exact_mod_cast (by positivity : (0 : ℝ) < (n : ℝ) + 2).ne'
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    exact (mul_eq_zero.mp ((div_eq_zero_iff.mp hmoment).resolve_right hden)).resolve_left
      (div_ne_zero hpi hfac)
  intro z hz
  have ht := Complex.taylorSeries_eq_on_ball' hz hh
  simp only [hderiv, mul_zero, zero_mul, tsum_zero] at ht
  exact ht.symm

end DifferentialGeometry.Analysis

end

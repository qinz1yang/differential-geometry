import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.PerMode
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section

open Set MeasureTheory Filter intervalIntegral
open scoped Topology ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace MaximalRegularity

def duhamelKernelSqIntegral (lam t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, Real.exp (-(2 * lam * (t - s)))

theorem two_lambda_mul_duhamelKernelSqIntegral (lam t : ℝ) :
    (2 * lam) * duhamelKernelSqIntegral lam t = 1 - Real.exp (-(2 * lam * t)) := by
  unfold duhamelKernelSqIntegral
  rw [← intervalIntegral.integral_const_mul]
  exact kernelIntegral_space (2 * lam) t

theorem duhamelKernelSqIntegral_nonneg {lam t : ℝ} (ht : 0 ≤ t) :
    0 ≤ duhamelKernelSqIntegral lam t := by
  unfold duhamelKernelSqIntegral
  exact intervalIntegral.integral_nonneg ht (fun s _ => (Real.exp_pos _).le)

theorem duhamelKernelSqIntegral_le_t {lam t : ℝ} (hlam : 0 ≤ lam) (ht : 0 ≤ t) :
    duhamelKernelSqIntegral lam t ≤ t := by
  unfold duhamelKernelSqIntegral
  calc ∫ s in (0 : ℝ)..t, Real.exp (-(2 * lam * (t - s)))
      ≤ ∫ _s in (0 : ℝ)..t, (1 : ℝ) := by
        refine intervalIntegral.integral_mono_on ht
          (Continuous.intervalIntegrable (by fun_prop) 0 t)
          intervalIntegral.intervalIntegrable_const (fun s hs => ?_)
        refine Real.exp_le_one_iff.mpr ?_
        have : 0 ≤ 2 * lam * (t - s) := by nlinarith [hs.1, hs.2]
        linarith
    _ = t := by simp

theorem one_add_lambda_mul_duhamel_kernel_sq_integral_le {lam t : ℝ}
    (hlam : 0 ≤ lam) (ht : 0 ≤ t) :
    (1 + lam) * duhamelKernelSqIntegral lam t ≤ t + 1 / 2 := by
  have hmass_nn : 0 ≤ duhamelKernelSqIntegral lam t :=
    duhamelKernelSqIntegral_nonneg ht
  have hmass_le_t : duhamelKernelSqIntegral lam t ≤ t :=
    duhamelKernelSqIntegral_le_t hlam ht
  have hlam_mass : lam * duhamelKernelSqIntegral lam t ≤ 1 / 2 := by
    have h := two_lambda_mul_duhamelKernelSqIntegral lam t
    have hexp_nn : (0 : ℝ) ≤ Real.exp (-(2 * lam * t)) := (Real.exp_pos _).le
    nlinarith [h, hexp_nn]
  have hexpand : (1 + lam) * duhamelKernelSqIntegral lam t
      = duhamelKernelSqIntegral lam t + lam * duhamelKernelSqIntegral lam t := by
    ring
  rw [hexpand]
  linarith

variable {f : ℝ → ℝ}

theorem perModeConv_endpoint_sq_le (lam : ℝ) (hf : Continuous f) {t : ℝ}
    (ht : 0 ≤ t) :
    (perModeConv lam f t) ^ 2
      ≤ duhamelKernelSqIntegral lam t * ∫ s in (0 : ℝ)..t, f s ^ 2 := by
  set k : ℝ → ℝ := fun s => Real.exp (-(lam * (t - s))) with hk_def
  have hconv_eq : perModeConv lam f t = ∫ s in (0 : ℝ)..t, k s * f s := rfl
  set A : ℝ := ∫ s in (0 : ℝ)..t, f s ^ 2 with hA
  set B : ℝ := ∫ s in (0 : ℝ)..t, k s * f s with hB
  set C : ℝ := ∫ s in (0 : ℝ)..t, k s ^ 2 with hC
  have hC_eq : C = duhamelKernelSqIntegral lam t := by
    rw [hC]
    unfold duhamelKernelSqIntegral
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    rw [hk_def, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hquad : ∀ c : ℝ, 0 ≤ A * (c * c) + (-(2 * B)) * c + C := by
    intro c
    have hintegrand : (fun s => (k s - c * f s) ^ 2)
        = fun s => (c * c) * f s ^ 2 + (-(2 * c)) * (k s * f s) + k s ^ 2 := by
      funext s
      ring
    have hi_f2 : IntervalIntegrable (fun s => f s ^ 2) volume 0 t :=
      ((hf.pow 2)).intervalIntegrable 0 t
    have hi_kf : IntervalIntegrable (fun s => k s * f s) volume 0 t := by
      apply Continuous.intervalIntegrable
      rw [hk_def]
      fun_prop
    have hi_k2 : IntervalIntegrable (fun s => k s ^ 2) volume 0 t := by
      apply Continuous.intervalIntegrable
      rw [hk_def]
      fun_prop
    have hexpand : (∫ s in (0 : ℝ)..t, (k s - c * f s) ^ 2)
        = (c * c) * A + (-(2 * c)) * B + C := by
      rw [hintegrand,
        intervalIntegral.integral_add
          ((hi_f2.const_mul (c * c)).add (hi_kf.const_mul (-(2 * c)))) hi_k2,
        intervalIntegral.integral_add (hi_f2.const_mul (c * c))
          (hi_kf.const_mul (-(2 * c))),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hnonneg : 0 ≤ ∫ s in (0 : ℝ)..t, (k s - c * f s) ^ 2 :=
      intervalIntegral.integral_nonneg ht (fun s _ => sq_nonneg _)
    rw [hexpand] at hnonneg
    nlinarith [hnonneg]
  have hdiscrim : discrim A (-(2 * B)) C ≤ 0 :=
    discrim_le_zero (fun c => by nlinarith [hquad c])
  rw [discrim] at hdiscrim
  rw [hC_eq] at hdiscrim
  rw [hconv_eq]
  nlinarith [hdiscrim]

theorem one_add_lambda_mul_perModeConv_endpoint_sq_le (lam : ℝ)
    (hlam : 0 ≤ lam) (hf : Continuous f) {t : ℝ} (ht : 0 ≤ t) :
    (1 + lam) * (perModeConv lam f t) ^ 2
      ≤ (t + 1 / 2) * ∫ s in (0 : ℝ)..t, f s ^ 2 := by
  have hcs := perModeConv_endpoint_sq_le (f := f) lam hf ht
  have hkernel := one_add_lambda_mul_duhamel_kernel_sq_integral_le hlam ht
  have hf2_nn : 0 ≤ ∫ s in (0 : ℝ)..t, f s ^ 2 :=
    intervalIntegral.integral_nonneg ht (fun s _ => sq_nonneg _)
  have h1plus_nn : 0 ≤ 1 + lam := by linarith
  calc (1 + lam) * (perModeConv lam f t) ^ 2
      ≤ (1 + lam) *
          (duhamelKernelSqIntegral lam t * ∫ s in (0 : ℝ)..t, f s ^ 2) :=
        mul_le_mul_of_nonneg_left hcs h1plus_nn
    _ = ((1 + lam) * duhamelKernelSqIntegral lam t) *
          ∫ s in (0 : ℝ)..t, f s ^ 2 := by ring
    _ ≤ (t + 1 / 2) * ∫ s in (0 : ℝ)..t, f s ^ 2 :=
        mul_le_mul_of_nonneg_right hkernel hf2_nn

end MaximalRegularity
end Parabolic
end Analysis
end DifferentialGeometry

end

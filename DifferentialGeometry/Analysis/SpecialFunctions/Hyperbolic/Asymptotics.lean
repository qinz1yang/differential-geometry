/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import Batteries.Data.BitVec.Lemmas
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

open Filter Topology

namespace DifferentialGeometry.HyperbolicFunctions

theorem tendsto_exp_sub_of_cosh {d : ℝ → ℝ} (A B : ℝ) (hAB : 0 < A + B)
    (hd : ∀ t, 0 ≤ d t) (hcosh : ∀ t, Real.cosh (d t) = Real.cosh t * A + Real.sinh t * B) :
    Tendsto (fun t => Real.exp (d t - t)) atTop (𝓝 (A + B)) := by
  set M : ℝ → ℝ := fun t => Real.cosh t * A + Real.sinh t * B with hM
  have hsinh : ∀ t, Real.sinh (d t) = Real.sqrt ((M t) ^ 2 - 1) := by
    intro t
    have h1 : 0 ≤ Real.sinh (d t) := Real.sinh_nonneg_iff.mpr (hd t)
    have hc := Real.cosh_sq_sub_sinh_sq (d t)
    rw [hcosh t] at hc
    have h2 : (M t) ^ 2 - 1 = Real.sinh (d t) ^ 2 := by linarith [hc]
    rw [h2]
    exact (Real.sqrt_sq h1).symm
  have hexpd : ∀ t, Real.exp (d t) = M t + Real.sqrt ((M t) ^ 2 - 1) := by
    intro t
    rw [← Real.cosh_add_sinh, hcosh t, hsinh t]
  have hexp : ∀ t, Real.exp (d t - t) = Real.exp (d t) * Real.exp (-t) := by
    intro t
    rw [Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg]
  have hE : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have hE2 : Tendsto (fun t : ℝ => (Real.exp (-t)) ^ 2) atTop (𝓝 0) := by
    have h := hE.pow 2
    simpa using h
  have hcosh_e : ∀ t : ℝ, Real.cosh t * Real.exp (-t) = (1 + (Real.exp (-t)) ^ 2) / 2 := by
    intro t
    rw [Real.cosh_eq]
    have h1 : Real.exp t * Real.exp (-t) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h2 : Real.exp (-t) * Real.exp (-t) = (Real.exp (-t)) ^ 2 := by ring
    calc (Real.exp t + Real.exp (-t)) / 2 * Real.exp (-t)
        = (Real.exp t * Real.exp (-t) + Real.exp (-t) * Real.exp (-t)) / 2 := by ring
      _ = (1 + (Real.exp (-t)) ^ 2) / 2 := by rw [h1, h2]
  have hsinh_e : ∀ t : ℝ, Real.sinh t * Real.exp (-t) = (1 - (Real.exp (-t)) ^ 2) / 2 := by
    intro t
    rw [Real.sinh_eq]
    have h1 : Real.exp t * Real.exp (-t) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h2 : Real.exp (-t) * Real.exp (-t) = (Real.exp (-t)) ^ 2 := by ring
    calc (Real.exp t - Real.exp (-t)) / 2 * Real.exp (-t)
        = (Real.exp t * Real.exp (-t) - Real.exp (-t) * Real.exp (-t)) / 2 := by ring
      _ = (1 - (Real.exp (-t)) ^ 2) / 2 := by rw [h1, h2]
  have hcl : Tendsto (fun t => Real.cosh t * Real.exp (-t)) atTop (𝓝 (1 / 2)) := by
    have hbase : Tendsto (fun t => (1 + (Real.exp (-t)) ^ 2) / 2) atTop (𝓝 ((1 + 0) / 2)) :=
      (tendsto_const_nhds.add hE2).div_const 2
    have h12 : (1 + (0 : ℝ)) / 2 = 1 / 2 := by norm_num
    rw [h12] at hbase
    exact hbase.congr fun t => (hcosh_e t).symm
  have hsl : Tendsto (fun t => Real.sinh t * Real.exp (-t)) atTop (𝓝 (1 / 2)) := by
    have hbase : Tendsto (fun t => (1 - (Real.exp (-t)) ^ 2) / 2) atTop (𝓝 ((1 - 0) / 2)) :=
      (tendsto_const_nhds.sub hE2).div_const 2
    have h12 : (1 - (0 : ℝ)) / 2 = 1 / 2 := by norm_num
    rw [h12] at hbase
    exact hbase.congr fun t => (hsinh_e t).symm
  have hMe : Tendsto (fun t => M t * Real.exp (-t)) atTop (𝓝 ((A + B) / 2)) := by
    have hrewrite : (fun t => M t * Real.exp (-t))
        = fun t => A * (Real.cosh t * Real.exp (-t)) + B * (Real.sinh t * Real.exp (-t)) := by
      funext t
      rw [hM]
      ring
    rw [hrewrite]
    have hsum := (hcl.const_mul A).add (hsl.const_mul B)
    have hval : A * (1 / 2) + B * (1 / 2) = (A + B) / 2 := by ring
    rw [hval] at hsum
    exact hsum
  have hS : Tendsto (fun t => Real.sqrt ((M t) ^ 2 - 1) * Real.exp (-t)) atTop
      (𝓝 ((A + B) / 2)) := by
    have hMnn : ∀ t, 0 ≤ (M t) ^ 2 - 1 := by
      intro t
      have hc := Real.cosh_sq_sub_sinh_sq (d t)
      rw [hcosh t] at hc
      nlinarith [hc, sq_nonneg (Real.sinh (d t))]
    have hrew : (fun t => Real.sqrt ((M t) ^ 2 - 1) * Real.exp (-t))
        = fun t => Real.sqrt (((M t) * Real.exp (-t)) ^ 2 - (Real.exp (-t)) ^ 2) := by
      funext t
      have hu : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
      calc Real.sqrt ((M t) ^ 2 - 1) * Real.exp (-t)
          = Real.sqrt ((M t) ^ 2 - 1) * Real.sqrt ((Real.exp (-t)) ^ 2) := by
            rw [Real.sqrt_sq hu]
        _ = Real.sqrt (((M t) ^ 2 - 1) * (Real.exp (-t)) ^ 2) := by
            rw [Real.sqrt_mul (hMnn t)]
        _ = Real.sqrt (((M t) * Real.exp (-t)) ^ 2 - (Real.exp (-t)) ^ 2) := by
            congr 1; ring
    rw [hrew]
    have hsq : Tendsto (fun t => ((M t) * Real.exp (-t)) ^ 2) atTop (𝓝 (((A + B) / 2) ^ 2)) :=
      hMe.pow 2
    have harg : Tendsto (fun t => ((M t) * Real.exp (-t)) ^ 2 - (Real.exp (-t)) ^ 2)
        atTop (𝓝 (((A + B) / 2) ^ 2 - 0)) := hsq.sub hE2
    have hsqrtc : ContinuousAt Real.sqrt (((A + B) / 2) ^ 2 - 0) :=
      Real.continuous_sqrt.continuousAt
    have hcom := hsqrtc.tendsto.comp harg
    have hval : Real.sqrt (((A + B) / 2) ^ 2 - 0) = (A + B) / 2 := by
      rw [sub_zero]
      exact Real.sqrt_sq (by linarith [hAB])
    rw [hval] at hcom
    exact hcom
  have hsum : Tendsto (fun t => M t * Real.exp (-t) + Real.sqrt ((M t) ^ 2 - 1) * Real.exp (-t))
      atTop (𝓝 ((A + B) / 2 + (A + B) / 2)) := hMe.add hS
  have hfin : (A + B) / 2 + (A + B) / 2 = A + B := by ring
  rw [hfin] at hsum
  refine hsum.congr fun t => ?_
  rw [hexp t, hexpd t]
  ring

theorem tendsto_sub_log_of_cosh {d : ℝ → ℝ} (A B : ℝ) (hAB : 0 < A + B)
    (hd : ∀ t, 0 ≤ d t) (hcosh : ∀ t, Real.cosh (d t) = Real.cosh t * A + Real.sinh t * B) :
    Tendsto (fun t => d t - t) atTop (𝓝 (Real.log (A + B))) := by
  have hmain := tendsto_exp_sub_of_cosh A B hAB hd hcosh
  have hlog : Tendsto (fun t => Real.log (Real.exp (d t - t))) atTop
      (𝓝 (Real.log (A + B))) :=
    (Real.continuousAt_log (ne_of_gt hAB)).tendsto.comp hmain
  exact hlog.congr fun t => Real.log_exp (d t - t)

theorem sinh_add_sinh_gen (A B : ℝ) :
    Real.sinh (A + B) + Real.sinh (A - B) = 2 * Real.sinh A * Real.cosh B := by
  rw [Real.sinh_add, Real.sinh_sub]; ring

theorem sinh_sub_add_sinh_le {T t : ℝ} (hT : 0 ≤ T) (ht0 : 0 ≤ t) (htT : t ≤ T) :
    Real.sinh (T - t) + Real.sinh t ≤ Real.sinh T := by
  have hsum : Real.sinh (T - t) + Real.sinh t
      = 2 * Real.sinh (T / 2) * Real.cosh (T / 2 - t) := by
    have h := sinh_add_sinh_gen (T / 2) (T / 2 - t)
    have e1 : T / 2 + (T / 2 - t) = T - t := by ring
    have e2 : T / 2 - (T / 2 - t) = t := by ring
    rw [e1, e2] at h
    exact h
  have hT2 : Real.sinh T = 2 * Real.sinh (T / 2) * Real.cosh (T / 2) := by
    have h := Real.sinh_two_mul (T / 2)
    have e : 2 * (T / 2) = T := by ring
    rw [e] at h
    exact h
  have hsinh_nn : (0:ℝ) ≤ Real.sinh (T / 2) := Real.sinh_nonneg_iff.mpr (by linarith)
  have hcosh : Real.cosh (T / 2 - t) ≤ Real.cosh (T / 2) := by
    rw [Real.cosh_le_cosh]
    have h1 : |T / 2 - t| ≤ T / 2 := by
      rw [abs_le]; constructor <;> linarith
    calc |T / 2 - t| ≤ T / 2 := h1
      _ = |T / 2| := (abs_of_nonneg (by linarith)).symm
  rw [hsum, hT2]
  exact mul_le_mul_of_nonneg_left hcosh (mul_nonneg (by norm_num) hsinh_nn)

end DifferentialGeometry.HyperbolicFunctions

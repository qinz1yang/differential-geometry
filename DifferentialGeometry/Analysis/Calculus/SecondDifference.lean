import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology

theorem ContDiff.tendsto_centered_second_difference
    {f : Real → Real} (hf : ContDiff Real 2 f) (x : Real) :
    Tendsto (fun h : Real ↦ (f (x + h) - 2 * f x + f (x - h)) / h ^ 2)
      (𝓝[≠] (0 : Real)) (𝓝 (deriv (deriv f) x)) := by
  have hTaylor : ∀ y : Real,
      taylorWithinEval f 2 univ x y =
        f x + (y - x) * deriv f x + (y - x) ^ 2 / 2 * deriv (deriv f) x := by
    intro y
    norm_num [taylorWithinEval_succ, taylor_within_zero_eval,
      iteratedDerivWithin_univ, iteratedDeriv_succ, iteratedDeriv_zero,
      smul_eq_mul]
    ring_nf
    simp
  have ht : Tendsto
      (fun y ↦ (f y - taylorWithinEval f 2 univ x y) / (y - x) ^ 2)
      (𝓝 x) (𝓝 0) := by
    simpa only [nhdsWithin_univ] using
      Real.taylor_tendsto convex_univ (mem_univ x) hf.contDiffOn
  have hh : Tendsto (fun h : Real ↦ h) (𝓝[≠] (0 : Real)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hp_arg : Tendsto (fun h : Real ↦ x + h)
      (𝓝[≠] (0 : Real)) (𝓝 x) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := x)).add hh
  have hm_arg : Tendsto (fun h : Real ↦ x - h)
      (𝓝[≠] (0 : Real)) (𝓝 x) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := x)).sub hh
  have hp := ht.comp hp_arg
  have hm := ht.comp hm_arg
  have hsum := (hp.add hm).add_const (deriv (deriv f) x)
  simp only [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh0
  have hhne : h ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hh0
  simp only [Function.comp_apply]
  rw [hTaylor, hTaylor]
  field_simp [hhne]
  ring

end

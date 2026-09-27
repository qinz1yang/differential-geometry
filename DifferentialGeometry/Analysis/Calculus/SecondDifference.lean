import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology

theorem ContDiffAt.tendsto_centered_second_difference
    {f : ℝ → ℝ} {x : ℝ} (hf : ContDiffAt ℝ 2 f x) :
    Tendsto (fun h : ℝ => (f (x + h) - 2 * f x + f (x - h)) / h ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (deriv (deriv f) x)) := by
  obtain ⟨U, hU, hfU⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hx : x ∈ Metric.ball x r := Metric.mem_ball_self hr
  have hfb : ContDiffOn ℝ 2 f (Metric.ball x r) := hfU.mono hball
  have hiter (n : ℕ) :
      iteratedDerivWithin n f (Metric.ball x r) x = iteratedDeriv n f x :=
    iteratedDerivWithin_of_isOpen Metric.isOpen_ball hx
  have hTaylor : ∀ y : ℝ,
      taylorWithinEval f 2 (Metric.ball x r) x y =
        f x + (y - x) * deriv f x + (y - x) ^ 2 / 2 * deriv (deriv f) x := by
    intro y
    norm_num [taylorWithinEval_succ, taylor_within_zero_eval, hiter,
      iteratedDeriv_succ, iteratedDeriv_zero, smul_eq_mul]
    ring_nf
    simp
  have ht : Tendsto
      (fun y => (f y - taylorWithinEval f 2 (Metric.ball x r) x y) / (y - x) ^ 2)
      (𝓝 x) (𝓝 0) := by
    simpa only [nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds x hr)] using
      Real.taylor_tendsto (convex_ball x r) hx hfb
  have hh : Tendsto (fun h : ℝ => h) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hp_arg : Tendsto (fun h : ℝ => x + h)
      (𝓝[≠] (0 : ℝ)) (𝓝 x) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := x)).add hh
  have hm_arg : Tendsto (fun h : ℝ => x - h)
      (𝓝[≠] (0 : ℝ)) (𝓝 x) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := x)).sub hh
  have hp := ht.comp hp_arg
  have hm := ht.comp hm_arg
  have hsum := (hp.add hm).add_const (deriv (deriv f) x)
  simp only [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh0
  have hhne : h ≠ 0 := by
    simpa only [mem_compl_iff, mem_singleton_iff] using hh0
  simp only [Function.comp_apply]
  rw [hTaylor, hTaylor]
  field_simp [hhne]
  ring

theorem ContDiffAt.deriv_deriv_comp_affine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {psi : E → ℝ} {x : E} (hpsi : ContDiffAt ℝ 2 psi x) (v : E) :
    deriv (deriv (fun t : ℝ => psi (x + t • v))) 0 =
      fderiv ℝ (fun y => fderiv ℝ psi y v) x v := by
  let line : ℝ → E := fun t => x + t • v
  let g : ℝ → ℝ := fun t => psi (line t)
  let G : E → ℝ := fun y => fderiv ℝ psi y v
  have hline : ContDiff ℝ 2 line :=
    contDiff_const.add (contDiff_id.smul_const v)
  have hline_deriv (t : ℝ) : HasDerivAt line v t := by
    simpa only [line, id_eq, one_smul] using ((hasDerivAt_id t).smul_const v).const_add x
  have hline_tendsto : Tendsto line (𝓝 (0 : ℝ)) (𝓝 x) := by
    simpa only [line, zero_smul, add_zero] using hline.continuous.tendsto (0 : ℝ)
  have hdiff : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ psi y :=
    (hpsi.eventually (by simp)).mono fun _ hy => hy.differentiableAt (by norm_num)
  have hderiv : deriv g =ᶠ[𝓝 (0 : ℝ)] fun t => G (line t) := by
    filter_upwards [hline_tendsto.eventually hdiff] with t ht
    simpa only [g, G, Function.comp_def] using
      (ht.hasFDerivAt.comp_hasDerivAt t (hline_deriv t)).deriv
  have hG : ContDiffAt ℝ 1 G x :=
    (hpsi.fderiv_right (by norm_num)).clm_apply contDiffAt_const
  have hG_deriv : HasFDerivAt G (fderiv ℝ G x) (line 0) := by
    simpa only [line, zero_smul, add_zero] using
      (hG.differentiableAt one_ne_zero).hasFDerivAt
  have hG_line : HasDerivAt (fun t => G (line t)) (fderiv ℝ G x v) 0 :=
    hG_deriv.comp_hasDerivAt 0 (hline_deriv 0)
  exact (hG_line.congr_of_eventuallyEq hderiv).deriv

theorem ContDiffAt.tendsto_directional_second_difference
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {psi : E → ℝ} {x : E} (hpsi : ContDiffAt ℝ 2 psi x) (v : E) :
    Tendsto
      (fun h : ℝ => (psi (x + h • v) - 2 * psi x + psi (x - h • v)) / h ^ 2)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (fderiv ℝ (fun y => fderiv ℝ psi y v) x v)) := by
  have hline : ContDiffAt ℝ 2 (fun t : ℝ => x + t • v) 0 :=
    contDiffAt_const.add (contDiffAt_id.smul_const v)
  have hpsi_line : ContDiffAt ℝ 2 psi (x + (0 : ℝ) • v) := by
    simpa only [zero_smul, add_zero] using hpsi
  have hg : ContDiffAt ℝ 2 (fun t : ℝ => psi (x + t • v)) 0 :=
    hpsi_line.comp 0 hline
  have hlim := hg.tendsto_centered_second_difference
  rw [hpsi.deriv_deriv_comp_affine v] at hlim
  simpa only [zero_add, zero_sub, zero_smul, add_zero, neg_smul,
    ← sub_eq_add_neg] using hlim

end

section

open Filter
open scoped Topology

theorem ContDiff.tendsto_centered_second_difference
    {f : Real → Real} (hf : ContDiff Real 2 f) (x : Real) :
    Tendsto (fun h : Real ↦ (f (x + h) - 2 * f x + f (x - h)) / h ^ 2)
      (𝓝[≠] (0 : Real)) (𝓝 (deriv (deriv f) x)) :=
  hf.contDiffAt.tendsto_centered_second_difference

end

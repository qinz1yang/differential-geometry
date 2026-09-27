import DifferentialGeometry.Topology.Compactness.Nonvanishing
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.Instances.AddCircle.Real

set_option autoImplicit false

open Set Metric Filter
open scoped Topology

namespace DifferentialGeometry.Calculus

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem eq_of_deriv_close_of_eq {f d : ℝ → F} {x y : ℝ} {v : F} {C : ℝ}
    (hf : ∀ r ∈ uIcc x y, HasDerivAt f (d r) r)
    (hd : ∀ r ∈ uIcc x y, ‖d r - v‖ ≤ C) (hC : C < ‖v‖) (heq : f x = f y) :
    x = y := by
  have hres : ∀ r ∈ uIcc x y,
      HasDerivWithinAt (fun t => f t - t • v) (d r - v) (uIcc x y) r := by
    intro r hr
    simpa only [one_smul, Pi.sub_apply, id_eq] using
      ((hf r hr).fun_sub ((hasDerivAt_id r).smul_const v)).hasDerivWithinAt
  have hb := (convex_uIcc x y).norm_image_sub_le_of_norm_hasDerivWithin_le
    hres hd left_mem_uIcc right_mem_uIcc
  have hid : (f y - y • v) - (f x - x • v) = -((y - x) • v) := by
    rw [heq, sub_smul]
    abel
  rw [hid, norm_neg, norm_smul] at hb
  by_contra hxy
  have hpos : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hxy))
  have hle : ‖v‖ ≤ C := (mul_le_mul_iff_right₀ hpos).mp (by simpa only [mul_comm] using hb)
  exact hC.not_ge hle

variable {P : Type*} [TopologicalSpace P] [CompactSpace P]
  {T : ℝ} [Fact (0 < T)]

theorem exists_uniform_injective_radius_of_deriv_close
    {c v : P → AddCircle T → F}
    (hv : Continuous (fun p : P × AddCircle T => v p.1 p.2))
    (hderiv : ∀ (p : P) (r : ℝ), HasDerivAt (fun t : ℝ => c p (t : AddCircle T))
      (v p (r : AddCircle T)) r)
    (hne : ∀ p z, v p z ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ (p : P) (g : AddCircle T → F),
        Differentiable ℝ (fun t : ℝ => g (t : AddCircle T)) →
        (∀ r : ℝ, ‖deriv (fun t : ℝ => g (t : AddCircle T)) r -
          deriv (fun t : ℝ => c p (t : AddCircle T)) r‖ < ε) →
        (∀ r : ℝ, deriv (fun t : ℝ => g (t : AddCircle T)) r ≠ 0) ∧
        ∀ z w : AddCircle T, dist z w < δ → g z = g w → z = w := by
  obtain ⟨m, hm, hbound⟩ :=
    DifferentialGeometry.Topology.exists_pos_lt_norm_of_isCompact isCompact_univ hv.continuousOn
      (fun q _ => hne q.1 q.2)
  have hcont : Continuous (fun a : ℝ × (P × AddCircle T) =>
      ‖v a.2.1 (a.2.2 + (a.1 : AddCircle T)) - v a.2.1 a.2.2‖) :=
    ((hv.comp (continuous_snd.fst.prodMk
      (continuous_snd.snd.add ((AddCircle.continuous_mk' T).comp continuous_fst)))).sub
      (hv.comp continuous_snd)).norm
  have hnear : ∀ᶠ r : ℝ in 𝓝 0, ∀ q : P × AddCircle T,
      ‖v q.1 (q.2 + (r : AddCircle T)) - v q.1 q.2‖ < m / 4 := by
    have hlocal : ∀ᶠ r : ℝ in 𝓝 0, ∀ q ∈ (univ : Set (P × AddCircle T)),
        ‖v q.1 (q.2 + (r : AddCircle T)) - v q.1 q.2‖ < m / 4 := by
      apply isCompact_univ.eventually_forall_of_forall_eventually
      intro q _
      apply hcont.continuousAt.eventually (gt_mem_nhds ?_)
      simpa only [AddCircle.coe_zero, add_zero, sub_self, norm_zero] using
        (div_pos hm (by norm_num : (0 : ℝ) < 4))
    filter_upwards [hlocal] with r hr q using hr q (mem_univ q)
  obtain ⟨δ, hδ, hmod⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨m / 4, div_pos hm (by norm_num), δ, hδ, ?_⟩
  intro p g hg hclose
  refine ⟨?_, ?_⟩
  · intro r hz
    have hh := hclose r
    rw [hz, (hderiv p r).deriv, zero_sub, norm_neg] at hh
    have hb := hbound (p, (r : AddCircle T)) (mem_univ _)
    linarith
  intro z w hzw heq
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective z
  have hnorm : ‖w - z‖ < δ := by simpa only [dist_eq_norm, norm_sub_rev] using hzw
  obtain ⟨d, hd, hsmall⟩ := QuotientAddGroup.norm_lt_iff.mp hnorm
  have hxd : ((x + d : ℝ) : AddCircle T) = w := by
    rw [AddCircle.coe_add, hx, hd]
    abel
  have heq' : g (x : AddCircle T) = g ((x + d : ℝ) : AddCircle T) := by
    simpa only [hx, hxd] using heq
  have hxy : x = x + d := by
    apply eq_of_deriv_close_of_eq
      (f := fun t : ℝ => g (t : AddCircle T))
      (d := deriv (fun t : ℝ => g (t : AddCircle T))) (v := v p z) (C := m / 2)
      (fun r _ => (hg r).hasDerivAt) ?_ ?_ heq'
    · intro r hr
      have hrsmall : ‖r - x‖ < δ :=
        (show ‖r - x‖ ≤ ‖d‖ by
          simpa only [Real.norm_eq_abs, add_sub_cancel_left] using
            abs_sub_left_of_mem_uIcc hr).trans_lt
          hsmall
      have hvariation := hmod (show r - x ∈ ball (0 : ℝ) δ by
        simpa only [mem_ball, dist_zero_right] using hrsmall) (p, z)
      have hrepr : z + ((r - x : ℝ) : AddCircle T) = (r : AddCircle T) := by
        rw [← hx, ← AddCircle.coe_add]
        congr 1
        abel
      rw [hrepr] at hvariation
      have hderivClose := hclose r
      rw [(hderiv p r).deriv] at hderivClose
      calc
        ‖deriv (fun t : ℝ => g (t : AddCircle T)) r - v p z‖ ≤
            ‖deriv (fun t : ℝ => g (t : AddCircle T)) r - v p (r : AddCircle T)‖ +
              ‖v p (r : AddCircle T) - v p z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ m / 2 := by linarith
    · have h := hbound (p, z) (mem_univ _)
      linarith
  simpa only [hx, hxd] using congrArg (fun t : ℝ => (t : AddCircle T)) hxy

theorem exists_uniform_injective_radius
    {c v : P → AddCircle T → F}
    (hv : Continuous (fun p : P × AddCircle T => v p.1 p.2))
    (hderiv : ∀ (p : P) (r : ℝ), HasDerivAt (fun t : ℝ => c p (t : AddCircle T))
      (v p (r : AddCircle T)) r)
    (hne : ∀ p z, v p z ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p z w, dist z w < δ → c p z = c p w → z = w := by
  obtain ⟨ε, hε, δ, hδ, hstable⟩ :=
    exists_uniform_injective_radius_of_deriv_close hv hderiv hne
  refine ⟨δ, hδ, fun p => ?_⟩
  exact (hstable p (c p) (fun r => (hderiv p r).differentiableAt)
    (fun _ => by simpa only [sub_self, norm_zero] using hε)).2

theorem isCompact_self_coincidences_of_hasDerivAt
    {c v : P → AddCircle T → F}
    (hc : Continuous (fun p : P × AddCircle T => c p.1 p.2))
    (hv : Continuous (fun p : P × AddCircle T => v p.1 p.2))
    (hderiv : ∀ (p : P) (r : ℝ), HasDerivAt (fun t : ℝ => c p (t : AddCircle T))
      (v p (r : AddCircle T)) r)
    (hne : ∀ p z, v p z ≠ 0) :
    IsCompact {q : P × (AddCircle T × AddCircle T) |
      q.2.1 ≠ q.2.2 ∧ c q.1 q.2.1 = c q.1 q.2.2} := by
  obtain ⟨δ, hδ, hsep⟩ := exists_uniform_injective_radius hv hderiv hne
  have hset : {q : P × (AddCircle T × AddCircle T) |
      q.2.1 ≠ q.2.2 ∧ c q.1 q.2.1 = c q.1 q.2.2} =
      {q : P × (AddCircle T × AddCircle T) |
      δ ≤ dist q.2.1 q.2.2 ∧ c q.1 q.2.1 = c q.1 q.2.2} := by
    ext q
    constructor
    · rintro ⟨hneq, heq⟩
      exact ⟨le_of_not_gt (fun hlt => hneq (hsep q.1 q.2.1 q.2.2 hlt heq)), heq⟩
    · rintro ⟨hgap, heq⟩
      refine ⟨?_, heq⟩
      intro hz
      rw [hz, dist_self] at hgap
      exact hδ.not_ge hgap
  rw [hset]
  exact ((isClosed_le continuous_const (continuous_snd.fst.dist continuous_snd.snd)).inter
    (isClosed_eq (hc.comp (continuous_fst.prodMk continuous_snd.fst))
      (hc.comp (continuous_fst.prodMk continuous_snd.snd)))).isCompact

end DifferentialGeometry.Calculus

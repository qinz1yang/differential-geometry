import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology

namespace DifferentialGeometry.Analysis.ODE

theorem le_gronwallBound_of_hasDerivAt_on_Ioo
    {u u' : ℝ → ℝ} {a b δ K ε : ℝ}
    (hcont : ContinuousOn u (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt u (u' t) t)
    (hinit : u a ≤ δ)
    (hsub : ∀ t ∈ Ioo a b, u' t ≤ K * u t + ε) :
    ∀ t ∈ Icc a b, u t ≤ gronwallBound δ K ε (t - a) := by
  let g (t : ℝ) := gronwallBound δ K ε (t - a)
  have hgd (t : ℝ) : HasDerivAt g (K * g t + ε) t :=
    hasDerivAt_gronwallBound_shift δ K ε t a
  let f (t : ℝ) := Real.exp (-K * t) * (u t - g t)
  have hc : ContinuousOn f (Icc a b) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
      (hcont.sub (fun t _ => (hgd t).continuousAt.continuousWithinAt))
  have hd (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt f (Real.exp (-K * t) * (u' t - K * u t - ε)) t := by
    convert (((hasDerivAt_id t).const_mul (-K)).exp.mul
      ((hderiv t ht).sub (hgd t))) using 1 <;>
      first | rfl | (simp only [id_eq, Pi.sub_apply, mul_one]; ring)
  have hm : AntitoneOn f (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b) hc
    · intro t ht
      exact (hd t (by simpa only [interior_Icc] using ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have hti : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
      rw [(hd t hti).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith [hsub t hti])
  intro t ht
  have hfa : f a ≤ 0 := by
    have hg : g a = δ := by simp only [g, sub_self, gronwallBound_x0]
    dsimp only [f]
    rw [hg]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr hinit)
  have hf := (hm ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1).trans hfa
  have hn : u t - g t ≤ 0 := nonpos_of_mul_nonpos_right hf (Real.exp_pos _)
  exact sub_nonpos.mp hn

theorem gronwall_zero_on {a c K : ℝ} (hac : a < c)
    (energy energy' : ℝ → ℝ)
    (hcont : ContinuousOn energy (Icc a c))
    (hzero : energy a = 0)
    (hnonneg : ∀ t ∈ Icc a c, 0 ≤ energy t)
    (hderiv : ∀ t ∈ Ioo a c, HasDerivAt energy (energy' t) t)
    (hbound : ∀ t ∈ Ioo a c, energy' t ≤ K * energy t) :
    ∀ t ∈ Icc a c, energy t = 0 := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with rfl | htpos
  · exact hzero
  have hlimc : Tendsto energy (nhdsWithin a (Ioo a c)) (𝓝 0) := by
    have hlim := (hcont a ⟨le_rfl, hac.le⟩).tendsto.mono_left
      (nhdsWithin_mono a Ioo_subset_Icc_self)
    simpa only [hzero] using hlim
  have hsub : Ioo a t ⊆ Ioo a c := fun s hs =>
    ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩
  have hlim : Tendsto energy (nhdsWithin a (Ioo a t)) (𝓝 0) :=
    hlimc.mono_left (nhdsWithin_mono a hsub)
  have : (nhdsWithin a (Ioo a t)).NeBot := by
    rw [nhdsWithin_Ioo_eq_nhdsGT htpos]
    infer_instance
  have heps : Tendsto (fun ε : ℝ => ε) (nhdsWithin a (Ioo a t)) (𝓝 a) :=
    (continuous_id.tendsto a).mono_left nhdsWithin_le_nhds
  have harg : Tendsto (fun ε : ℝ => K * (t - ε))
      (nhdsWithin a (Ioo a t)) (𝓝 (K * (t - a))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub heps)
  have hexp : Tendsto (fun ε : ℝ => Real.exp (K * (t - ε)))
      (nhdsWithin a (Ioo a t)) (𝓝 (Real.exp (K * (t - a)))) :=
    Real.continuous_exp.continuousAt.tendsto.comp harg
  have hrhs : Tendsto (fun ε : ℝ => energy ε * Real.exp (K * (t - ε)))
      (nhdsWithin a (Ioo a t)) (𝓝 0) := by
    simpa only [zero_mul] using hlim.mul hexp
  have hev : ∀ᶠ ε in nhdsWithin a (Ioo a t),
      energy t ≤ energy ε * Real.exp (K * (t - ε)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hcontε : ContinuousOn energy (Icc ε t) :=
      hcont.mono (Icc_subset_Icc hε.1.le ht.2)
    have hslope : ∀ x ∈ Ico ε t, ∀ r, energy' x < r →
        ∃ᶠ z in 𝓝[>] x, (z - x)⁻¹ * (energy z - energy x) < r := by
      intro x hx r hr
      have hxc : x ∈ Ioo a c :=
        ⟨lt_of_lt_of_le hε.1 hx.1, lt_of_lt_of_le hx.2 ht.2⟩
      exact (hderiv x hxc).hasDerivWithinAt.liminf_right_slope_le hr
    have hgr := le_gronwallBound_of_liminf_deriv_right_le
      (ε := 0) hcontε hslope le_rfl
      (fun x hx => by
        have hxc : x ∈ Ioo a c :=
          ⟨lt_of_lt_of_le hε.1 hx.1, lt_of_lt_of_le hx.2 ht.2⟩
        simpa only [add_zero] using hbound x hxc) t ⟨hε.2.le, le_rfl⟩
    simpa only [gronwallBound_ε0] using hgr
  exact le_antisymm (ge_of_tendsto hrhs hev) (hnonneg t ht)

end DifferentialGeometry.Analysis.ODE

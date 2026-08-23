import Mathlib.Analysis.ODE.Gronwall

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology

namespace DifferentialGeometry.Analysis.ODE

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
  haveI : (nhdsWithin a (Ioo a t)).NeBot := by
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

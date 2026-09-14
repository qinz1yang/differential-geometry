import DifferentialGeometry.Topology.Diffeomorph.TimeDependentFlow
import DifferentialGeometry.Analysis.Calculus.ProportionalTransport
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.LevelTransport

open scoped ContDiff Manifold Topology

namespace Diffeomorph

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem timeDependentFlow_mem_iff_of_eq_zero
    (V : ℝ × E → E) (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V)
    {W : Set E} (hz : ∀ t x, x ∉ W → V (t, x) = 0) (s t : ℝ) (x : E) :
    timeDependentFlow V hV hs s t x ∈ W ↔ x ∈ W := by
  have hfix : EqOn (timeDependentFlow V hV hs s t) id Wᶜ := by
    intro y hy
    exact timeDependentFlow_apply_eq_self_of_forall_eq_zero V hV hs
      (fun u => hz u y hy) s t
  have himage : timeDependentFlow V hV hs s t '' W = W := by
    apply compl_injective
    exact ((timeDependentFlow V hV hs s t).toEquiv.image_compl W).symm.trans
      hfix.image_eq_self
  exact (Set.ext_iff.mp
    (((timeDependentFlow V hV hs s t).toEquiv.eq_preimage_iff_image_eq W W).mpr
      himage) x).symm

theorem timeDependentFlow_symm_mem_iff_of_eq_zero
    (V : ℝ × E → E) (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V)
    {W : Set E} (hz : ∀ t x, x ∉ W → V (t, x) = 0) (s t : ℝ) (x : E) :
    (timeDependentFlow V hV hs s t).symm x ∈ W ↔ x ∈ W := by
  rw [timeDependentFlow_symm]
  exact timeDependentFlow_mem_iff_of_eq_zero V hV hs hz t s x

theorem timeDependentFlow_level_and_sublevels_iff_of_proportional_transport
    (V : ℝ × E → E) (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V)
    {W : Set E} (hz : ∀ t x, x ∉ W → V (t, x) = 0)
    {F κ : ℝ × E → ℝ} {Ω : Set (ℝ × E)} {a b r : ℝ}
    (hab : a ≤ b) (hΩ : IsOpen Ω) (hcover : Icc a b ×ˢ W ⊆ Ω)
    (hF : DifferentiableOn ℝ F Ω) (hκ : ContinuousOn κ Ω)
    (htransport : ∀ z ∈ Ω,
      deriv (fun u => F (u, z.2)) z.1 +
        fderiv ℝ (fun y => F (z.1, y)) z.2 (V z) = κ z * (F z - r))
    {x : E} (hx : x ∈ W) :
    (F (a, x) = r ↔ F (b, timeDependentFlow V hV hs a b x) = r) ∧
      (F (a, x) < r ↔ F (b, timeDependentFlow V hV hs a b x) < r) ∧
      (F (a, x) ≤ r ↔ F (b, timeDependentFlow V hV hs a b x) ≤ r) := by
  let γ : ℝ → E := fun t => timeDependentFlow V hV hs a t x
  have hγ : IsIntegralCurve γ (fun t y => V (t, y)) :=
    isIntegralCurve_timeDependentFlow V hV hs a x
  have hγW (t : ℝ) : γ t ∈ W :=
    (timeDependentFlow_mem_iff_of_eq_zero V hV hs hz a t x).mpr hx
  have hγcont : Continuous γ :=
    continuous_iff_continuousAt.mpr (fun t => (hγ t).continuousAt)
  have hpre : IsOpen ((fun t => (t, γ t)) ⁻¹' Ω) :=
    hΩ.preimage (continuous_id.prodMk hγcont)
  have hprecover : Icc a b ⊆ (fun t => (t, γ t)) ⁻¹' Ω :=
    fun t ht => hcover ⟨ht, hγW t⟩
  obtain ⟨c, v, ha, hac⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hpre.mem_nhds (hprecover ⟨le_rfl, hab⟩))
  obtain ⟨u, d, hb, hbd⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hpre.mem_nhds (hprecover ⟨hab, le_rfl⟩))
  have hstay (t : ℝ) (ht : t ∈ Ioo c d) : (t, γ t) ∈ Ω := by
    by_cases hta : t < a
    · exact hac ⟨ht.1, hta.trans ha.2⟩
    · by_cases hbt : b < t
      · exact hbd ⟨hb.1.trans hbt, ht.2⟩
      · exact hprecover ⟨le_of_not_gt hta, le_of_not_gt hbt⟩
  have ha' : a ∈ Ioo c d := ⟨ha.1, hab.trans_lt hb.2⟩
  have hb' : b ∈ Ioo c d := ⟨ha.1.trans_le hab, hb.2⟩
  have ht (t : ℝ) (ht : t ∈ Ioo c d) := htransport (t, γ t) (hstay t ht)
  have he := (hγ.isIntegralCurveOn (Ioo c d)).level_eq_iff_of_proportional_transport_Ioo
    hΩ hstay hF hκ ht ha' hb'
  have hl := (hγ.isIntegralCurveOn (Ioo c d)).sublevel_lt_iff_of_proportional_transport_Ioo
    hΩ hstay hF hκ ht ha' hb'
  have hw := (hγ.isIntegralCurveOn (Ioo c d)).sublevel_le_iff_of_proportional_transport_Ioo
    hΩ hstay hF hκ ht ha' hb'
  simpa only [γ, timeDependentFlow_refl, Diffeomorph.coe_refl, id_eq] using
    (And.intro he (And.intro hl hw))

theorem timeDependentFlow_symm_level_and_sublevels_iff_of_proportional_transport
    (V : ℝ × E → E) (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V)
    {W : Set E} (hz : ∀ t x, x ∉ W → V (t, x) = 0)
    {F κ : ℝ × E → ℝ} {Ω : Set (ℝ × E)} {a b r : ℝ}
    (hab : a ≤ b) (hΩ : IsOpen Ω) (hcover : Icc a b ×ˢ W ⊆ Ω)
    (hF : DifferentiableOn ℝ F Ω) (hκ : ContinuousOn κ Ω)
    (htransport : ∀ z ∈ Ω,
      deriv (fun u => F (u, z.2)) z.1 +
        fderiv ℝ (fun y => F (z.1, y)) z.2 (V z) = κ z * (F z - r))
    {x : E} (hx : x ∈ W) :
    (F (b, x) = r ↔ F (a, (timeDependentFlow V hV hs a b).symm x) = r) ∧
      (F (b, x) < r ↔ F (a, (timeDependentFlow V hV hs a b).symm x) < r) ∧
      (F (b, x) ≤ r ↔ F (a, (timeDependentFlow V hV hs a b).symm x) ≤ r) := by
  have hx' := (timeDependentFlow_symm_mem_iff_of_eq_zero V hV hs hz a b x).mpr hx
  obtain ⟨he, hl, hw⟩ := timeDependentFlow_level_and_sublevels_iff_of_proportional_transport V hV hs hz
    hab hΩ hcover hF hκ htransport hx'
  simpa only [Diffeomorph.apply_symm_apply] using
    (And.intro he.symm (And.intro hl.symm hw.symm))

theorem exists_diffeomorph_level_and_sublevels_of_proportional_interpolation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A B : E → ℝ} (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    {W J : Set E} (hW : IsOpen W) (hJ : IsCompact J) (hJW : J ⊆ W)
    (hregular : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ J,
      (1 - t) * A x + t * B x = 0 →
        fderiv ℝ (fun y => (1 - t) * A y + t * B y) x ≠ 0)
    (hprop : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ W,
      (1 - t) * A x + t * B x = 0 → x ∉ J →
        ∃ r : ℝ, 0 < r ∧ ∃ N : Set E, IsOpen N ∧ x ∈ N ∧ N ⊆ W ∧
          EqOn B (fun y => r * A y) N) :
    ∃ (K : Set E) (e : E ≃ₘ[ℝ] E),
      IsCompact K ∧ J ⊆ interior K ∧ K ⊆ W ∧
      EqOn e id Kᶜ ∧ EqOn e.symm id Kᶜ ∧
      (∀ x, e x ∈ W ↔ x ∈ W) ∧ (∀ x, e.symm x ∈ W ↔ x ∈ W) ∧
      (∀ x ∈ W, (A x = 0 ↔ B (e x) = 0) ∧
        (A x < 0 ↔ B (e x) < 0) ∧ (A x ≤ 0 ↔ B (e x) ≤ 0)) ∧
      ∀ x ∈ W, (B x = 0 ↔ A (e.symm x) = 0) ∧
        (B x < 0 ↔ A (e.symm x) < 0) ∧ (B x ≤ 0 ↔ A (e.symm x) ≤ 0) := by
  obtain ⟨K, V, Ω, κ, hK, hJK, hKW, hV, hs, hΩ, hcover, _, hκ, ht, hz⟩ :=
    DifferentialGeometry.Analysis.exists_contDiff_compactly_supported_proportional_vector_field
      hA hB hW hJ hJW hregular hprop
  let e := timeDependentFlow V hV hs 0 1
  let F : ℝ × E → ℝ := fun z => (1 - z.1) * A z.2 + z.1 * B z.2
  have hF : ContDiff ℝ ∞ F :=
    ((contDiff_const.sub contDiff_fst).mul (hA.comp contDiff_snd)).add
      (contDiff_fst.mul (hB.comp contDiff_snd))
  have hzero (t : ℝ) (x : E) (hx : x ∉ W) : V (t, x) = 0 :=
    hz t x (fun h => hx (hKW h))
  have htransport (z : ℝ × E) (hzΩ : z ∈ Ω) :
      deriv (fun u => F (u, z.2)) z.1 +
        fderiv ℝ (fun y => F (z.1, y)) z.2 (V z) = κ z * (F z - 0) := by
    simpa only [F, sub_zero] using ht z hzΩ
  refine ⟨K, e, hK, hJK, hKW, ?_, ?_,
    timeDependentFlow_mem_iff_of_eq_zero V hV hs hzero 0 1,
    timeDependentFlow_symm_mem_iff_of_eq_zero V hV hs hzero 0 1, ?_, ?_⟩
  · exact fun x hx => timeDependentFlow_apply_eq_self_of_forall_eq_zero V hV hs
      (fun u => hz u x hx) 0 1
  · intro x hx
    change (timeDependentFlow V hV hs 0 1).symm x = x
    rw [timeDependentFlow_symm]
    exact timeDependentFlow_apply_eq_self_of_forall_eq_zero V hV hs
      (fun u => hz u x hx) 1 0
  · intro x hx
    have h := timeDependentFlow_level_and_sublevels_iff_of_proportional_transport
      V hV hs hzero (a := 0) (b := 1) (r := 0) (by norm_num) hΩ hcover
      (hF.differentiable (by simp)).differentiableOn hκ.continuousOn htransport hx
    simpa only [F, e, sub_zero, sub_self, zero_mul, one_mul, add_zero, zero_add] using h
  · intro x hx
    have h := timeDependentFlow_symm_level_and_sublevels_iff_of_proportional_transport
      V hV hs hzero (a := 0) (b := 1) (r := 0) (by norm_num) hΩ hcover
      (hF.differentiable (by simp)).differentiableOn hκ.continuousOn htransport hx
    simpa only [F, e, sub_zero, sub_self, zero_mul, one_mul, add_zero, zero_add] using h

end Diffeomorph

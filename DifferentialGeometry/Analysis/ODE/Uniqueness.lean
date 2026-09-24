import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Extend

open Set

namespace DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem integralCurve_eqOn_Icc_of_locallyLipschitzOn
    {f : ℝ → E → E} {γ η : ℝ → E} {a b t₀ : ℝ}
    (hf : LocallyLipschitzOn (Icc a b ×ˢ (univ : Set E)) (Function.uncurry f))
    (hγ : IsIntegralCurveOn γ f (Icc a b)) (hη : IsIntegralCurveOn η f (Icc a b))
    (ht₀ : t₀ ∈ Icc a b) (hinit : γ t₀ = η t₀) : EqOn γ η (Icc a b) := by
  let S : Set (ℝ × E) := (fun t => (t, γ t)) '' Icc a b ∪
    (fun t => (t, η t)) '' Icc a b
  have hS : IsCompact S :=
    (isCompact_Icc.image_of_continuousOn (continuousOn_id.prodMk hγ.continuousOn)).union
      (isCompact_Icc.image_of_continuousOn (continuousOn_id.prodMk hη.continuousOn))
  have hsub : S ⊆ Icc a b ×ˢ (univ : Set E) := by
    rintro p (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) <;> exact ⟨ht, mem_univ _⟩
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hS (hf.mono hsub)
  let s : ℝ → Set E := fun t => {v | (t, v) ∈ S}
  have hLip (t : ℝ) : LipschitzOnWith K (f t) (s t) := by
    intro v hv w hw
    simpa only [Function.uncurry_apply_pair, Prod.edist_eq, edist_self, zero_max] using hK hv hw
  have hγmem (t : ℝ) (ht : t ∈ Icc a b) : γ t ∈ s t :=
    Or.inl ⟨t, ht, rfl⟩
  have hηmem (t : ℝ) (ht : t ∈ Icc a b) : η t ∈ s t :=
    Or.inr ⟨t, ht, rfl⟩
  rw [← Icc_union_Icc_eq_Icc ht₀.1 ht₀.2]
  refine EqOn.union ?_ ?_
  · have hI : Icc a t₀ ⊆ Icc a b := Icc_subset_Icc_right ht₀.2
    exact ODE_solution_unique_of_mem_Icc_left
      (fun t _ => hLip t) (hγ.continuousOn.mono hI)
      (fun t ht => (hγ t (hI (Ioc_subset_Icc_self ht))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem ⟨ht.1, ht.2.trans ht₀.2⟩))
      (fun t ht => hγmem t (hI (Ioc_subset_Icc_self ht))) (hη.continuousOn.mono hI)
      (fun t ht => (hη t (hI (Ioc_subset_Icc_self ht))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem ⟨ht.1, ht.2.trans ht₀.2⟩))
      (fun t ht => hηmem t (hI (Ioc_subset_Icc_self ht))) hinit
  · have hI : Icc t₀ b ⊆ Icc a b := Icc_subset_Icc_left ht₀.1
    exact ODE_solution_unique_of_mem_Icc_right
      (fun t _ => hLip t) (hγ.continuousOn.mono hI)
      (fun t ht => (hγ t (hI (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨ht₀.1.trans ht.1, ht.2⟩))
      (fun t ht => hγmem t (hI (Ico_subset_Icc_self ht))) (hη.continuousOn.mono hI)
      (fun t ht => (hη t (hI (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨ht₀.1.trans ht.1, ht.2⟩))
      (fun t ht => hηmem t (hI (Ico_subset_Icc_self ht))) hinit

theorem IsIntegralCurveOn.eqOn_of_locallyLipschitzOn
    {f : ℝ → E → E} {γ η : ℝ → E} {J : Set ℝ} {t₀ : ℝ}
    (hγ : IsIntegralCurveOn γ f J) (hη : IsIntegralCurveOn η f J)
    (hJ : J.OrdConnected) (hf : LocallyLipschitzOn (J ×ˢ (univ : Set E)) (Function.uncurry f))
    (ht₀ : t₀ ∈ J) (hinit : γ t₀ = η t₀) : EqOn γ η J := by
  intro t ht
  have hsub : uIcc t₀ t ⊆ J := hJ.uIcc_subset ht₀ ht
  exact integralCurve_eqOn_Icc_of_locallyLipschitzOn
    (hf.mono (prod_mono_left hsub)) (hγ.mono hsub) (hη.mono hsub)
    left_mem_uIcc hinit right_mem_uIcc

theorem IsIntegralCurveOn.eqOn_of_contDiffOn
    {f : ℝ → E → E} {γ η : ℝ → E} {J : Set ℝ} {t₀ : ℝ}
    (hγ : IsIntegralCurveOn γ f J) (hη : IsIntegralCurveOn η f J)
    (hJ : J.OrdConnected) (hf : ContDiffOn ℝ 1 (Function.uncurry f) (J ×ˢ (univ : Set E)))
    (ht₀ : t₀ ∈ J) (hinit : γ t₀ = η t₀) : EqOn γ η J :=
  IsIntegralCurveOn.eqOn_of_locallyLipschitzOn hγ hη hJ
    (hf.locallyLipschitzOn ((convex_iff_ordConnected.mpr hJ).prod convex_univ)) ht₀ hinit

end DifferentialGeometry.Analysis.ODE

section

open Filter
open scoped Topology

namespace DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_eqOn_Icc_of_hasDerivAt_of_contDiffAt
    {v : ℝ → E → E} {f g : ℝ → E} {a b : ℝ} (hab : a < b)
    (hv : ContDiffAt ℝ 1 (Function.uncurry v) (b, f b))
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (v t (f t)) t)
    (hg : ∀ t ∈ Ioo a b, HasDerivAt g (v t (g t)) t)
    (hfb : ContinuousWithinAt f (Iic b) b)
    (hgb : ContinuousWithinAt g (Iic b) b)
    (hfg : f b = g b) :
    ∃ c ∈ Ioo a b, EqOn f g (Icc c b) := by
  have hf_rhs : ContinuousWithinAt (fun t => v t (f t)) (Iic b) b :=
    hv.continuousAt.tendsto.comp (continuousWithinAt_id.prodMk hfb).tendsto
  have hg_rhs : ContinuousWithinAt (fun t => v t (g t)) (Iic b) b := by
    have hv' : ContinuousAt (Function.uncurry v) (b, g b) := by
      simpa only [hfg] using hv.continuousAt
    exact hv'.tendsto.comp (continuousWithinAt_id.prodMk hgb).tendsto
  have hfd : HasDerivWithinAt f (v b (f b)) (Iic b) b := by
    refine hasDerivWithinAt_Iic_of_tendsto_deriv (s := Ioo a b)
      (fun t ht => (hf t ht).differentiableAt.differentiableWithinAt)
      (hfb.mono (Ioo_subset_Iio_self.trans Iio_subset_Iic_self)) (Ioo_mem_nhdsLT hab) ?_
    exact (hf_rhs.mono Iio_subset_Iic_self).tendsto.congr'
      (Filter.eventuallyEq_of_mem (Ioo_mem_nhdsLT hab)
        fun t ht => (hf t ht).deriv).symm
  have hgd : HasDerivWithinAt g (v b (g b)) (Iic b) b := by
    refine hasDerivWithinAt_Iic_of_tendsto_deriv (s := Ioo a b)
      (fun t ht => (hg t ht).differentiableAt.differentiableWithinAt)
      (hgb.mono (Ioo_subset_Iio_self.trans Iio_subset_Iic_self)) (Ioo_mem_nhdsLT hab) ?_
    exact (hg_rhs.mono Iio_subset_Iic_self).tendsto.congr'
      (Filter.eventuallyEq_of_mem (Ioo_mem_nhdsLT hab)
        fun t ht => (hg t ht).deriv).symm
  obtain ⟨K, U, hU, hLip⟩ := hv.exists_lipschitzOnWith
  have hfgU : ∀ᶠ t in 𝓝[≤] b, (t, f t) ∈ U ∧ (t, g t) ∈ U := by
    apply Filter.Eventually.and
    · exact (continuousWithinAt_id.prodMk hfb).tendsto hU
    · apply (continuousWithinAt_id.prodMk hgb).tendsto
      simpa only [hfg, id_eq] using hU
  obtain ⟨c₀, hc₀, hc₀U⟩ := mem_nhdsLE_iff_exists_Icc_subset.mp hfgU
  let c := (max a c₀ + b) / 2
  have hm : max a c₀ < b := max_lt hab hc₀
  have hac : a < c := by dsimp [c]; linarith [le_max_left a c₀]
  have hc₀c : c₀ ≤ c := by dsimp [c]; linarith [le_max_right a c₀]
  have hcb : c < b := by dsimp [c]; linarith
  have hUsub : ∀ t ∈ Icc c b, (t, f t) ∈ U ∧ (t, g t) ∈ U :=
    fun t ht => hc₀U ⟨hc₀c.trans ht.1, ht.2⟩
  let s : ℝ → Set E := fun t => {z | (t, z) ∈ U}
  have hLip' (t : ℝ) : LipschitzOnWith K (v t) (s t) := by
    intro z hz w hw
    simpa only [Function.uncurry_apply_pair, Prod.edist_eq, edist_self, zero_max]
      using hLip hz hw
  have hfc : ContinuousOn f (Icc c b) := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with htb | rfl
    · exact (hf t ⟨hac.trans_le ht.1, htb⟩).continuousAt.continuousWithinAt
    · exact hfb.mono Icc_subset_Iic_self
  have hgc : ContinuousOn g (Icc c b) := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with htb | rfl
    · exact (hg t ⟨hac.trans_le ht.1, htb⟩).continuousAt.continuousWithinAt
    · exact hgb.mono Icc_subset_Iic_self
  have hfd' : ∀ t ∈ Ioc c b, HasDerivWithinAt f (v t (f t)) (Iic t) t := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with htb | rfl
    · exact (hf t ⟨hac.trans ht.1, htb⟩).hasDerivWithinAt
    · exact hfd
  have hgd' : ∀ t ∈ Ioc c b, HasDerivWithinAt g (v t (g t)) (Iic t) t := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with htb | rfl
    · exact (hg t ⟨hac.trans ht.1, htb⟩).hasDerivWithinAt
    · exact hgd
  refine ⟨c, ⟨hac, hcb⟩, ?_⟩
  exact ODE_solution_unique_of_mem_Icc_left (fun t _ => hLip' t) hfc hfd'
    (fun t ht => (hUsub t (Ioc_subset_Icc_self ht)).1) hgc hgd'
    (fun t ht => (hUsub t (Ioc_subset_Icc_self ht)).2) hfg

end DifferentialGeometry.Analysis.ODE

end

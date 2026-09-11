import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike

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

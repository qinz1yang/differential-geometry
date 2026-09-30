/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CutAndPaste

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

open Classical in
noncomputable def crossRegluedPullback (P' P : Set (EuclideanSpace ℝ (Fin 2)))
    (h f₁ f₂ f₃ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
  fun x => if x ∈ P' then (if h x ∈ P then f₁ (h x) else f₂ (h x)) else f₃ x

section Values

variable {P P' : Set (EuclideanSpace ℝ (Fin 2))}
  {h f₁ f₂ f₃ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
  {x : EuclideanSpace ℝ (Fin 2)}

open Classical in
theorem crossRegluedPullback_eq_left (hx : x ∈ P') (hhx : h x ∈ P) :
    crossRegluedPullback P' P h f₁ f₂ f₃ x = f₁ (h x) := by
  change (if x ∈ P' then (if h x ∈ P then f₁ (h x) else f₂ (h x)) else f₃ x) = f₁ (h x)
  rw [ite_eq_left hx, ite_eq_left hhx]

open Classical in
theorem crossRegluedPullback_eq_middle (hx : x ∈ P') (hhx : h x ∉ P) :
    crossRegluedPullback P' P h f₁ f₂ f₃ x = f₂ (h x) := by
  change (if x ∈ P' then (if h x ∈ P then f₁ (h x) else f₂ (h x)) else f₃ x) = f₂ (h x)
  rw [ite_eq_left hx, ite_eq_right hhx]

open Classical in
theorem crossRegluedPullback_eq_right (hx : x ∉ P') :
    crossRegluedPullback P' P h f₁ f₂ f₃ x = f₃ x := by
  change (if x ∈ P' then (if h x ∈ P then f₁ (h x) else f₂ (h x)) else f₃ x) = f₃ x
  rw [ite_eq_right hx]

end Values

theorem injOn_of_forall_exists_partner {X Y : Type*} (φ : X → Y) {R S : Set X} (hSR : S ⊆ R)
    (hfiber : ∀ y, (R ∩ φ ⁻¹' {y}).encard ≤ 2)
    (hpartner : ∀ v ∈ S, ∃ w ∈ R, w ∉ S ∧ φ w = φ v) : InjOn φ S := by
  classical
  intro v₁ h₁ v₂ h₂ hv
  by_contra hne
  obtain ⟨w, hwR, hwS, hwv⟩ := hpartner v₁ h₁
  have hfib := fiber_eq_pair_of_encard_le_two φ R (hSR h₁) (hSR h₂) hne rfl hv.symm
    (hfiber (φ v₁))
  have hwmem : w ∈ R ∩ φ ⁻¹' {φ v₁} := ⟨hwR, hwv⟩
  rw [hfib] at hwmem
  simp only [mem_insert_iff, mem_singleton_iff] at hwmem
  rcases hwmem with rfl | rfl
  · exact hwS h₁
  · exact hwS h₂

section CrossReglued

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D H G : SingularTwoCell M} {BdM B : Set M}
  {A C U₁ U₂ U₃ P Q P' Q' A' : Set (EuclideanSpace ℝ (Fin 2))}
  {g f₁ f₂ h f₃ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}

theorem apply_crossReglued_left (hH₁ : EqOn H (D ∘ f₁) P) (hGH : EqOn G (H ∘ h) P')
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ P') (hhx : h x ∈ P) :
    ⇑G x = ⇑D (f₁ (h x)) := by
  have h₁ : ⇑G x = ⇑H (h x) := hGH hx
  have h₂ : ⇑H (h x) = ⇑D (f₁ (h x)) := hH₁ hhx
  rw [h₁, h₂]

theorem apply_crossReglued_middle (hH₂ : EqOn H (D ∘ f₂) Q) (hGH : EqOn G (H ∘ h) P')
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ P') (hhx : h x ∈ Q) :
    ⇑G x = ⇑D (f₂ (h x)) := by
  have h₁ : ⇑G x = ⇑H (h x) := hGH hx
  have h₂ : ⇑H (h x) = ⇑D (f₂ (h x)) := hH₂ hhx
  rw [h₁, h₂]

theorem apply_crossReglued_right (hG₃ : EqOn G (D ∘ f₃) Q')
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ Q') : ⇑G x = ⇑D (f₃ x) := hG₃ hx

theorem mapsTo_crossRegluedPullback (hdomains : U₁ ∪ U₂ ∪ U₃ = D.domain)
    (hHdomain : H.domain = P ∪ Q) (hf₁ : IsPLHomeomorphOn f₁ P U₁)
    (hf₂ : IsPLHomeomorphOn f₂ Q U₂) (hGdomain : G.domain = P' ∪ Q')
    (hh : IsPLHomeomorphOn h P' H.domain) (hf₃ : IsPLHomeomorphOn f₃ Q' U₃) :
    MapsTo (crossRegluedPullback P' P h f₁ f₂ f₃) G.domain D.domain := by
  intro x hx
  rw [hGdomain] at hx
  by_cases hxP' : x ∈ P'
  · have hhx : h x ∈ P ∪ Q := by
      rw [← hHdomain]
      exact hh.bijOn.mapsTo hxP'
    by_cases hhxP : h x ∈ P
    · rw [crossRegluedPullback_eq_left hxP' hhxP, ← hdomains]
      exact Or.inl (Or.inl (hf₁.bijOn.mapsTo hhxP))
    · rw [crossRegluedPullback_eq_middle hxP' hhxP, ← hdomains]
      exact Or.inl (Or.inr (hf₂.bijOn.mapsTo (hhx.resolve_left hhxP)))
  · rw [crossRegluedPullback_eq_right hxP', ← hdomains]
    exact Or.inr (hf₃.bijOn.mapsTo (hx.resolve_left hxP'))

theorem map_crossRegluedPullback (hHdomain : H.domain = P ∪ Q) (hH₁ : EqOn H (D ∘ f₁) P)
    (hH₂ : EqOn H (D ∘ f₂) Q) (hGdomain : G.domain = P' ∪ Q')
    (hh : IsPLHomeomorphOn h P' H.domain) (hGH : EqOn G (H ∘ h) P')
    (hG₃ : EqOn G (D ∘ f₃) Q') :
    ∀ x ∈ G.domain, ⇑D (crossRegluedPullback P' P h f₁ f₂ f₃ x) = ⇑G x := by
  intro x hx
  rw [hGdomain] at hx
  by_cases hxP' : x ∈ P'
  · have hhx : h x ∈ P ∪ Q := by
      rw [← hHdomain]
      exact hh.bijOn.mapsTo hxP'
    by_cases hhxP : h x ∈ P
    · rw [crossRegluedPullback_eq_left hxP' hhxP]
      exact (apply_crossReglued_left hH₁ hGH hxP' hhxP).symm
    · rw [crossRegluedPullback_eq_middle hxP' hhxP]
      exact (apply_crossReglued_middle hH₂ hGH hxP' (hhx.resolve_left hhxP)).symm
  · rw [crossRegluedPullback_eq_right hxP']
    exact (apply_crossReglued_right hG₃ (hx.resolve_left hxP')).symm

theorem crossRegluedPullback_notMem_crosscut (hAC : Disjoint A C) (hinter₁₂ : U₁ ∩ U₂ = A)
    (hinter₂₃ : U₂ ∩ U₃ = C) (hHdomain : H.domain = P ∪ Q) (hf₁ : IsPLHomeomorphOn f₁ P U₁)
    (hf₂ : IsPLHomeomorphOn f₂ Q U₂) (hf₂seam : f₂ '' (P ∩ Q) = C)
    (hGdomain : G.domain = P' ∪ Q') (hh : IsPLHomeomorphOn h P' H.domain)
    (hf₃ : IsPLHomeomorphOn f₃ Q' U₃) (hf₃seam : f₃ '' (P' ∩ Q') = C) :
    ∀ x ∈ G.domain, crossRegluedPullback P' P h f₁ f₂ f₃ x ∉ C := by
  intro x hx
  have hCU₂ : C ⊆ U₂ := fun w hw => (hinter₂₃.symm.subset hw).1
  rw [hGdomain] at hx
  by_cases hxP' : x ∈ P'
  · have hhx : h x ∈ P ∪ Q := by
      rw [← hHdomain]
      exact hh.bijOn.mapsTo hxP'
    by_cases hhxP : h x ∈ P
    · rw [crossRegluedPullback_eq_left hxP' hhxP]
      intro hmem
      exact Set.disjoint_left.mp hAC
        (hinter₁₂.subset ⟨hf₁.bijOn.mapsTo hhxP, hCU₂ hmem⟩) hmem
    · rw [crossRegluedPullback_eq_middle hxP' hhxP]
      intro hmem
      have hhxQ : h x ∈ Q := hhx.resolve_left hhxP
      rw [← hf₂seam] at hmem
      exact hhxP ((hf₂.bijOn.injOn.mem_image_iff inter_subset_right hhxQ).mp hmem).1
  · rw [crossRegluedPullback_eq_right hxP']
    intro hmem
    have hxQ' : x ∈ Q' := hx.resolve_left hxP'
    rw [← hf₃seam] at hmem
    exact hxP' ((hf₃.bijOn.injOn.mem_image_iff inter_subset_right hxQ').mp hmem).1

theorem eq_of_crossRegluedPullback_eq_of_mem_iff (hinter₂₃ : U₂ ∩ U₃ = C)
    (hHdomain : H.domain = P ∪ Q) (hf₁ : IsPLHomeomorphOn f₁ P U₁)
    (hf₂ : IsPLHomeomorphOn f₂ Q U₂) (hf₂seam : f₂ '' (P ∩ Q) = C)
    (hGdomain : G.domain = P' ∪ Q') (hh : IsPLHomeomorphOn h P' H.domain)
    (hf₃ : IsPLHomeomorphOn f₃ Q' U₃) {x x' : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ G.domain) (hx' : x' ∈ G.domain)
    (hmode : (x ∈ P' ∧ h x ∈ P) ↔ (x' ∈ P' ∧ h x' ∈ P))
    (hk : crossRegluedPullback P' P h f₁ f₂ f₃ x =
      crossRegluedPullback P' P h f₁ f₂ f₃ x') : x = x' := by
  have hxu : x ∈ P' ∪ Q' := by rw [← hGdomain]; exact hx
  have hx'u : x' ∈ P' ∪ Q' := by rw [← hGdomain]; exact hx'
  have hsheet : ∀ {u : EuclideanSpace ℝ (Fin 2)}, u ∈ P' → h u ∉ P → h u ∈ Q := by
    intro u hu hhu
    have hmem : h u ∈ P ∪ Q := by
      rw [← hHdomain]
      exact hh.bijOn.mapsTo hu
    exact hmem.resolve_left hhu
  have key : ∀ u u' : EuclideanSpace ℝ (Fin 2), u ∈ P' → h u ∉ P → u' ∈ Q' → u' ∉ P' →
      crossRegluedPullback P' P h f₁ f₂ f₃ u ≠ crossRegluedPullback P' P h f₁ f₂ f₃ u' := by
    intro u u' huP' huhP hu'Q' hu'P' hcontra
    rw [crossRegluedPullback_eq_middle huP' huhP, crossRegluedPullback_eq_right hu'P'] at hcontra
    have huhQ : h u ∈ Q := hsheet huP' huhP
    have hmem : f₂ (h u) ∈ C := by
      rw [← hinter₂₃]
      refine ⟨hf₂.bijOn.mapsTo huhQ, ?_⟩
      rw [hcontra]
      exact hf₃.bijOn.mapsTo hu'Q'
    rw [← hf₂seam] at hmem
    exact huhP ((hf₂.bijOn.injOn.mem_image_iff inter_subset_right huhQ).mp hmem).1
  by_cases hxmode : x ∈ P' ∧ h x ∈ P
  · have hx'mode := hmode.mp hxmode
    rw [crossRegluedPullback_eq_left hxmode.1 hxmode.2,
      crossRegluedPullback_eq_left hx'mode.1 hx'mode.2] at hk
    exact hh.bijOn.injOn hxmode.1 hx'mode.1 (hf₁.bijOn.injOn hxmode.2 hx'mode.2 hk)
  · have hx'mode : ¬(x' ∈ P' ∧ h x' ∈ P) := fun hc => hxmode (hmode.mpr hc)
    by_cases hxP' : x ∈ P'
    · have hxhP : h x ∉ P := fun hc => hxmode ⟨hxP', hc⟩
      by_cases hx'P' : x' ∈ P'
      · have hx'hP : h x' ∉ P := fun hc => hx'mode ⟨hx'P', hc⟩
        rw [crossRegluedPullback_eq_middle hxP' hxhP,
          crossRegluedPullback_eq_middle hx'P' hx'hP] at hk
        exact hh.bijOn.injOn hxP' hx'P'
          (hf₂.bijOn.injOn (hsheet hxP' hxhP) (hsheet hx'P' hx'hP) hk)
      · exact absurd hk (key x x' hxP' hxhP (hx'u.resolve_left hx'P') hx'P')
    · by_cases hx'P' : x' ∈ P'
      · have hx'hP : h x' ∉ P := fun hc => hx'mode ⟨hx'P', hc⟩
        exact absurd hk.symm (key x' x hx'P' hx'hP (hxu.resolve_left hxP') hxP')
      · rw [crossRegluedPullback_eq_right hxP', crossRegluedPullback_eq_right hx'P'] at hk
        exact hf₃.bijOn.injOn (hxu.resolve_left hxP') (hx'u.resolve_left hx'P') hk

theorem eq_of_crossRegluedPullback_eq_of_notMem (hinter₁₂ : U₁ ∩ U₂ = A)
    (hinter₂₃ : U₂ ∩ U₃ = C) (hdisjoint₁₃ : Disjoint U₁ U₃) (hHdomain : H.domain = P ∪ Q)
    (hf₁ : IsPLHomeomorphOn f₁ P U₁) (hf₂ : IsPLHomeomorphOn f₂ Q U₂)
    (hf₂seam : f₂ '' (P ∩ Q) = C) (hGdomain : G.domain = P' ∪ Q')
    (hh : IsPLHomeomorphOn h P' H.domain) (hf₃ : IsPLHomeomorphOn f₃ Q' U₃)
    {x x' : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ G.domain) (hx' : x' ∈ G.domain)
    (hk : crossRegluedPullback P' P h f₁ f₂ f₃ x = crossRegluedPullback P' P h f₁ f₂ f₃ x')
    (hnot : crossRegluedPullback P' P h f₁ f₂ f₃ x ∉ A) : x = x' := by
  have hxu : x ∈ P' ∪ Q' := by rw [← hGdomain]; exact hx
  have hx'u : x' ∈ P' ∪ Q' := by rw [← hGdomain]; exact hx'
  have hmem₁ : ∀ {u : EuclideanSpace ℝ (Fin 2)}, u ∈ P' → h u ∈ P →
      crossRegluedPullback P' P h f₁ f₂ f₃ u ∈ U₁ := by
    intro u hu hhu
    rw [crossRegluedPullback_eq_left hu hhu]
    exact hf₁.bijOn.mapsTo hhu
  have hmem₂ : ∀ {u : EuclideanSpace ℝ (Fin 2)}, u ∈ P' ∪ Q' → ¬(u ∈ P' ∧ h u ∈ P) →
      crossRegluedPullback P' P h f₁ f₂ f₃ u ∈ U₂ ∪ U₃ := by
    intro u hu hnu
    by_cases huP' : u ∈ P'
    · have hhu : h u ∉ P := fun hc => hnu ⟨huP', hc⟩
      have hhuQ : h u ∈ Q := by
        have hmem : h u ∈ P ∪ Q := by
          rw [← hHdomain]
          exact hh.bijOn.mapsTo huP'
        exact hmem.resolve_left hhu
      rw [crossRegluedPullback_eq_middle huP' hhu]
      exact Or.inl (hf₂.bijOn.mapsTo hhuQ)
    · rw [crossRegluedPullback_eq_right huP']
      exact Or.inr (hf₃.bijOn.mapsTo (hu.resolve_left huP'))
  have hclash : ∀ {u v : EuclideanSpace ℝ (Fin 2)},
      crossRegluedPullback P' P h f₁ f₂ f₃ u ∈ U₁ →
      crossRegluedPullback P' P h f₁ f₂ f₃ v ∈ U₂ ∪ U₃ →
      crossRegluedPullback P' P h f₁ f₂ f₃ u = crossRegluedPullback P' P h f₁ f₂ f₃ v →
      crossRegluedPullback P' P h f₁ f₂ f₃ u ∈ A := by
    intro u v hu hv huv
    have hv' : crossRegluedPullback P' P h f₁ f₂ f₃ u ∈ U₂ ∪ U₃ := by
      rw [huv]
      exact hv
    rcases hv' with hv₂ | hv₃
    · exact hinter₁₂.subset ⟨hu, hv₂⟩
    · exact absurd hv₃ (Set.disjoint_left.mp hdisjoint₁₃ hu)
  have hmode : (x ∈ P' ∧ h x ∈ P) ↔ (x' ∈ P' ∧ h x' ∈ P) := by
    constructor
    · intro hxm
      by_contra hx'm
      exact hnot (hclash (hmem₁ hxm.1 hxm.2) (hmem₂ hx'u hx'm) hk)
    · intro hx'm
      by_contra hxm
      have hA' : crossRegluedPullback P' P h f₁ f₂ f₃ x' ∈ A :=
        hclash (hmem₁ hx'm.1 hx'm.2) (hmem₂ hxu hxm) hk.symm
      rw [hk] at hnot
      exact hnot hA'
  exact eq_of_crossRegluedPullback_eq_of_mem_iff hinter₂₃ hHdomain hf₁ hf₂ hf₂seam hGdomain
    hh hf₃ hx hx' hmode hk

theorem encard_crossRegluedPullback_fiber_le_two (hinter₂₃ : U₂ ∩ U₃ = C)
    (hHdomain : H.domain = P ∪ Q) (hf₁ : IsPLHomeomorphOn f₁ P U₁)
    (hf₂ : IsPLHomeomorphOn f₂ Q U₂) (hf₂seam : f₂ '' (P ∩ Q) = C)
    (hGdomain : G.domain = P' ∪ Q') (hh : IsPLHomeomorphOn h P' H.domain)
    (hf₃ : IsPLHomeomorphOn f₃ Q' U₃) (v : EuclideanSpace ℝ (Fin 2)) :
    (G.domain ∩ crossRegluedPullback P' P h f₁ f₂ f₃ ⁻¹' {v}).encard ≤ 2 := by
  classical
  have hone : ∀ T : Set (EuclideanSpace ℝ (Fin 2)),
      T ⊆ G.domain ∩ crossRegluedPullback P' P h f₁ f₂ f₃ ⁻¹' {v} →
      (∀ a ∈ T, ∀ b ∈ T, ((a ∈ P' ∧ h a ∈ P) ↔ (b ∈ P' ∧ h b ∈ P))) → T.encard ≤ 1 := by
    intro T hTF hT
    rw [Set.encard_le_one_iff]
    intro a b ha hb
    have hka : crossRegluedPullback P' P h f₁ f₂ f₃ a = v := (hTF ha).2
    have hkb : crossRegluedPullback P' P h f₁ f₂ f₃ b = v := (hTF hb).2
    exact eq_of_crossRegluedPullback_eq_of_mem_iff hinter₂₃ hHdomain hf₁ hf₂ hf₂seam
      hGdomain hh hf₃ (hTF ha).1 (hTF hb).1 (hT a ha b hb) (hka.trans hkb.symm)
  have hsplit : G.domain ∩ crossRegluedPullback P' P h f₁ f₂ f₃ ⁻¹' {v} ⊆
      ((G.domain ∩ crossRegluedPullback P' P h f₁ f₂ f₃ ⁻¹' {v}) ∩
          {u | u ∈ P' ∧ h u ∈ P}) ∪
        ((G.domain ∩ crossRegluedPullback P' P h f₁ f₂ f₃ ⁻¹' {v}) \
          {u | u ∈ P' ∧ h u ∈ P}) := by
    intro w hw
    by_cases hwS : w ∈ {u : EuclideanSpace ℝ (Fin 2) | u ∈ P' ∧ h u ∈ P}
    · exact Or.inl ⟨hw, hwS⟩
    · exact Or.inr ⟨hw, hwS⟩
  have h₁ : ((G.domain ∩ crossRegluedPullback P' P h f₁ f₂ f₃ ⁻¹' {v}) ∩
      {u | u ∈ P' ∧ h u ∈ P}).encard ≤ 1 :=
    hone _ inter_subset_left fun a ha b hb => iff_of_true ha.2 hb.2
  have h₂ : ((G.domain ∩ crossRegluedPullback P' P h f₁ f₂ f₃ ⁻¹' {v}) \
      {u | u ∈ P' ∧ h u ∈ P}).encard ≤ 1 :=
    hone _ Set.sdiff_subset fun a ha b hb => iff_of_false ha.2 hb.2
  calc (G.domain ∩ crossRegluedPullback P' P h f₁ f₂ f₃ ⁻¹' {v}).encard
      ≤ (((G.domain ∩ crossRegluedPullback P' P h f₁ f₂ f₃ ⁻¹' {v}) ∩
            {u | u ∈ P' ∧ h u ∈ P}) ∪
          ((G.domain ∩ crossRegluedPullback P' P h f₁ f₂ f₃ ⁻¹' {v}) \
            {u | u ∈ P' ∧ h u ∈ P})).encard := Set.encard_mono hsplit
    _ ≤ ((G.domain ∩ crossRegluedPullback P' P h f₁ f₂ f₃ ⁻¹' {v}) ∩
          {u | u ∈ P' ∧ h u ∈ P}).encard +
        ((G.domain ∩ crossRegluedPullback P' P h f₁ f₂ f₃ ⁻¹' {v}) \
          {u | u ∈ P' ∧ h u ∈ P}).encard := Set.encard_union_le _ _
    _ ≤ 1 + 1 := add_le_add h₁ h₂
    _ = 2 := by norm_num

theorem exists_mem_crossRegluedPullback_eq (hdomains : U₁ ∪ U₂ ∪ U₃ = D.domain)
    (hHdomain : H.domain = P ∪ Q) (hf₁ : IsPLHomeomorphOn f₁ P U₁)
    (hf₂ : IsPLHomeomorphOn f₂ Q U₂) (hf₂seam : f₂ '' (P ∩ Q) = C)
    (hGdomain : G.domain = P' ∪ Q') (hh : IsPLHomeomorphOn h P' H.domain)
    (hf₃ : IsPLHomeomorphOn f₃ Q' U₃) (hf₃seam : f₃ '' (P' ∩ Q') = C)
    {u : EuclideanSpace ℝ (Fin 2)} (hu : u ∈ D.domain) (huC : u ∉ C) :
    ∃ x ∈ G.domain, crossRegluedPullback P' P h f₁ f₂ f₃ x = u := by
  rw [← hdomains] at hu
  rcases hu with (hu₁ | hu₂) | hu₃
  · obtain ⟨w, hwP, hwu⟩ := hf₁.bijOn.surjOn hu₁
    have hwH : w ∈ H.domain := by
      rw [hHdomain]
      exact Or.inl hwP
    obtain ⟨x, hxP', hxw⟩ := hh.bijOn.surjOn hwH
    have hhxP : h x ∈ P := by rw [hxw]; exact hwP
    refine ⟨x, by rw [hGdomain]; exact Or.inl hxP', ?_⟩
    rw [crossRegluedPullback_eq_left hxP' hhxP, hxw, hwu]
  · obtain ⟨w, hwQ, hwu⟩ := hf₂.bijOn.surjOn hu₂
    have hwP : w ∉ P := by
      intro hwP
      apply huC
      rw [← hwu, ← hf₂seam]
      exact ⟨w, ⟨hwP, hwQ⟩, rfl⟩
    have hwH : w ∈ H.domain := by
      rw [hHdomain]
      exact Or.inr hwQ
    obtain ⟨x, hxP', hxw⟩ := hh.bijOn.surjOn hwH
    have hhxP : h x ∉ P := by rw [hxw]; exact hwP
    refine ⟨x, by rw [hGdomain]; exact Or.inl hxP', ?_⟩
    rw [crossRegluedPullback_eq_middle hxP' hhxP, hxw, hwu]
  · obtain ⟨x, hxQ', hxu⟩ := hf₃.bijOn.surjOn hu₃
    have hxP' : x ∉ P' := by
      intro hxP'
      apply huC
      rw [← hxu, ← hf₃seam]
      exact ⟨x, ⟨hxP', hxQ'⟩, rfl⟩
    refine ⟨x, by rw [hGdomain]; exact Or.inr hxQ', ?_⟩
    rw [crossRegluedPullback_eq_right hxP', hxu]

theorem NormalSingularCellData.exists_mem_nhdsWithin_injOn_of_eqOn_comp
    (hD : NormalSingularCellData D BdM B)
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {x : EuclideanSpace ℝ (Fin 2)} (hS : S ∈ 𝓝[G.domain] x) (hxS : x ∈ S)
    (hcont : ContinuousWithinAt φ S x) (hmaps : MapsTo φ S D.domain) (hinj : InjOn φ S)
    (heq : EqOn G (D ∘ φ) S) : ∃ V ∈ 𝓝[G.domain] x, InjOn (⇑G) V := by
  obtain ⟨U, hU, hinjU⟩ := hD.locallyInjective (φ x) (hmaps hxS)
  have hpre : φ ⁻¹' U ∈ 𝓝[S] x := hcont.tendsto_nhdsWithin hmaps hU
  refine ⟨S ∩ φ ⁻¹' U, mem_nhdsWithin_of_mem_nhdsWithin_of_mem_nhdsWithin
    (Filter.inter_mem self_mem_nhdsWithin hpre) hS, ?_⟩
  intro w hw z hz hwz
  apply hinj hw.1 hz.1
  apply hinjU hw.2 hz.2
  have h₁ : ⇑G w = ⇑D (φ w) := heq hw.1
  have h₂ : ⇑G z = ⇑D (φ z) := heq hz.1
  rw [← h₁, ← h₂, hwz]

theorem NormalSingularCellData.doublePointSet_crossReglued_eq
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    (hAC : Disjoint A C) (hcover : hD.branchPreimage c = A ∪ C)
    (hg : IsPLHomeomorphOn g A C) (hcompat : EqOn D (D ∘ g) A)
    (hdomains : U₁ ∪ U₂ ∪ U₃ = D.domain) (hinter₁₂ : U₁ ∩ U₂ = A)
    (hinter₂₃ : U₂ ∩ U₃ = C) (hdisjoint₁₃ : Disjoint U₁ U₃)
    (hHdomain : H.domain = P ∪ Q) (hf₁ : IsPLHomeomorphOn f₁ P U₁)
    (hf₂ : IsPLHomeomorphOn f₂ Q U₂) (hf₂seam : f₂ '' (P ∩ Q) = C)
    (hH₁ : EqOn H (D ∘ f₁) P) (hH₂ : EqOn H (D ∘ f₂) Q)
    (hGdomain : G.domain = P' ∪ Q') (hh : IsPLHomeomorphOn h P' H.domain)
    (hf₃ : IsPLHomeomorphOn f₃ Q' U₃) (hf₃seam : f₃ '' (P' ∩ Q') = C)
    (hGH : EqOn G (H ∘ h) P') (hG₃ : EqOn G (D ∘ f₃) Q')
    (hbranch : hD.singularSet.branchCarrier c ⊆ doublePointSet G G.domain) :
    doublePointSet G G.domain = doublePointSet D D.domain := by
  classical
  have hCU₂ : C ⊆ U₂ := fun w hw => (hinter₂₃.symm.subset hw).1
  have hU₂D : U₂ ⊆ D.domain := fun w hw => hdomains.subset (Or.inl (Or.inr hw))
  have hCD : C ⊆ D.domain := hCU₂.trans hU₂D
  have hmap := map_crossRegluedPullback hHdomain hH₁ hH₂ hGdomain hh hGH hG₃
  have hmem := mapsTo_crossRegluedPullback hdomains hHdomain hf₁ hf₂ hGdomain hh hf₃
  apply Subset.antisymm
  · rintro y ⟨x, hx, x', hx', hxx', hxy, hx'y⟩
    by_cases hk : crossRegluedPullback P' P h f₁ f₂ f₃ x =
        crossRegluedPullback P' P h f₁ f₂ f₃ x'
    · have hA' : crossRegluedPullback P' P h f₁ f₂ f₃ x ∈ A := by
        by_contra hnA
        exact hxx' (eq_of_crossRegluedPullback_eq_of_notMem hinter₁₂ hinter₂₃ hdisjoint₁₃
          hHdomain hf₁ hf₂ hf₂seam hGdomain hh hf₃ hx hx' hk hnA)
      have hgC : g (crossRegluedPullback P' P h f₁ f₂ f₃ x) ∈ C := hg.bijOn.mapsTo hA'
      have hcompatx : ⇑D (crossRegluedPullback P' P h f₁ f₂ f₃ x) =
          ⇑D (g (crossRegluedPullback P' P h f₁ f₂ f₃ x)) := hcompat hA'
      refine ⟨crossRegluedPullback P' P h f₁ f₂ f₃ x, hmem hx,
        g (crossRegluedPullback P' P h f₁ f₂ f₃ x), hCD hgC, ?_, (hmap x hx).trans hxy, ?_⟩
      · intro hcontra
        apply Set.disjoint_left.mp hAC hA'
        rw [hcontra]
        exact hgC
      · rw [← hcompatx]
        exact (hmap x hx).trans hxy
    · exact ⟨crossRegluedPullback P' P h f₁ f₂ f₃ x, hmem hx,
        crossRegluedPullback P' P h f₁ f₂ f₃ x', hmem hx', hk,
        (hmap x hx).trans hxy, (hmap x' hx').trans hx'y⟩
  · intro y hy
    by_cases hybranch : y ∈ hD.singularSet.branchCarrier c
    · exact hbranch hybranch
    · obtain ⟨u, hu, u', hu', huu', huy, hu'y⟩ := hy
      have hnotC : ∀ {w : EuclideanSpace ℝ (Fin 2)}, ⇑D w = y → w ∉ C := by
        intro w hwy hwC
        apply hybranch
        rw [← hwy]
        have hpre : w ∈ hD.branchPreimage c := by
          rw [hcover]
          exact Or.inr hwC
        exact hpre.2
      obtain ⟨x, hx, hxu⟩ := exists_mem_crossRegluedPullback_eq hdomains hHdomain hf₁ hf₂
        hf₂seam hGdomain hh hf₃ hf₃seam hu (hnotC huy)
      obtain ⟨x', hx', hx'u⟩ := exists_mem_crossRegluedPullback_eq hdomains hHdomain hf₁ hf₂
        hf₂seam hGdomain hh hf₃ hf₃seam hu' (hnotC hu'y)
      refine ⟨x, hx, x', hx', ?_, ?_, ?_⟩
      · intro hcontra
        apply huu'
        rw [← hxu, ← hx'u, hcontra]
      · rw [← hmap x hx, hxu, huy]
      · rw [← hmap x' hx', hx'u, hu'y]

theorem NormalSingularCellData.fiber_le_two_crossReglued
    (hD : NormalSingularCellData D BdM B)
    (hAC : Disjoint A C) (hg : IsPLHomeomorphOn g A C) (hcompat : EqOn D (D ∘ g) A)
    (hdomains : U₁ ∪ U₂ ∪ U₃ = D.domain) (hinter₁₂ : U₁ ∩ U₂ = A)
    (hinter₂₃ : U₂ ∩ U₃ = C) (hdisjoint₁₃ : Disjoint U₁ U₃)
    (hHdomain : H.domain = P ∪ Q) (hf₁ : IsPLHomeomorphOn f₁ P U₁)
    (hf₂ : IsPLHomeomorphOn f₂ Q U₂) (hf₂seam : f₂ '' (P ∩ Q) = C)
    (hH₁ : EqOn H (D ∘ f₁) P) (hH₂ : EqOn H (D ∘ f₂) Q)
    (hGdomain : G.domain = P' ∪ Q') (hh : IsPLHomeomorphOn h P' H.domain)
    (hf₃ : IsPLHomeomorphOn f₃ Q' U₃) (hf₃seam : f₃ '' (P' ∩ Q') = C)
    (hGH : EqOn G (H ∘ h) P') (hG₃ : EqOn G (D ∘ f₃) Q') :
    ∀ y, (G.domain ∩ ⇑G ⁻¹' {y}).encard ≤ 2 := by
  classical
  intro y
  have hCU₂ : C ⊆ U₂ := fun w hw => (hinter₂₃.symm.subset hw).1
  have hU₂D : U₂ ⊆ D.domain := fun w hw => hdomains.subset (Or.inl (Or.inr hw))
  have hCD : C ⊆ D.domain := hCU₂.trans hU₂D
  have hmap := map_crossRegluedPullback hHdomain hH₁ hH₂ hGdomain hh hGH hG₃
  have hmem := mapsTo_crossRegluedPullback hdomains hHdomain hf₁ hf₂ hGdomain hh hf₃
  have hnotC := crossRegluedPullback_notMem_crosscut hAC hinter₁₂ hinter₂₃ hHdomain hf₁ hf₂
    hf₂seam hGdomain hh hf₃ hf₃seam
  by_cases hcase : ∃ x ∈ G.domain ∩ ⇑G ⁻¹' {y}, crossRegluedPullback P' P h f₁ f₂ f₃ x ∈ A
  · obtain ⟨x₀, hx₀, hx₀A⟩ := hcase
    have hv : ⇑D (crossRegluedPullback P' P h f₁ f₂ f₃ x₀) = y := (hmap x₀ hx₀.1).trans hx₀.2
    have hgC : g (crossRegluedPullback P' P h f₁ f₂ f₃ x₀) ∈ C := hg.bijOn.mapsTo hx₀A
    have hgne : crossRegluedPullback P' P h f₁ f₂ f₃ x₀ ≠
        g (crossRegluedPullback P' P h f₁ f₂ f₃ x₀) := by
      intro hcontra
      apply Set.disjoint_left.mp hAC hx₀A
      rw [hcontra]
      exact hgC
    have hcompatx : ⇑D (crossRegluedPullback P' P h f₁ f₂ f₃ x₀) =
        ⇑D (g (crossRegluedPullback P' P h f₁ f₂ f₃ x₀)) := hcompat hx₀A
    have hgy : ⇑D (g (crossRegluedPullback P' P h f₁ f₂ f₃ x₀)) = y := by
      rw [← hcompatx]
      exact hv
    have hfib : D.domain ∩ ⇑D ⁻¹' {y} =
        {crossRegluedPullback P' P h f₁ f₂ f₃ x₀,
          g (crossRegluedPullback P' P h f₁ f₂ f₃ x₀)} :=
      fiber_eq_pair_of_encard_le_two (⇑D) D.domain (hmem hx₀.1) (hCD hgC) hgne hv hgy
        (hD.fiber_le_two y)
    have hsub : G.domain ∩ ⇑G ⁻¹' {y} ⊆ G.domain ∩
        crossRegluedPullback P' P h f₁ f₂ f₃ ⁻¹'
          {crossRegluedPullback P' P h f₁ f₂ f₃ x₀} := by
      intro w hw
      refine ⟨hw.1, ?_⟩
      have hwfib : crossRegluedPullback P' P h f₁ f₂ f₃ w ∈ D.domain ∩ ⇑D ⁻¹' {y} :=
        ⟨hmem hw.1, (hmap w hw.1).trans hw.2⟩
      rw [hfib] at hwfib
      simp only [mem_insert_iff, mem_singleton_iff] at hwfib
      rcases hwfib with hcase' | hcase'
      · exact hcase'
      · exfalso
        apply hnotC w hw.1
        rw [hcase']
        exact hgC
    exact le_trans (Set.encard_mono hsub) (encard_crossRegluedPullback_fiber_le_two hinter₂₃
      hHdomain hf₁ hf₂ hf₂seam hGdomain hh hf₃ _)
  · have hnotA : ∀ x ∈ G.domain ∩ ⇑G ⁻¹' {y},
        crossRegluedPullback P' P h f₁ f₂ f₃ x ∉ A := by
      intro w hw hwA
      exact hcase ⟨w, hw, hwA⟩
    have hinj : InjOn (crossRegluedPullback P' P h f₁ f₂ f₃) (G.domain ∩ ⇑G ⁻¹' {y}) := by
      intro a ha b hb hab
      exact eq_of_crossRegluedPullback_eq_of_notMem hinter₁₂ hinter₂₃ hdisjoint₁₃ hHdomain
        hf₁ hf₂ hf₂seam hGdomain hh hf₃ ha.1 hb.1 hab (hnotA a ha)
    calc (G.domain ∩ ⇑G ⁻¹' {y}).encard
        = (crossRegluedPullback P' P h f₁ f₂ f₃ '' (G.domain ∩ ⇑G ⁻¹' {y})).encard :=
          hinj.encard_image.symm
      _ ≤ (D.domain ∩ ⇑D ⁻¹' {y}).encard := Set.encard_le_encard (by
          rintro _ ⟨w, hw, rfl⟩
          exact ⟨hmem hw.1, (hmap w hw.1).trans hw.2⟩)
      _ ≤ 2 := hD.fiber_le_two y

theorem NormalSingularCellData.locallyInjective_crossReglued [T2Space M]
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    (hAC : Disjoint A C) (hcover : hD.branchPreimage c = A ∪ C)
    (hg : IsPLHomeomorphOn g A C) (hcompat : EqOn D (D ∘ g) A)
    (hdomains : U₁ ∪ U₂ ∪ U₃ = D.domain) (hinter₁₂ : U₁ ∩ U₂ = A)
    (hinter₂₃ : U₂ ∩ U₃ = C) (hdisjoint₁₃ : Disjoint U₁ U₃)
    (hP : IsPLBall 2 P) (hQ : IsPLBall 2 Q) (hHdomain : H.domain = P ∪ Q)
    (hf₁ : IsPLHomeomorphOn f₁ P U₁) (hf₂ : IsPLHomeomorphOn f₂ Q U₂)
    (hf₁seam : f₁ '' (P ∩ Q) = A) (hf₂seam : f₂ '' (P ∩ Q) = C)
    (hH₁ : EqOn H (D ∘ f₁) P) (hH₂ : EqOn H (D ∘ f₂) Q)
    (hA'def : A' = Function.invFunOn f₂ Q '' A) (hA'seam : Disjoint A' (P ∩ Q))
    (hP' : IsPLBall 2 P') (hQ' : IsPLBall 2 Q') (hGdomain : G.domain = P' ∪ Q')
    (hh : IsPLHomeomorphOn h P' H.domain) (hf₃ : IsPLHomeomorphOn f₃ Q' U₃)
    (hhseam : h '' (P' ∩ Q') = A') (hf₃seam : f₃ '' (P' ∩ Q') = C)
    (hGH : EqOn G (H ∘ h) P') (hG₃ : EqOn G (D ∘ f₃) Q') :
    ∀ x ∈ G.domain, ∃ V ∈ 𝓝[G.domain] x, InjOn (⇑G) V := by
  classical
  have hAU₁ : A ⊆ U₁ := fun w hw => (hinter₁₂.symm.subset hw).1
  have hAU₂ : A ⊆ U₂ := fun w hw => (hinter₁₂.symm.subset hw).2
  have hCU₂ : C ⊆ U₂ := fun w hw => (hinter₂₃.symm.subset hw).1
  have hU₁D : U₁ ⊆ D.domain := fun w hw => hdomains.subset (Or.inl (Or.inl hw))
  have hU₂D : U₂ ⊆ D.domain := fun w hw => hdomains.subset (Or.inl (Or.inr hw))
  have hU₃D : U₃ ⊆ D.domain := fun w hw => hdomains.subset (Or.inr hw)
  have hAD : A ⊆ D.domain := hAU₁.trans hU₁D
  have hCD : C ⊆ D.domain := hCU₂.trans hU₂D
  have hA'Q : A' ⊆ Q := by
    rw [hA'def]
    rintro _ ⟨v, hv, rfl⟩
    exact hf₂.bijOn.surjOn.mapsTo_invFunOn (hAU₂ hv)
  have hf₂A' : f₂ '' A' = A := by
    rw [hA'def, ← image_comp]
    calc (f₂ ∘ Function.invFunOn f₂ Q) '' A = id '' A :=
          Set.image_congr fun v hv => hf₂.bijOn.invOn_invFunOn.2 (hAU₂ hv)
      _ = A := image_id A
  have hAiff : ∀ {w : EuclideanSpace ℝ (Fin 2)}, w ∈ P → (f₁ w ∈ A ↔ w ∈ P ∩ Q) := by
    intro w hw
    rw [← hf₁seam]
    exact hf₁.bijOn.injOn.mem_image_iff inter_subset_left hw
  have hCiff : ∀ {w : EuclideanSpace ℝ (Fin 2)}, w ∈ Q → (f₂ w ∈ C ↔ w ∈ P ∩ Q) := by
    intro w hw
    rw [← hf₂seam]
    exact hf₂.bijOn.injOn.mem_image_iff inter_subset_right hw
  have hA'iff : ∀ {w : EuclideanSpace ℝ (Fin 2)}, w ∈ Q → (f₂ w ∈ A ↔ w ∈ A') := by
    intro w hw
    rw [← hf₂A']
    exact hf₂.bijOn.injOn.mem_image_iff hA'Q hw
  have hC₃iff : ∀ {w : EuclideanSpace ℝ (Fin 2)}, w ∈ Q' → (f₃ w ∈ C ↔ w ∈ P' ∩ Q') := by
    intro w hw
    rw [← hf₃seam]
    exact hf₃.bijOn.injOn.mem_image_iff inter_subset_right hw
  have hhiff : ∀ {w : EuclideanSpace ℝ (Fin 2)}, w ∈ P' → (h w ∈ A' ↔ w ∈ P' ∩ Q') := by
    intro w hw
    rw [← hhseam]
    exact hh.bijOn.injOn.mem_image_iff inter_subset_left hw
  have hsheet : ∀ {w : EuclideanSpace ℝ (Fin 2)}, w ∈ P' → h w ∈ P ∪ Q := by
    intro w hw
    rw [← hHdomain]
    exact hh.bijOn.mapsTo hw
  have hDinjA : InjOn (⇑D) A :=
    injOn_of_forall_exists_partner (⇑D) hAD hD.fiber_le_two fun v hv =>
      ⟨g v, hCD (hg.bijOn.mapsTo hv),
        fun hcon => Set.disjoint_left.mp hAC hcon (hg.bijOn.mapsTo hv), (hcompat hv).symm⟩
  have hDinjC : InjOn (⇑D) C := by
    refine injOn_of_forall_exists_partner (⇑D) hCD hD.fiber_le_two ?_
    intro w hw
    obtain ⟨v, hvA, hvw⟩ := hg.bijOn.surjOn hw
    refine ⟨v, hAD hvA, fun hcon => Set.disjoint_left.mp hAC hvA hcon, ?_⟩
    have hcv : ⇑D v = ⇑D (g v) := hcompat hvA
    rw [hcv, hvw]
  have hGleft : ∀ {w : EuclideanSpace ℝ (Fin 2)}, w ∈ P' → h w ∈ P → ⇑G w = ⇑D (f₁ (h w)) :=
    fun hw hhw => apply_crossReglued_left hH₁ hGH hw hhw
  have hGmid : ∀ {w : EuclideanSpace ℝ (Fin 2)}, w ∈ P' → h w ∈ Q → ⇑G w = ⇑D (f₂ (h w)) :=
    fun hw hhw => apply_crossReglued_middle hH₂ hGH hw hhw
  have hGright : ∀ {w : EuclideanSpace ℝ (Fin 2)}, w ∈ Q' → ⇑G w = ⇑D (f₃ w) :=
    fun hw => apply_crossReglued_right hG₃ hw
  have hbranchOf : ∀ {w : EuclideanSpace ℝ (Fin 2)}, w ∈ A →
      ⇑D w ∈ hD.singularSet.branchCarrier c := by
    intro w hw
    have hpre : w ∈ hD.branchPreimage c := by
      rw [hcover]
      exact Or.inl hw
    exact hpre.2
  have hpreA : ∀ {w : EuclideanSpace ℝ (Fin 2)}, w ∈ D.domain →
      ⇑D w ∈ hD.singularSet.branchCarrier c → w ∈ A ∪ C := by
    intro w hw hwb
    rw [← hcover]
    exact ⟨hw, hwb⟩
  let _ : Finite hD.singularSet.complex.faces := hD.singularSet.finite_faces.to_subtype
  let _ : Finite hD.singularSet.complex.vertices :=
    (SimplicialComplex.finite_vertices hD.singularSet.complex).to_subtype
  let _ : Finite hD.singularSet.Branch := inferInstance
  let otherBranches : Set M :=
    ⋃ d : {d : hD.singularSet.Branch // d ≠ c}, hD.singularSet.branchCarrier d.1
  have hotherCompact : IsCompact otherBranches :=
    isCompact_iUnion fun d => hD.singularSet.branchCarrier_isCompact d.1
  have hselectedOther : Disjoint (hD.singularSet.branchCarrier c) otherBranches := by
    apply Set.disjoint_left.mpr
    intro z hzc hzo
    obtain ⟨d, hzd⟩ := mem_iUnion.mp hzo
    exact Set.disjoint_left.mp
      (hD.singularSet.pairwise_disjoint_branchCarrier d.2.symm) hzc hzd
  have hselected : ∀ {z : M}, z ∈ doublePointSet D D.domain → z ∉ otherBranches →
      z ∈ hD.singularSet.branchCarrier c := by
    intro z hz hzo
    have hzunion : z ∈ ⋃ d : hD.singularSet.Branch, hD.singularSet.branchCarrier d := by
      rw [hD.singularSet.iUnion_branchCarrier]
      exact hz
    obtain ⟨d, hzd⟩ := mem_iUnion.mp hzunion
    by_cases hdc : d = c
    · simpa only [hdc] using hzd
    · exact (hzo (mem_iUnion.mpr ⟨⟨d, hdc⟩, hzd⟩)).elim
  intro x hx
  have hxu : x ∈ P' ∪ Q' := by
    rw [← hGdomain]
    exact hx
  by_cases hxP' : x ∈ P'
  · by_cases hxQ' : x ∈ Q'
    · have hhxA' : h x ∈ A' := (hhiff hxP').mpr ⟨hxP', hxQ'⟩
      have hhxQ : h x ∈ Q := hA'Q hhxA'
      have hhxP : h x ∉ P := fun hcon =>
        Set.disjoint_left.mp hA'seam hhxA' ⟨hcon, hhxQ⟩
      have hfxA : f₂ (h x) ∈ A := (hA'iff hhxQ).mpr hhxA'
      have hGxb : ⇑G x ∈ hD.singularSet.branchCarrier c := by
        rw [hGmid hxP' hhxQ]
        exact hbranchOf hfxA
      have hGxo : ⇑G x ∉ otherBranches := Set.disjoint_left.mp hselectedOther hGxb
      obtain ⟨UA, hUA, hinjA⟩ := hD.locallyInjective (f₂ (h x)) (hU₂D (hf₂.bijOn.mapsTo hhxQ))
      obtain ⟨UC, hUC, hinjC⟩ := hD.locallyInjective (f₃ x) (hU₃D (hf₃.bijOn.mapsTo hxQ'))
      have hGother : ⇑G ⁻¹' (otherBranchesᶜ) ∈ 𝓝[G.domain] x :=
        (G.continuousOn x hx).preimage_mem_nhdsWithin
          (hotherCompact.isClosed.isOpen_compl.mem_nhds hGxo)
      have hT : P' ∩ h ⁻¹' (Pᶜ : Set (EuclideanSpace ℝ (Fin 2))) ∈ 𝓝[P'] x :=
        Filter.inter_mem self_mem_nhdsWithin
          ((hh.isPiecewiseAffineOn.continuousOn x hxP').preimage_mem_nhdsWithin
            (hP.isPolyhedron.isClosed.isOpen_compl.mem_nhds hhxP))
      have hmapsT : MapsTo (f₂ ∘ h) (P' ∩ h ⁻¹' (Pᶜ : Set (EuclideanSpace ℝ (Fin 2))))
          D.domain := fun w hw => hU₂D (hf₂.bijOn.mapsTo ((hsheet hw.1).resolve_left hw.2))
      have hcontT : ContinuousWithinAt (f₂ ∘ h)
          (P' ∩ h ⁻¹' (Pᶜ : Set (EuclideanSpace ℝ (Fin 2)))) x :=
        (hf₂.isPiecewiseAffineOn.continuousOn.comp
          (hh.isPiecewiseAffineOn.continuousOn.mono inter_subset_left)
          (fun w hw => (hsheet hw.1).resolve_left hw.2)) x ⟨hxP', hhxP⟩
      have hW₁ : (P' ∩ h ⁻¹' (Pᶜ : Set (EuclideanSpace ℝ (Fin 2)))) ∩ (f₂ ∘ h) ⁻¹' UA ∩
          ⇑G ⁻¹' otherBranchesᶜ ∈ 𝓝[P'] x := by
        refine Filter.inter_mem ?_ (nhdsWithin_mono x
          (fun w hw => hGdomain.symm.subset (Or.inl hw)) hGother)
        exact mem_nhdsWithin_of_mem_nhdsWithin_of_mem_nhdsWithin
          (Filter.inter_mem self_mem_nhdsWithin (hcontT.tendsto_nhdsWithin hmapsT hUA)) hT
      have hW₂ : Q' ∩ f₃ ⁻¹' UC ∩ ⇑G ⁻¹' otherBranchesᶜ ∈ 𝓝[Q'] x := by
        refine Filter.inter_mem (Filter.inter_mem self_mem_nhdsWithin ?_)
          (nhdsWithin_mono x (fun w hw => hGdomain.symm.subset (Or.inr hw)) hGother)
        exact (hf₃.isPiecewiseAffineOn.continuousOn x hxQ').tendsto_nhdsWithin
          (fun w hw => hU₃D (hf₃.bijOn.mapsTo hw)) hUC
      have hcross : ∀ u v : EuclideanSpace ℝ (Fin 2), u ∈ P' → h u ∉ P →
          ⇑G u ∉ otherBranches → v ∈ Q' → ⇑G u = ⇑G v → u = v := by
        intro u v huP' huhP huother hvQ' huv
        have huhQ : h u ∈ Q := (hsheet huP').resolve_left huhP
        by_cases hsame : f₂ (h u) = f₃ v
        · exfalso
          have hmemC : f₂ (h u) ∈ C := by
            rw [← hinter₂₃]
            refine ⟨hf₂.bijOn.mapsTo huhQ, ?_⟩
            rw [hsame]
            exact hf₃.bijOn.mapsTo hvQ'
          exact huhP ((hCiff huhQ).mp hmemC).1
        · have hdbl : ⇑G u ∈ doublePointSet D D.domain :=
            ⟨f₂ (h u), hU₂D (hf₂.bijOn.mapsTo huhQ), f₃ v, hU₃D (hf₃.bijOn.mapsTo hvQ'),
              hsame, (hGmid huP' huhQ).symm, (hGright hvQ').symm.trans huv.symm⟩
          have hbr : ⇑G u ∈ hD.singularSet.branchCarrier c := hselected hdbl huother
          have huAC : f₂ (h u) ∈ A ∪ C := by
            refine hpreA (hU₂D (hf₂.bijOn.mapsTo huhQ)) ?_
            rw [← hGmid huP' huhQ]
            exact hbr
          have hvAC : f₃ v ∈ A ∪ C := by
            refine hpreA (hU₃D (hf₃.bijOn.mapsTo hvQ')) ?_
            rw [← hGright hvQ', ← huv]
            exact hbr
          have huA : f₂ (h u) ∈ A := by
            rcases huAC with hl | hr
            · exact hl
            · exact absurd ((hCiff huhQ).mp hr).1 huhP
          have hvC : f₃ v ∈ C := by
            rcases hvAC with hl | hr
            · exact absurd (hf₃.bijOn.mapsTo hvQ')
                (Set.disjoint_left.mp hdisjoint₁₃ (hAU₁ hl))
            · exact hr
          have huseam : u ∈ P' ∩ Q' := (hhiff huP').mp ((hA'iff huhQ).mp huA)
          refine hf₃.bijOn.injOn huseam.2 hvQ'
            (hDinjC ((hC₃iff huseam.2).mpr huseam) hvC ?_)
          exact ((hGright huseam.2).symm.trans huv).trans (hGright hvQ')
      refine ⟨((P' ∩ h ⁻¹' (Pᶜ : Set (EuclideanSpace ℝ (Fin 2)))) ∩ (f₂ ∘ h) ⁻¹' UA ∩
        ⇑G ⁻¹' otherBranchesᶜ) ∪ (Q' ∩ f₃ ⁻¹' UC ∩ ⇑G ⁻¹' otherBranchesᶜ), ?_, ?_⟩
      · rw [hGdomain, nhdsWithin_union]
        exact ⟨Filter.mem_of_superset hW₁ subset_union_left,
          Filter.mem_of_superset hW₂ subset_union_right⟩
      · rintro u (hu | hu) v (hv | hv) huv
        · have huhQ : h u ∈ Q := (hsheet hu.1.1.1).resolve_left hu.1.1.2
          have hvhQ : h v ∈ Q := (hsheet hv.1.1.1).resolve_left hv.1.1.2
          exact hh.bijOn.injOn hu.1.1.1 hv.1.1.1
            (hf₂.bijOn.injOn huhQ hvhQ
              (hinjA hu.1.2 hv.1.2
                (((hGmid hu.1.1.1 huhQ).symm.trans huv).trans (hGmid hv.1.1.1 hvhQ))))
        · exact hcross u v hu.1.1.1 hu.1.1.2 hu.2 hv.1.1 huv
        · exact (hcross v u hv.1.1.1 hv.1.1.2 hv.2 hu.1.1 huv.symm).symm
        · exact hf₃.bijOn.injOn hu.1.1 hv.1.1
            (hinjC hu.1.2 hv.1.2
              (((hGright hu.1.1).symm.trans huv).trans (hGright hv.1.1)))
    · have hempty : (∅ : Set (EuclideanSpace ℝ (Fin 2))) ∈ 𝓝[Q'] x := by
        apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
        exact ⟨Q'ᶜ, hQ'.isPolyhedron.isClosed.isOpen_compl.mem_nhds hxQ', by simp⟩
      by_cases hhxP : h x ∈ P
      · by_cases hhxQ : h x ∈ Q
        · have hfxA : f₁ (h x) ∈ A := (hAiff hhxP).mpr ⟨hhxP, hhxQ⟩
          have hGxb : ⇑G x ∈ hD.singularSet.branchCarrier c := by
            rw [hGleft hxP' hhxP]
            exact hbranchOf hfxA
          have hGxo : ⇑G x ∉ otherBranches := Set.disjoint_left.mp hselectedOther hGxb
          obtain ⟨UA, hUA, hinjA⟩ :=
            hD.locallyInjective (f₁ (h x)) (hU₁D (hf₁.bijOn.mapsTo hhxP))
          obtain ⟨UC, hUC, hinjC⟩ :=
            hD.locallyInjective (f₂ (h x)) (hU₂D (hf₂.bijOn.mapsTo hhxQ))
          have hGother : ⇑G ⁻¹' (otherBranchesᶜ) ∈ 𝓝[G.domain] x :=
            (G.continuousOn x hx).preimage_mem_nhdsWithin
              (hotherCompact.isClosed.isOpen_compl.mem_nhds hGxo)
          have hQ'nhds : (Q'ᶜ : Set (EuclideanSpace ℝ (Fin 2))) ∈ 𝓝 x :=
            hQ'.isPolyhedron.isClosed.isOpen_compl.mem_nhds hxQ'
          have hcontP : ContinuousWithinAt (f₁ ∘ h) (P' ∩ h ⁻¹' P) x :=
            (hf₁.isPiecewiseAffineOn.continuousOn.comp
              (hh.isPiecewiseAffineOn.continuousOn.mono inter_subset_left)
              (fun w hw => hw.2)) x ⟨hxP', hhxP⟩
          have hcontQ : ContinuousWithinAt (f₂ ∘ h) (P' ∩ h ⁻¹' Q) x :=
            (hf₂.isPiecewiseAffineOn.continuousOn.comp
              (hh.isPiecewiseAffineOn.continuousOn.mono inter_subset_left)
              (fun w hw => hw.2)) x ⟨hxP', hhxQ⟩
          have hW₁ : (P' ∩ h ⁻¹' P) ∩ (f₁ ∘ h) ⁻¹' UA ∩ ⇑G ⁻¹' otherBranchesᶜ ∩ Q'ᶜ ∈
              𝓝[P' ∩ h ⁻¹' P] x :=
            Filter.inter_mem (Filter.inter_mem (Filter.inter_mem self_mem_nhdsWithin
              (hcontP.tendsto_nhdsWithin
                (fun w hw => hU₁D (hf₁.bijOn.mapsTo hw.2)) hUA))
              (nhdsWithin_mono x (fun w hw => hGdomain.symm.subset (Or.inl hw.1)) hGother))
              (mem_nhdsWithin_of_mem_nhds hQ'nhds)
          have hW₂ : (P' ∩ h ⁻¹' Q) ∩ (f₂ ∘ h) ⁻¹' UC ∩ ⇑G ⁻¹' otherBranchesᶜ ∩ Q'ᶜ ∈
              𝓝[P' ∩ h ⁻¹' Q] x :=
            Filter.inter_mem (Filter.inter_mem (Filter.inter_mem self_mem_nhdsWithin
              (hcontQ.tendsto_nhdsWithin
                (fun w hw => hU₂D (hf₂.bijOn.mapsTo hw.2)) hUC))
              (nhdsWithin_mono x (fun w hw => hGdomain.symm.subset (Or.inl hw.1)) hGother))
              (mem_nhdsWithin_of_mem_nhds hQ'nhds)
          have hP'split : P' = (P' ∩ h ⁻¹' P) ∪ (P' ∩ h ⁻¹' Q) := by
            ext w
            constructor
            · intro hw
              rcases hsheet hw with hl | hr
              · exact Or.inl ⟨hw, hl⟩
              · exact Or.inr ⟨hw, hr⟩
            · rintro (⟨hw, -⟩ | ⟨hw, -⟩) <;> exact hw
          have hsplitP : 𝓝[P'] x = 𝓝[P' ∩ h ⁻¹' P] x ⊔ 𝓝[P' ∩ h ⁻¹' Q] x := by
            rw [← nhdsWithin_union, ← hP'split]
          have hcross : ∀ u v : EuclideanSpace ℝ (Fin 2), u ∈ P' → h u ∈ P → u ∉ Q' →
              ⇑G u ∉ otherBranches → v ∈ P' → h v ∈ Q → v ∉ Q' → ⇑G u = ⇑G v → u = v := by
            intro u v huP' huhP huQ' huother hvP' hvhQ hvQ' huv
            by_cases hsame : f₁ (h u) = f₂ (h v)
            · exfalso
              have hmemA : f₂ (h v) ∈ A := by
                rw [← hinter₁₂]
                refine ⟨?_, hf₂.bijOn.mapsTo hvhQ⟩
                rw [← hsame]
                exact hf₁.bijOn.mapsTo huhP
              exact hvQ' ((hhiff hvP').mp ((hA'iff hvhQ).mp hmemA)).2
            · have hdbl : ⇑G u ∈ doublePointSet D D.domain :=
                ⟨f₁ (h u), hU₁D (hf₁.bijOn.mapsTo huhP), f₂ (h v),
                  hU₂D (hf₂.bijOn.mapsTo hvhQ), hsame, (hGleft huP' huhP).symm,
                  (hGmid hvP' hvhQ).symm.trans huv.symm⟩
              have hbr : ⇑G u ∈ hD.singularSet.branchCarrier c := hselected hdbl huother
              have huAC : f₁ (h u) ∈ A ∪ C := by
                refine hpreA (hU₁D (hf₁.bijOn.mapsTo huhP)) ?_
                rw [← hGleft huP' huhP]
                exact hbr
              have hvAC : f₂ (h v) ∈ A ∪ C := by
                refine hpreA (hU₂D (hf₂.bijOn.mapsTo hvhQ)) ?_
                rw [← hGmid hvP' hvhQ, ← huv]
                exact hbr
              have huA : f₁ (h u) ∈ A := by
                rcases huAC with hl | hr
                · exact hl
                · exact absurd hr (Set.disjoint_left.mp hAC
                    (hinter₁₂.subset ⟨hf₁.bijOn.mapsTo huhP, hCU₂ hr⟩))
              have hvC : f₂ (h v) ∈ C := by
                rcases hvAC with hl | hr
                · exact absurd ((hhiff hvP').mp ((hA'iff hvhQ).mp hl)).2 hvQ'
                · exact hr
              have hvhP : h v ∈ P := ((hCiff hvhQ).mp hvC).1
              have hvA : f₁ (h v) ∈ A := (hAiff hvhP).mpr ⟨hvhP, hvhQ⟩
              refine hh.bijOn.injOn huP' hvP' (hf₁.bijOn.injOn huhP hvhP ?_)
              refine hDinjA huA hvA ?_
              exact ((hGleft huP' huhP).symm.trans huv).trans (hGleft hvP' hvhP)
          refine ⟨((P' ∩ h ⁻¹' P) ∩ (f₁ ∘ h) ⁻¹' UA ∩ ⇑G ⁻¹' otherBranchesᶜ ∩ Q'ᶜ) ∪
            ((P' ∩ h ⁻¹' Q) ∩ (f₂ ∘ h) ⁻¹' UC ∩ ⇑G ⁻¹' otherBranchesᶜ ∩ Q'ᶜ), ?_, ?_⟩
          · rw [hGdomain, nhdsWithin_union]
            refine ⟨?_, Filter.mem_of_superset hempty (empty_subset _)⟩
            rw [hsplitP]
            exact ⟨Filter.mem_of_superset hW₁ subset_union_left,
              Filter.mem_of_superset hW₂ subset_union_right⟩
          · rintro u (hu | hu) v (hv | hv) huv
            · exact hh.bijOn.injOn hu.1.1.1.1 hv.1.1.1.1
                (hf₁.bijOn.injOn hu.1.1.1.2 hv.1.1.1.2
                  (hinjA hu.1.1.2 hv.1.1.2
                    (((hGleft hu.1.1.1.1 hu.1.1.1.2).symm.trans huv).trans
                      (hGleft hv.1.1.1.1 hv.1.1.1.2))))
            · exact hcross u v hu.1.1.1.1 hu.1.1.1.2 hu.2 hu.1.2 hv.1.1.1.1 hv.1.1.1.2
                hv.2 huv
            · exact (hcross v u hv.1.1.1.1 hv.1.1.1.2 hv.2 hv.1.2 hu.1.1.1.1 hu.1.1.1.2
                hu.2 huv.symm).symm
            · exact hh.bijOn.injOn hu.1.1.1.1 hv.1.1.1.1
                (hf₂.bijOn.injOn hu.1.1.1.2 hv.1.1.1.2
                  (hinjC hu.1.1.2 hv.1.1.2
                    (((hGmid hu.1.1.1.1 hu.1.1.1.2).symm.trans huv).trans
                      (hGmid hv.1.1.1.1 hv.1.1.1.2))))
        · have hSsub : MapsTo h (P' ∩ h ⁻¹' (Qᶜ : Set (EuclideanSpace ℝ (Fin 2)))) P :=
            fun w hw => (hsheet hw.1).resolve_right hw.2
          have hS : P' ∩ h ⁻¹' (Qᶜ : Set (EuclideanSpace ℝ (Fin 2))) ∈ 𝓝[G.domain] x := by
            rw [hGdomain, nhdsWithin_union]
            refine ⟨Filter.inter_mem self_mem_nhdsWithin ?_,
              Filter.mem_of_superset hempty (empty_subset _)⟩
            exact (hh.isPiecewiseAffineOn.continuousOn x hxP').preimage_mem_nhdsWithin
              (hQ.isPolyhedron.isClosed.isOpen_compl.mem_nhds hhxQ)
          exact hD.exists_mem_nhdsWithin_injOn_of_eqOn_comp hS ⟨hxP', hhxQ⟩
            ((hf₁.isPiecewiseAffineOn.continuousOn.comp
              (hh.isPiecewiseAffineOn.continuousOn.mono inter_subset_left) hSsub) x
                ⟨hxP', hhxQ⟩)
            (fun w hw => hU₁D (hf₁.bijOn.mapsTo (hSsub hw)))
            (fun u hu v hv huv =>
              hh.bijOn.injOn hu.1 hv.1 (hf₁.bijOn.injOn (hSsub hu) (hSsub hv) huv))
            (fun w hw => hGleft hw.1 (hSsub hw))
      · have hSsub : MapsTo h (P' ∩ h ⁻¹' (Pᶜ : Set (EuclideanSpace ℝ (Fin 2)))) Q :=
          fun w hw => (hsheet hw.1).resolve_left hw.2
        have hS : P' ∩ h ⁻¹' (Pᶜ : Set (EuclideanSpace ℝ (Fin 2))) ∈ 𝓝[G.domain] x := by
          rw [hGdomain, nhdsWithin_union]
          refine ⟨Filter.inter_mem self_mem_nhdsWithin ?_,
            Filter.mem_of_superset hempty (empty_subset _)⟩
          exact (hh.isPiecewiseAffineOn.continuousOn x hxP').preimage_mem_nhdsWithin
            (hP.isPolyhedron.isClosed.isOpen_compl.mem_nhds hhxP)
        exact hD.exists_mem_nhdsWithin_injOn_of_eqOn_comp hS ⟨hxP', hhxP⟩
          ((hf₂.isPiecewiseAffineOn.continuousOn.comp
            (hh.isPiecewiseAffineOn.continuousOn.mono inter_subset_left) hSsub) x
              ⟨hxP', hhxP⟩)
          (fun w hw => hU₂D (hf₂.bijOn.mapsTo (hSsub hw)))
          (fun u hu v hv huv =>
            hh.bijOn.injOn hu.1 hv.1 (hf₂.bijOn.injOn (hSsub hu) (hSsub hv) huv))
          (fun w hw => hGmid hw.1 (hSsub hw))
  · have hxQ' : x ∈ Q' := hxu.resolve_left hxP'
    have hempty : (∅ : Set (EuclideanSpace ℝ (Fin 2))) ∈ 𝓝[P'] x := by
      apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      exact ⟨P'ᶜ, hP'.isPolyhedron.isClosed.isOpen_compl.mem_nhds hxP', by simp⟩
    have hS : Q' ∩ (P'ᶜ : Set (EuclideanSpace ℝ (Fin 2))) ∈ 𝓝[G.domain] x := by
      rw [hGdomain, nhdsWithin_union]
      exact ⟨Filter.mem_of_superset hempty (empty_subset _),
        Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds
          (hP'.isPolyhedron.isClosed.isOpen_compl.mem_nhds hxP'))⟩
    exact hD.exists_mem_nhdsWithin_injOn_of_eqOn_comp hS ⟨hxQ', hxP'⟩
      (hf₃.isPiecewiseAffineOn.continuousOn.mono inter_subset_left x ⟨hxQ', hxP'⟩)
      (fun w hw => hU₃D (hf₃.bijOn.mapsTo hw.1))
      (hf₃.bijOn.injOn.mono inter_subset_left)
      (fun w hw => hGright hw.1)

end CrossReglued

theorem NormalSingularCellData.exists_cross_reglued_cell_fields_of_boundaryBranch
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [T2Space M]
    {D : SingularTwoCell M} {BdM B : Set M} (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hc : hD.singularSet.IsBoundaryBranch c) :
    ∃ G : SingularTwoCell M,
      ⇑G '' G.domain ⊆ ⇑D '' D.domain ∧
      hD.singularSet.branchCarrier c ⊆ doublePointSet G G.domain ∧
      doublePointSet G G.domain = doublePointSet D D.domain ∧
      (∀ x ∈ G.domain, ∃ V ∈ 𝓝[G.domain] x, InjOn (⇑G) V) ∧
      (∀ y, (G.domain ∩ ⇑G ⁻¹' {y}).encard ≤ 2) ∧
      ∃ (x y : M) (σ : Path x y) (ω : Path y x) (e : loopCircle ≃ₜ frontier G.domain),
        ∀ θ, ⇑G (e θ) = pathToCircle (σ.trans ω) θ := by
  obtain ⟨A, C, U₁, U₂, U₃, P, Q, P', Q', A', _, _, _, _, _, _, _, _, g, f₁, f₂, h, f₃, H, G,
    -, -, hAC, hcover, hg, hcompat, -, -, -, -, -, hdomains, hinter₁₂, hinter₂₃,
    hdisjoint₁₃, hP, hQ, hHdomain, hf₁, hf₂, hf₁seam, hf₂seam, hH₁, hH₂,
    hA'def, -, hA'seam, -, -, hP', hQ', hGdomain, hh, hf₃, hhseam, hf₃seam, hGH, hG₃,
    -, -, -, -, -, -, -, -, -,
    hGimage, hbranch, x, y, σ, ω, e, -, -, hboundaryParam, -⟩ :=
    hD.exists_cross_reglued_cell_of_boundaryBranch hc
  exact ⟨G, hGimage, hbranch,
    hD.doublePointSet_crossReglued_eq hAC hcover hg hcompat hdomains hinter₁₂ hinter₂₃
      hdisjoint₁₃ hHdomain hf₁ hf₂ hf₂seam hH₁ hH₂ hGdomain hh hf₃ hf₃seam hGH hG₃ hbranch,
    hD.locallyInjective_crossReglued hAC hcover hg hcompat hdomains hinter₁₂ hinter₂₃
      hdisjoint₁₃ hP hQ hHdomain hf₁ hf₂ hf₁seam hf₂seam hH₁ hH₂ hA'def hA'seam hP' hQ'
      hGdomain hh hf₃ hhseam hf₃seam hGH hG₃,
    hD.fiber_le_two_crossReglued hAC hg hcompat hdomains hinter₁₂ hinter₂₃ hdisjoint₁₃
      hHdomain hf₁ hf₂ hf₂seam hH₁ hH₂ hGdomain hh hf₃ hf₃seam hGH hG₃,
    x, y, σ, ω, e, hboundaryParam⟩

end DifferentialGeometry.Topology.PiecewiseLinear

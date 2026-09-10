/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.VanKampen.TwoSidedCollarCover

set_option autoImplicit false

open Filter Topology
open scoped ContinuousMap

universe u v

namespace DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar

open Set

variable {S : Type v} [TopologicalSpace S] {X : Type u} [TopologicalSpace X]
  {e : S → X} (h : TwoSidedCollar e)

include h

noncomputable def negativeRetractionValue
    [Nonempty S]
    (x : h.negativeCover) : X := by
  classical
  exact if hx : x.1 ∈ h.range then
      let p := h.homeomorphRange.symm ⟨x.1, hx⟩
      h.toFun (p.1, min p.2 0)
    else x.1

theorem negativeRetractionValue_eq_of_mem_negativeSide
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X]
    (x : h.negativeCover) (hxN : x.1 ∈ h.negativeSide) :
    h.negativeRetractionValue x = x.1 := by
  unfold negativeRetractionValue
  split_ifs with hx
  · let p := h.homeomorphRange.symm (⟨x.1, hx⟩ : h.range)
    have hp : h.toFun p = x.1 :=
      congrArg Subtype.val (h.homeomorphRange.apply_symm_apply ⟨x.1, hx⟩)
    have ht : p.2 < 0 := by
      have := h.time_neg_of_mem_negativeSide_range (⟨x.1, hx⟩ : h.range) hxN
      change p.2 < 0 at this
      exact this
    change h.toFun (p.1, min p.2 0) = x.1
    rw [min_eq_left ht.le]
    exact hp
  · rfl

theorem negativeRetractionValue_eq_of_mem_collarSlice
    [Nonempty S]
    (x : h.negativeCover) (hx : x.1 ∈ h.collarSlice (Set.Iio 1)) :
    h.negativeRetractionValue x =
      let p := h.homeomorphRange.symm
        ⟨x.1, h.collarSlice_subset_range _ hx⟩
      h.toFun (p.1, min p.2 0) := by
  unfold negativeRetractionValue
  rw [dif_pos (h.collarSlice_subset_range _ hx)]

theorem continuous_negativeRetractionValue
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X] :
    Continuous h.negativeRetractionValue := by
  let A : Set h.negativeCover := Subtype.val ⁻¹' h.negativeSide
  let B : Set h.negativeCover := Subtype.val ⁻¹' h.collarSlice (Set.Iio 1)
  have hA : IsOpen A := h.isOpen_negativeSide.preimage continuous_subtype_val
  have hB : IsOpen B := (h.isOpen_collarSlice isOpen_Iio).preimage continuous_subtype_val
  have hAB : A ∪ B = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact x.2
  rw [← continuousOn_univ, ← hAB,
    continuousOn_union_iff_of_isOpen hA hB]
  constructor
  · exact continuous_subtype_val.continuousOn.congr fun x hx =>
      h.negativeRetractionValue_eq_of_mem_negativeSide x hx
  · rw [continuousOn_iff_continuous_domRestrict]
    let j : B → h.range := fun x =>
      ⟨x.1.1, h.collarSlice_subset_range _ x.2⟩
    have hj : Continuous j := continuous_subtype_val.comp continuous_subtype_val |>.subtype_mk _
    let g : B → X := fun x =>
      let p := h.homeomorphRange.symm (j x)
      h.toFun (p.1, min p.2 0)
    have hg : Continuous g := by
      apply h.isOpenEmbedding_toFun.continuous.comp
      apply Continuous.prodMk
      · exact continuous_fst.comp (h.homeomorphRange.symm.continuous.comp hj)
      · exact (continuous_snd.comp (h.homeomorphRange.symm.continuous.comp hj)).min continuous_const
    apply hg.congr
    intro x
    exact (h.negativeRetractionValue_eq_of_mem_collarSlice x.1 x.2).symm

theorem negativeRetractionValue_mem_closure
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X]
    (x : h.negativeCover) :
    h.negativeRetractionValue x ∈ closure h.negativeSide := by
  rw [h.closure_negativeSide]
  unfold negativeRetractionValue
  split_ifs with hx
  · let p := h.homeomorphRange.symm (⟨x.1, hx⟩ : h.range)
    change h.toFun (p.1, min p.2 0) ∈ h.negativeSide ∪ Set.range e
    by_cases ht : p.2 < 0
    · exact Or.inl (by
        rw [min_eq_left ht.le]
        exact h.toFun_mem_negativeSide_of_neg p.1 ht)
    · right
      refine ⟨p.1, ?_⟩
      rw [min_eq_right (le_of_not_gt ht)]
      exact (h.zero_eq p.1).symm
  · exact Or.inl (by
      rcases x.2 with hxN | hxC
      · exact hxN
      · exact False.elim (hx (h.collarSlice_subset_range _ hxC)))

noncomputable def negativeRetraction
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X] :
    C(h.negativeCover, closure h.negativeSide) where
  toFun x := ⟨h.negativeRetractionValue x, h.negativeRetractionValue_mem_closure x⟩
  continuous_toFun := h.continuous_negativeRetractionValue.subtype_mk _

theorem negativeRetractionValue_eq_of_mem_zeroSlice
    [Nonempty S]
    (x : h.negativeCover) (hxZ : x.1 ∈ Set.range e) :
    h.negativeRetractionValue x = x.1 := by
  rcases hxZ with ⟨s, hs⟩
  have hxC : x.1 ∈ h.collarSlice (Set.Iio 1) :=
    ⟨(s, 0), ⟨trivial, by norm_num⟩, (h.zero_eq s).trans hs⟩
  have hxR : x.1 ∈ h.range := h.collarSlice_subset_range _ hxC
  unfold negativeRetractionValue
  rw [dif_pos hxR]
  let p := h.homeomorphRange.symm
    (⟨x.1, hxR⟩ : h.range)
  have hpval : h.toFun p = x.1 :=
    congrArg Subtype.val
      (h.homeomorphRange.apply_symm_apply
        (⟨x.1, hxR⟩ : h.range))
  have hp : p = (s, 0) := by
    apply h.isOpenEmbedding_toFun.injective
    rw [hpval, h.zero_eq, hs]
  change h.toFun (p.1, min p.2 0) = x.1
  rw [hp]
  simp only [min_self]
  exact (h.zero_eq s).trans hs

theorem negativeRetraction_comp_inclusion
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X] :
    h.negativeRetraction.comp h.negativeClosureInclusion =
      ContinuousMap.id (closure h.negativeSide) := by
  ext x
  change h.negativeRetractionValue (h.negativeClosureInclusion x) = x.1
  have hx : x.1 ∈ h.negativeSide ∪ Set.range e :=
    (Set.ext_iff.mp h.closure_negativeSide x.1).mp x.2
  rcases hx with hxN | hxZ
  · exact h.negativeRetractionValue_eq_of_mem_negativeSide _ hxN
  · exact h.negativeRetractionValue_eq_of_mem_zeroSlice _ hxZ

noncomputable def positiveRetractionValue
    [Nonempty S]
    (x : h.positiveCover) : X := by
  classical
  exact if hx : x.1 ∈ h.range then
      let p := h.homeomorphRange.symm ⟨x.1, hx⟩
      h.toFun (p.1, max p.2 0)
    else x.1

theorem positiveRetractionValue_eq_of_mem_positiveSide
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X]
    (x : h.positiveCover) (hxP : x.1 ∈ h.positiveSide) :
    h.positiveRetractionValue x = x.1 := by
  unfold positiveRetractionValue
  split_ifs with hx
  · let p := h.homeomorphRange.symm (⟨x.1, hx⟩ : h.range)
    have hp : h.toFun p = x.1 :=
      congrArg Subtype.val (h.homeomorphRange.apply_symm_apply ⟨x.1, hx⟩)
    have ht : 0 < p.2 := by
      have := h.time_pos_of_mem_positiveSide_range (⟨x.1, hx⟩ : h.range) hxP
      change 0 < p.2 at this
      exact this
    change h.toFun (p.1, max p.2 0) = x.1
    rw [max_eq_left ht.le]
    exact hp
  · rfl

theorem positiveRetractionValue_eq_of_mem_collarSlice
    [Nonempty S]
    (x : h.positiveCover) (hx : x.1 ∈ h.collarSlice (Set.Ioi (-1))) :
    h.positiveRetractionValue x =
      let p := h.homeomorphRange.symm
        ⟨x.1, h.collarSlice_subset_range _ hx⟩
      h.toFun (p.1, max p.2 0) := by
  unfold positiveRetractionValue
  rw [dif_pos (h.collarSlice_subset_range _ hx)]

theorem continuous_positiveRetractionValue
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X] :
    Continuous h.positiveRetractionValue := by
  let A : Set h.positiveCover := Subtype.val ⁻¹' h.positiveSide
  let B : Set h.positiveCover := Subtype.val ⁻¹' h.collarSlice (Set.Ioi (-1))
  have hA : IsOpen A := h.isOpen_positiveSide.preimage continuous_subtype_val
  have hB : IsOpen B := (h.isOpen_collarSlice isOpen_Ioi).preimage continuous_subtype_val
  have hAB : A ∪ B = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact x.2
  rw [← continuousOn_univ, ← hAB,
    continuousOn_union_iff_of_isOpen hA hB]
  constructor
  · exact continuous_subtype_val.continuousOn.congr fun x hx =>
      h.positiveRetractionValue_eq_of_mem_positiveSide x hx
  · rw [continuousOn_iff_continuous_domRestrict]
    let j : B → h.range := fun x =>
      ⟨x.1.1, h.collarSlice_subset_range _ x.2⟩
    have hj : Continuous j := continuous_subtype_val.comp continuous_subtype_val |>.subtype_mk _
    let g : B → X := fun x =>
      let p := h.homeomorphRange.symm (j x)
      h.toFun (p.1, max p.2 0)
    have hg : Continuous g := by
      apply h.isOpenEmbedding_toFun.continuous.comp
      apply Continuous.prodMk
      · exact continuous_fst.comp (h.homeomorphRange.symm.continuous.comp hj)
      · exact (continuous_snd.comp (h.homeomorphRange.symm.continuous.comp hj)).max continuous_const
    apply hg.congr
    intro x
    exact (h.positiveRetractionValue_eq_of_mem_collarSlice x.1 x.2).symm

theorem positiveRetractionValue_mem_closure
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X]
    (x : h.positiveCover) :
    h.positiveRetractionValue x ∈ closure h.positiveSide := by
  rw [h.closure_positiveSide]
  unfold positiveRetractionValue
  split_ifs with hx
  · let p := h.homeomorphRange.symm (⟨x.1, hx⟩ : h.range)
    change h.toFun (p.1, max p.2 0) ∈ h.positiveSide ∪ Set.range e
    by_cases ht : 0 < p.2
    · exact Or.inl (by
        rw [max_eq_left ht.le]
        exact h.toFun_mem_positiveSide_of_pos p.1 ht)
    · right
      refine ⟨p.1, ?_⟩
      rw [max_eq_right (le_of_not_gt ht)]
      exact (h.zero_eq p.1).symm
  · exact Or.inl (by
      rcases x.2 with hxP | hxC
      · exact hxP
      · exact False.elim (hx (h.collarSlice_subset_range _ hxC)))

noncomputable def positiveRetraction
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X] :
    C(h.positiveCover, closure h.positiveSide) where
  toFun x := ⟨h.positiveRetractionValue x, h.positiveRetractionValue_mem_closure x⟩
  continuous_toFun := h.continuous_positiveRetractionValue.subtype_mk _

theorem positiveRetractionValue_eq_of_mem_zeroSlice
    [Nonempty S]
    (x : h.positiveCover) (hxZ : x.1 ∈ Set.range e) :
    h.positiveRetractionValue x = x.1 := by
  rcases hxZ with ⟨s, hs⟩
  have hxC : x.1 ∈ h.collarSlice (Set.Ioi (-1)) :=
    ⟨(s, 0), ⟨trivial, by norm_num⟩, (h.zero_eq s).trans hs⟩
  have hxR : x.1 ∈ h.range := h.collarSlice_subset_range _ hxC
  unfold positiveRetractionValue
  rw [dif_pos hxR]
  let p := h.homeomorphRange.symm
    (⟨x.1, hxR⟩ : h.range)
  have hpval : h.toFun p = x.1 :=
    congrArg Subtype.val
      (h.homeomorphRange.apply_symm_apply
        (⟨x.1, hxR⟩ : h.range))
  have hp : p = (s, 0) := by
    apply h.isOpenEmbedding_toFun.injective
    rw [hpval, h.zero_eq, hs]
  change h.toFun (p.1, max p.2 0) = x.1
  rw [hp]
  simp only [max_self]
  exact (h.zero_eq s).trans hs

theorem positiveRetraction_comp_inclusion
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X] :
    h.positiveRetraction.comp h.positiveClosureInclusion =
      ContinuousMap.id (closure h.positiveSide) := by
  ext x
  change h.positiveRetractionValue (h.positiveClosureInclusion x) = x.1
  have hx : x.1 ∈ h.positiveSide ∪ Set.range e :=
    (Set.ext_iff.mp h.closure_positiveSide x.1).mp x.2
  rcases hx with hxP | hxZ
  · exact h.positiveRetractionValue_eq_of_mem_positiveSide _ hxP
  · exact h.positiveRetractionValue_eq_of_mem_zeroSlice _ hxZ

noncomputable def sideRetractions
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X] :
    SideRetractions h where
  negative := h.negativeRetraction
  negative_comp_inclusion := h.negativeRetraction_comp_inclusion
  positive := h.positiveRetraction
  positive_comp_inclusion := h.positiveRetraction_comp_inclusion

theorem simplyConnectedSpace_closure_sides
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X] [SimplyConnectedSpace S] :
    SimplyConnectedSpace (closure h.negativeSide) ∧
      SimplyConnectedSpace (closure h.positiveSide) :=
  h.simplyConnectedSpace_closure_sides_of_retractions h.sideRetractions

end DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar

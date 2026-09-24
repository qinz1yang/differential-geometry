import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.SetTheory.Cardinal.Finite

open Set

theorem IsClopen.injective_connectedComponentsMap_subtype_val
    {X : Type*} [TopologicalSpace X] {s : Set X} (hs : IsClopen s) :
    Function.Injective (continuous_subtype_val.connectedComponentsMap :
      ConnectedComponents s → ConnectedComponents X) := by
  intro C D hCD
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe D
  change ConnectedComponents.mk x.val = ConnectedComponents.mk y.val at hCD
  rw [ConnectedComponents.coe_eq_coe] at hCD ⊢
  rw [← Set.image_val_inj, ← connectedComponentIn_eq_image x.property,
    ← connectedComponentIn_eq_image y.property, hs.connectedComponentIn_eq x.property,
    hs.connectedComponentIn_eq y.property]
  exact hCD

theorem IsClopen.natCard_connectedComponents_lt
    {X : Type*} [TopologicalSpace X] [Finite (ConnectedComponents X)]
    {s : Set X} (hs : IsClopen s) (hne : sᶜ.Nonempty) :
    Nat.card (ConnectedComponents s) < Nat.card (ConnectedComponents X) := by
  classical
  let f : ConnectedComponents s → ConnectedComponents X :=
    continuous_subtype_val.connectedComponentsMap
  have hf : Function.Injective f := hs.injective_connectedComponentsMap_subtype_val
  let : Finite (ConnectedComponents s) := Finite.of_injective f hf
  let : Fintype (ConnectedComponents s) := Fintype.ofFinite _
  let : Fintype (ConnectedComponents X) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  obtain ⟨x, hx⟩ := hne
  apply Fintype.card_lt_of_injective_of_notMem f hf (b := ConnectedComponents.mk x)
  rintro ⟨C, hC⟩
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe C
  change ConnectedComponents.mk y.val = ConnectedComponents.mk x at hC
  exact hx (hs.connectedComponent_subset y.property
    (ConnectedComponents.coe_eq_coe'.mp hC.symm))

theorem Topology.IsEmbedding.natCard_connectedComponents_preimage_lt_of_range_inter_eq
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {e : X → Z} {g : Y → Z}
    (he : Topology.IsEmbedding e) (hg : Topology.IsEmbedding g)
    {C : Set Z} (hclosed : IsClosed (range g ∩ C)) {D : Set X} (hD : IsClosed D)
    [Finite (ConnectedComponents (e ⁻¹' C))]
    (hne : (D ∩ e ⁻¹' C).Nonempty)
    (hlevel : range g ∩ C = e '' Dᶜ ∩ C) :
    Nat.card (ConnectedComponents (g ⁻¹' C)) <
      Nat.card (ConnectedComponents (e ⁻¹' C)) := by
  let L := e ⁻¹' C
  let V : Set L := {x | x.val ∉ D}
  let q : V → Z := fun x => e x.val.val
  let r : (g ⁻¹' C) → Z := fun x => g x.val
  have hq : Topology.IsEmbedding q :=
    he.comp (Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal)
  have hr : Topology.IsEmbedding r := hg.comp Topology.IsEmbedding.subtypeVal
  have hrangeq : range q = e '' Dᶜ ∩ C := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x.val.val, x.property, rfl⟩, x.val.property⟩
    · rintro ⟨⟨x, hx, rfl⟩, hxc⟩
      exact ⟨⟨⟨x, hxc⟩, hx⟩, rfl⟩
  have hranger : range r = range g ∩ C := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨mem_range_self x.val, x.property⟩
    · rintro ⟨⟨x, rfl⟩, hxc⟩
      exact ⟨⟨x, hxc⟩, rfl⟩
  have hVeq : V = (fun x : L => e x.val) ⁻¹' (range g ∩ C) := by
    ext x
    constructor
    · intro hx
      exact hlevel.symm.subset ⟨⟨x.val, hx, rfl⟩, x.property⟩
    · intro hx
      obtain ⟨⟨y, hy, hyx⟩, _⟩ := hlevel.subset hx
      change x.val ∉ D
      rw [← he.injective hyx]
      exact hy
  have hV : IsClopen V := by
    refine ⟨?_, hD.isOpen_compl.preimage continuous_subtype_val⟩
    rw [hVeq]
    exact hclosed.preimage (he.continuous.comp continuous_subtype_val)
  have hVne : Vᶜ.Nonempty := by
    obtain ⟨x, hxD, hxC⟩ := hne
    exact ⟨⟨x, hxC⟩, fun hx => hx hxD⟩
  let A : (g ⁻¹' C) ≃ₜ V := hr.toHomeomorph.trans
    ((Homeomorph.setCongr (hranger.trans (hlevel.trans hrangeq.symm))).trans
      hq.toHomeomorph.symm)
  let B : ConnectedComponents (g ⁻¹' C) ≃ₜ ConnectedComponents V :=
    A.isQuotientMap.isCoinducing.connectedComponentsHomeomorph (fun y => by
      have hfiber : A ⁻¹' {y} = {A.symm y} := by
        ext x
        change A x = y ↔ x = A.symm y
        constructor
        · intro h
          exact (A.symm_apply_apply x).symm.trans (congrArg A.symm h)
        · rintro rfl
          exact A.apply_symm_apply y
      rw [hfiber]
      exact isConnected_singleton)
  rw [Nat.card_congr B.toEquiv]
  exact hV.natCard_connectedComponents_lt hVne

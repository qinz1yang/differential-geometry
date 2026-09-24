import Mathlib.Topology.Homeomorph.Lemmas

open Set

namespace Homeomorph

variable {N L X : Type*} [TopologicalSpace N] [TopologicalSpace L] [TopologicalSpace X]
  [PartialOrder L] {a : L} {S : Set X}

noncomputable def restrictProdIoi (E : N × Ici a ≃ₜ S)
    (hfront : frontier S = range (fun p => (E (p, ⟨a, le_rfl⟩) : X))) :
    N × Ioi a ≃ₜ interior S := by
  have hboundary (x : N × Ici a) : (E x : X) ∈ frontier S ↔ (x.2 : L) = a := by
    rw [hfront]
    constructor
    · rintro ⟨p, hp⟩
      have hx : (p, (⟨a, le_rfl⟩ : Ici a)) = x := E.injective (Subtype.ext hp)
      exact (congrArg (fun z : N × Ici a => (z.2 : L)) hx).symm
    · intro hx
      have hxeq : x = (x.1, (⟨a, le_rfl⟩ : Ici a)) := Prod.ext rfl (Subtype.ext hx)
      exact ⟨x.1, congrArg (fun z => (E z : X)) hxeq.symm⟩
  have hinterior (x : N × Ici a) : (E x : X) ∈ interior S ↔ a < (x.2 : L) := by
    have hiff : (E x : X) ∈ interior S ↔ (E x : X) ∉ frontier S := by
      rw [frontier]
      simp only [mem_sdiff, subset_closure (E x).property, true_and, not_not]
    rw [hiff, hboundary]
    exact ⟨fun hn => lt_of_le_of_ne x.2.property (Ne.symm hn), fun hp => ne_of_gt hp⟩
  let i : N × Ioi a → N × Ici a := Prod.map id (Set.inclusion Ioi_subset_Ici_self)
  have hi : Topology.IsEmbedding i :=
    Topology.IsEmbedding.id.prodMap (Topology.IsEmbedding.inclusion Ioi_subset_Ici_self)
  have hmap (x : N × Ioi a) : (E (i x) : X) ∈ interior S := (hinterior _).mpr x.2.property
  let f := Set.codRestrict (fun x => (E (i x) : X)) (interior S) hmap
  have hf : Topology.IsEmbedding f :=
    (Topology.IsEmbedding.subtypeVal.comp (E.isEmbedding.comp hi)).codRestrict _ _
  have hsurj : Function.Surjective f := by
    intro y
    let x := E.symm ⟨y, interior_subset y.property⟩
    have hxy : (E x : X) = y := congrArg Subtype.val (E.apply_symm_apply _)
    have hx : a < (x.2 : L) := (hinterior x).mp (hxy.symm ▸ y.property)
    refine ⟨(x.1, ⟨x.2, hx⟩), ?_⟩
    apply Subtype.ext
    exact hxy
  exact hf.toHomeomorphOfSurjective hsurj

@[simp]
theorem restrictProdIoi_apply_coe (E : N × Ici a ≃ₜ S)
    (hfront : frontier S = range (fun p => (E (p, ⟨a, le_rfl⟩) : X)))
    (p : N) (s : Ioi a) :
    (E.restrictProdIoi hfront (p, s) : X) = (E (p, ⟨s, s.property.le⟩) : X) := rfl

@[simp]
theorem restrictProdIoi_symm_apply (E : N × Ici a ≃ₜ S)
    (hfront : frontier S = range (fun p => (E (p, ⟨a, le_rfl⟩) : X))) (y : interior S) :
    Prod.map id (Set.inclusion Ioi_subset_Ici_self) ((E.restrictProdIoi hfront).symm y) =
      E.symm ⟨y, interior_subset y.property⟩ := by
  apply E.injective
  apply Subtype.ext
  rw [E.apply_symm_apply]
  exact (E.restrictProdIoi_apply_coe hfront _ _).symm.trans
    (congrArg Subtype.val ((E.restrictProdIoi hfront).apply_symm_apply y))

end Homeomorph

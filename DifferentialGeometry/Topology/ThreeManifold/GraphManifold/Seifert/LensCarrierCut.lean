import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LensCarrierIncidence
import DifferentialGeometry.Topology.Manifold.Diffeomorph.Sigma

/-!
# The cut carrier of a two-piece genus-one presentation

The two clopen components give an actual smooth sum decomposition of the entire cut carrier.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u v

namespace GC.Seifert

def lensClopenSumDiffeomorph (C : CompactCarrier.{u})
    (U V : TopologicalSpace.Opens C.Carrier)
    (hd : Disjoint (U : Set C.Carrier) V) (hc : (U : Set C.Carrier) ∪ V = Set.univ) :
    (U ⊕ V) ≃ₘ⟮C.model, C.model⟯ C.Carrier := by
  let : Nonempty C.kind.Space := by cases C.kind <;> infer_instance
  let f : U ⊕ V → C.Carrier := Sum.elim Subtype.val Subtype.val
  have hf : IsLocalDiffeomorph C.model C.model ∞ f := by
    intro x
    cases x with
    | inl x =>
      exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp
        (isLocalDiffeomorph_subtype_val (I := C.model) U x)
        (isLocalDiffeomorph_sum_inl (I := C.model) (M := U) (N := V) x)
    | inr x =>
      exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp
        (isLocalDiffeomorph_subtype_val (I := C.model) V x)
        (isLocalDiffeomorph_sum_inr (I := C.model) (M := V) (N := U) x)
  refine hf.diffeomorphOfBijective ⟨?_, ?_⟩
  · intro x y hxy
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (Subtype.ext hxy)
      | inr y =>
        change x.val = y.val at hxy
        exact ((Set.disjoint_left.mp hd) x.property (hxy.symm ▸ y.property)).elim
    | inr x =>
      cases y with
      | inl y =>
        change x.val = y.val at hxy
        exact ((Set.disjoint_left.mp hd) y.property (hxy ▸ x.property)).elim
      | inr y => exact congrArg Sum.inr (Subtype.ext hxy)
  · intro x
    have hx : x ∈ (U : Set C.Carrier) ∪ V := hc.symm ▸ Set.mem_univ x
    rcases hx with hx | hx
    · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
    · exact ⟨Sum.inr ⟨x, hx⟩, rfl⟩

theorem lensClopenSumDiffeomorph_inl (C : CompactCarrier.{u})
    (U V : TopologicalSpace.Opens C.Carrier)
    (hd : Disjoint (U : Set C.Carrier) V) (hc : (U : Set C.Carrier) ∪ V = Set.univ) (x : U) :
    lensClopenSumDiffeomorph C U V hd hc (Sum.inl x) = x.val := rfl

theorem lensClopenSumDiffeomorph_inr (C : CompactCarrier.{u})
    (U V : TopologicalSpace.Opens C.Carrier)
    (hd : Disjoint (U : Set C.Carrier) V) (hc : (U : Set C.Carrier) ∪ V = Set.univ) (x : V) :
    lensClopenSumDiffeomorph C U V hd hc (Sum.inr x) = x.val := rfl

theorem twoComponent_union (C : CompactCarrier.{u}) (D : C.Components) (hc : D.count = 2)
    (i j : Fin D.count) (hne : i ≠ j) :
    (D.piece i : Set C.Carrier) ∪ D.piece j = Set.univ := by
  classical
  have hall : ({i, j} : Finset (Fin D.count)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hne, Fintype.card_fin, hc]
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ ⋃ k, (D.piece k : Set C.Carrier) := D.covers.symm ▸ Set.mem_univ x
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
  have hkij : k ∈ ({i, j} : Finset (Fin D.count)) := hall.symm ▸ Finset.mem_univ k
  simp only [Finset.mem_insert, Finset.mem_singleton] at hkij
  rcases hkij with rfl | rfl
  · exact Or.inl hk
  · exact Or.inr hk

def twoComponentCutSumDiffeomorph (C : CompactCarrier.{u}) (D : C.Components)
    (hc : D.count = 2) (i j : Fin D.count) (hne : i ≠ j) :
    (D.piece i ⊕ D.piece j) ≃ₘ⟮C.model, C.model⟯ C.Carrier :=
  lensClopenSumDiffeomorph C (D.piece i) (D.piece j) (D.disjoint hne)
    (twoComponent_union C D hc i j hne)

theorem twoComponentCutSumDiffeomorph_inl (C : CompactCarrier.{u}) (D : C.Components)
    (hc : D.count = 2) (i j : Fin D.count) (hne : i ≠ j) (x : D.piece i) :
    twoComponentCutSumDiffeomorph C D hc i j hne (Sum.inl x) = x.val := rfl

theorem twoComponentCutSumDiffeomorph_inr (C : CompactCarrier.{u}) (D : C.Components)
    (hc : D.count = 2) (i j : Fin D.count) (hne : i ≠ j) (x : D.piece j) :
    twoComponentCutSumDiffeomorph C D hc i j hne (Sum.inr x) = x.val := rfl

section Comparison

variable (C : CompactCarrier.{u}) (D : C.Components)
    (C' : CompactCarrier.{v}) (D' : C'.Components)
    (hc : D.count = 2) (hc' : D'.count = 2)
    (i j : Fin D.count) (i' j' : Fin D'.count) (hne : i ≠ j) (hne' : i' ≠ j')
    (L : D.piece i ≃ₘ⟮C.model, C'.model⟯ D'.piece i')
    (R : D.piece j ≃ₘ⟮C.model, C'.model⟯ D'.piece j')

def twoComponentComparisonDiffeomorph : C.Carrier ≃ₘ⟮C.model, C'.model⟯ C'.Carrier := by
  let H : (D.piece i ⊕ D.piece j) ≃ₘ⟮C.model, C'.model⟯ (D'.piece i' ⊕ D'.piece j') :=
    { toEquiv := Equiv.sumCongr L.toEquiv R.toEquiv
      contMDiff_toFun := L.contMDiff.sumMap R.contMDiff
      contMDiff_invFun := L.symm.contMDiff.sumMap R.symm.contMDiff }
  exact (twoComponentCutSumDiffeomorph C D hc i j hne).symm.trans
    (H.trans (twoComponentCutSumDiffeomorph C' D' hc' i' j' hne'))

theorem twoComponentComparisonDiffeomorph_left (x : D.piece i) :
    twoComponentComparisonDiffeomorph C D C' D' hc hc' i j i' j' hne hne' L R x.val =
      (L x).val := by
  rw [← twoComponentCutSumDiffeomorph_inl C D hc i j hne x]
  change (twoComponentCutSumDiffeomorph C' D' hc' i' j' hne')
    (Sum.map L R ((twoComponentCutSumDiffeomorph C D hc i j hne).symm
      ((twoComponentCutSumDiffeomorph C D hc i j hne) (Sum.inl x)))) = _
  rw [Diffeomorph.symm_apply_apply]
  rfl

theorem twoComponentComparisonDiffeomorph_right (x : D.piece j) :
    twoComponentComparisonDiffeomorph C D C' D' hc hc' i j i' j' hne hne' L R x.val =
      (R x).val := by
  rw [← twoComponentCutSumDiffeomorph_inr C D hc i j hne x]
  change (twoComponentCutSumDiffeomorph C' D' hc' i' j' hne')
    (Sum.map L R ((twoComponentCutSumDiffeomorph C D hc i j hne).symm
      ((twoComponentCutSumDiffeomorph C D hc i j hne) (Sum.inr x)))) = _
  rw [Diffeomorph.symm_apply_apply]
  rfl

end Comparison

end GC.Seifert

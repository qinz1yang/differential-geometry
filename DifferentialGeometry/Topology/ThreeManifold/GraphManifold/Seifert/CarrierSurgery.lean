import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgeryShrink
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgeryPresentation
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgerySeamOrientation
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgeryOrientedQuotient
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.NoCuts

/-!
Actual torus-pairing quotient surgery, with retained external boundary or with no external tori.
A common collar shrink installs the quotient atlas and orientation before forming the presentation.
-/

set_option autoImplicit false

noncomputable section

open Set Topology TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Manifold GC.Seifert
open scoped Manifold ContDiff

universe u

namespace GC.Seifert

theorem exists_torusQuotientPresentation (C : CompactCarrier.{u}) (D : C.Components)
    (P : TorusPairing C) (n : ℕ) (E : BoundaryTori C n)
    (hb : C.model.boundary C.Carrier = (⋃ j, P.gluing.block j) ∪ E.image)
    (hd : Disjoint (⋃ j, P.gluing.block j) E.image)
    (left right : Fin P.count → Fin D.count) (external : Fin n → Fin D.count)
    (hl : ∀ j, P.gluing.left j ⊆ D.piece (left j))
    (hr : ∀ j, P.gluing.right j ⊆ D.piece (right j))
    (he : ∀ j, range (E.torusMap j) ⊆ D.piece (external j)) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (W : CompactCarrier.{u})
      (T : TorusPresentation W) (hC : T.cutCarrier = C) (hn : T.externalCount = n),
      (hC ▸ T.components) = D ∧ (hC ▸ T.pairing) = P.shrink hδ hδ1 ∧
      (hC ▸ (hn ▸ T.cutExternal)) = E.shrink hδ hδ1 ∧
      ∃ e : P.QuotientSpace ≃ₜ W.Carrier,
        ∀ x : C.Carrier, e (P.quotientMap x) = T.cutMap (hC.symm ▸ x) := by
  obtain ⟨δ, hδ, hδ1, hs, hex⟩ := P.exists_surgeryCommonShrink E hd
  let S := P.shrink hδ hδ1
  let F := E.shrink hδ hδ1
  have hbS := P.surgeryShrink_boundary E hδ hδ1 hb
  obtain ⟨A, hman, hpatch⟩ := S.exists_surgeryHalfQuotientAtlas D F hs hex hbS
  let := A
  let := hman
  obtain ⟨O, ho⟩ :=
    S.exists_surgeryQuotientOrientation (k := .withBoundary) D F hs hex hbS hpatch
      (fun j => S.surgerySignedOrientation hs j)
      (fun j x hx => S.surgerySignedOrientation_map hs j (x := x) hx)
  let W := S.surgeryCarrier (k := .withBoundary) O
  let T : TorusPresentation W :=
    S.surgeryPresentation (k := .withBoundary) D F hs hex hbS hpatch O ho
    left right external hl hr (TorusPairing.surgeryShrink_external_owned E hδ hδ1 D external he)
  exact ⟨δ, hδ, hδ1, W, T, rfl, rfl, rfl, rfl, rfl,
    Homeomorph.refl P.QuotientSpace, fun x => rfl⟩

private def surgeryEmptyBoundary (C : CompactCarrier.{u}) : BoundaryTori C 0 where
  collar i := i.elim0
  source_eq i := i.elim0
  boundary_zero i := i.elim0
  disjoint i := i.elim0

private theorem surgeryEmptyBoundary_image (C : CompactCarrier.{u}) :
    (surgeryEmptyBoundary C).image = ∅ := by
  ext x
  simp only [BoundaryTori.image, iUnion_of_empty, mem_empty_iff_false]

theorem exists_closedTorusQuotientPresentation (C : CompactCarrier.{u}) (D : C.Components)
    (P : TorusPairing C) (hb : C.model.boundary C.Carrier = ⋃ j, P.gluing.block j)
    [ConnectedSpace P.QuotientSpace]
    (left right : Fin P.count → Fin D.count)
    (hl : ∀ j, P.gluing.left j ⊆ D.piece (left j))
    (hr : ∀ j, P.gluing.right j ⊆ D.piece (right j)) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
      (Q : ConnectedClosedOrientedManifold.{u} 3)
      (T : TorusPresentation (NoCuts.carrier Q)) (hC : T.cutCarrier = C),
      (hC ▸ T.components) = D ∧ (hC ▸ T.pairing) = P.shrink hδ hδ1 ∧
      ∃ e : P.QuotientSpace ≃ₜ Q.Carrier,
        ∀ x : C.Carrier, e (P.quotientMap x) = T.cutMap (hC.symm ▸ x) := by
  let E := surgeryEmptyBoundary C
  have hE : E.image = ∅ := surgeryEmptyBoundary_image C
  have hd : Disjoint (⋃ j, P.gluing.block j) E.image := by
    rw [hE]
    exact disjoint_empty _
  have hbE : C.model.boundary C.Carrier = (⋃ j, P.gluing.block j) ∪ E.image := by
    rw [hE, union_empty]
    exact hb
  obtain ⟨δ, hδ, hδ1, hs, hex⟩ := P.exists_surgeryCommonShrink E hd
  let S := P.shrink hδ hδ1
  let F := E.shrink hδ hδ1
  have hbS := P.surgeryShrink_boundary E hδ hδ1 hbE
  obtain ⟨A, hman, hpatch⟩ := S.exists_surgeryClosedQuotientAtlas D F hs hex hbS
  let := A
  let := hman
  obtain ⟨O, ho⟩ := S.exists_surgeryQuotientOrientation (k := .closed) D F hs hex hbS hpatch
    (fun j => S.surgerySignedOrientation hs j)
    (fun j x hx => S.surgerySignedOrientation_map hs j (x := x) hx)
  let Q : ConnectedClosedOrientedManifold.{u} 3 :=
    { Carrier := P.QuotientSpace
      topology := inferInstance
      charts := A
      smooth := hman
      hausdorff := inferInstance
      compact := inferInstance
      orientation := O
      connected := inferInstance }
  let T : TorusPresentation (NoCuts.carrier Q) :=
    S.surgeryPresentation (k := .closed) D F hs hex hbS hpatch
    O ho left right (fun i => i.elim0) hl hr (fun i => i.elim0)
  exact ⟨δ, hδ, hδ1, Q, T, rfl, rfl, rfl,
    Homeomorph.refl P.QuotientSpace, fun x => rfl⟩

end GC.Seifert

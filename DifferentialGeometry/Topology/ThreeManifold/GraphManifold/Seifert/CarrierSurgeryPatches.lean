import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgerySeam

/-!
Actual interior and retained-boundary patches for torus surgery. Each patch is built directly
from the quotient map on an open set avoiding every paired core, with exact original collar maps.
-/

set_option autoImplicit false

noncomputable section

open Set Topology TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Manifold GC.Seifert
open scoped Manifold ContDiff

universe u

namespace GC.GraphManifold.TorusPairing

variable {C : CompactCarrier.{u}}

private theorem surgeryCore_mem_sideTarget (P : TorusPairing C) (j : Fin P.count)
    {x : C.Carrier} (hx : x ∈ P.gluing.block j) :
    x ∈ (P.leftCollar j).target ∪ (P.rightCollar j).target := by
  rcases hx with hx | hx
  · left
    rw [← P.leftCollar_zero_range] at hx
    obtain ⟨t, rfl⟩ := hx
    apply (P.leftCollar j).map_source'
    rw [P.left_source]
    exact zero_mem_halfCollarSource t
  · right
    rw [← P.rightCollar_zero_range] at hx
    obtain ⟨t, rfl⟩ := hx
    apply (P.rightCollar j).map_source'
    rw [P.right_source]
    exact zero_mem_halfCollarSource t

private theorem surgeryExternal_target_avoids (P : TorusPairing C) {n : ℕ}
    (E : BoundaryTori C n)
    (he : ∀ i j, Disjoint (E.collar i).target (P.surgerySideCollar j).target)
    (i : Fin n) {x : C.Carrier} (hx : x ∈ (E.collar i).target) (j : Fin P.count) :
    x ∉ P.gluing.block j := by
  intro hj
  rcases P.surgeryCore_mem_sideTarget j hj with hl | hr
  · exact (he i (.inl j)).le_bot ⟨hx, hl⟩
  · exact (he i (.inr j)).le_bot ⟨hx, hr⟩

def surgeryExternalPatch (P : TorusPairing C) {n : ℕ} (E : BoundaryTori C n)
    (he : ∀ i j, Disjoint (E.collar i).target (P.surgerySideCollar j).target)
    (i : Fin n) : OpenPartialHomeomorph C.Carrier P.QuotientSpace := by
  let U : TopologicalSpace.Opens C.Carrier := ⟨(E.collar i).target, (E.collar i).open_target⟩
  have hu : Nonempty U := ⟨⟨E.collar i (1, halfZero), (E.collar i).map_source' (by
    rw [E.source_eq]
    exact zero_mem_halfCollarSource 1)⟩⟩
  let q : U → P.QuotientSpace := fun x => P.quotientMap x.val
  letI := hu
  exact (U.openPartialHomeomorphSubtypeCoe hu).symm.trans
    ((P.surgery_quotientMap_isOpenEmbedding U (by
      intro x hx j
      exact P.surgeryExternal_target_avoids E he i hx j)).toOpenPartialHomeomorph q)

theorem surgeryExternalPatch_source (P : TorusPairing C) {n : ℕ} (E : BoundaryTori C n)
    (he : ∀ i j, Disjoint (E.collar i).target (P.surgerySideCollar j).target)
    (i : Fin n) : (P.surgeryExternalPatch E he i).source = (E.collar i).target := by
  simp [surgeryExternalPatch]

theorem surgeryExternalPatch_apply (P : TorusPairing C) {n : ℕ} (E : BoundaryTori C n)
    (he : ∀ i j, Disjoint (E.collar i).target (P.surgerySideCollar j).target)
    (i : Fin n) {x : C.Carrier} (hx : x ∈ (E.collar i).target) :
    P.surgeryExternalPatch E he i x = P.quotientMap x := by
  let U : TopologicalSpace.Opens C.Carrier := ⟨(E.collar i).target, (E.collar i).open_target⟩
  have hu : Nonempty U := ⟨⟨E.collar i (1, halfZero), (E.collar i).map_source' (by
    rw [E.source_eq]
    exact zero_mem_halfCollarSource 1)⟩⟩
  let a := U.openPartialHomeomorphSubtypeCoe hu
  have hxa : x ∈ a.target := by
    rw [Opens.openPartialHomeomorphSubtypeCoe_target]
    exact hx
  have ha : (a.symm x).val = x := a.right_inv hxa
  change P.quotientMap (a.symm x).val = P.quotientMap x
  exact congrArg P.quotientMap ha

def surgeryExternalCollar (P : TorusPairing C) {n : ℕ} (E : BoundaryTori C n)
    (he : ∀ i j, Disjoint (E.collar i).target (P.surgerySideCollar j).target)
    (i : Fin n) : OpenPartialHomeomorph (Torus × EuclideanHalfSpace 1) P.QuotientSpace :=
  (E.collar i).toOpenPartialHomeomorph.trans (P.surgeryExternalPatch E he i)

theorem surgeryExternalCollar_source (P : TorusPairing C) {n : ℕ} (E : BoundaryTori C n)
    (he : ∀ i j, Disjoint (E.collar i).target (P.surgerySideCollar j).target)
    (i : Fin n) : (P.surgeryExternalCollar E he i).source = halfCollarSource := by
  rw [surgeryExternalCollar, OpenPartialHomeomorph.trans_source, P.surgeryExternalPatch_source]
  ext p
  constructor
  · intro hp
    exact (E.source_eq i) ▸ hp.1
  · intro hp
    have hs : p ∈ (E.collar i).source := (E.source_eq i).symm ▸ hp
    exact ⟨hs, (E.collar i).map_source' hs⟩

theorem surgeryExternalCollar_apply (P : TorusPairing C) {n : ℕ} (E : BoundaryTori C n)
    (he : ∀ i j, Disjoint (E.collar i).target (P.surgerySideCollar j).target)
    (i : Fin n) {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    P.surgeryExternalCollar E he i p = P.quotientMap (E.collar i p) :=
  P.surgeryExternalPatch_apply E he i ((E.collar i).map_source' ((E.source_eq i).symm ▸ hp))

private theorem surgeryInterior_nonempty (D : C.Components) : Nonempty C.interior := by
  let i : Fin D.count := ⟨0, D.count_pos⟩
  let := D.interior_connected i
  let x : C.pieceInterior (D.piece i) := Classical.choice inferInstance
  exact ⟨⟨x.val, x.property.2⟩⟩

def surgeryInteriorPatch (P : TorusPairing C) (D : C.Components)
    (hb : (⋃ j, P.gluing.block j) ⊆ C.model.boundary C.Carrier) :
    OpenPartialHomeomorph C.Carrier P.QuotientSpace := by
  have hu := surgeryInterior_nonempty D
  let q : C.interior → P.QuotientSpace := fun x => P.quotientMap x.val
  letI := hu
  exact (C.interior.openPartialHomeomorphSubtypeCoe hu).symm.trans
    ((P.surgery_quotientMap_isOpenEmbedding C.interior (by
      intro x hx j hj
      exact C.model.disjoint_interior_boundary.le_bot
        ⟨hx, hb (mem_iUnion.mpr ⟨j, hj⟩)⟩)).toOpenPartialHomeomorph q)

theorem surgeryInteriorPatch_source (P : TorusPairing C) (D : C.Components)
    (hb : (⋃ j, P.gluing.block j) ⊆ C.model.boundary C.Carrier) :
    (P.surgeryInteriorPatch D hb).source = C.interior := by
  simp [surgeryInteriorPatch]

theorem surgeryInteriorPatch_apply (P : TorusPairing C) (D : C.Components)
    (hb : (⋃ j, P.gluing.block j) ⊆ C.model.boundary C.Carrier)
    {x : C.Carrier} (hx : x ∈ C.interior) :
    P.surgeryInteriorPatch D hb x = P.quotientMap x := by
  let a := C.interior.openPartialHomeomorphSubtypeCoe (surgeryInterior_nonempty D)
  have hxa : x ∈ a.target := by
    rw [Opens.openPartialHomeomorphSubtypeCoe_target]
    exact hx
  have ha : (a.symm x).val = x := a.right_inv hxa
  change P.quotientMap (a.symm x).val = P.quotientMap x
  exact congrArg P.quotientMap ha

theorem surgeryInteriorPatch_target (P : TorusPairing C) (D : C.Components)
    (hb : (⋃ j, P.gluing.block j) ⊆ C.model.boundary C.Carrier) :
    (P.surgeryInteriorPatch D hb).target = P.quotientMap '' C.interior := by
  rw [← (P.surgeryInteriorPatch D hb).image_source_eq_target, P.surgeryInteriorPatch_source]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (P.surgeryInteriorPatch_apply D hb hx).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, P.surgeryInteriorPatch_apply D hb hx⟩

theorem surgeryExternalCollar_target (P : TorusPairing C) {n : ℕ} (E : BoundaryTori C n)
    (he : ∀ i j, Disjoint (E.collar i).target (P.surgerySideCollar j).target)
    (i : Fin n) : (P.surgeryExternalCollar E he i).target =
      P.quotientMap '' (E.collar i).target := by
  rw [← (P.surgeryExternalCollar E he i).image_source_eq_target,
    P.surgeryExternalCollar_source]
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨E.collar i p, (E.collar i).map_source' ((E.source_eq i).symm ▸ hp), ?_⟩
    exact (P.surgeryExternalCollar_apply E he i hp).symm
  · rintro ⟨x, hx, rfl⟩
    let p := (E.collar i).symm x
    have hp : p ∈ halfCollarSource := (E.source_eq i) ▸ (E.collar i).map_target' hx
    refine ⟨p, hp, ?_⟩
    rw [P.surgeryExternalCollar_apply E he i hp]
    exact congrArg P.quotientMap ((E.collar i).right_inv' hx)

theorem surgeryCoreBoundarySubset (P : TorusPairing C) {n : ℕ} (E : BoundaryTori C n)
    (hb : C.model.boundary C.Carrier = (⋃ j, P.gluing.block j) ∪ E.image) :
    (⋃ j, P.gluing.block j) ⊆ C.model.boundary C.Carrier := by
  rw [hb]
  exact subset_union_left

theorem surgeryPatches_cover (P : TorusPairing C) (D : C.Components) {n : ℕ}
    (E : BoundaryTori C n)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (he : ∀ i j, Disjoint (E.collar i).target (P.surgerySideCollar j).target)
    (hb : C.model.boundary C.Carrier = (⋃ j, P.gluing.block j) ∪ E.image)
    (q : P.QuotientSpace) :
    q ∈ (P.surgeryInteriorPatch D (P.surgeryCoreBoundarySubset E hb)).target ∨
      (∃ j, q ∈ (P.surgerySignedSeam hd j).target) ∨
      ∃ i, q ∈ (P.surgeryExternalCollar E he i).target := by
  induction q using Quotient.inductionOn with
  | h x =>
    by_cases hx : x ∈ C.interior
    · left
      rw [P.surgeryInteriorPatch_target]
      exact ⟨x, hx, rfl⟩
    · have hxb : x ∈ C.model.boundary C.Carrier :=
        (C.model.isBoundaryPoint_iff_not_isInteriorPoint x).mpr hx
      rw [hb] at hxb
      rcases hxb with hj | hi
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hj
        right
        left
        refine ⟨j, ?_⟩
        rw [P.surgerySignedSeam_target, P.surgerySeamMap_range]
        exact ⟨x, P.surgeryCore_mem_sideTarget j hj, rfl⟩
      · obtain ⟨i, t, ht⟩ := mem_iUnion.mp hi
        right
        right
        refine ⟨i, ?_⟩
        rw [P.surgeryExternalCollar_target]
        refine ⟨x, ?_, rfl⟩
        rw [← ht]
        exact (E.collar i).map_source' ((E.source_eq i).symm ▸ zero_mem_halfCollarSource t)

end GC.GraphManifold.TorusPairing

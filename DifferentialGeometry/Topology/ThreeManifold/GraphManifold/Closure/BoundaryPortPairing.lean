import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.CarrierSum
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Presentation

/-!
Actual one-port boundary pairing and retained ports on an oriented disjoint carrier sum.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.Endpoint.CompactCarrier
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

variable (C D : CompactCarrier.{u}) (hC : C.kind = .withBoundary) (hD : D.kind = .withBoundary)
variable [Nonempty C.Carrier] [Nonempty D.Carrier]
variable {n : ℕ} (E1 : BoundaryTori C 1) (E2 : BoundaryTori D (n + 1))


def boundaryPortLeftCollar :
    PartialDiffeomorph halfCollarModel (withBoundarySum C D hC hD).model
      (Torus × EuclideanHalfSpace 1) (withBoundarySum C D hC hD).Carrier ∞ :=
  (E1.collar 0).trans (withBoundarySumLeft C D hC hD)

def boundaryPortRightCollar (i : Fin (n + 1)) :
    PartialDiffeomorph halfCollarModel (withBoundarySum C D hC hD).model
      (Torus × EuclideanHalfSpace 1) (withBoundarySum C D hC hD).Carrier ∞ :=
  (E2.collar i).trans (withBoundarySumRight C D hC hD)

omit [Nonempty D.Carrier] in
theorem boundaryPortLeftCollar_source :
    (boundaryPortLeftCollar C D hC hD E1).source = halfCollarSource := by
  ext p
  change (p ∈ (E1.collar 0).source ∧
    E1.collar 0 p ∈ (withBoundarySumLeft C D hC hD).source) ↔ p ∈ halfCollarSource
  rw [withBoundarySumLeft_source, E1.source_eq]
  simp

omit [Nonempty C.Carrier] in
theorem boundaryPortRightCollar_source (i : Fin (n + 1)) :
    (boundaryPortRightCollar C D hC hD E2 i).source = halfCollarSource := by
  ext p
  change (p ∈ (E2.collar i).source ∧
    E2.collar i p ∈ (withBoundarySumRight C D hC hD).source) ↔ p ∈ halfCollarSource
  rw [withBoundarySumRight_source, E2.source_eq]
  simp

omit [Nonempty D.Carrier] in
theorem boundaryPortLeftCollar_apply (p : Torus × EuclideanHalfSpace 1) :
    boundaryPortLeftCollar C D hC hD E1 p = Sum.inl (E1.collar 0 p) :=
  withBoundarySumLeft_apply C D hC hD (E1.collar 0 p)

omit [Nonempty C.Carrier] in
theorem boundaryPortRightCollar_apply (i : Fin (n + 1))
    (p : Torus × EuclideanHalfSpace 1) :
    boundaryPortRightCollar C D hC hD E2 i p = Sum.inr (E2.collar i p) :=
  withBoundarySumRight_apply C D hC hD (E2.collar i p)

omit [Nonempty D.Carrier] in
theorem boundaryPortLeftCollar_target :
    (boundaryPortLeftCollar C D hC hD E1).target =
      (Sum.inl : C.Carrier → (withBoundarySum C D hC hD).Carrier) ''
      (E1.collar 0).target := by
  erw [← (boundaryPortLeftCollar C D hC hD E1).toOpenPartialHomeomorph.image_source_eq_target]
  erw [boundaryPortLeftCollar_source]
  have hf : (boundaryPortLeftCollar C D hC hD E1 :
      Torus × EuclideanHalfSpace 1 → (withBoundarySum C D hC hD).Carrier) =
      Sum.inl ∘ E1.collar 0 := funext (boundaryPortLeftCollar_apply C D hC hD E1)
  change (boundaryPortLeftCollar C D hC hD E1 :
    Torus × EuclideanHalfSpace 1 → (withBoundarySum C D hC hD).Carrier) ''
    halfCollarSource = _
  erw [hf, image_comp, ← E1.source_eq 0,
    (E1.collar 0).toOpenPartialHomeomorph.image_source_eq_target]
  rfl

omit [Nonempty C.Carrier] in
theorem boundaryPortRightCollar_target (i : Fin (n + 1)) :
    (boundaryPortRightCollar C D hC hD E2 i).target =
      (Sum.inr : D.Carrier → (withBoundarySum C D hC hD).Carrier) ''
      (E2.collar i).target := by
  erw [← (boundaryPortRightCollar C D hC hD E2 i).toOpenPartialHomeomorph.image_source_eq_target]
  erw [boundaryPortRightCollar_source]
  have hf : (boundaryPortRightCollar C D hC hD E2 i :
      Torus × EuclideanHalfSpace 1 → (withBoundarySum C D hC hD).Carrier) =
      Sum.inr ∘ E2.collar i := funext (boundaryPortRightCollar_apply C D hC hD E2 i)
  change (boundaryPortRightCollar C D hC hD E2 i :
    Torus × EuclideanHalfSpace 1 → (withBoundarySum C D hC hD).Carrier) ''
    halfCollarSource = _
  erw [hf, image_comp, ← E2.source_eq i,
    (E2.collar i).toOpenPartialHomeomorph.image_source_eq_target]
  rfl

omit [Nonempty C.Carrier] in
private theorem boundaryPortRightCollar_disjoint (i j : Fin (n + 1)) (hij : i ≠ j) :
    Disjoint (boundaryPortRightCollar C D hC hD E2 i).target
      (boundaryPortRightCollar C D hC hD E2 j).target := by
  rw [boundaryPortRightCollar_target, boundaryPortRightCollar_target]
  exact (E2.disjoint hij).image Sum.inr_injective.injOn (subset_univ _) (subset_univ _)

omit [Nonempty C.Carrier] in
private theorem boundaryPortRightCollar_boundary (i : Fin (n + 1)) (t : Torus) :
    (withBoundarySum C D hC hD).model.IsBoundaryPoint
      (boundaryPortRightCollar C D hC hD E2 i (t, halfZero)) := by
  rw [boundaryPortRightCollar_apply]
  change Sum.inr (E2.collar i (t, halfZero)) ∈
    (withBoundarySum C D hC hD).model.boundary (withBoundarySum C D hC hD).Carrier
  rw [withBoundarySum_boundary]
  exact Or.inr ⟨E2.collar i (t, halfZero), E2.boundary_zero i t, rfl⟩


def boundaryPortRemaining : BoundaryTori (withBoundarySum C D hC hD) n where
  collar i := boundaryPortRightCollar C D hC hD E2 i.succ
  source_eq i := boundaryPortRightCollar_source C D hC hD E2 i.succ
  boundary_zero i t := boundaryPortRightCollar_boundary C D hC hD E2 i.succ t
  disjoint i j hij := boundaryPortRightCollar_disjoint C D hC hD E2 i.succ j.succ
    (fun heq => hij (Fin.succ_injective n heq))

def boundaryPortLeftMap : Torus → (withBoundarySum C D hC hD).Carrier :=
  fun t => Sum.inl (E1.torusMap 0 t)

def boundaryPortRightMap (i : Fin (n + 1)) :
    Torus → (withBoundarySum C D hC hD).Carrier :=
  fun t => Sum.inr (E2.torusMap i t)

omit [Nonempty C.Carrier] [Nonempty D.Carrier] in
private theorem boundaryPortLeftMap_embedding :
    _root_.Topology.IsEmbedding (boundaryPortLeftMap C D hC hD E1) :=
  _root_.Topology.IsEmbedding.inl.comp (E1.torusMap_isEmbedding 0)

omit [Nonempty C.Carrier] [Nonempty D.Carrier] in
private theorem boundaryPortRightMap_embedding (i : Fin (n + 1)) :
    _root_.Topology.IsEmbedding (boundaryPortRightMap C D hC hD E2 i) :=
  _root_.Topology.IsEmbedding.inr.comp (E2.torusMap_isEmbedding i)


def boundaryPortGluing (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    BoundaryGluing (withBoundarySum C D hC hD).Carrier (Fin 1) where
  left j := range (boundaryPortLeftMap C D hC hD E1)
  right j := range (boundaryPortRightMap C D hC hD E2 0)
  attaching j := (boundaryPortLeftMap_embedding C D hC hD E1).toHomeomorph.symm.trans
    (f.toHomeomorph.trans (boundaryPortRightMap_embedding C D hC hD E2 0).toHomeomorph)
  isClosed_left j := (isCompact_range
    (continuous_inl.comp (E1.torusMap_smooth 0).continuous)).isClosed
  isClosed_right j := (isCompact_range
    (continuous_inr.comp (E2.torusMap_smooth 0).continuous)).isClosed
  disjoint_left_right j := by
    rw [disjoint_left]
    rintro x ⟨t, rfl⟩ ⟨s, heq⟩
    change Sum.inr (E2.torusMap 0 s) = Sum.inl (E1.torusMap 0 t) at heq
    exact Sum.inr_ne_inl heq
  disjoint_blocks i j hij := False.elim (hij (Subsingleton.elim i j))

def boundaryPortPairing (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (hrev : ReversesBoundaryOrientation (withBoundarySum C D hC hD)
      (boundaryPortLeftCollar C D hC hD E1)
      (fun p => boundaryPortRightCollar C D hC hD E2 0 (f p.1, p.2))) :
    TorusPairing (withBoundarySum C D hC hD) where
  count := 1
  gluing := boundaryPortGluing C D hC hD E1 E2 f
  leftParam j := (boundaryPortLeftMap_embedding C D hC hD E1).toHomeomorph
  rightParam j := (boundaryPortRightMap_embedding C D hC hD E2 0).toHomeomorph
  matching j := f
  matching_eq j t := by
    change ((boundaryPortLeftMap_embedding C D hC hD E1).toHomeomorph.symm.trans
      (f.toHomeomorph.trans (boundaryPortRightMap_embedding C D hC hD E2 0).toHomeomorph))
      ((boundaryPortLeftMap_embedding C D hC hD E1).toHomeomorph t) = _
    simp only [Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
    rfl
  leftCollar j := boundaryPortLeftCollar C D hC hD E1
  rightCollar j := boundaryPortRightCollar C D hC hD E2 0
  left_source j := boundaryPortLeftCollar_source C D hC hD E1
  right_source j := boundaryPortRightCollar_source C D hC hD E2 0
  left_zero j t := boundaryPortLeftCollar_apply C D hC hD E1 (t, halfZero)
  right_zero j t := boundaryPortRightCollar_apply C D hC hD E2 0 (t, halfZero)
  reversing j := hrev

variable (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
variable (hrev : ReversesBoundaryOrientation (withBoundarySum C D hC hD)
  (boundaryPortLeftCollar C D hC hD E1)
  (fun p => boundaryPortRightCollar C D hC hD E2 0 (f p.1, p.2)))


theorem boundaryPortPairing_count :
    (boundaryPortPairing C D hC hD E1 E2 f hrev).count = 1 := rfl

theorem boundaryPortPairing_matching (j : Fin 1) :
    (boundaryPortPairing C D hC hD E1 E2 f hrev).matching j = f := rfl

theorem boundaryPortPairing_leftCollar (j : Fin 1) :
    (boundaryPortPairing C D hC hD E1 E2 f hrev).leftCollar j =
      (E1.collar 0).trans (withBoundarySumLeft C D hC hD) := rfl

theorem boundaryPortPairing_rightCollar (j : Fin 1) :
    (boundaryPortPairing C D hC hD E1 E2 f hrev).rightCollar j =
      (E2.collar 0).trans (withBoundarySumRight C D hC hD) := rfl

theorem boundaryPortPairing_left_zero (j : Fin 1) (t : Torus) :
    ((boundaryPortPairing C D hC hD E1 E2 f hrev).leftParam j t).val =
      Sum.inl (E1.collar 0 (t, halfZero)) := rfl

theorem boundaryPortPairing_right_zero (j : Fin 1) (t : Torus) :
    ((boundaryPortPairing C D hC hD E1 E2 f hrev).rightParam j t).val =
      Sum.inr (E2.collar 0 (t, halfZero)) := rfl

omit [Nonempty C.Carrier] in
theorem boundaryPortRemaining_collar (i : Fin n) :
    (boundaryPortRemaining C D hC hD E2).collar i =
      (E2.collar i.succ).trans (withBoundarySumRight C D hC hD) := rfl

omit [Nonempty C.Carrier] in
theorem boundaryPortRemaining_apply (i : Fin n) (p : Torus × EuclideanHalfSpace 1) :
    (boundaryPortRemaining C D hC hD E2).collar i p = Sum.inr (E2.collar i.succ p) :=
  boundaryPortRightCollar_apply C D hC hD E2 i.succ p

omit [Nonempty C.Carrier] in
theorem boundaryPortRemaining_torusMap (i : Fin n) (t : Torus) :
    (boundaryPortRemaining C D hC hD E2).torusMap i t =
      boundaryPortRightMap C D hC hD E2 i.succ t :=
  boundaryPortRightCollar_apply C D hC hD E2 i.succ (t, halfZero)

omit [Nonempty C.Carrier] in
theorem boundaryPortRemaining_image :
    (boundaryPortRemaining C D hC hD E2).image =
      ⋃ i : Fin n, range (boundaryPortRightMap C D hC hD E2 i.succ) := by
  unfold BoundaryTori.image
  congr 1
  funext i
  exact congrArg range (funext (boundaryPortRemaining_torusMap C D hC hD E2 i))

theorem boundaryPortPairing_blocks :
    (⋃ j, (boundaryPortPairing C D hC hD E1 E2 f hrev).gluing.block j) =
      range (boundaryPortLeftMap C D hC hD E1) ∪
        range (boundaryPortRightMap C D hC hD E2 0) := by
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨j, hx⟩
    exact hx
  · intro hx
    exact ⟨(0 : Fin 1), hx⟩

omit [Nonempty C.Carrier] [Nonempty D.Carrier] in
private theorem boundaryPortLeft_image :
    (Sum.inl : C.Carrier → (withBoundarySum C D hC hD).Carrier) '' E1.image =
      range (boundaryPortLeftMap C D hC hD E1) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨i, t, ht⟩ := mem_iUnion.mp hy
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    exact ⟨t, congrArg Sum.inl ht⟩
  · rintro ⟨t, rfl⟩
    exact ⟨E1.torusMap 0 t, mem_iUnion.mpr ⟨0, t, rfl⟩, rfl⟩

omit [Nonempty C.Carrier] in
private theorem boundaryPortRight_image :
    (Sum.inr : D.Carrier → (withBoundarySum C D hC hD).Carrier) '' E2.image =
      range (boundaryPortRightMap C D hC hD E2 0) ∪
        (boundaryPortRemaining C D hC hD E2).image := by
  rw [boundaryPortRemaining_image]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨i, t, ht⟩ := mem_iUnion.mp hy
    cases i using Fin.cases with
    | zero => exact Or.inl ⟨t, congrArg Sum.inr ht⟩
    | succ i => exact Or.inr (mem_iUnion.mpr ⟨i, t, congrArg Sum.inr ht⟩)
  · rintro (⟨t, rfl⟩ | hx)
    · exact ⟨E2.torusMap 0 t, mem_iUnion.mpr ⟨0, t, rfl⟩, rfl⟩
    · obtain ⟨i, t, ht⟩ := mem_iUnion.mp hx
      exact ⟨E2.torusMap i.succ t, mem_iUnion.mpr ⟨i.succ, t, rfl⟩, ht⟩

theorem boundaryPortPairing_boundary
    (hbC : C.model.boundary C.Carrier = E1.image)
    (hbD : D.model.boundary D.Carrier = E2.image) :
    (withBoundarySum C D hC hD).model.boundary (withBoundarySum C D hC hD).Carrier =
      (⋃ j, (boundaryPortPairing C D hC hD E1 E2 f hrev).gluing.block j) ∪
        (boundaryPortRemaining C D hC hD E2).image := by
  rw [withBoundarySum_boundary C D hC hD, hbC, hbD,
    boundaryPortLeft_image C D hC hD E1, boundaryPortRight_image C D hC hD E2,
    boundaryPortPairing_blocks C D hC hD E1 E2 f hrev, union_assoc]
  rfl

omit [Nonempty C.Carrier] in
private theorem boundaryPortRightMap_mem_target (i : Fin (n + 1)) (t : Torus) :
    boundaryPortRightMap C D hC hD E2 i t ∈
      (boundaryPortRightCollar C D hC hD E2 i).target := by
  have hs : (t, halfZero) ∈ (boundaryPortRightCollar C D hC hD E2 i).source := by
    rw [boundaryPortRightCollar_source]
    change (0 : ℝ) < 1
    norm_num
  have he : boundaryPortRightCollar C D hC hD E2 i (t, halfZero) =
      boundaryPortRightMap C D hC hD E2 i t :=
    boundaryPortRightCollar_apply C D hC hD E2 i (t, halfZero)
  exact he ▸ (boundaryPortRightCollar C D hC hD E2 i).map_source hs

theorem boundaryPortPairing_external_disjoint :
    Disjoint (⋃ j, (boundaryPortPairing C D hC hD E1 E2 f hrev).gluing.block j)
      (boundaryPortRemaining C D hC hD E2).image := by
  rw [boundaryPortPairing_blocks, boundaryPortRemaining_image, disjoint_left]
  rintro x (⟨t, rfl⟩ | ⟨t, rfl⟩) hx
  · obtain ⟨i, s, hs⟩ := mem_iUnion.mp hx
    change Sum.inr (E2.torusMap i.succ s) = Sum.inl (E1.torusMap 0 t) at hs
    exact Sum.inr_ne_inl hs
  · obtain ⟨i, s, hs⟩ := mem_iUnion.mp hx
    exact (boundaryPortRightCollar_disjoint C D hC hD E2 0 i.succ
      (Fin.succ_ne_zero i).symm).le_bot
        ⟨boundaryPortRightMap_mem_target C D hC hD E2 0 t,
          hs ▸ boundaryPortRightMap_mem_target C D hC hD E2 i.succ s⟩

end GC.GraphManifold

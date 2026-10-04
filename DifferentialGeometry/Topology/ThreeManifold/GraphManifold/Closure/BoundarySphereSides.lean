import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.BoundaryPortPairing

/-!
The actual sides of a sphere complement remain separated after a one-port boundary attachment.
-/

set_option autoImplicit false

noncomputable section

open Set Function Topology TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

variable (C D : CompactCarrier.{u}) (hC : C.kind = .withBoundary) (hD : D.kind = .withBoundary)
  [ConnectedSpace C.Carrier] [ConnectedSpace D.Carrier]
  {n : ℕ} (E1 : BoundaryTori C 1) (E2 : BoundaryTori D (n + 1))
  (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
  (hrev : ReversesBoundaryOrientation (C.withBoundarySum D hC hD)
    (boundaryPortLeftCollar C D hC hD E1)
    (fun p => boundaryPortRightCollar C D hC hD E2 0 (f p.1, p.2)))

private abbrev boundarySphereP := boundaryPortPairing C D hC hD E1 E2 f hrev

def boundarySphereSumSide (A : Bool → Set D.Carrier) (t0 t : Bool) :
    Set (C.Carrier ⊕ D.Carrier) :=
  {s | Sum.elim (Function.const C.Carrier (t = t0)) (fun x => x ∈ A t) s}

omit [ConnectedSpace D.Carrier] in
private theorem boundarySphereSide_eq_owner (A : Bool → Set D.Carrier)
    (hdisjoint : Disjoint (A false) (A true)) (t0 t : Bool) {x : D.Carrier}
    (hx : x ∈ A t0) : x ∈ A t ↔ t = t0 := by
  constructor
  · intro ht
    cases t <;> cases t0
    · rfl
    · exact False.elim ((disjoint_left.mp hdisjoint) ht hx)
    · exact False.elim ((disjoint_left.mp hdisjoint) hx ht)
    · rfl
  · rintro rfl
    exact hx

set_option backward.isDefEq.respectTransparency false in
private theorem boundarySphereSumSide_block (A : Bool → Set D.Carrier)
    (hdisjoint : Disjoint (A false) (A true)) (t0 : Bool)
    (hport : range (E2.torusMap 0) ⊆ A t0) (t : Bool)
    {x : (C.withBoundarySum D hC hD).Carrier} (k : Fin 1)
    (hx : x ∈ (boundarySphereP C D hC hD E1 E2 f hrev).gluing.block k) :
    x ∈ boundarySphereSumSide C D A t0 t ↔ t = t0 := by
  rcases hx with hx | hx
  · obtain ⟨z, rfl⟩ := hx
    rfl
  · obtain ⟨z, rfl⟩ := hx
    exact boundarySphereSide_eq_owner D A hdisjoint t0 t (hport (mem_range_self z))

set_option backward.isDefEq.respectTransparency false in
private theorem boundarySphereSumSide_saturated (A : Bool → Set D.Carrier)
    (hdisjoint : Disjoint (A false) (A true)) (t0 : Bool)
    (hport : range (E2.torusMap 0) ⊆ A t0) (t : Bool)
    (x y : (C.withBoundarySum D hC hD).Carrier)
    (hxy : (boundarySphereP C D hC hD E1 E2 f hrev).gluing.rel x y) :
    x ∈ boundarySphereSumSide C D A t0 t ↔ y ∈ boundarySphereSumSide C D A t0 t := by
  rcases hxy with rfl | ⟨k, hx, rfl⟩
  · rfl
  · have hy := (boundarySphereP C D hC hD E1 E2 f hrev).gluing.flip_mem_block hx
    have hxo := boundarySphereSumSide_block C D hC hD E1 E2 f hrev A hdisjoint t0 hport t k hx
    have hyo := boundarySphereSumSide_block C D hC hD E1 E2 f hrev A hdisjoint t0 hport t k hy
    exact hxo.trans hyo.symm

omit [ConnectedSpace C.Carrier] [ConnectedSpace D.Carrier] in
private theorem boundarySphereSumSide_open (A : Bool → Set D.Carrier)
    (hopen : ∀ t, IsOpen (A t)) (t0 t : Bool) :
    IsOpen (boundarySphereSumSide C D A t0 t) := by
  rw [isOpen_sum_iff]
  constructor
  · by_cases ht : t = t0
    · simp [boundarySphereSumSide, ht]
    · simp [boundarySphereSumSide, ht]
  · exact hopen t

omit [ConnectedSpace C.Carrier] [ConnectedSpace D.Carrier] in
private theorem boundarySphereSumSide_disjoint (A : Bool → Set D.Carrier)
    (hdisjoint : Disjoint (A false) (A true)) (t0 : Bool) :
    Disjoint (boundarySphereSumSide C D A t0 false) (boundarySphereSumSide C D A t0 true) := by
  rw [disjoint_left]
  intro x hx hy
  cases x with
  | inl x =>
    change false = t0 at hx
    change true = t0 at hy
    exact Bool.false_ne_true (hx.trans hy.symm)
  | inr x => exact (disjoint_left.mp hdisjoint) hx hy

variable (N : CompactCarrier.{u})
  (e : (boundarySphereP C D hC hD E1 E2 f hrev).QuotientSpace ≃ₜ N.Carrier)

def boundarySphereSide (A : Bool → Set D.Carrier) (t0 t : Bool) : Set N.Carrier :=
  e '' ((boundarySphereP C D hC hD E1 E2 f hrev).quotientMap ''
    boundarySphereSumSide C D A t0 t)

def boundarySphereZero (Z : Set D.Carrier) : Set N.Carrier :=
  e '' ((boundarySphereP C D hC hD E1 E2 f hrev).quotientMap '' (Sum.inr '' Z))

set_option backward.isDefEq.respectTransparency false in
theorem boundarySphereSide_preimage (A : Bool → Set D.Carrier)
    (hdisjoint : Disjoint (A false) (A true)) (t0 : Bool)
    (hport : range (E2.torusMap 0) ⊆ A t0) (t : Bool) :
    (fun x => e ((boundarySphereP C D hC hD E1 E2 f hrev).quotientMap x)) ⁻¹'
      boundarySphereSide C D hC hD E1 E2 f hrev N e A t0 t =
        boundarySphereSumSide C D A t0 t := by
  ext x
  constructor
  · rintro ⟨q, ⟨y, hy, rfl⟩, heq⟩
    have hrel : (boundarySphereP C D hC hD E1 E2 f hrev).gluing.rel y x :=
      (Quotient.eq' (s₁ := (boundarySphereP C D hC hD E1 E2 f hrev).gluing.setoid)).mp
        (e.injective heq)
    exact (boundarySphereSumSide_saturated C D hC hD E1 E2 f hrev A hdisjoint t0 hport t
      y x hrel).mp hy
  · intro hx
    exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem boundarySphereSide_open (A : Bool → Set D.Carrier)
    (hopen : ∀ t, IsOpen (A t)) (hdisjoint : Disjoint (A false) (A true)) (t0 : Bool)
    (hport : range (E2.torusMap 0) ⊆ A t0) (t : Bool) :
    IsOpen (boundarySphereSide C D hC hD E1 E2 f hrev N e A t0 t) := by
  apply e.isOpenMap
  exact isOpen_quotient_mk_image_of_saturated
    (boundarySphereSumSide_saturated C D hC hD E1 E2 f hrev A hdisjoint t0 hport t)
    (boundarySphereSumSide_open C D A hopen t0 t)

set_option backward.isDefEq.respectTransparency false in
theorem boundarySphereSide_disjoint (A : Bool → Set D.Carrier)
    (hdisjoint : Disjoint (A false) (A true)) (t0 : Bool)
    (hport : range (E2.torusMap 0) ⊆ A t0) :
    Disjoint (boundarySphereSide C D hC hD E1 E2 f hrev N e A t0 false)
      (boundarySphereSide C D hC hD E1 E2 f hrev N e A t0 true) := by
  rw [disjoint_left]
  rintro x ⟨q, ⟨y, hy, rfl⟩, rfl⟩ hx
  have hx' : y ∈ (fun y => e ((boundarySphereP C D hC hD E1 E2 f hrev).quotientMap y)) ⁻¹'
      boundarySphereSide C D hC hD E1 E2 f hrev N e A t0 true := hx
  rw [boundarySphereSide_preimage C D hC hD E1 E2 f hrev N e A hdisjoint t0 hport true]
    at hx'
  exact (disjoint_left.mp (boundarySphereSumSide_disjoint C D A hdisjoint t0)) hy hx'

set_option backward.isDefEq.respectTransparency false in
theorem boundarySphereSide_connected (A : Bool → Set D.Carrier)
    (hconnected : ∀ t, IsConnected (A t)) (t0 : Bool)
    (hport : range (E2.torusMap 0) ⊆ A t0) (t : Bool) :
    IsConnected (boundarySphereSide C D hC hD E1 E2 f hrev N e A t0 t) := by
  let P := boundarySphereP C D hC hD E1 E2 f hrev
  let l : C.Carrier → P.QuotientSpace := fun x => P.quotientMap (Sum.inl x)
  let r : D.Carrier → P.QuotientSpace := fun x => P.quotientMap (Sum.inr x)
  have hl : Continuous l := P.quotientMap.continuous.comp continuous_inl
  have hr : Continuous r := P.quotientMap.continuous.comp continuous_inr
  apply IsConnected.image _ _ e.continuous.continuousOn
  change IsConnected (P.quotientMap '' boundarySphereSumSide C D A t0 t)
  by_cases ht : t = t0
  · subst t
    have hside : P.quotientMap '' boundarySphereSumSide C D A t0 t0 =
        range l ∪ r '' A t0 := by
      ext q
      constructor
      · rintro ⟨x, hx, rfl⟩
        cases x with
        | inl x => exact Or.inl (mem_range_self x)
        | inr x => exact Or.inr ⟨x, hx, rfl⟩
      · rintro (⟨x, rfl⟩ | ⟨x, hx, rfl⟩)
        · exact ⟨Sum.inl x, rfl, rfl⟩
        · exact ⟨Sum.inr x, hx, rfl⟩
    rw [hside]
    have he : l (E1.torusMap 0 1) = r (E2.torusMap 0 (f 1)) := by
      apply Quotient.sound
      have hrel := P.gluing.rel_of_mem_left (P.leftParam ⟨0, Nat.one_pos⟩ 1).property
      rw [P.matching_eq] at hrel
      exact hrel
    have hmeet : (range l ∩ r '' A t0).Nonempty :=
      ⟨l (E1.torusMap 0 1), mem_range_self _,
        ⟨E2.torusMap 0 (f 1), hport (mem_range_self _), he.symm⟩⟩
    exact (isConnected_range hl).union hmeet ((hconnected t0).image r hr.continuousOn)
  · have hside : P.quotientMap '' boundarySphereSumSide C D A t0 t = r '' A t := by
      ext q
      constructor
      · rintro ⟨x, hx, rfl⟩
        cases x with
        | inl x => exact False.elim (ht hx)
        | inr x => exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨Sum.inr x, hx, rfl⟩
    rw [hside]
    exact (hconnected t).image r hr.continuousOn


set_option backward.isDefEq.respectTransparency false in
private theorem boundarySphereZero_not_block (Z : Set D.Carrier) (hZ : Z ⊆ D.interior)
    {x : (C.withBoundarySum D hC hD).Carrier} (hx : x ∈ Sum.inr '' Z) (k : Fin 1) :
    x ∉ (boundarySphereP C D hC hD E1 E2 f hrev).gluing.block k := by
  obtain ⟨z, hz, rfl⟩ := hx
  rintro (⟨t, ht⟩ | ⟨t, ht⟩)
  · exact Sum.inl_ne_inr ht
  · have he : E2.torusMap 0 t = z := Sum.inr_injective ht
    have hi : D.model.IsInteriorPoint (E2.torusMap 0 t) := he.symm ▸ hZ hz
    exact (D.model.isInteriorPoint_iff_not_isBoundaryPoint _).mp hi (E2.boundary_zero 0 t)

set_option backward.isDefEq.respectTransparency false in
theorem boundarySphereZero_preimage (Z : Set D.Carrier) (hZ : Z ⊆ D.interior) :
    (fun x => e ((boundarySphereP C D hC hD E1 E2 f hrev).quotientMap x)) ⁻¹'
      boundarySphereZero C D hC hD E1 E2 f hrev N e Z = Sum.inr '' Z := by
  ext x
  constructor
  · rintro ⟨q, ⟨y, hy, rfl⟩, heq⟩
    have hrel : (boundarySphereP C D hC hD E1 E2 f hrev).gluing.rel y x :=
      (Quotient.eq' (s₁ := (boundarySphereP C D hC hD E1 E2 f hrev).gluing.setoid)).mp
        (e.injective heq)
    have he := (boundarySphereP C D hC hD E1 E2 f hrev).gluing.eq_of_rel_of_notMem
      (boundarySphereZero_not_block C D hC hD E1 E2 f hrev Z hZ hy) hrel
    exact he ▸ hy
  · intro hx
    exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem boundarySphereSide_complement (Z : Set D.Carrier) (hZ : Z ⊆ D.interior)
    (A : Bool → Set D.Carrier) (hdisjoint : Disjoint (A false) (A true))
    (hcover : Zᶜ = A false ∪ A true) (t0 : Bool)
    (hport : range (E2.torusMap 0) ⊆ A t0) :
    (boundarySphereZero C D hC hD E1 E2 f hrev N e Z)ᶜ =
      boundarySphereSide C D hC hD E1 E2 f hrev N e A t0 false ∪
        boundarySphereSide C D hC hD E1 E2 f hrev N e A t0 true := by
  ext q
  obtain ⟨q, rfl⟩ := e.surjective q
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  have hz : e ((boundarySphereP C D hC hD E1 E2 f hrev).quotientMap x) ∈
      boundarySphereZero C D hC hD E1 E2 f hrev N e Z ↔ x ∈ Sum.inr '' Z :=
    Set.ext_iff.mp (boundarySphereZero_preimage C D hC hD E1 E2 f hrev N e Z hZ) x
  have ht (t : Bool) :
      e ((boundarySphereP C D hC hD E1 E2 f hrev).quotientMap x) ∈
        boundarySphereSide C D hC hD E1 E2 f hrev N e A t0 t ↔
          x ∈ boundarySphereSumSide C D A t0 t :=
    Set.ext_iff.mp
      (boundarySphereSide_preimage C D hC hD E1 E2 f hrev N e A hdisjoint t0 hport t) x
  have hsum : x ∉ Sum.inr '' Z ↔
      x ∈ boundarySphereSumSide C D A t0 false ∨ x ∈ boundarySphereSumSide C D A t0 true := by
    cases x with
    | inl x =>
      change (Sum.inl x : C.Carrier ⊕ D.Carrier) ∉ Sum.inr '' Z ↔ false = t0 ∨ true = t0
      cases t0 <;> simp
    | inr x =>
      change (Sum.inr x : C.Carrier ⊕ D.Carrier) ∉ Sum.inr '' Z ↔ x ∈ A false ∨ x ∈ A true
      have hm : (Sum.inr x : C.Carrier ⊕ D.Carrier) ∈ Sum.inr '' Z ↔ x ∈ Z := by
        constructor
        · rintro ⟨y, hy, he⟩
          exact Sum.inr_injective he ▸ hy
        · intro hx
          exact ⟨x, hx, rfl⟩
      rw [hm]
      exact Set.ext_iff.mp hcover x
  exact (not_congr hz).trans (hsum.trans ((ht false).symm.or (ht true).symm))

set_option backward.isDefEq.respectTransparency false in
theorem boundarySphereSide_remaining_owner (A : Bool → Set D.Carrier) (t0 t : Bool)
    (i : Fin n) (hi : range (E2.torusMap i.succ) ⊆ A t) :
    range (fun z => e ((boundarySphereP C D hC hD E1 E2 f hrev).quotientMap
      (Sum.inr (E2.torusMap i.succ z)))) ⊆
        boundarySphereSide C D hC hD E1 E2 f hrev N e A t0 t := by
  rintro x ⟨z, rfl⟩
  exact ⟨_, ⟨Sum.inr (E2.torusMap i.succ z), hi (mem_range_self z), rfl⟩, rfl⟩

end GC.GraphManifold

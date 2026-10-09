import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CollarGermAdapter

/-!
Topology of the actual abstract torus-pairing quotient. The closed quotient map gives a countable
basis through finite unions of source basis elements, and is an open embedding off the seam cores.
-/

set_option autoImplicit false

noncomputable section

open Set Topology TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff

universe u

namespace GC.GraphManifold.TorusPairing

variable {C : CompactCarrier.{u}}

theorem surgery_quotientMap_isClosedMap (P : TorusPairing C) : IsClosedMap P.quotientMap :=
  isClosedMap_quotient_mk_of_isClosed_rel P.gluing.isClosed_setOf_rel

theorem surgery_quotientMap_surjective (P : TorusPairing C) :
    Function.Surjective P.quotientMap := Quotient.mk''_surjective

theorem surgery_quotientMap_eq_iff (P : TorusPairing C) (x y : C.Carrier) :
    P.quotientMap x = P.quotientMap y ↔ P.gluing.rel x y := Quotient.eq'

theorem surgery_quotient_secondCountable (P : TorusPairing C) :
    SecondCountableTopology P.QuotientSpace := by
  classical
  let B := countableBasis C.Carrier
  let U : Finset B → Set C.Carrier := fun b => ⋃ s ∈ b, (s : Set C.Carrier)
  let V : Finset B → Set P.QuotientSpace := fun b => (P.quotientMap '' (U b)ᶜ)ᶜ
  have hU : ∀ b, IsOpen (U b) := by
    intro b
    exact isOpen_biUnion fun s => Function.const (s ∈ b)
      (isOpen_of_mem_countableBasis s.property)
  have hV : ∀ b, IsOpen (V b) := fun b =>
    (P.surgery_quotientMap_isClosedMap (U b)ᶜ (hU b).isClosed_compl).isOpen_compl
  have hcount : (range V).Countable := Set.countable_range V
  apply (isTopologicalBasis_of_isOpen_of_nhds ?_ ?_).secondCountableTopology hcount
  · rintro A ⟨b, rfl⟩
    exact hV b
  · intro q A hq hA
    let K : Set C.Carrier := P.quotientMap ⁻¹' {q}
    have hK : IsCompact K := (isClosed_singleton.preimage P.quotientMap.continuous).isCompact
    have hx : ∀ x : K, ∃ b : B, x.val ∈ b.val ∧ b.val ⊆ P.quotientMap ⁻¹' A := by
      intro x
      have hpx : P.quotientMap x.val = q := x.property
      obtain ⟨b, hb, hxb, hbA⟩ := (isBasis_countableBasis C.Carrier).isOpen_iff.mp
        (hA.preimage P.quotientMap.continuous) x.val (by
          change P.quotientMap x.val ∈ A
          rw [hpx]
          exact hq)
      exact ⟨⟨b, hb⟩, hxb, hbA⟩
    let b : K → B := fun x => (hx x).choose
    have hb : ∀ x : K, x.val ∈ (b x).val ∧ (b x).val ⊆ P.quotientMap ⁻¹' A :=
      fun x => (hx x).choose_spec
    obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K => (b x).val)
      (fun x => isOpen_of_mem_countableBasis (b x).property) (by
        intro x hxK
        exact mem_iUnion.mpr ⟨⟨x, hxK⟩, (hb ⟨x, hxK⟩).1⟩)
    let t : Finset B := s.image b
    have hKU : K ⊆ U t := by
      intro x hxK
      obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs hxK)
      exact mem_iUnion₂.mpr ⟨b y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, hxy⟩
    have hUA : U t ⊆ P.quotientMap ⁻¹' A := by
      intro x hxU
      obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp hxU
      obtain ⟨y, hy, hyz⟩ := Finset.mem_image.mp hz
      rw [← hyz] at hxz
      exact (hb y).2 hxz
    refine ⟨V t, mem_range_self t, ?_, ?_⟩
    · rintro ⟨x, hx, hxq⟩
      exact hx (hKU hxq)
    · intro y hy
      obtain ⟨x, rfl⟩ := P.surgery_quotientMap_surjective y
      apply hUA
      by_contra hx
      exact hy ⟨x, hx, rfl⟩

theorem surgery_quotientMap_isOpenEmbedding (P : TorusPairing C)
    (U : TopologicalSpace.Opens C.Carrier)
    (hU : ∀ x ∈ U, ∀ j, x ∉ P.gluing.block j) :
    _root_.Topology.IsOpenEmbedding (fun x : U => P.quotientMap x.val) := by
  apply _root_.Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact P.quotientMap.continuous.comp continuous_subtype_val
  · intro x y hxy
    apply Subtype.ext
    exact P.gluing.eq_of_rel_of_notMem (hU x.val x.property) (Quotient.exact hxy)
  · intro A hA
    have ho : IsOpen (Subtype.val '' A : Set C.Carrier) :=
      U.isOpen.isOpenMap_subtype_val A hA
    have hsat : ∀ x y, P.gluing.setoid x y →
        (x ∈ Subtype.val '' A ↔ y ∈ Subtype.val '' A) := by
      intro x y hxy
      constructor
      · rintro ⟨z, hz, rfl⟩
        have he := P.gluing.eq_of_rel_of_notMem (hU z.val z.property) hxy
        exact ⟨z, hz, he⟩
      · rintro ⟨z, hz, rfl⟩
        have he := P.gluing.eq_of_rel_of_notMem (hU z.val z.property)
          (P.gluing.setoid.symm hxy)
        exact ⟨z, hz, he⟩
    have hopen := isOpen_quotient_mk_image_of_saturated hsat ho
    change IsOpen ((fun x : U => @Quotient.mk' C.Carrier P.gluing.setoid x.val) '' A)
    simpa only [Set.image_image, Function.comp_def] using hopen

end GC.GraphManifold.TorusPairing

import DifferentialGeometry.Topology.Manifold.Attachment.AdjunctionInjectivity
import DifferentialGeometry.Topology.Attachment.Basic
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace DifferentialGeometry.Topology
namespace DifferentialGeometry.Topology.Manifold.Attachment
variable {A B X : Type*}

private theorem saturation_inl (i : A → B) (φ : A → X) (hi : Injective i) (hφ : Injective φ)
    (s : Set (B ⊕ X)) :
    Sum.inl ⁻¹' (adjunctionMk i φ ⁻¹' (adjunctionMk i φ '' s)) =
      (Sum.inl ⁻¹' s) ∪ i '' (φ ⁻¹' (Sum.inr ⁻¹' s)) := by
  ext b
  constructor
  · rintro ⟨p, hp, he⟩
    cases p with
    | inl c =>
      have hc := adjunctionCell_injective i φ hi hφ he
      exact Or.inl (hc ▸ hp)
    | inr x =>
      obtain ⟨a, ha, hx⟩ := (adjunctionCell_eq_lower_iff i φ hi b x).mp he.symm
      refine Or.inr ⟨a, ?_, ha⟩
      change Sum.inr (φ a) ∈ s
      rw [hx]
      exact hp
  · rintro (hb | ⟨a, ha, rfl⟩)
    · exact ⟨Sum.inl b, hb, rfl⟩
    · exact ⟨Sum.inr (φ a), ha, (adjunction_coherence i φ a).symm⟩

private theorem saturation_inr (i : A → B) (φ : A → X) (hi : Injective i)
    (s : Set (B ⊕ X)) :
    Sum.inr ⁻¹' (adjunctionMk i φ ⁻¹' (adjunctionMk i φ '' s)) =
      (Sum.inr ⁻¹' s) ∪ φ '' (i ⁻¹' (Sum.inl ⁻¹' s)) := by
  ext x
  constructor
  · rintro ⟨p, hp, he⟩
    cases p with
    | inl b =>
      obtain ⟨a, ha, hx⟩ := (adjunctionCell_eq_lower_iff i φ hi b x).mp he
      refine Or.inr ⟨a, ?_, hx⟩
      change Sum.inl (i a) ∈ s
      rw [ha]
      exact hp
    | inr y =>
      have hy := adjunctionLower_injective i φ hi he
      exact Or.inl (hy ▸ hp)
  · rintro (hx | ⟨a, ha, rfl⟩)
    · exact ⟨Sum.inr x, hx, rfl⟩
    · exact ⟨Sum.inl (i a), ha, adjunction_coherence i φ a⟩

theorem adjunctionMk_finite_fiber (i : A → B) (φ : A → X) (hi : Injective i) (hφ : Injective φ)
    (q : AdjunctionSpace i φ) : (adjunctionMk i φ ⁻¹' {q}).Finite := by
  apply finite_preimage_inl_and_inr.mp
  change (adjunctionCell i φ ⁻¹' {q}).Finite ∧ (adjunctionLower (i := i) φ ⁻¹' {q}).Finite
  exact ⟨(finite_singleton q).preimage (adjunctionCell_injective i φ hi hφ).injOn,
    (finite_singleton q).preimage (adjunctionLower_injective i φ hi).injOn⟩

variable [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X]
variable [CompactSpace A] [T2Space B] [T2Space X]

theorem isClosedMap_adjunctionMk (i : A → B) (φ : A → X)
    (hi : Injective i) (hφ : Injective φ) (hci : Continuous i) (hcφ : Continuous φ) :
    IsClosedMap (adjunctionMk i φ) := by
  intro s hs
  apply (isQuotientMap_adjunctionMk i φ).isCoinducing.isClosed_preimage.mp
  apply isClosed_sum_iff.mpr
  rw [saturation_inl i φ hi hφ s, saturation_inr i φ hi s]
  exact ⟨(hs.preimage continuous_inl).union
    (((hs.preimage continuous_inr).preimage hcφ).isCompact.image hci).isClosed,
    (hs.preimage continuous_inr).union
    (((hs.preimage continuous_inl).preimage hci).isCompact.image hcφ).isClosed⟩

theorem adjunction_t2Space (i : A → B) (φ : A → X)
    (hi : Injective i) (hφ : Injective φ) (hci : Continuous i) (hcφ : Continuous φ) :
    T2Space (AdjunctionSpace i φ) := by
  let f := adjunctionMk i φ
  have hclosed := isClosedMap_adjunctionMk i φ hi hφ hci hcφ
  have hsurj := (isQuotientMap_adjunctionMk i φ).surjective
  refine ⟨fun x y hxy => ?_⟩
  have hd : Disjoint (f ⁻¹' {x}) (f ⁻¹' {y}) := by
    apply disjoint_left.mpr
    intro p hp hq
    exact hxy (hp.symm.trans hq)
  obtain ⟨u, v, hu, hv, hxu, hyv, huv⟩ := SeparatedNhds.of_isCompact_isCompact
    (adjunctionMk_finite_fiber i φ hi hφ x).isCompact
    (adjunctionMk_finite_fiber i φ hi hφ y).isCompact hd
  refine ⟨kernImage f u, kernImage f v, isClosedMap_iff_kernImage.mp hclosed hu,
    isClosedMap_iff_kernImage.mp hclosed hv, ?_, ?_, ?_⟩
  · intro p hp
    exact hxu hp
  · intro p hp
    exact hyv hp
  · apply disjoint_left.mpr
    intro q hq hr
    obtain ⟨p, rfl⟩ := hsurj q
    exact disjoint_left.mp huv (hq rfl) (hr rfl)

theorem isClosedEmbedding_adjunctionCell (i : A → B) (φ : A → X)
    (hi : Injective i) (hφ : Injective φ) (hci : Continuous i) (hcφ : Continuous φ) :
    _root_.Topology.IsClosedEmbedding (adjunctionCell i φ) :=
  _root_.Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_adjunctionCell i φ) (adjunctionCell_injective i φ hi hφ)
      ((isClosedMap_adjunctionMk i φ hi hφ hci hcφ).comp isClosedMap_inl)

theorem isClosedEmbedding_adjunctionLower (i : A → B) (φ : A → X)
    (hi : Injective i) (hφ : Injective φ) (hci : Continuous i) (hcφ : Continuous φ) :
    _root_.Topology.IsClosedEmbedding (adjunctionLower (i := i) φ) :=
  _root_.Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_adjunctionLower i φ) (adjunctionLower_injective i φ hi)
      ((isClosedMap_adjunctionMk i φ hi hφ hci hcφ).comp isClosedMap_inr)
end DifferentialGeometry.Topology.Manifold.Attachment

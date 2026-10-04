import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions

/-! ZSP05 (master207B, B:6597): the remaining carrier after zero and slim removal, as a
point-set kernel. `M₁ = M \ int Z`, the slim piece `S ⊆ M₁` is a regular closed set that contains
its relative collar along `∂M₁` (ZSP04's (SF)), and `M₂ = M₁ \ int_{M₁} S` uses the RELATIVE
interior (subtype topology on `M₁`). Faces are topological frontiers in `M`. -/

set_option autoImplicit false
open Set

namespace DifferentialGeometry.Topology

theorem mem_image_interior_preimage_val_iff {M : Type*} [TopologicalSpace M] {A S : Set M}
    {x : M} :
    x ∈ (Subtype.val '' interior (Subtype.val ⁻¹' S : Set A)) ↔
      x ∈ A ∧ ∃ O : Set M, IsOpen O ∧ x ∈ O ∧ O ∩ A ⊆ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_interior] at hy
    obtain ⟨t, hts, ht, hyt⟩ := hy
    obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.mp ht
    refine ⟨y.2, O, hO, hyt, ?_⟩
    rintro z ⟨hzO, hzA⟩
    exact hts (show (⟨z, hzA⟩ : A) ∈ Subtype.val ⁻¹' O from hzO)
  · rintro ⟨hxA, O, hO, hxO, hOA⟩
    refine ⟨⟨x, hxA⟩, ?_, rfl⟩
    rw [mem_interior]
    refine ⟨Subtype.val ⁻¹' O, fun z hz => hOA ⟨hz, z.2⟩, hO.preimage continuous_subtype_val, hxO⟩

/-- ZSP05 (RC)/(RF) kernel. -/
theorem relative_interior_removal {M : Type*} [TopologicalSpace M] (Z S : Set M)
    (hSM : S ⊆ (interior Z)ᶜ) (hreg : closure (interior S) = S)
    (hcollar : S ∩ frontier (interior Z)ᶜ ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' S : Set ↥(interior Z)ᶜ)) :
    let M₁ : Set M := (interior Z)ᶜ
    let M₂ : Set M := M₁ \ Subtype.val '' interior (Subtype.val ⁻¹' S : Set M₁)
    IsClosed M₂ ∧ Z ∪ S ∪ M₂ = univ ∧
      frontier M₂ = (frontier M₁ \ S) ∪ (frontier S \ frontier M₁) ∧
      Disjoint (frontier M₁ \ S) (frontier S \ frontier M₁) ∧
      S ∩ M₂ = frontier S \ frontier M₁ ∧
      Disjoint (interior Z) (interior S) ∧ Disjoint (interior S) (interior M₂) ∧
      Disjoint (interior Z) (interior M₂) := by
  intro M₁ M₂
  set rel : Set M := Subtype.val '' interior (Subtype.val ⁻¹' S : Set M₁) with hrel
  have hS : IsClosed S := hreg ▸ isClosed_closure
  have hM₁ : IsClosed M₁ := isOpen_interior.isClosed_compl
  have hrelS : rel ⊆ S := fun x hx => by
    obtain ⟨-, O, -, hxO, hOA⟩ := mem_image_interior_preimage_val_iff.mp hx
    obtain ⟨y, -, rfl⟩ := hx
    exact hOA ⟨hxO, y.2⟩
  have hrelM : rel ⊆ M₁ := fun x hx => (mem_image_interior_preimage_val_iff.mp hx).1
  have hintrel : interior S ⊆ rel := fun x hx =>
    mem_image_interior_preimage_val_iff.mpr
      ⟨hSM (interior_subset hx), interior S, isOpen_interior, hx,
        fun y hy => interior_subset hy.1⟩
  -- (5) the shared part of the slim piece and `M₂`
  have hfive : S ∩ M₂ = frontier S \ frontier M₁ := by
    ext x
    constructor
    · rintro ⟨hxS, hxM₁, hxrel⟩
      refine ⟨?_, fun hxf => hxrel (hcollar ⟨hxS, hxf⟩)⟩
      rw [hS.frontier_eq]
      exact ⟨hxS, fun hint => hxrel (hintrel hint)⟩
    · rintro ⟨hxf, hxf₁⟩
      rw [hS.frontier_eq] at hxf
      have hxM₁ : x ∈ M₁ := hSM hxf.1
      have hxint₁ : x ∈ interior M₁ := by
        by_contra h
        rw [hM₁.frontier_eq] at hxf₁
        exact hxf₁ ⟨hxM₁, h⟩
      refine ⟨hxf.1, hxM₁, fun hxrel => ?_⟩
      obtain ⟨-, O, hO, hxO, hOA⟩ := mem_image_interior_preimage_val_iff.mp hxrel
      apply hxf.2
      rw [mem_interior]
      exact ⟨O ∩ interior M₁, fun y hy => hOA ⟨hy.1, interior_subset hy.2⟩,
        hO.inter isOpen_interior, hxO, hxint₁⟩
  have hM₂closed : IsClosed M₂ := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro x hx
    by_cases hxM₁ : x ∈ M₁
    · have hxrel : x ∈ rel := by
        by_contra h
        exact hx ⟨hxM₁, h⟩
      obtain ⟨-, O, hO, hxO, hOA⟩ := mem_image_interior_preimage_val_iff.mp hxrel
      refine ⟨O, fun y hyO hyM₂ => hyM₂.2 ?_, hO, hxO⟩
      exact mem_image_interior_preimage_val_iff.mpr ⟨hyM₂.1, O, hO, hyO, hOA⟩
    · refine ⟨interior Z, fun y hy hyM₂ => hyM₂.1 hy, isOpen_interior, ?_⟩
      by_contra h
      exact hxM₁ h
  refine ⟨hM₂closed, ?_, ?_, ?_, hfive, ?_, ?_, ?_⟩
  · apply eq_univ_of_forall
    intro x
    by_cases hxZ : x ∈ Z
    · exact Or.inl (Or.inl hxZ)
    · have hxM₁ : x ∈ M₁ := fun hint => hxZ (interior_subset hint)
      by_cases hxrel : x ∈ rel
      · exact Or.inl (Or.inr (hrelS hxrel))
      · exact Or.inr ⟨hxM₁, hxrel⟩
  · ext x
    constructor
    · intro hx
      rw [hM₂closed.frontier_eq] at hx
      obtain ⟨hxM₂, hxint⟩ := hx
      by_cases hxf₁ : x ∈ frontier M₁
      · left
        exact ⟨hxf₁, fun hxS => hxM₂.2 (hcollar ⟨hxS, hxf₁⟩)⟩
      · right
        have hxint₁ : x ∈ interior M₁ := by
          by_contra h
          rw [hM₁.frontier_eq] at hxf₁
          exact hxf₁ ⟨hxM₂.1, h⟩
        by_cases hxS : x ∈ S
        · rw [← hfive]
          exact ⟨hxS, hxM₂⟩
        · exfalso
          apply hxint
          rw [mem_interior]
          refine ⟨interior M₁ ∩ Sᶜ, fun y hy => ⟨interior_subset hy.1, fun hyrel => hy.2 (hrelS hyrel)⟩,
            isOpen_interior.inter hS.isOpen_compl, hxint₁, hxS⟩
    · rintro (⟨hxf₁, hxS⟩ | hx)
      · rw [hM₁.frontier_eq] at hxf₁
        rw [hM₂closed.frontier_eq]
        exact ⟨⟨hxf₁.1, fun hrel' => hxS (hrelS hrel')⟩,
          fun hint => hxf₁.2 (interior_mono sdiff_subset hint)⟩
      · have hxSM₂ : x ∈ S ∩ M₂ := by rw [hfive]; exact hx
        rw [hM₂closed.frontier_eq]
        refine ⟨hxSM₂.2, fun hint => ?_⟩
        have hcl : x ∈ closure (interior S) := by rw [hreg]; exact hxSM₂.1
        obtain ⟨y, hy₁, hy₂⟩ := mem_closure_iff.mp hcl (interior M₂) isOpen_interior hint
        exact (interior_subset hy₁).2 (hintrel hy₂)
  · exact Set.disjoint_left.mpr fun x hx hx' => hx'.2 hx.1
  · exact Set.disjoint_left.mpr fun x hxZ hxS => hSM (interior_subset hxS) hxZ
  · exact Set.disjoint_left.mpr fun x hxS hxM₂ => (interior_subset hxM₂).2 (hintrel hxS)
  · exact Set.disjoint_left.mpr fun x hxZ hxM₂ => (interior_subset hxM₂).1 hxZ

theorem isCompact_relative_interior_removal {M : Type*} [TopologicalSpace M] [CompactSpace M]
    (Z S : Set M) :
    IsCompact ((interior Z)ᶜ \
      Subtype.val '' interior (Subtype.val ⁻¹' S : Set ↥(interior Z)ᶜ)) := by
  apply IsClosed.isCompact
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  by_cases hxM₁ : x ∈ (interior Z)ᶜ
  · have hxrel : x ∈ Subtype.val '' interior (Subtype.val ⁻¹' S : Set ↥(interior Z)ᶜ) := by
      by_contra h
      exact hx ⟨hxM₁, h⟩
    obtain ⟨-, O, hO, hxO, hOA⟩ := mem_image_interior_preimage_val_iff.mp hxrel
    refine ⟨O, fun y hyO hyM₂ => hyM₂.2 ?_, hO, hxO⟩
    exact mem_image_interior_preimage_val_iff.mpr ⟨hyM₂.1, O, hO, hyO, hOA⟩
  · refine ⟨interior Z, fun y hy hyM₂ => hyM₂.1 hy, isOpen_interior, ?_⟩
    by_contra h
    exact hxM₁ h

end DifferentialGeometry.Topology

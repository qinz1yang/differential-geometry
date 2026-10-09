import DifferentialGeometry.Topology.Maps.RelativeInteriorRemoval

/-!
# FDC03/FDC04 point-set kernel: the third relative removal and the four-piece cover

Blueprint `master207B.tex`, FDC03 (B:7285–7308, (Last) `M₃ = M₂ \ int_{M₂} M^edge`,
(LastFaces) `M₂ = M^edge ∪ M₃`, `M^edge ∩ M₃ = V_e`) and FDC04 (B:7367–7383: the domains
`Z, M^slim, M^edge, M^{2-stratum}` "cover the carrier, and have disjoint ambient interiors";
"Combine (RF) and (LastFaces) for the union and every complement identity"). Point-set form, after
ZSP05's kernel `relative_interior_removal` (`M₁ = M \ int Z`, `M₂ = M₁ \ int_{M₁} S`, RELATIVE
interiors in the subtype topology):

* `relative_removal_third_FDC`: for a closed `A ⊆ M₂` and `M₃ = M₂ \ int_{M₂} A`: `M₃` is closed,
  `M₂ = A ∪ M₃`, `A ∩ M₃ = A \ int_{M₂} A` (the relative frontier: FDC03's vertical face `V_e`),
  `Z ∪ S ∪ A ∪ M₃ = M`, and the six pairs among `int Z, int S, int A, int M₃` are disjoint.
* `isCompact_relative_removal_third_FDC`: in a compact space `M₃` is compact.
-/

set_option autoImplicit false
open Set

namespace DifferentialGeometry.Topology

/-- **The third relative removal and the four-piece cover** (FDC03 (Last)/(LastFaces), FDC04's
cover and disjoint interiors, point-set form). -/
theorem relative_removal_third_FDC {M : Type*} [TopologicalSpace M] (Z S A M₁ M₂ M₃ : Set M)
    (hM₁ : M₁ = (interior Z)ᶜ)
    (hM₂ : M₂ = M₁ \ Subtype.val '' interior (Subtype.val ⁻¹' S : Set M₁))
    (hM₃ : M₃ = M₂ \ Subtype.val '' interior (Subtype.val ⁻¹' A : Set M₂))
    (hSM : S ⊆ (interior Z)ᶜ) (hreg : closure (interior S) = S)
    (hcollar : S ∩ frontier (interior Z)ᶜ ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' S : Set ↥(interior Z)ᶜ))
    (hA : A ⊆ M₂) :
    IsClosed M₃ ∧ M₂ = A ∪ M₃ ∧
      A ∩ M₃ = A \ Subtype.val '' interior (Subtype.val ⁻¹' A : Set M₂) ∧
      Z ∪ S ∪ A ∪ M₃ = univ ∧
      Disjoint (interior Z) (interior S) ∧ Disjoint (interior Z) (interior A) ∧
      Disjoint (interior Z) (interior M₃) ∧ Disjoint (interior S) (interior A) ∧
      Disjoint (interior S) (interior M₃) ∧ Disjoint (interior A) (interior M₃) := by
  have hzsp := relative_interior_removal Z S hSM hreg hcollar
  obtain ⟨hM₂c, hcov, -, -, -, hZS, -, -⟩ := hzsp
  rw [← hM₁] at hM₂c hcov
  rw [← hM₂] at hM₂c hcov
  set rel : Set M := Subtype.val '' interior (Subtype.val ⁻¹' A : Set M₂) with hrel
  have hrelA : rel ⊆ A := fun x hx => by
    obtain ⟨-, O, -, hxO, hOA⟩ := mem_image_interior_preimage_val_iff.mp hx
    obtain ⟨y, -, rfl⟩ := hx
    exact hOA ⟨hxO, y.2⟩
  have hM₃M₂ : M₃ ⊆ M₂ := by
    rw [hM₃]
    exact sdiff_subset
  have hM₂M₁ : M₂ ⊆ M₁ := by
    rw [hM₂]
    exact sdiff_subset
  -- interiors inside `M₂` are relative interiors
  have hintA : interior A ⊆ rel := fun x hx =>
    mem_image_interior_preimage_val_iff.mpr
      ⟨hA (interior_subset hx), interior A, isOpen_interior, hx,
        fun y hy => interior_subset hy.1⟩
  have hintS : ∀ x ∈ interior S, x ∉ M₂ := by
    intro x hx hxM₂
    have hxM₁ := hM₂M₁ hxM₂
    rw [hM₂] at hxM₂
    apply hxM₂.2
    exact mem_image_interior_preimage_val_iff.mpr
      ⟨hxM₁, interior S, isOpen_interior, hx, fun y hy => interior_subset hy.1⟩
  have hintZ : ∀ x ∈ interior Z, x ∉ M₂ := by
    intro x hx hxM₂
    have hxM₁ := hM₂M₁ hxM₂
    rw [hM₁] at hxM₁
    exact hxM₁ hx
  -- `M₂ = A ∪ M₃`
  have hunion : M₂ = A ∪ M₃ := by
    ext x
    constructor
    · intro hx
      by_cases hxr : x ∈ rel
      · exact Or.inl (hrelA hxr)
      · right
        rw [hM₃]
        exact ⟨hx, hxr⟩
    · rintro (hx | hx)
      · exact hA hx
      · exact hM₃M₂ hx
  -- `M₃` is closed
  have hM₃c : IsClosed M₃ := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro x hx
    by_cases hxM₂ : x ∈ M₂
    · have hxr : x ∈ rel := by
        by_contra h
        apply hx
        rw [hM₃]
        exact ⟨hxM₂, h⟩
      obtain ⟨-, O, hO, hxO, hOA⟩ := mem_image_interior_preimage_val_iff.mp hxr
      refine ⟨O, fun y hyO hyM₃ => ?_, hO, hxO⟩
      have hyM₂ := hM₃M₂ hyM₃
      rw [hM₃] at hyM₃
      exact hyM₃.2 (mem_image_interior_preimage_val_iff.mpr ⟨hyM₂, O, hO, hyO, hOA⟩)
    · refine ⟨M₂ᶜ, fun y hy hyM₃ => hy (hM₃M₂ hyM₃), hM₂c.isOpen_compl, hxM₂⟩
  refine ⟨hM₃c, hunion, ?_, ?_, hZS, ?_, ?_, ?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨hxA, hxM₃⟩
      rw [hM₃] at hxM₃
      exact ⟨hxA, hxM₃.2⟩
    · rintro ⟨hxA, hxr⟩
      refine ⟨hxA, ?_⟩
      rw [hM₃]
      exact ⟨hA hxA, hxr⟩
  · rw [eq_univ_iff_forall]
    intro x
    have hx : x ∈ Z ∪ S ∪ M₂ := by
      rw [hcov]
      exact mem_univ x
    rcases hx with (hx | hx) | hx
    · exact Or.inl (Or.inl (Or.inl hx))
    · exact Or.inl (Or.inl (Or.inr hx))
    · rw [hunion] at hx
      rcases hx with hx | hx
      · exact Or.inl (Or.inr hx)
      · exact Or.inr hx
  · exact Set.disjoint_left.mpr fun x hxZ hxA => hintZ x hxZ (hA (interior_subset hxA))
  · exact Set.disjoint_left.mpr fun x hxZ hxM₃ =>
      hintZ x hxZ (hM₃M₂ (interior_subset hxM₃))
  · exact Set.disjoint_left.mpr fun x hxS hxA => hintS x hxS (hA (interior_subset hxA))
  · exact Set.disjoint_left.mpr fun x hxS hxM₃ =>
      hintS x hxS (hM₃M₂ (interior_subset hxM₃))
  · refine Set.disjoint_left.mpr fun x hxA hxM₃ => ?_
    have hx3 := interior_subset hxM₃
    rw [hM₃] at hx3
    exact hx3.2 (hintA hxA)

/-- **The remainder `M₃` is compact** in a compact space. -/
theorem isCompact_relative_removal_third_FDC {M : Type*} [TopologicalSpace M] [CompactSpace M]
    (Z S A M₁ M₂ M₃ : Set M) (hM₁ : M₁ = (interior Z)ᶜ)
    (hM₂ : M₂ = M₁ \ Subtype.val '' interior (Subtype.val ⁻¹' S : Set M₁))
    (hM₃ : M₃ = M₂ \ Subtype.val '' interior (Subtype.val ⁻¹' A : Set M₂))
    (hSM : S ⊆ (interior Z)ᶜ) (hreg : closure (interior S) = S)
    (hcollar : S ∩ frontier (interior Z)ᶜ ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' S : Set ↥(interior Z)ᶜ))
    (hA : A ⊆ M₂) : IsCompact M₃ :=
  (relative_removal_third_FDC Z S A M₁ M₂ M₃ hM₁ hM₂ hM₃ hSM hreg hcollar hA).1.isCompact

end DifferentialGeometry.Topology

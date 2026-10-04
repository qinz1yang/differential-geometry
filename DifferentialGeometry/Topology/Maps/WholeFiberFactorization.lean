import DifferentialGeometry.Topology.Maps.CompactFullPreimage

/-! GAF07 (master207B, B:6049): the point-set parts of the proper whole circle/slim bundles.
The restriction of a global continuous map on a compact carrier to the FULL preimage of a base
set is proper (X63's CompactFullPreimage) and onto when every base point has a preimage; WHOLE
fibres agree under an injective later factorization and under an injective base coordinate. -/

set_option autoImplicit false
open Set Function

namespace DifferentialGeometry.Topology

theorem isProperMap_and_surjective_restrictPreimage_of_compact {M H : Type*}
    [TopologicalSpace M] [CompactSpace M] [TopologicalSpace H] [T2Space H]
    (f : M → H) (hf : Continuous f) (A : Set H) (hA : A ⊆ range f) :
    IsProperMap (A.restrictPreimage f) ∧ Surjective (A.restrictPreimage f) := by
  refine ⟨isProperMap_restrictPreimage_of_compact f hf A, ?_⟩
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := hA hy
  exact ⟨⟨x, hy⟩, rfl⟩

/-- Whole stage fibre = whole final fibre: `g = Θ ∘ f` wherever `f` lands in `V`, `Θ` is injective
on `V`, and every final preimage of `Θ y` has stage image in `V` (GAF06 + CGP08). -/
theorem preimage_singleton_eq_of_injOn_factor {M Y Z : Type*} (f : M → Y) (g : M → Z)
    (Θ : Y → Z) (V : Set Y) (hinj : InjOn Θ V) (hfac : ∀ p, f p ∈ V → g p = Θ (f p))
    {y : Y} (hy : y ∈ V) (hloc : ∀ p, g p = Θ y → f p ∈ V) :
    g ⁻¹' {Θ y} = f ⁻¹' {y} := by
  ext p
  simp only [mem_preimage, mem_singleton_iff]
  constructor
  · intro hp
    have hV := hloc p hp
    exact hinj hV hy ((hfac p hV).symm.trans hp)
  · intro hp
    rw [← hp]
    exact hfac p (hp ▸ hy)

/-- Whole final fibre = level set of the coordinate family on the original chart: every preimage
of `w` lies in `Y`, `g` maps `Y` into the marked patch `V`, and the coordinate `κ` is injective on
`V` (GAF05). -/
theorem preimage_singleton_eq_inter_coordinate {M Z A : Type*} (g : M → Z) (κ : Z → A)
    (Y : Set M) (V : Set Z) (hinj : InjOn κ V) {w : Z} (hw : w ∈ V)
    (hYV : ∀ p ∈ Y, g p ∈ V) (hloc : ∀ p, g p = w → p ∈ Y) :
    g ⁻¹' {w} = Y ∩ (κ ∘ g) ⁻¹' {κ w} := by
  ext p
  simp only [mem_preimage, mem_singleton_iff, mem_inter_iff, comp_apply]
  constructor
  · intro hp
    exact ⟨hloc p hp, by rw [hp]⟩
  · rintro ⟨hpY, hp⟩
    exact hinj (hYV p hpY) hw hp

end DifferentialGeometry.Topology

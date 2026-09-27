import DifferentialGeometry.Topology.Homology.Relative.Map

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology Set
namespace DifferentialGeometry.Homology
universe u
variable {X Y : TopCat.{u}} {s : Set X} {t : Set Y}
  {k : Type u} [Ring k] (R : ModuleCat.{u} k)

theorem relativeChainMap_eq_zero_of_range_subset (f : X ⟶ Y) (hf : MapsTo f s t)
    (h : range f ⊆ t) : relativeChainMap R f hf = 0 := by
  let g : X ⟶ TopCat.of t := TopCat.ofHom ⟨fun x => ⟨f x, h (mem_range_self x)⟩,
    f.hom.continuous.subtype_mk _⟩
  have he : f = g ≫ (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(t,Y))) := rfl
  have : Epi (relativeProjection X s R) := inferInstanceAs (Epi (cokernel.π _))
  apply (cancel_epi (relativeProjection X s R)).mp
  rw [relativeProjection_chainMap,he,Functor.map_comp,Category.assoc,comp_zero]
  change _ ≫ relativeInclusion Y t R ≫ relativeProjection Y t R = 0
  rw [show relativeInclusion Y t R ≫ relativeProjection Y t R = 0 from cokernel.condition _,comp_zero]


theorem relativeHomologyMap_eq_zero_of_range_subset (f : X ⟶ Y) (hf : MapsTo f s t)
    (h : range f ⊆ t) (n : ℕ) : relativeHomologyMap R f hf n = 0 := by
  unfold relativeHomologyMap
  rw [relativeChainMap_eq_zero_of_range_subset R f hf h]
  exact (_root_.HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.down ℕ) n).map_zero _ _
end DifferentialGeometry.Homology

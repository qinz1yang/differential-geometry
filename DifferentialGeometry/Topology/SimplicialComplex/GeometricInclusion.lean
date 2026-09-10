import DifferentialGeometry.Topology.SimplicialComplex.GeometricRealizationMap
import DifferentialGeometry.Topology.SimplicialComplex.OrderedMaps

set_option autoImplicit false
noncomputable section
open CategoryTheory Simplicial
namespace Poincare.Topology.SimplicialComplex
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]
  {K L : Geometry.SimplicialComplex ℝ E}

omit [LinearOrder E] in
theorem geometricSpace_mono (h : K ≤ L) : K.space ⊆ L.space := by
  intro x hx
  obtain ⟨s, hs, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
  exact Geometry.SimplicialComplex.mem_space_iff.mpr ⟨s, h hs, hx⟩


def geometricInclusion (h : K ≤ L) : TopCat.of K.space ⟶ TopCat.of L.space :=
  TopCat.ofHom ⟨Set.inclusion (geometricSpace_mono h), continuous_subtype_val.subtype_mk _⟩

omit [LinearOrder E] in
@[simp]
theorem geometricInclusion_val (h : K ≤ L) (x : K.space) :
    (geometricInclusion h x : E) = x := rfl


@[reassoc]
theorem geometricSingularMap_inclusion (h : K ≤ L) :
    orderedInclusion h ≫ geometricSingularMap L =
      geometricSingularMap K ≫ TopCat.toSSet.map (geometricInclusion h) := by
  ext n s
  apply (TopCat.toSSetObjEquiv (TopCat.of L.space) n).injective
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  rfl

@[reassoc]
theorem geometricRealizationMap_inclusion (h : K ≤ L) :
    SSet.toTop.map (orderedInclusion h) ≫ geometricRealizationMap L =
      geometricRealizationMap K ≫ geometricInclusion h := by
  apply (sSetTopAdj.homEquiv _ _).injective
  rw [sSetTopAdj.homEquiv_naturality_left, sSetTopAdj.homEquiv_naturality_right]
  simp only [geometricRealizationMap, Equiv.apply_symm_apply]
  exact geometricSingularMap_inclusion h

end Poincare.Topology.SimplicialComplex

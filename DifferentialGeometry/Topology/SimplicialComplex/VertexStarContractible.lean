import DifferentialGeometry.Topology.SimplicialComplex.VertexStar
import DifferentialGeometry.Topology.Homology.EulerCharacteristic
import Mathlib.Analysis.Convex.Contractible

set_option autoImplicit false
noncomputable section
open Set

namespace Poincare.Topology.SimplicialComplex

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]
  (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (p : E) (hp : {p} ∈ K.faces)

include hp


theorem vertex_mem_openStar : p ∈ vertexOpenStar K p := by
  apply (vertexHeight_pos_iff K p ⟨p, Geometry.SimplicialComplex.vertices_subset_space hp⟩).mp
  rw [(vertexHeight_eq_one_iff K p hp _).mpr rfl]
  exact zero_lt_one


theorem starConvex_vertexOpenStar : StarConvex ℝ p (vertexOpenStar K p) := by
  intro x hx a b ha hb hab
  obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx.1
  have hps : p ∈ s := by
    by_contra h
    exact hx.2 (Geometry.SimplicialComplex.mem_space_iff.mpr
      ⟨s, ⟨hs, by simpa only [Finset.singleton_subset_iff] using h⟩, hxs⟩)
  have hph : p ∈ convexHull ℝ (s : Set E) := subset_convexHull ℝ _ hps
  let pp : K.space := ⟨p, Geometry.SimplicialComplex.vertices_subset_space hp⟩
  let xx : K.space := ⟨x, hx.1⟩
  have hc : a • p + b • x ∈ K.space :=
    Geometry.SimplicialComplex.convexHull_subset_space hs
      ((convex_convexHull ℝ (s : Set E)) hph hxs ha hb hab)
  have hpp : vertexHeight K p pp = 1 := (vertexHeight_eq_one_iff K p hp pp).mpr rfl
  have hxx : 0 < vertexHeight K p xx := (vertexHeight_pos_iff K p xx).mpr hx
  have hv := vertexFunction_combo K (fun q ↦ if q = p then 1 else 0)
    hs pp xx hph hxs ha hb hab
  change vertexHeight K p ⟨a • p + b • x, _⟩ =
    a * vertexHeight K p pp + b * vertexHeight K p xx at hv
  rw [hpp, mul_one] at hv
  apply (vertexHeight_pos_iff K p ⟨_, hc⟩).mp
  rw [hv]
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by simpa only [hb0, add_zero] using hab
    rw [hb0, ha1, zero_mul, add_zero]
    exact zero_lt_one
  · exact add_pos_of_nonneg_of_pos ha (mul_pos (lt_of_le_of_ne hb (Ne.symm hb0)) hxx)


def vertexOpenStarContraction :
    ContinuousMap.Homotopy (ContinuousMap.id (vertexOpenStar K p))
      (ContinuousMap.const (vertexOpenStar K p) ⟨p, vertex_mem_openStar K p hp⟩) where
  toFun z := ⟨z.1.val • p + (1 - z.1.val) • z.2.val,
    starConvex_vertexOpenStar K p hp z.2.prop z.1.prop.1
      (sub_nonneg.mpr z.1.prop.2) (add_sub_cancel _ _)⟩
  continuous_toFun :=
    (((continuous_subtype_val.comp continuous_fst).smul continuous_const).add
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left x := by
    apply Subtype.ext
    simp
  map_one_left x := by
    apply Subtype.ext
    simp


@[simp]
theorem vertexOpenStarContraction_apply (t : unitInterval) (x : vertexOpenStar K p) :
    (vertexOpenStarContraction K p hp (t, x)).val =
      t.val • p + (1 - t.val) • x.val := rfl


theorem contractibleSpace_vertexOpenStar : ContractibleSpace (vertexOpenStar K p) :=
  (starConvex_vertexOpenStar K p hp).contractibleSpace ⟨p, vertex_mem_openStar K p hp⟩


theorem finiteHomologyType_vertexOpenStar (k : Type u) [Field k] :
    Poincare.Homology.finiteHomologyType k (TopCat.of (vertexOpenStar K p)) := by
  let := contractibleSpace_vertexOpenStar K p hp
  exact Poincare.Homology.finiteHomologyType_of_contractible k


theorem eulerChar_vertexOpenStar (k : Type u) [Field k] :
    Poincare.Homology.eulerChar k (TopCat.of (vertexOpenStar K p)) = 1 := by
  let := contractibleSpace_vertexOpenStar K p hp
  exact Poincare.Homology.eulerChar_of_contractible k

end Poincare.Topology.SimplicialComplex

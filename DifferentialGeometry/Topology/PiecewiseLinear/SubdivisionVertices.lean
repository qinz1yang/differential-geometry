/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.IsomorphicSubdivision

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_isSubdivision_forall_singleton_mem [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {ι : Type*} [Finite ι] (x : ι → E)
    (hx : ∀ i, x i ∈ K.space) :
    ∃ K' : Geometry.SimplicialComplex ℝ E, IsSubdivision K' K ∧ K'.faces.Finite ∧
      K'.space = K.space ∧ ∀ i, ({x i} : Finset E) ∈ K'.faces := by
  classical
  have hpoly : ∀ i, IsPolyhedron ({x i} : Set E) := by
    intro i
    have hsub : Subsingleton {u // u ∈ ({x i} : Finset E)} :=
      ⟨fun a b => Subtype.ext ((Finset.mem_singleton.mp a.2).trans
        (Finset.mem_singleton.mp b.2).symm)⟩
    have h := isPolyhedron_convexHull_of_affineIndependent ({x i} : Finset E)
      (affineIndependent_of_subsingleton ℝ _)
    rwa [Finset.coe_singleton, convexHull_singleton] at h
  obtain ⟨K', hsub, hfin, hunion⟩ := exists_isSubdivision_subcomplexes K
    (fun i => ({x i} : Set E)) hpoly fun i => singleton_subset_iff.mpr (hx i)
  refine ⟨K', hsub, hfin, hsub.space_eq, ?_⟩
  intro i
  have hxmem : x i ∈ ({x i} : Set E) := rfl
  obtain ⟨s, ⟨hs, hsx⟩, -⟩ := mem_iUnion₂.mp ((hunion i).subset hxmem)
  have hmem : ∀ w ∈ s, w = x i := fun w hw =>
    Set.mem_singleton_iff.mp (hsx (subset_convexHull ℝ _ (Finset.mem_coe.mpr hw)))
  obtain ⟨v, hv⟩ := K'.nonempty_of_mem_faces hs
  have hseq : s = {x i} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hmem v hv ▸ hv, hmem⟩
  exact hseq ▸ hs

end DifferentialGeometry.Topology.PiecewiseLinear

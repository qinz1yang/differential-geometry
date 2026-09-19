/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ArcDerivedNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.FrontierBoundary

/-!
# Ball neighborhoods of interior simplicial arcs
-/

open Set Filter

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem arcComplexIn_space_subset_interior_of_interior_faces [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hn : Module.finrank ℝ E = 3) (hK : IsCombinatorialManifoldWithBoundary 3 K)
    {n : ℕ} {v : ℕ → E}
    (hinterior : ∀ j ≤ 2 * n, arcChainFace v j ∉ (boundaryComplex 3 K).faces) :
    (arcComplexIn K v n).space ⊆ interior K.space := by
  intro x hx
  have hxK : x ∈ K.space :=
    space_mono_of_faces_subset (arcComplexIn_faces_subset K v n) hx
  apply (mem_interior_iff_notMem_frontier hxK).mpr
  rw [frontier_space_eq_boundaryComplex_space_of_finrank (n := 2) hn K hK]
  intro hxB
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex (arcComplexIn K v n) hx
  obtain ⟨hsK, j, hj, rfl⟩ := hs
  exact notMem_space_of_notMem_faces (boundaryComplex_faces_subset 3 K) hsK
    (hinterior j hj) hxs hxB

open Classical in
theorem arcComplexIn_space_subset_interior_derivedNeighborhood_of_interior_faces
    [FiniteDimensional ℝ E] {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hn : Module.finrank ℝ E = 3) (hK : IsCombinatorialManifoldWithBoundary 3 K)
    {n : ℕ} {v : ℕ → E}
    (hinterior : ∀ j ≤ 2 * n, arcChainFace v j ∉ (boundaryComplex 3 K).faces) :
    (arcComplexIn K v n).space ⊆
      interior (PiecewiseLinear.derivedNeighborhood K (arcComplexIn K v n)).space := by
  intro x hx
  have hxint := arcComplexIn_space_subset_interior_of_interior_faces hn hK hinterior hx
  have hKn : K.space ∈ nhds x := mem_interior_iff_mem_nhds.mp hxint
  obtain ⟨U, hU, hUsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp
    (derivedNeighborhood_mem_nhdsWithin (arcComplexIn_faces_subset K v n) hx)
  apply mem_interior_iff_mem_nhds.mpr
  exact mem_of_superset (inter_mem hU hKn) hUsub

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isPLBall_neighborhood_arcComplexIn
    [FiniteDimensional ℝ E] {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hn : Module.finrank ℝ E = 3)
    {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    (hinj : ∀ i ≤ n, ∀ j ≤ n, v i = v j → i = j)
    (hinterior : ∀ j ≤ 2 * n, arcChainFace v j ∉ (boundaryComplex 3 K).faces) :
    ∃ C : Set E, IsPLBall 3 C ∧ (arcComplexIn K v n).space ⊆ interior C ∧ C ⊆ K.space := by
  refine ⟨(PiecewiseLinear.derivedNeighborhood K (arcComplexIn K v n)).space,
    hK.isPLBall_derivedNeighborhood_arcComplexIn hvert hedge hinj, ?_,
    derivedNeighborhood_space_subset K (arcComplexIn K v n)⟩
  exact arcComplexIn_space_subset_interior_derivedNeighborhood_of_interior_faces
    hn hK hinterior

end DifferentialGeometry.Topology.PiecewiseLinear

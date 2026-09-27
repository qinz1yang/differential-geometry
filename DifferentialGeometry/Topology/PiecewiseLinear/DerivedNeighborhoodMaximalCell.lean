/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodCellFrontier

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem derivedNeighborhoodCell_inter_derivedNeighborhood_eq_boundaryComplex_of_maximal
    {n : ℕ} (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold (n + 2) K) (hLK : L.faces ⊆ K.faces)
    {s : Finset E} (hs : s ∈ K.faces) (hmax : ∀ t ∈ K.faces, s ⊆ t → s = t)
    (hsL : s ∉ L.faces)
    (hproper : ∀ t : Finset E, t.Nonempty → t ⊂ s → t ∈ L.faces) :
    (derivedNeighborhoodCell K s).space ∩ (derivedNeighborhood K L).space =
      (boundaryComplex (n + 2) (derivedNeighborhoodCell K s)).space := by
  classical
  rw [boundaryComplex_derivedNeighborhoodCell_space K hK hs,
    ← iUnion_derivedNeighborhoodCell_space K L hLK]
  apply Subset.antisymm
  · rintro x ⟨hxs, hxL⟩
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hxL
    exact ⟨hxs, mem_iUnion₂.mpr ⟨t, ⟨hLK ht, fun h => hsL (h ▸ ht)⟩, hxt⟩⟩
  · rintro x ⟨hxs, hxR⟩
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hxR
    have hts : t ⊆ s := by
      rcases subset_or_subset_of_nonempty_derivedNeighborhoodCell_inter K
        hs ht.1 ⟨x, hxs, hxt⟩ with h | h
      · exact (ht.2 (hmax t ht.1 h).symm).elim
      · exact h
    exact ⟨hxs, mem_iUnion₂.mpr ⟨t,
      hproper t (K.nonempty_of_mem_faces ht.1)
        (Finset.ssubset_iff_subset_ne.mpr ⟨hts, ht.2⟩), hxt⟩⟩

open Classical in
theorem exists_isPLHomeomorphOn_derivedNeighborhoodCell_maximal
    {n : ℕ} (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold (n + 2) K) (hLK : L.faces ⊆ K.faces)
    {s : Finset E} (hs : s ∈ K.faces) (hmax : ∀ t ∈ K.faces, s ⊆ t → s = t)
    (hsL : s ∉ L.faces)
    (hproper : ∀ t : Finset E, t.Nonempty → t ⊂ s → t ∈ L.faces) :
    ∃ g : (Fin (n + 3) → ℝ) → E,
      IsPLHomeomorphOn g (stdSimplex ℝ (Fin (n + 3)))
        (derivedNeighborhoodCell K s).space ∧
      IsPLHomeomorphOn g (stdSimplexBoundary (n + 2))
        ((derivedNeighborhoodCell K s).space ∩ (derivedNeighborhood K L).space) := by
  classical
  let C := derivedNeighborhoodCell K s
  let _ : Finite C.faces := (derivedNeighborhoodCell_faces_finite K s).to_subtype
  obtain ⟨g, hg⟩ := hK.isCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhoodCell hs
  have hB := boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex C hg
  rw [simplexBoundary_stdVertices_space] at hB
  refine ⟨g, hg, ?_⟩
  rw [derivedNeighborhoodCell_inter_derivedNeighborhood_eq_boundaryComplex_of_maximal
    K L hK hLK hs hmax hsL hproper]
  change IsPLHomeomorphOn g (stdSimplexBoundary (n + 2)) (boundaryComplex (n + 2) C).space
  rw [hB]
  have hpoly : IsPolyhedron (stdSimplexBoundary (n + 2)) := by
    rw [← simplexBoundary_stdVertices_space (n + 1)]
    exact (isPLSphere_simplexBoundary_std (n + 1)).isPolyhedron
  exact hg.restrict hpoly (fun _ hx => hx.1)

end DifferentialGeometry.Topology.PiecewiseLinear

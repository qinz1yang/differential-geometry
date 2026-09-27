/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedIntervalLink
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactResidualCells

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem closure_sdiff_derivedNeighborhood_inter_subcomplex
    (M A K L : Geometry.SimplicialComplex ℝ E) [Finite M.faces]
    (hAM : A.faces ⊆ M.faces) (hKA : K.faces ⊆ A.faces)
    (hLM : L.faces ⊆ M.faces) :
    closure (A.space \ (derivedNeighborhood A L).space) ∩ K.space =
      closure (K.space \ (derivedNeighborhood K L).space) := by
  have hKM := hKA.trans hAM
  let _ : Finite A.faces := ((Set.toFinite M.faces).subset hAM).to_subtype
  let _ : Finite K.faces := ((Set.toFinite M.faces).subset hKM).to_subtype
  rw [closure_space_sdiff_derivedNeighborhood_space hAM hLM,
    closure_space_sdiff_derivedNeighborhood_space hKM hLM]
  apply Subset.antisymm
  · rintro x ⟨hx, hxK⟩
    obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
    by_cases hsK : s ∈ K.faces
    · refine mem_iUnion₂.mpr ⟨s, ⟨hsK, hs.2⟩, ?_⟩
      rw [← derivedNeighborhoodCell_inter_subcomplex A K hKA hsK]
      exact ⟨hxs, hxK⟩
    · exact (disjoint_left.mp
        (derivedNeighborhoodCell_disjoint_subcomplex_of_not_mem A K hKA hs.1 hsK)
        hxs hxK).elim
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
    have hxMK : x ∈ (derivedNeighborhoodCell A s).space ∩ K.space := by
      rw [derivedNeighborhoodCell_inter_subcomplex A K hKA hs.1]
      exact hxs
    exact ⟨mem_iUnion₂.mpr ⟨s, ⟨hKA hs.1, hs.2⟩, hxMK.1⟩, hxMK.2⟩

end DifferentialGeometry.Topology.PiecewiseLinear

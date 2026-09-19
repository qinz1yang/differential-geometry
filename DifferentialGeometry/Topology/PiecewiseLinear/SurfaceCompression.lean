/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.FundamentalGroup.SimplyConnected
import DifferentialGeometry.Topology.PiecewiseLinear.NullhomotopyNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSimplyConnected

/-!
# Nontrivial surface loops in finite ambient neighborhoods
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifold.exists_neighborhood_nontrivial_fundamentalGroup_kernel
    {n : ℕ} (hdim : Module.finrank ℝ E = n + 1)
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifold 2 L) (hconn : IsConnected L.space)
    (hnot : ¬ IsPLSphere 2 L.space) {U : Set E} (hU : IsOpen U)
    (hLU : L.space ⊆ U) [SimplyConnectedSpace U] (x : L.space) :
    ∃ g : FundamentalGroup L.space x, g ≠ 1 ∧
      ∃ N : Geometry.SimplicialComplex ℝ E, N.faces.Finite ∧
        IsCombinatorialManifoldWithBoundary (n + 1) N ∧ N.space ⊆ U ∧
        L.space ⊆ N.space \ (boundaryComplex (n + 1) N).space ∧
        ∀ hLN : L.space ⊆ N.space,
          FundamentalGroup.map (⟨Set.inclusion hLN, continuous_inclusion hLN⟩ :
            C(L.space, N.space)) x g = 1 := by
  let _ : PathConnectedSpace L.space := isPathConnected_iff_pathConnectedSpace.mp
    (SimplicialComplex.isPathConnected_geometricSpace L hconn)
  have hnot' : ¬ SimplyConnectedSpace L.space := by
    intro h
    let _ := h
    exact hnot (hL.isPLSphere_two_of_simplyConnectedSpace L)
  obtain ⟨g, hg⟩ := exists_fundamentalGroup_ne_one_of_not_simplyConnectedSpace hnot' x
  obtain ⟨N, hNfin, hN, hLN, hNU, hmap⟩ :=
    exists_neighborhood_fundamentalGroup_map_eq_one_of_simplyConnectedSpace
      hdim (isPolyhedron_space L).isCompact hU hLU x g
  let _ := hNfin.to_subtype
  refine ⟨g, hg, N, hNfin, hN, hNU, ?_, hmap⟩
  intro y hy
  refine ⟨interior_subset (hLN hy), ?_⟩
  rw [← frontier_space_eq_boundaryComplex_space_of_finrank hdim N hN]
  exact fun hfront => hfront.2 (hLN hy)

end DifferentialGeometry.Topology.PiecewiseLinear

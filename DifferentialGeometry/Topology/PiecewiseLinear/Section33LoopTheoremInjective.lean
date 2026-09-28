/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ExtendedLoopTheoremStatement
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceEssentialDisk

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem injective_fundamentalGroup_map_of_moise264Orientable (h264 : Moise264Orientable)
    (hdim : Module.finrank ℝ E = 3)
    {L : Geometry.SimplicialComplex ℝ E} [Finite L.faces] (hL : IsCombinatorialManifold 2 L)
    (hLc : IsConnected L.space) {S : Set E} (hLS : L.space = S) {U : Set E} (hU : IsOpen U)
    (hLU : S ⊆ U)
    (hno : ∀ (Δ : Set E) (r : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ → Δ ⊆ U →
        Δ ∩ S = r '' stdSimplexBoundary 2 → ∀ hb : r '' stdSimplexBoundary 2 ⊆ S,
          (⟨Set.inclusion hb, continuous_inclusion hb⟩ :
            C(r '' stdSimplexBoundary 2, S)).Nullhomotopic)
    (x : S) :
    Function.Injective (FundamentalGroup.map
      (⟨Set.inclusion hLU, continuous_inclusion hLU⟩ : C(S, U)) x) := by
  subst hLS
  rw [injective_iff_map_eq_one]
  intro g hg
  by_contra hne
  obtain ⟨N₀, hN₀fin, hN₀, -, hLN, hN₀U, hnull⟩ :=
    exists_connected_neighborhood_fundamentalGroup_map_eq_one (n := 2) hdim
      (isPolyhedron_space L).isCompact hLc hU hLU x g hg
  let _ : Finite N₀.faces := hN₀fin.to_subtype
  have hLint : L.space ⊆ N₀.space \ (boundaryComplex 3 N₀).space := by
    rw [← frontier_space_eq_boundaryComplex_space_of_finrank hdim N₀ hN₀]
    exact fun y hy => ⟨interior_subset (hLN hy), fun hz => hz.2 (hLN hy)⟩
  obtain ⟨T, -, hTcard, hNT⟩ := exists_affineIndependent_openSimplex_superset 3 hdim
    (isPolyhedron_space N₀).isCompact.isBounded
  have hor : IsOrientable 3 N₀ := isOrientable_of_space_subset_convexHull N₀ hN₀ T hTcard
    (hNT.trans (openSimplex_subset_convexHull T))
  have htwo : IsTwoSided (((↑) : N₀.space → E) ⁻¹' L.space) := by
    refine (hL.isTwoSided L hdim hLc).preimage_of_isInducing IsInducing.subtypeVal ?_
    rw [Subtype.range_coe]
    exact Filter.mem_of_superset (isOpen_interior.mem_nhdsSet.mpr hLN) interior_subset
  obtain ⟨Δ, r, hr, hΔ, hmeet, hb, hnon⟩ :=
    h264 N₀ inferInstance hN₀ hor L inferInstance hL hLint htwo x g hne (hnull _)
  exact hnon (hno Δ r hr (hΔ.trans (sdiff_subset.trans hN₀U)) hmeet hb)

end DifferentialGeometry.Topology.PiecewiseLinear

/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceEssentialDisk

/-!
# Incompressible closed surfaces from the extended loop theorem

Let `L` be a connected closed combinatorial surface, with `|L| = S`, in an open set `U` of `ℝ³`
such that every piecewise linear disk in `U` meeting `S` exactly in its boundary has a
nullhomotopic boundary in `S`.  If a loop class `g ≠ 1` of `|L|` died in `U`, the
nullhomotopy would lie in a compact connected combinatorial three-manifold `N₀ ⊆ U` with `|L|` in
its interior (`exists_connected_neighborhood_fundamentalGroup_map_eq_one`), and the extended loop
theorem (`Moise264`, `|L|` two-sided by `IsCombinatorialManifold.isTwoSided`) would give such a
disk in the interior of `N₀` with essential boundary.  Hence `π₁(S) → π₁(U)` is injective
(`injective_fundamentalGroup_map_of_moise264`).  This is the injectivity half of Moise,
Section 33, Lemma 10.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem injective_fundamentalGroup_map_of_moise264 (h264 : Moise264)
    (hdim : Module.finrank ℝ E = 3)
    {L : Geometry.SimplicialComplex ℝ E} [Finite L.faces] (hL : IsCombinatorialManifold 2 L)
    (hLc : IsConnected L.space) {S : Set E} (hLS : L.space = S) {U : Set E} (hU : IsOpen U)
    (hLU : S ⊆ U)
    (hno : ∀ (Δ : Set E) (r : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) Δ → Δ ⊆ U →
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
  have htwo := hL.isTwoSided L hdim hLc
  obtain ⟨Δ, r, hr, hΔ, hmeet, hb, hnon⟩ :=
    h264 N₀ inferInstance hN₀ L inferInstance hL hLint htwo x g hne hnull
  exact hnon (hno Δ r hr (hΔ.trans (sdiff_subset.trans hN₀U)) hmeet hb)

end DifferentialGeometry.Topology.PiecewiseLinear

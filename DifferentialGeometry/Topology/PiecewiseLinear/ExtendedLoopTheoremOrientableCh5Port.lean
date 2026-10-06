import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.Moise252Producer

/-!
Ch5 port (P0-PORT): the ch5 workbench (baseline b0f2c40, `LoopTheorem/TwoSidedSurface.lean`)
states the interior-surface Loop Theorem directly as `exists_compressing_disk_of_twoSided_surface`.
dg-ch15 packages the same statement as the `Prop` `Moise264Orientable` with producer
`moise264Orientable`. This file exposes the ch5 name, proved from the dg-ch15 producer.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_compressing_disk_of_twoSided_surface
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (hKfin : Finite K.faces)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hKo : IsOrientable 3 K)
    (L : Geometry.SimplicialComplex ℝ E) (hLfin : Finite L.faces)
    (hL : IsCombinatorialManifold 2 L)
    (hLK : L.space ⊆ K.space \ (boundaryComplex 3 K).space)
    (htwo : IsTwoSided (((↑) : K.space → E) ⁻¹' L.space))
    (x : L.space) (g : FundamentalGroup L.space x) (hg : g ≠ 1)
    (hgin : FundamentalGroup.map
      (⟨Set.inclusion (hLK.trans sdiff_subset), continuous_inclusion _⟩ : C(L.space, K.space)) x g = 1) :
    ∃ (Δ : Set E) (r : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧
      Δ ⊆ K.space \ (boundaryComplex 3 K).space ∧
      Δ ∩ L.space = r '' stdSimplexBoundary 2 ∧
      ∃ hb : r '' stdSimplexBoundary 2 ⊆ L.space,
        ¬ (⟨Set.inclusion hb, continuous_inclusion hb⟩ : C(r '' stdSimplexBoundary 2, L.space)).Nullhomotopic :=
  moise264Orientable K hKfin hK hKo L hLfin hL hLK htwo x g hg hgin

end DifferentialGeometry.Topology.PiecewiseLinear

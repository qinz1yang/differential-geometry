/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PrismCornerTransport
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodTriangle

/-! Rounded local corner charts on actual derived-neighborhood two-handles. -/

open Set Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_rounded_derivedNeighborhood_triangle_corner
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 3 K) (hLK : L.faces ⊆ K.faces)
    (hL : ∀ t ∈ L.faces, t.card ≤ 3) {s : Finset E} (hs : s ∈ K.faces)
    (hcard : s.card = 3) (hsL : s ∉ L.faces)
    (hproper : ∀ t : Finset E, t.Nonempty → t ⊂ s → t ∈ L.faces) :
    ∃ g : (Fin 3 → ℝ) × ℝ → E,
      IsPLHomeomorphOn g (stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1)
        (derivedNeighborhoodCell K s).space ∧
      ∃ U : TopologicalSpace.Opens (derivedNeighborhoodCell K s).space,
      ∃ charts : ChartedSpace (EuclideanHalfSpace 3) U,
        let _ := charts
        IsManifold (𝓡∂ 3) ∞ U ∧
        ∃ d : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) U prismCornerTarget ∞,
          (∀ x : U, x.val.val ∈ (derivedNeighborhood K L).space ↔
            (d x).val.val 0 = 0 ∧ (d x).val.val 1 ≤ 0) ∧
          (∀ x : U, x ∈ (𝓡∂ 3).boundary U ↔ (d x).val.val 0 = 0) ∧
          ∃ x : U, (d x).val = 0 ∧ x.val.val = g (![0, (1 : ℝ) / 2, 1 / 2], 0) := by
  obtain ⟨g, hg, hgB⟩ := exists_isPLHomeomorphOn_derivedNeighborhoodCell_triangle K L hK hLK hL
    hs hcard hsL hproper
  exact ⟨g, hg, hg.exists_rounded_corner_chart hgB.image_eq⟩

end DifferentialGeometry.Topology.PiecewiseLinear

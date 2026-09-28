/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PrismAnnulusTransport
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodTriangle

open Set Metric Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_rounded_derivedNeighborhood_triangle_annulus
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 3 K) (hLK : L.faces ⊆ K.faces)
    (hL : ∀ t ∈ L.faces, t.card ≤ 3) {s : Finset E} (hs : s ∈ K.faces)
    (hcard : s.card = 3) (hsL : s ∉ L.faces)
    (hproper : ∀ t : Finset E, t.Nonempty → t ⊂ s → t ∈ L.faces) :
    let _ := prismAnnulusChartedSpace
    ∃ g : (Fin 3 → ℝ) × ℝ → E,
      IsPLHomeomorphOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1)
        (derivedNeighborhoodCell K s).space ∧
      ∃ U : TopologicalSpace.Opens (derivedNeighborhoodCell K s).space,
        (derivedNeighborhoodCell K s).space ∩ (derivedNeighborhood K L).space ⊆
          (fun x : (derivedNeighborhoodCell K s).space => x.val) '' (U : Set _) ∧
        ∃ charts : ChartedSpace
          (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanHalfSpace 2)) U,
          let _ := charts
          IsManifold ((𝓡 1).prod (𝓡∂ 2)) ∞ U ∧
          ∃ d : Diffeomorph ((𝓡 1).prod (𝓡∂ 2)) ((𝓡 1).prod (𝓡∂ 2))
              U prismAnnulusSource ∞,
            (∀ x : U, g (d x).val.val = x.val.val) ∧
            (∀ x : U, x.val.val ∈ (derivedNeighborhood K L).space ↔
              (d x).val.val.1 ∈ stdSimplexBoundary 2) ∧
            (∀ x : U, x ∈ ((𝓡 1).prod (𝓡∂ 2)).boundary U ↔
              (d x).val.val.1 ∈ stdSimplexBoundary 2 ∨
                (d x).val.val.2 = 0 ∨ (d x).val.val.2 = 1) ∧
            ∀ v : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, ∀ i : Bool,
              d.toHomeomorph.toOpenPartialHomeomorph.trans (prismAnnulusChart v i) ∈
                atlas (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanHalfSpace 2)) U := by
  let _ := prismAnnulusChartedSpace
  obtain ⟨g, hg, hgB⟩ := exists_isPLHomeomorphOn_derivedNeighborhoodCell_triangle K L hK hLK hL
    hs hcard hsL hproper
  exact ⟨g, hg, hg.exists_rounded_annulus_atlas hgB.image_eq⟩

end DifferentialGeometry.Topology.PiecewiseLinear

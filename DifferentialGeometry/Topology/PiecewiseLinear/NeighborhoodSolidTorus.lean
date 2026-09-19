/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CombinatorialSolidTorus
import DifferentialGeometry.Topology.PiecewiseLinear.SolidTorusProduct
import DifferentialGeometry.Topology.PiecewiseLinear.NeighborhoodCycle

/-! Cyclic cell decompositions and solid tori around polygonal circles. -/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_cyclic_derivedNeighborhoodCell_decomposition_disjoint
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hLK : L.faces ⊆ K.faces)
    (hL : IsCombinatorialManifold 1 L) (hconn : IsConnected L.space) :
    ∃ n : ℕ, 3 ≤ n ∧ ∃ e : Fin n ≃ L.faces,
      (⋃ i, (derivedNeighborhoodCell K (e i).val).space) = (derivedNeighborhood K L).space ∧
      (∀ i, IsPLBall 3 (derivedNeighborhoodCell K (e i).val).space) ∧
      (∀ i j, i ≠ j →
        (((derivedNeighborhoodCell K (e i).val).space ∩
          (derivedNeighborhoodCell K (e j).val).space).Nonempty ↔
            (SimpleGraph.cycleGraph n).Adj i j) ∧
        ((SimpleGraph.cycleGraph n).Adj i j →
          IsPLBall 2 ((derivedNeighborhoodCell K (e i).val).space ∩
            (derivedNeighborhoodCell K (e j).val).space) ∧
          (derivedNeighborhoodCell K (e i).val).space ∩
            (derivedNeighborhoodCell K (e j).val).space ⊆
              (boundaryComplex 3 (derivedNeighborhoodCell K (e i).val)).space ∧
          (derivedNeighborhoodCell K (e i).val).space ∩
            (derivedNeighborhoodCell K (e j).val).space ⊆
              (boundaryComplex 3 (derivedNeighborhoodCell K (e j).val)).space)) ∧
      (∀ i j, i ≠ j → ¬ (SimpleGraph.cycleGraph n).Adj i j →
        Disjoint (derivedNeighborhoodCell K (e i).val).space
          (derivedNeighborhoodCell K (e j).val).space) ∧
      ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        Disjoint ((derivedNeighborhoodCell K (e i).val).space ∩
          (derivedNeighborhoodCell K (e j).val).space)
          (derivedNeighborhoodCell K (e k).val).space := by
  obtain ⟨n, hn, e, hcover, hball, hpair⟩ :=
    exists_cyclic_derivedNeighborhoodCell_decomposition K L hK hLK hL hconn
  refine ⟨n, hn, e, hcover, hball, hpair, ?_, ?_⟩
  · intro i j hij hnot
    exact disjoint_left.mpr fun x hxi hxj => hnot ((hpair i j hij).1.mp ⟨x, hxi, hxj⟩)
  · intro i j k hij hik hjk
    exact disjoint_derivedNeighborhoodCell_inter_of_card_le_two K L hLK
      (fun s hs => hL.card_le L hs) (e i).property (e j).property (e k).property
      (fun h => hij (e.injective (Subtype.ext h)))
      (fun h => hik (e.injective (Subtype.ext h)))
      (fun h => hjk (e.injective (Subtype.ext h)))

open Classical in
theorem isCombinatorialSolidTorus_derivedNeighborhood_circle
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hLK : L.faces ⊆ K.faces)
    (hL : IsCombinatorialManifold 1 L) (hconn : IsConnected L.space) (hor : IsOrientable 3 K) :
    IsCombinatorialSolidTorus (derivedNeighborhood K L).space := by
  obtain ⟨n, hn, e, hcover, hball, hpair, _, _⟩ :=
    exists_cyclic_derivedNeighborhoodCell_decomposition_disjoint K L hK hLK hL hconn
  exact ⟨isTopologicalSolidTorus_derivedNeighborhood_circle K L hK hLK hL hconn hor,
    n, hn, fun i => derivedNeighborhoodCell K (e i).val,
    fun i => derivedNeighborhoodCell_faces_finite K (e i).val, hcover, hball, hpair⟩

end DifferentialGeometry.Topology.PiecewiseLinear

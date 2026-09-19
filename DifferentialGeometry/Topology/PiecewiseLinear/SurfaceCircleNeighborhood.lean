/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.NeighborhoodCycle
import DifferentialGeometry.Topology.PiecewiseLinear.BallIntersectionBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.IntervalCylinder

/-!
# Cyclic disk neighborhoods of polygonal circles in surfaces
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_disk_pair_with_boundary_cover_derivedNeighborhood_circle
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hLK : L.faces ⊆ K.faces)
    (hL : IsCombinatorialManifold 1 L) (hconn : IsConnected L.space) :
    ∃ (A B : Geometry.SimplicialComplex ℝ E) (D₀ D₁ : Set E),
      A.faces.Finite ∧ B.faces.Finite ∧ IsPLBall 2 A.space ∧ IsPLBall 2 B.space ∧
      IsPLBall 1 D₀ ∧ IsPLBall 1 D₁ ∧ Disjoint D₀ D₁ ∧
      A.space ∪ B.space = (derivedNeighborhood K L).space ∧ A.space ∩ B.space = D₀ ∪ D₁ ∧
      D₀ ⊆ (boundaryComplex 2 A).space ∧ D₁ ⊆ (boundaryComplex 2 A).space ∧
      D₀ ⊆ (boundaryComplex 2 B).space ∧ D₁ ⊆ (boundaryComplex 2 B).space := by
  let _ : DecidableEq E := Classical.decEq _
  obtain ⟨A, B, D₀, D₁, hA, hB, hD₀, hD₁, hdis, hcover, hinter, Q, hQfin, hQB, hD₀Q, hD₁Q⟩ :=
    exists_isPLBall_two_pair_cover_derivedNeighborhood_circle_with_boundary K L hK hLK hL hconn
  obtain ⟨R, hRfin, hRA⟩ := hA.isPolyhedron.exists_simplicialComplex
  let _ : Finite R.faces := hRfin.to_subtype
  let _ : Finite Q.faces := hQfin.to_subtype
  have hR : IsPLBall 2 R.space := hRA.symm ▸ hA
  have hQ : IsPLBall 2 Q.space := hQB.symm ▸ hB
  have hRK : R.space ⊆ K.space := hRA.subset.trans
    (subset_union_left.trans (hcover.subset.trans (derivedNeighborhood_space_subset K L)))
  have hQK : Q.space ⊆ K.space := hQB.subset.trans
    (subset_union_right.trans (hcover.subset.trans (derivedNeighborhood_space_subset K L)))
  have hmeet : R.space ∩ Q.space = D₀ ∪ D₁ := by rwa [hRA, hQB]
  have hmeetQ : R.space ∩ Q.space ⊆ (boundaryComplex 2 Q).space :=
    hmeet.subset.trans (union_subset hD₀Q hD₁Q)
  have hD₀R := hK.subset_boundaryComplex_of_subset_inter_of_isPLBall R Q hR hQ hRK hQK hmeetQ
    hD₀ (subset_union_left.trans hmeet.symm.subset)
  have hD₁R := hK.subset_boundaryComplex_of_subset_inter_of_isPLBall R Q hR hQ hRK hQK hmeetQ
    hD₁ (subset_union_right.trans hmeet.symm.subset)
  refine ⟨R, Q, D₀, D₁, hRfin, hQfin, hR, hQ, hD₀, hD₁, hdis, ?_, hmeet,
    hD₀R, hD₁R, hD₀Q, hD₁Q⟩
  rwa [hRA, hQB]

open Classical in
theorem exists_cylindricalDiagram_Icc_derivedNeighborhood_circle
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hLK : L.faces ⊆ K.faces)
    (hL : IsCombinatorialManifold 1 L) (hconn : IsConnected L.space) :
    ∃ φ : ℝ × ℝ → E, IsCylindricalDiagram φ (Icc 0 1) (derivedNeighborhood K L).space := by
  classical
  obtain ⟨A, B, D₀, D₁, hAfin, hBfin, hA, hB, hD₀, hD₁, hdis, hcover, hinter,
    hD₀A, hD₁A, hD₀B, hD₁B⟩ :=
    exists_disk_pair_with_boundary_cover_derivedNeighborhood_circle K L hK hLK hL hconn
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite B.faces := hBfin.to_subtype
  obtain ⟨g₀, hg₀⟩ := exists_isPLHomeomorphOn_Icc_of_isPLBall_one hD₀
  obtain ⟨φ, hφ, _⟩ := exists_cylindricalDiagram_of_disk_pair zero_lt_one A B hA hB hD₁ hdis
    hD₀A hD₁A hD₀B hD₁B hinter hg₀
  exact ⟨φ, hcover ▸ hφ⟩

end DifferentialGeometry.Topology.PiecewiseLinear

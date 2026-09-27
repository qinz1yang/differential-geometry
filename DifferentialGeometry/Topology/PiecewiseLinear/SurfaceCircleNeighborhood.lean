/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.NeighborhoodCycle
import DifferentialGeometry.Topology.PiecewiseLinear.BallIntersectionBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.IntervalCylinder
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusCylinder
import DifferentialGeometry.Topology.PiecewiseLinear.Exhaustion
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexMesh

open Set Topology

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

open Classical in
theorem exists_isPLHomeomorphOn_annulus_derivedNeighborhood_circle
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hLK : L.faces ⊆ K.faces)
    (hL : IsCombinatorialManifold 1 L) (hconn : IsConnected L.space) (hor : IsOrientable 2 K) :
    ∃ H : (Fin 3 → ℝ) × ℝ → E,
      IsPLHomeomorphOn H (stdSimplexBoundary 2 ×ˢ Icc 0 1) (derivedNeighborhood K L).space := by
  obtain ⟨φ, hφ⟩ := exists_cylindricalDiagram_Icc_derivedNeighborhood_circle K L hK hLK hL hconn
  exact hφ.exists_isPLHomeomorphOn_annulus_of_isOrientable K hK hor
    (derivedNeighborhood_space_subset K L)

theorem exists_annular_neighborhood
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hor : IsOrientable 2 K)
    {S U : Set E} (hS : IsPLSphere 1 S) (hSK : S ⊆ K.space) (hU : IsOpen U) (hSU : S ⊆ U) :
    ∃ N : Geometry.SimplicialComplex ℝ E, N.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 2 N ∧ N.space ⊆ K.space ∧ N.space ⊆ U ∧
      (∀ x ∈ S, N.space ∈ 𝓝[K.space] x) ∧
      ∃ H : (Fin 3 → ℝ) × ℝ → E, IsPLHomeomorphOn H (stdSimplexBoundary 2 ×ˢ Icc 0 1) N.space := by
  classical
  obtain ⟨R₀, hR₀, hR₀fin, hS₀⟩ := exists_isSubdivision_restrict_space K hS.isPolyhedron hSK
  let _ : Finite R₀.faces := hR₀fin.to_subtype
  let L₀ := restrict R₀ S
  obtain ⟨δ, hδ, hthick⟩ := hS.isPolyhedron.isCompact.exists_cthickening_subset_open hU hSU
  obtain ⟨R, hR, hRfin, hdiam, hLsub⟩ :=
    exists_isSubdivision_diam_lt_restrict_isSubdivision R₀ L₀ (restrict_faces_subset R₀ S) hδ
  let _ : Finite R.faces := hRfin.to_subtype
  let L := restrict R L₀.space
  let _ : Finite L.faces := (restrict_faces_finite R L₀.space).to_subtype
  have hLspace : L.space = S := hLsub.space_eq.trans hS₀
  have hL : IsPLSphere 1 L.space := hLspace.symm ▸ hS
  have hRK : IsSubdivision R K := hR.trans hR₀
  have hRman := hK.of_isSubdivision hRK
  refine ⟨derivedNeighborhood R L, derivedNeighborhood_faces_finite R L,
    hRman.derivedNeighborhood L,
    (derivedNeighborhood_space_subset R L).trans hRK.space_eq.subset, ?_, ?_,
    exists_isPLHomeomorphOn_annulus_derivedNeighborhood_circle R L hRman
      (restrict_faces_subset R L₀.space) hL.isCombinatorialManifold hL.isConnected
      (hor.subdivision hK hRK)⟩
  · apply derivedNeighborhood_space_subset_of_forall_face
    intro s hs t ht hst z hzt
    apply hthick
    apply Metric.mem_cthickening_of_dist_le z (s.centroid ℝ id) δ S
      (hLspace.subset (L.convexHull_subset_space hs
        (s.centroid_mem_convexHull (L.nonempty_of_mem_faces hs))))
    exact ((Metric.dist_le_diam_of_mem (t.finite_toSet.isCompact_convexHull ℝ).isBounded
      hzt hst).trans_lt (hdiam t ht)).le
  · intro x hx
    rw [← hRK.space_eq]
    exact derivedNeighborhood_mem_nhdsWithin (restrict_faces_subset R L₀.space)
      (hLspace.symm.subset hx)

end DifferentialGeometry.Topology.PiecewiseLinear

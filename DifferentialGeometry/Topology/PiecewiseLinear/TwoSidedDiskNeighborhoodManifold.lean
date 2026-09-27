/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.TwoSidedDiskNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldPieceInclusion
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralBallTopology
import DifferentialGeometry.Topology.PiecewiseLinear.ExhaustionGeneral

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

open Classical in
theorem PLPieceIn.exists_isPolyhedralBall_pair_inter_frontier_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    {Y N D U : Set X} (P : PLPieceIn E 3 X Y)
    (hP : IsCombinatorialManifoldWithBoundary 3 P.complex)
    (hN : IsPolyhedralManifoldWithBoundary (n := 3) 3 N) (hNY : N ⊆ interior Y)
    (hD : IsPolyhedralBall (n := 3) 2 D) (hDN : D ⊆ frontier N) (hU : U ∈ 𝓝ˢ D) :
    ∃ C₁ C₂ : Set X, IsPolyhedralBall (n := 3) 3 C₁ ∧
      IsPolyhedralBall (n := 3) 3 C₂ ∧ C₁ ⊆ N ∧ C₂ ⊆ closure (Y \ N) ∧
        C₁ ⊆ U ∧ C₂ ⊆ U ∧ C₁ ∩ frontier N = D ∧
          C₂ ∩ frontier N = D ∧ C₁ ∩ C₂ = D := by
  let _ : Finite P.complex.faces := P.finite_faces.to_subtype
  have hNsub : N ⊆ Y := hNY.trans interior_subset
  obtain ⟨S, hSspace, hSmap, hS⟩ :=
    P.exists_restrict_of_isPolyhedralManifoldWithBoundary hN hNsub
  let _ : Finite S.complex.faces := S.finite_faces.to_subtype
  have hSK : S.complex.space ⊆ P.complex.space := hSspace.subset.trans inter_subset_left
  have hfront : frontier N = P.map '' (boundaryComplex 3 S.complex).space := by
    exact (S.frontier_eq_image_boundaryComplex (n := 2) hS).trans
      (congrArg (fun f => f '' (boundaryComplex 3 S.complex).space) hSmap)
  have hdis : Disjoint S.complex.space (boundaryComplex 3 P.complex).space := by
    apply disjoint_left.mpr
    intro x hx hb
    have hxN : P.map x ∈ N := (hSspace.subset hx).2
    exact (P.mem_interior_iff_not_mem_boundaryComplex_space (n := 2) hP (hSK hx)).mp
      (hNY hxN) hb
  let Q := P.complex.space ∩ P.map ⁻¹' D
  have hDN' : D ⊆ N := hDN.trans hN.isCompact.isClosed.frontier_subset
  have hDY : D ⊆ Y := hDN'.trans hNsub
  have hQball : IsPLBall 2 Q := hD.isPLBall_inter_preimage P hDY
  have hQB : Q ⊆ (boundaryComplex 3 S.complex).space := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hfront.subset (hDN hx.2)
    have heq : y = x := P.bijOn.injOn
      (hSK (boundaryComplex_space_subset 3 S.complex hy)) hx.1 hyx
    exact heq ▸ hy
  have hQimage : P.map '' Q = D := by
    apply Subset.antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact hy.2
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := P.bijOn.surjOn (hDY hx)
      exact ⟨y, ⟨hy, hx⟩, rfl⟩
  obtain ⟨A, B, hA, hB, hAS, hBR, hAU, hBU, hABd, hBBd, hAB⟩ :=
    hP.exists_isPLBall_pair_inter_boundaryComplex_eq hS hSK hdis hQball hQB
      (P.continuousOn.preimage_mem_nhdsSetWithin_of_mem_nhdsSet hU)
  have hRK : closure (P.complex.space \ S.complex.space) ⊆ P.complex.space :=
    closure_minimal sdiff_subset P.isPolyhedron_space.isClosed
  have hAK := hAS.trans hSK
  have hBK := hBR.trans hRK
  have hBdK := (boundaryComplex_space_subset 3 S.complex).trans hSK
  refine ⟨P.map '' A, P.map '' B,
    P.isPolyhedralBall_image hA hAK, P.isPolyhedralBall_image hB hBK,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    exact (hSspace.subset (hAS hy)).2
  · apply (image_mono hBR).trans
    apply (P.continuousOn.mono hRK).image_closure.trans
    apply closure_mono
    rintro x ⟨y, hy, rfl⟩
    refine ⟨P.bijOn.mapsTo hy.1, ?_⟩
    intro hyN
    exact hy.2 (hSspace.symm.subset ⟨hy.1, hyN⟩)
  · exact image_subset_iff.mpr hAU
  · exact image_subset_iff.mpr hBU
  · rw [hfront, ← P.bijOn.injOn.image_inter hAK hBdK, hABd, hQimage]
  · rw [hfront, ← P.bijOn.injOn.image_inter hBK hBdK, hBBd, hQimage]
  · rw [← P.bijOn.injOn.image_inter hAK hBK, hAB, hQimage]

open Classical in
theorem IsPolyhedralManifoldWithBoundary.exists_isPolyhedralBall_pair_inter_frontier_eq
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [HasGroupoid X (plGroupoid 3)]
    {N M D U : Set X} (hN : IsPolyhedralManifoldWithBoundary (n := 3) 3 N)
    (hNM : N ⊆ interior M) (hD : IsPolyhedralBall (n := 3) 2 D)
    (hDN : D ⊆ frontier N) (hU : U ∈ 𝓝ˢ D) :
    ∃ C₁ C₂ : Set X, IsPolyhedralBall (n := 3) 3 C₁ ∧
      IsPolyhedralBall (n := 3) 3 C₂ ∧ C₁ ⊆ N ∧ C₂ ⊆ closure (M \ N) ∧
        C₁ ⊆ U ∧ C₂ ⊆ U ∧ C₁ ∩ frontier N = D ∧
          C₂ ∩ frontier N = D ∧ C₁ ∩ C₂ = D := by
  let _ : Nonempty X := ⟨hD.nonempty.some⟩
  obtain ⟨Y, _, ⟨P, hP⟩, hNY, hYM⟩ :=
    exists_isPolyhedralManifoldWithBoundary_neighborhood (m := 2)
      hN.isCompact isOpen_interior hNM
  obtain ⟨C₁, C₂, h₁, h₂, h₁N, h₂Y, h₁U, h₂U, h₁D, h₂D, h₁₂⟩ :=
    P.piece.exists_isPolyhedralBall_pair_inter_frontier_eq hP hN hNY hD hDN hU
  exact ⟨C₁, C₂, h₁, h₂, h₁N,
    h₂Y.trans (closure_mono (sdiff_subset_sdiff_left (hYM.trans interior_subset))),
    h₁U, h₂U, h₁D, h₂D, h₁₂⟩

end DifferentialGeometry.Topology.PiecewiseLinear

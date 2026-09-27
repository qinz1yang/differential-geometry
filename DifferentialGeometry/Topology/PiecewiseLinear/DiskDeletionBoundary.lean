/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleBoundaryMove
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryMonotonicity

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem boundary_inter_disk_complement_eq
    (K A L : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] [Finite A.faces] [Finite L.faces]
    (hK : IsPLBall 2 K.space) (hA : IsPLBall 2 A.space) (hL : IsPLBall 2 L.space)
    (hAK : A.space ⊆ K.space)
    (htrace : IsPLBall 1 (A.space ∩ (boundaryComplex 2 K).space))
    (hLspace : L.space = closure (K.space \ A.space)) :
    (boundaryComplex 2 K).space ∩ L.space =
      closure ((boundaryComplex 2 K).space \ A.space) := by
  let S := A.space ∩ (boundaryComplex 2 K).space
  let P := closure ((boundaryComplex 2 K).space \ A.space)
  let Q := closure ((boundaryComplex 2 A).space \ (boundaryComplex 2 K).space)
  have hKS := isPLSphere_boundaryComplex_space_of_isPLBall K hK
  have hAS := isPLSphere_boundaryComplex_space_of_isPLBall A hA
  have hSA : S ⊆ (boundaryComplex 2 A).space :=
    inter_boundaryComplex_space_subset_of_subset K A hK.isCombinatorialManifoldWithBoundary
      hA.isCombinatorialManifoldWithBoundary hAK
  obtain ⟨γ, hγ⟩ := exists_isPLHomeomorphOn_Icc_of_isPLBall_one htrace
  have hdiffK : (boundaryComplex 2 K).space \ A.space =
      (boundaryComplex 2 K).space \ S := by
    ext x
    simp only [S, mem_sdiff, mem_inter_iff]
    tauto
  have hdiffA : (boundaryComplex 2 A).space \ (boundaryComplex 2 K).space =
      (boundaryComplex 2 A).space \ S := by
    ext x
    constructor
    · rintro ⟨hx, hxK⟩
      exact ⟨hx, fun hxS => hxK hxS.2⟩
    · rintro ⟨hx, hxS⟩
      exact ⟨hx, fun hxK => hxS ⟨boundaryComplex_space_subset 2 A hx, hxK⟩⟩
  have hSP : S ∩ P = {γ 0, γ 1} := by
    change S ∩ closure ((boundaryComplex 2 K).space \ A.space) = _
    rw [hdiffK]
    exact hγ.inter_closure_circle_sdiff hKS inter_subset_right
  have hSQ : S ∩ Q = {γ 0, γ 1} := by
    change S ∩ closure ((boundaryComplex 2 A).space \ (boundaryComplex 2 K).space) = _
    rw [hdiffA]
    exact hγ.inter_closure_circle_sdiff hAS hSA
  have hQsub : Q ⊆ A.space :=
    (closure_minimal sdiff_subset hAS.isPolyhedron.isClosed).trans
      (boundaryComplex_space_subset 2 A)
  have hLsub : L.space ⊆ K.space := by
    rw [hLspace]
    exact closure_minimal sdiff_subset hK.isPolyhedron.isClosed
  have hbdL : (boundaryComplex 2 L).space = P ∪ Q :=
    boundaryComplex_space_of_closure_sdiff K A L hK.isCombinatorialManifoldWithBoundary
      hA.isCombinatorialManifoldWithBoundary hAK hL.isCombinatorialManifoldWithBoundary hLspace
  apply Subset.antisymm
  · intro x hx
    have hxL : x ∈ (boundaryComplex 2 L).space :=
      inter_boundaryComplex_space_subset_of_subset K L hK.isCombinatorialManifoldWithBoundary
        hL.isCombinatorialManifoldWithBoundary hLsub ⟨hx.2, hx.1⟩
    rcases hbdL.subset hxL with hxP | hxQ
    · exact hxP
    · exact (hSP.symm.subset (hSQ.subset ⟨⟨hQsub hxQ, hx.1⟩, hxQ⟩)).2
  · intro x hx
    refine ⟨closure_minimal sdiff_subset hKS.isPolyhedron.isClosed hx, ?_⟩
    rw [hLspace]
    exact closure_mono (sdiff_subset_sdiff_left (boundaryComplex_space_subset 2 K)) hx

end DifferentialGeometry.Topology.PiecewiseLinear

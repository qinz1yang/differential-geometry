/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CommonCircleDerivedNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodPolygon
import DifferentialGeometry.Topology.PiecewiseLinear.DisplacedArcConnected
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldRelativeTopology

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLSphere.exists_isPLBall_one_neighborhood {S F U : Set E}
    (hS : IsPLSphere 1 S) (hF : IsPLBall 1 F) (hFS : F ⊆ S)
    (hU : IsOpen U) (hFU : F ⊆ U) :
    ∃ (A : Set E) (q : (Fin 2 → ℝ) → E),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) A ∧ A ⊆ S ∩ U ∧
      F ⊆ A ∧ A ∈ 𝓝ˢ[S] F ∧ Disjoint F (q '' stdSimplexBoundary 1) := by
  classical
  let _ : DecidableEq E := Classical.decEq _
  obtain ⟨z, hzS, hzF⟩ : ∃ z ∈ S, z ∉ F := by
    by_contra! h
    exact hF.not_isPLSphere (Subset.antisymm hFS h ▸ hS)
  let W := U \ {z}
  have hW : IsOpen W := hU.sdiff isClosed_singleton
  have hFW : F ⊆ W := fun x hx => ⟨hFU hx, fun h => hzF (h ▸ hx)⟩
  obtain ⟨K, hKfin, hKS⟩ := hS.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hFK : F ⊆ K.space := hFS.trans hKS.symm.subset
  obtain ⟨R, L, P₀, P₁, hRfin, hLfin, -, -, hRK, hLF, -, -, hP₀R, -, hLP₀, -, hNW,
      hnhds, -, -⟩ := exists_common_derivedNeighborhood_with_surface_traces K hF.isPolyhedron
      hS.isPolyhedron hS.isPolyhedron hFK hKS.symm.subset hKS.symm.subset hFS hFS hW hFW
  let _ : Finite R.faces := hRfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  have hLR : L.faces ⊆ R.faces := hLP₀.trans hP₀R
  let N := derivedNeighborhood R L
  let _ : Finite N.faces := (derivedNeighborhood_faces_finite R L).to_subtype
  have hRS : R.space = S := hRK.space_eq.trans hKS
  have hNS : N.space ⊆ S := (derivedNeighborhood_space_subset R L).trans hRS.subset
  have hFN : F ⊆ N.space := by
    rw [← hLF]
    exact subcomplex_space_subset_derivedNeighborhood hLR
  have hNconn : IsConnected N.space :=
    isConnected_derivedNeighborhood_space hLR (hLF.symm ▸ hF.isConnected)
  have hNproper : N.space ⊂ S := by
    refine ⟨hNS, fun h => ?_⟩
    exact (hNW (h hzS)).2 rfl
  have hNball : IsPLBall 1 N.space :=
    hS.isPLBall_one_of_isClosed_of_isConnected_of_ssubset (isPolyhedron_space N).isClosed
      hNconn (hF.nontrivial.mono hFN) hNproper
  obtain ⟨q, hq⟩ := id hNball
  have hRman : IsCombinatorialManifold 1 R := (hRS.symm ▸ hS).isCombinatorialManifold
  have hNman : IsCombinatorialManifoldWithBoundary 1 N :=
    (show IsPLBall 1 N.space from ⟨q, hq⟩).isCombinatorialManifoldWithBoundary
  have hRbd : (boundaryComplex 1 R).space = ∅ := by
    change (⋃ t ∈ (boundaryComplex 1 R).faces, convexHull ℝ (t : Set E)) = ∅
    rw [hRman.boundaryComplex_faces_eq_empty]
    simp
  have hNbd : (boundaryComplex 1 N).space = q '' stdSimplexBoundary 1 := by
    simpa only [simplexBoundary_stdVertices_space] using
      boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex N hq
  refine ⟨N.space, q, hq, fun x hx => ⟨hNS hx, (hNW hx).1⟩, hFN, ?_, ?_⟩
  · rwa [hKS] at hnhds
  · refine disjoint_left.mpr fun x hxF hxJ => ?_
    have hlocal := derivedNeighborhood_mem_nhdsWithin hLR (hLF.symm ▸ hxF)
    have hxRbd := (mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin R N
      hRman.isCombinatorialManifoldWithBoundary hNman
        (derivedNeighborhood_space_subset R L) (hFN hxF) hlocal).mp (hNbd.symm ▸ hxJ)
    simp only [hRbd, mem_empty_iff_false] at hxRbd

end DifferentialGeometry.Topology.PiecewiseLinear

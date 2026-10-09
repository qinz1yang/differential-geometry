/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryGluing
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldDisjointUnion

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isCombinatorialManifold_union_ball
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    {D : Set E} {r : (Fin (n + 2) → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2))) D)
    (hmeet : K.space ∩ D = r '' stdSimplexBoundary (n + 1))
    (hboundary : (boundaryComplex (n + 1) K).space = r '' stdSimplexBoundary (n + 1)) :
    ∃ R : Geometry.SimplicialComplex ℝ E, R.faces.Finite ∧
      IsCombinatorialManifold (n + 1) R ∧ R.space = K.space ∪ D := by
  have hD : IsPLBall (n + 1) D := ⟨r, hr⟩
  obtain ⟨L, hLfin, hLspace⟩ := hD.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  have hL : IsPLBall (n + 1) L.space := hLspace.symm ▸ hD
  have hrL : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2))) L.space := hLspace.symm ▸ hr
  have hLboundary : (boundaryComplex (n + 1) L).space = r '' stdSimplexBoundary (n + 1) := by
    rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex L hrL,
      simplexBoundary_stdVertices_space]
  obtain ⟨R, hRfin, hR, hRspace⟩ := exists_isCombinatorialManifold_space_union K L hK
    hL.isCombinatorialManifoldWithBoundary
    (by rw [hLspace, hmeet, hboundary]) (by rw [hLspace, hmeet, hLboundary])
  exact ⟨R, hRfin, hR, hRspace.trans (congrArg (K.space ∪ ·) hLspace)⟩

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isCombinatorialManifold_union_ball_pair
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    {D₀ D₁ : Set E} {r₀ r₁ : (Fin (n + 2) → ℝ) → E}
    (hr₀ : IsPLHomeomorphOn r₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2))) D₀)
    (hr₁ : IsPLHomeomorphOn r₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2))) D₁) (hdis : Disjoint D₀ D₁)
    (hmeet₀ : K.space ∩ D₀ = r₀ '' stdSimplexBoundary (n + 1))
    (hmeet₁ : K.space ∩ D₁ = r₁ '' stdSimplexBoundary (n + 1))
    (hboundary : (boundaryComplex (n + 1) K).space =
      r₀ '' stdSimplexBoundary (n + 1) ∪ r₁ '' stdSimplexBoundary (n + 1)) :
    ∃ R : Geometry.SimplicialComplex ℝ E, R.faces.Finite ∧
      IsCombinatorialManifold (n + 1) R ∧ R.space = K.space ∪ D₀ ∪ D₁ := by
  have hball₀ : IsPLBall (n + 1) D₀ := ⟨r₀, hr₀⟩
  have hball₁ : IsPLBall (n + 1) D₁ := ⟨r₁, hr₁⟩
  obtain ⟨A, hAfin, hAspace⟩ := hball₀.isPolyhedron.exists_simplicialComplex
  obtain ⟨B, hBfin, hBspace⟩ := hball₁.isPolyhedron.exists_simplicialComplex
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite B.faces := hBfin.to_subtype
  have hA : IsPLBall (n + 1) A.space := hAspace.symm ▸ hball₀
  have hB : IsPLBall (n + 1) B.space := hBspace.symm ▸ hball₁
  have hAbd : (boundaryComplex (n + 1) A).space = r₀ '' stdSimplexBoundary (n + 1) := by
    rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex A (hAspace.symm ▸ hr₀),
      simplexBoundary_stdVertices_space]
  have hBbd : (boundaryComplex (n + 1) B).space = r₁ '' stdSimplexBoundary (n + 1) := by
    rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex B (hBspace.symm ▸ hr₁),
      simplexBoundary_stdVertices_space]
  obtain ⟨L, hLfin, hL, hLspace, hLbd⟩ :=
    hA.isCombinatorialManifoldWithBoundary.exists_space_disjoint_union A B
      hB.isCombinatorialManifoldWithBoundary (by rwa [hAspace, hBspace])
  let _ : Finite L.faces := hLfin.to_subtype
  have hmeet : K.space ∩ L.space =
      r₀ '' stdSimplexBoundary (n + 1) ∪ r₁ '' stdSimplexBoundary (n + 1) := by
    rw [hLspace, hAspace, hBspace, inter_union_distrib_left, hmeet₀, hmeet₁]
  obtain ⟨R, hRfin, hR, hRspace⟩ := exists_isCombinatorialManifold_space_union K L hK hL
    (hmeet.trans hboundary.symm) (by rw [hmeet, hLbd, hAbd, hBbd])
  exact ⟨R, hRfin, hR, by rw [hRspace, hLspace, hAspace, hBspace, union_assoc]⟩

end DifferentialGeometry.Topology.PiecewiseLinear

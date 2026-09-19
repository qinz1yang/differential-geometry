/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryGluing

/-!
# Capping the entire boundary of a combinatorial manifold by a ball
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isCombinatorialManifold_union_ball
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    {D : Set E} {r : (Fin (n + 2) → ℝ) → E}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin (n + 2))) D)
    (hmeet : K.space ∩ D = r '' stdSimplexBoundary (n + 1))
    (hboundary : (boundaryComplex (n + 1) K).space = r '' stdSimplexBoundary (n + 1)) :
    ∃ R : Geometry.SimplicialComplex ℝ E, R.faces.Finite ∧
      IsCombinatorialManifold (n + 1) R ∧ R.space = K.space ∪ D := by
  have hD : IsPLBall (n + 1) D := ⟨r, hr⟩
  obtain ⟨L, hLfin, hLspace⟩ := hD.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  have hL : IsPLBall (n + 1) L.space := hLspace.symm ▸ hD
  have hrL : IsPLHomeomorphOn r (stdSimplex ℝ (Fin (n + 2))) L.space := hLspace.symm ▸ hr
  have hLboundary : (boundaryComplex (n + 1) L).space = r '' stdSimplexBoundary (n + 1) := by
    rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex L hrL,
      simplexBoundary_stdVertices_space]
  obtain ⟨R, hRfin, hR, hRspace⟩ := exists_isCombinatorialManifold_space_union K L hK
    hL.isCombinatorialManifoldWithBoundary
    (by rw [hLspace, hmeet, hboundary]) (by rw [hLspace, hmeet, hLboundary])
  exact ⟨R, hRfin, hR, hRspace.trans (congrArg (K.space ∪ ·) hLspace)⟩

end DifferentialGeometry.Topology.PiecewiseLinear

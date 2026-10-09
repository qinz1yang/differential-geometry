/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryArcStability
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInvariance

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem eventually_geometricLink_section_subsingleton_of_boundary_segment
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [dE : DecidableEq E] (M : Geometry.SimplicialComplex ℝ E) [Finite M.faces]
    (hM : IsPLBall 2 M.space) (ℓ : E →L[ℝ] ℝ) {q a b : E}
    (hqB : {q} ∈ (boundaryComplex 2 M).faces)
    (ha : {a} ∈ (SimplicialComplex.geometricLink (boundaryComplex 2 M) {q}).faces)
    (hb : {b} ∈ (SimplicialComplex.geometricLink (boundaryComplex 2 M) {q}).faces)
    (hab : a ≠ b) (hq : q ∈ openSegment ℝ a b)
    (hside : ∀ v ∈ (SimplicialComplex.geometricLink M {q}).vertices,
      v ≠ a → v ≠ b → ℓ v < ℓ q) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ,
      InjOn f (insert q (SimplicialComplex.geometricLink M {q}).vertices) →
        ((SimplicialComplex.geometricLink M {q}).space ∩
          {x | f x = f q}).Subsingleton := by
  classical
  cases Subsingleton.elim dE (Classical.decEq E)
  have hman : IsCombinatorialManifoldWithBoundary 2 M :=
    hM.isCombinatorialManifoldWithBoundary
  have hlinkBall : IsPLBall 1 (SimplicialComplex.geometricLink M {q}).space := by
    have h := ((hman.mem_boundaryComplex_faces_iff M).mp hqB).2.2
    simpa only [Finset.card_singleton, Nat.reduceSub] using h
  have hlink : IsCombinatorialManifoldWithBoundary 1
      (SimplicialComplex.geometricLink M {q}) :=
    hlinkBall.isCombinatorialManifoldWithBoundary
  have haB : {a} ∈
      (boundaryComplex 1 (SimplicialComplex.geometricLink M {q})).faces := by
    rw [← geometricLink_boundaryComplex (n := 1) M q]
    exact ha
  have hbB : {b} ∈
      (boundaryComplex 1 (SimplicialComplex.geometricLink M {q})).faces := by
    rw [← geometricLink_boundaryComplex (n := 1) M q]
    exact hb
  exact eventually_height_section_subsingleton_of_boundary_segment
    (SimplicialComplex.geometricLink M {q}) hlink ℓ haB hbB hab hq hside

end DifferentialGeometry.Topology.PiecewiseLinear

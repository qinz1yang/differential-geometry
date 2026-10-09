/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryFacetDirections
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryLinkGerm

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem eventually_geometricLink_section_subsingleton_of_boundary_openSimplex_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [dE : DecidableEq E] (M : Geometry.SimplicialComplex ℝ E) [Finite M.faces]
    (hM : IsPLBall 2 M.space) (ℓ : E →L[ℝ] ℝ) {q : E}
    (hqB : {q} ∈ (boundaryComplex 2 M).faces) {s : Finset E}
    (hscard : s.card = 2) (hqs : q ∈ openSimplex s)
    (hsB : convexHull ℝ (s : Set E) ⊆ (boundaryComplex 2 M).space)
    (hhalf : ∀ᶠ x in 𝓝 q, x ∈ M.space → ℓ x ≤ ℓ q)
    (hboundary : ∀ᶠ x in 𝓝 q,
      x ∈ (boundaryComplex 2 M).space ↔ x ∈ M.space ∧ ℓ x = ℓ q) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ,
      InjOn f (insert q (SimplicialComplex.geometricLink M {q}).vertices) →
        ((SimplicialComplex.geometricLink M {q}).space ∩
          {x | f x = f q}).Subsingleton := by
  classical
  cases Subsingleton.elim dE (Classical.decEq E)
  let _ : Finite (boundaryComplex 2 M).faces :=
    ((Set.toFinite M.faces).subset (boundaryComplex_faces_subset 2 M)).to_subtype
  have hBM : IsCombinatorialManifold 1 (boundaryComplex 2 M) :=
    isCombinatorialManifold_boundaryComplex M hM.isCombinatorialManifoldWithBoundary
  obtain ⟨a, b, hab, ha, hb, hq⟩ :=
    exists_geometricLink_pair_openSegment_of_openSimplex_two
      (boundaryComplex 2 M) hBM hqB hscard hqs hsB
  exact eventually_geometricLink_section_subsingleton_of_halfSpace_boundary_germ
    M hM ℓ hqB ha hb hab hq hhalf hboundary

end DifferentialGeometry.Topology.PiecewiseLinear

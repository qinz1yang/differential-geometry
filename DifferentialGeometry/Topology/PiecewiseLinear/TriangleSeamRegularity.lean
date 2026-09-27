/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryFacetLink
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleEdgeLink
import DifferentialGeometry.Topology.PiecewiseLinear.LinkUnionSection

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem eventually_geometricLink_section_encard_le_two_of_triangle_facet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [dE : DecidableEq E]
    (R M N : Geometry.SimplicialComplex ℝ E) [Finite M.faces]
    (hMR : M.faces ⊆ R.faces)
    (hcover : ∀ s ∈ R.faces, s ∈ M.faces ∨ s ∈ N.faces)
    (hM : IsPLBall 2 M.space) (T : Finset E)
    (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : T.card = 3)
    {a q : E} (ha : a ∈ T) (hq : q ∈ openSimplex (T.erase a))
    (hNspace : N.space = convexHull ℝ (T : Set E))
    (hqM : {q} ∈ (boundaryComplex 2 M).faces)
    (hfacet : convexHull ℝ ((T.erase a : Finset E) : Set E) ⊆
      (boundaryComplex 2 M).space)
    (ℓ : E →L[ℝ] ℝ)
    (hhalf : ∀ᶠ x in 𝓝 q, x ∈ M.space → ℓ x ≤ ℓ q)
    (hboundary : ∀ᶠ x in 𝓝 q,
      x ∈ (boundaryComplex 2 M).space ↔ x ∈ M.space ∧ ℓ x = ℓ q) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ,
      InjOn f (insert q R.vertices ∪ (T : Set E)) →
        ((SimplicialComplex.geometricLink R {q}).space ∩
          {x | f x = f q}).encard ≤ 2 := by
  classical
  cases Subsingleton.elim dE (Classical.decEq E)
  have hFcard : (T.erase a).card = 2 := by
    rw [Finset.card_erase_of_mem ha, hcard]
  have hret :=
    eventually_geometricLink_section_subsingleton_of_boundary_openSimplex_two
      M hM ℓ hqM hFcard hq hfacet hhalf hboundary
  have hlinkV : (SimplicialComplex.geometricLink M {q}).vertices ⊆ R.vertices := by
    intro v hv
    exact hMR (SimplicialComplex.geometricLink_le M {q} hv)
  filter_upwards [hret] with f hf
  intro hfinj
  have hfinjR : InjOn f (insert q R.vertices) := hfinj.mono subset_union_left
  have hfinjM : InjOn f
      (insert q (SimplicialComplex.geometricLink M {q}).vertices) :=
    hfinjR.mono (insert_subset_insert hlinkV)
  have hfinjT : InjOn f (T : Set E) := hfinj.mono subset_union_right
  have hcap := geometricLink_section_subsingleton_of_simplex_facet
    T hT hcard ha (openSimplex_subset_convexHull _ hq) N hNspace f hfinjT
  exact geometricLink_section_encard_le_two_of_faces_cover R M N hcover f
    (hf hfinjM) hcap

end DifferentialGeometry.Topology.PiecewiseLinear

/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleSeamRegularity
import DifferentialGeometry.Topology.PiecewiseLinear.VertexSectionSubdivision

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem eventually_notMem_heightSingularPoints_of_triangle_facet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [dE : DecidableEq E] (hdimE : Module.finrank ℝ E = 3)
    (R M N : Geometry.SimplicialComplex ℝ E) [Finite R.faces] [Finite M.faces]
    (hR : IsPLSphere 2 R.space) (hMR : M.faces ⊆ R.faces)
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
        q ∉ heightSingularPoints R.space f := by
  classical
  cases Subsingleton.elim dE (Classical.decEq E)
  have hqR : {q} ∈ R.faces := hMR (boundaryComplex_faces_subset 2 M hqM)
  have hsection := eventually_geometricLink_section_encard_le_two_of_triangle_facet
    R M N hMR hcover hM T hT hcard ha hq hNspace hqM hfacet ℓ hhalf hboundary
  filter_upwards [hsection] with f hf
  intro hfinj
  have hfinjR : InjOn f (insert q R.vertices) := hfinj.mono subset_union_left
  obtain ⟨u, hu, v, hv, huv⟩ :=
    Finset.one_lt_card.mp (show 1 < T.card by omega)
  have hfne : f ≠ 0 := by
    intro hfzero
    apply huv
    apply hfinj
      (show u ∈ insert q R.vertices ∪ (T : Set E) from Or.inr hu)
      (show v ∈ insert q R.vertices ∪ (T : Set E) from Or.inr hv)
    simp only [hfzero, zero_apply]
  exact notMem_heightSingularPoints_of_geometricLink_section_encard_le_two_of_injOn
    hdimE R hR hqR f hfne hfinjR (hf hfinj)

end DifferentialGeometry.Topology.PiecewiseLinear

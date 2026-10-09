/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleCornerRegularity
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleSeamNonsingular

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem mem_or_exists_mem_openSimplex_erase_of_mem_simplexBoundary_space
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : T.card = 3)
    {q : E} (hq : q ∈ (simplexBoundary T hT).space) :
    q ∈ T ∨ ∃ a ∈ T, q ∈ openSimplex (T.erase a) := by
  obtain ⟨s, hs, hqs⟩ := exists_face_mem_openSimplex (simplexBoundary T hT) hq
  have hscard_pos : 0 < s.card := Finset.card_pos.mpr hs.2.1
  have hscard_le : s.card ≤ 2 := by
    have hproper : s ⊂ T :=
      ⟨hs.1, fun hTs => hs.2.2 (Finset.Subset.antisymm hs.1 hTs)⟩
    have hlt := Finset.card_lt_card hproper
    omega
  by_cases hscard : s.card = 1
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hscard
    have hqa : q = a := by
      have hqconv := openSimplex_subset_convexHull ({a} : Finset E) hqs
      simpa only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] using hqconv
    left
    exact hqa ▸ hs.1 (Finset.mem_singleton_self a)
  · have hscard_two : s.card = 2 := by omega
    obtain ⟨a, haT, has⟩ :=
      Finset.exists_mem_notMem_of_card_lt_card (by omega : s.card < T.card)
    have hserase : s = T.erase a := by
      apply Finset.eq_of_subset_of_card_le
      · intro v hv
        exact Finset.mem_erase.mpr ⟨fun hva => has (hva ▸ hv), hs.1 hv⟩
      · rw [Finset.card_erase_of_mem haT, hcard, hscard_two]
    exact Or.inr ⟨a, haT, hserase ▸ hqs⟩

theorem eventually_notMem_heightSingularPoints_on_triangle_boundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [dE : DecidableEq E] (hdimE : Module.finrank ℝ E = 3)
    (R M N : Geometry.SimplicialComplex ℝ E) [Finite R.faces] [Finite M.faces]
    [Finite N.faces] (hR : IsPLSphere 2 R.space) (hMR : M.faces ⊆ R.faces)
    (hcover : ∀ s ∈ R.faces, s ∈ M.faces ∨ s ∈ N.faces)
    (hM : IsPLBall 2 M.space) (T : Finset E)
    (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : T.card = 3)
    (hNspace : N.space = convexHull ℝ (T : Set E))
    (hboundaryMN : (boundaryComplex 2 M).space = (boundaryComplex 2 N).space)
    (z : E) (ℓ : E →L[ℝ] ℝ)
    (hhalf : ∀ q ∈ (boundaryComplex 2 M).space \ {z},
      ∀ᶠ x in 𝓝 q, x ∈ M.space → ℓ x ≤ ℓ q)
    (hboundary : ∀ q ∈ (boundaryComplex 2 M).space \ {z},
      ∀ᶠ x in 𝓝 q,
        x ∈ (boundaryComplex 2 M).space ↔ x ∈ M.space ∧ ℓ x = ℓ q) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∀ p ∈ T,
      InjOn f (R.vertices ∪ (T : Set E)) →
      (∀ x ∈ convexHull ℝ (T : Set E) \ {p}, f p < f x) →
      ∀ q ∈ (boundaryComplex 2 M).vertices \ {z},
        q ∉ heightSingularPoints R.space f := by
  classical
  cases Subsingleton.elim dE (Classical.decEq E)
  let _ : Finite (boundaryComplex 2 M).faces :=
    (boundaryComplex_faces_finite 2 M).to_subtype
  have hboundaryN : (boundaryComplex 2 N).space = (simplexBoundary T hT).space :=
    boundaryComplex_space_eq_simplexBoundary_of_space_eq_convexHull N T hT hcard hNspace
  have hV : ((boundaryComplex 2 M).vertices \ {z}).Finite :=
    (Set.Finite.preimage Finset.singleton_injective.injOn
      (Set.toFinite (boundaryComplex 2 M).faces)).subset sdiff_subset
  have hall : ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ,
      ∀ q ∈ (boundaryComplex 2 M).vertices \ {z}, ∀ p ∈ (T : Set E),
        InjOn f (R.vertices ∪ (T : Set E)) →
        (∀ x ∈ convexHull ℝ (T : Set E) \ {p}, f p < f x) →
          q ∉ heightSingularPoints R.space f := by
    rw [hV.eventually_all]
    intro q hq
    rw [T.finite_toSet.eventually_all]
    intro p hp
    have hqMspace : q ∈ (boundaryComplex 2 M).space :=
      (boundaryComplex 2 M).vertices_subset_space hq.1
    have hqz : q ≠ z := by simpa only [mem_singleton_iff] using hq.2
    have hqNspace : q ∈ (boundaryComplex 2 N).space := hboundaryMN ▸ hqMspace
    have hqsimplex : q ∈ (simplexBoundary T hT).space := hboundaryN ▸ hqNspace
    have hqR : q ∈ R.vertices := by
      exact hMR (boundaryComplex_faces_subset 2 M hq.1)
    rcases mem_or_exists_mem_openSimplex_erase_of_mem_simplexBoundary_space
      T hT hcard hqsimplex with hqT | ⟨a, ha, hqopen⟩
    · have hcorner := eventually_notMem_heightSingularPoints_of_triangle_vertex
        hdimE R M N hR hMR hcover hM T hT hcard hp hqT hNspace hboundaryMN ℓ
        (hhalf q ⟨hqMspace, hqz⟩) (hboundary q ⟨hqMspace, hqz⟩)
      filter_upwards [hcorner] with f hf
      intro hfinj hstrict
      apply hf
      · simpa only [insert_eq_of_mem hqR] using hfinj
      · exact hstrict
    · have hfacet : convexHull ℝ ((T.erase a : Finset E) : Set E) ⊆
          (boundaryComplex 2 M).space := by
        rw [hboundaryMN, hboundaryN]
        exact (simplexBoundary T hT).convexHull_subset_space
          (erase_mem_simplexBoundary_faces hT (by omega) ha)
      have hseam := eventually_notMem_heightSingularPoints_of_triangle_facet
        hdimE R M N hR hMR hcover hM T hT hcard ha hqopen hNspace hq.1 hfacet ℓ
        (hhalf q ⟨hqMspace, hqz⟩) (hboundary q ⟨hqMspace, hqz⟩)
      filter_upwards [hseam] with f hf
      intro hfinj _
      apply hf
      simpa only [insert_eq_of_mem hqR] using hfinj
  filter_upwards [hall] with f hf
  intro p hp hfinj hstrict q hq
  exact hf q hq p hp hfinj hstrict

end DifferentialGeometry.Topology.PiecewiseLinear

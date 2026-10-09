/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryArcSection
import DifferentialGeometry.Topology.PiecewiseLinear.HeightPerturbation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem eventually_height_section_subsingleton_of_boundary_segment
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifoldWithBoundary 1 L) (ℓ : E →L[ℝ] ℝ)
    {q a b : E} (ha : {a} ∈ (boundaryComplex 1 L).faces)
    (hb : {b} ∈ (boundaryComplex 1 L).faces) (hab : a ≠ b)
    (hq : q ∈ openSegment ℝ a b)
    (hside : ∀ v ∈ L.vertices, v ≠ a → v ≠ b → ℓ v < ℓ q) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, InjOn f (insert q L.vertices) →
      (L.space ∩ {x | f x = f q}).Subsingleton := by
  have hvertices : L.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite L.faces)
  have hfinite : (insert q L.vertices).Finite := hvertices.insert q
  have horder := eventually_preserves_strict_order hfinite ℓ
  have haV : a ∈ L.vertices := boundaryComplex_faces_subset 1 L ha
  have hbV : b ∈ L.vertices := boundaryComplex_faces_subset 1 L hb
  filter_upwards [horder] with f hforder
  intro hfinj
  have hfab : f a ≠ f b := by
    intro h
    apply hab
    apply hfinj
    · exact Set.mem_insert_iff.mpr (Or.inr haV)
    · exact Set.mem_insert_iff.mpr (Or.inr hbV)
    · exact h
  have hfq : f q ∈ openSegment ℝ (f a) (f b) := by
    have hfq' := Set.mem_image_of_mem f.toLinearMap.toAffineMap hq
    rw [image_openSegment] at hfq'
    exact hfq'
  rcases lt_or_gt_of_ne hfab with hfablt | hfbalt
  · rw [openSegment_eq_Ioo hfablt] at hfq
    apply height_section_subsingleton_of_unique_high_boundary_vertex
      L hL hb f.toLinearMap (f q) hfq.2
    intro v hv hvb
    by_cases hva : v = a
    · exact hva ▸ hfq.1
    · exact hforder v (Set.mem_insert_iff.mpr (Or.inr hv)) q
        (Set.mem_insert_iff.mpr (Or.inl rfl)) (hside v hv hva hvb)
  · have hfq' : f q ∈ openSegment ℝ (f b) (f a) := by
      rwa [openSegment_symm]
    rw [openSegment_eq_Ioo hfbalt] at hfq'
    apply height_section_subsingleton_of_unique_high_boundary_vertex
      L hL ha f.toLinearMap (f q) hfq'.2
    intro v hv hva
    by_cases hvb : v = b
    · exact hvb ▸ hfq'.1
    · exact hforder v (Set.mem_insert_iff.mpr (Or.inr hv)) q
        (Set.mem_insert_iff.mpr (Or.inl rfl)) (hside v hv hva hvb)

end DifferentialGeometry.Topology.PiecewiseLinear

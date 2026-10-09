/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallStarring
import DifferentialGeometry.Topology.PiecewiseLinear.CellAttachment
import DifferentialGeometry.Topology.PiecewiseLinear.CellMapTriangulation
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexNhdsWithin

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open Classical in
theorem boundaryComplex_space_of_isPLCellAttachmentWith_zero [FiniteDimensional ℝ E]
    {L N' : Geometry.SimplicialComplex ℝ E} [Finite L.faces] [Finite N'.faces]
    (hL : IsCombinatorialManifoldWithBoundary 3 L)
    (hN' : IsCombinatorialManifoldWithBoundary 3 N') {C : Set E} {g : (Fin 4 → ℝ) → E}
    (hatt : IsPLCellAttachmentWith 3 (Convexity.StdSimplex.coordinateSet ℝ (Fin 4)) ∅ L C N'.space g) :
    (boundaryComplex 3 N').space = (boundaryComplex 3 L).space ∪ g '' stdSimplexBoundary 3 := by
  obtain ⟨hP, hBP, hg, hgB, φ, hφ, hφg, hφbd, e, helow, hecell⟩ := hatt
  have hN : N'.space = L.space ∪ C := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨q, hq⟩ := Quot.exists_rep (e.symm ⟨x, hx⟩)
      have hqe : e (Quot.mk (adjunctionRel Subtype.val φ) q) = ⟨x, hx⟩ := by
        rw [hq, e.apply_symm_apply]
      cases q with
      | inl z =>
          have hzx : (e (adjunctionCell Subtype.val φ z) : E) = x := by
            change (e (Quot.mk (adjunctionRel Subtype.val φ) (Sum.inl z)) : E) = x
            exact congrArg Subtype.val hqe
          have hzC : g z ∈ C := hg.bijOn.mapsTo z.property
          right
          rw [← hzx, hecell z]
          exact hzC
      | inr z =>
          have hzx : (e (adjunctionLower φ z) : E) = x := by
            change (e (Quot.mk (adjunctionRel Subtype.val φ) (Sum.inr z)) : E) = x
            exact congrArg Subtype.val hqe
          left
          rw [← hzx, helow z]
          exact z.property
    · rintro x (hx | hx)
      · have hxN := (e (adjunctionLower φ ⟨x, hx⟩)).property
        rwa [helow ⟨x, hx⟩] at hxN
      · obtain ⟨z, hz, hzx⟩ := hg.bijOn.surjOn hx
        have hzN := (e (adjunctionCell Subtype.val φ ⟨z, hz⟩)).property
        rw [hecell ⟨z, hz⟩] at hzN
        rwa [hzx] at hzN
  have hdis : Disjoint L.space C := by
    have hCL : C ∩ L.space = ∅ := by
      simpa using hgB.image_eq.symm
    rw [Set.disjoint_left]
    intro x hxL hxC
    have hx : x ∈ C ∩ L.space := ⟨hxC, hxL⟩
    rw [hCL] at hx
    exact Set.notMem_empty x hx
  have hCpoly : IsPolyhedron C := by
    rw [← hg.image_eq]
    exact hg.isPiecewiseAffineOn.isPolyhedron_image hP.isPolyhedron
  obtain ⟨Q, hQfin, hQspace⟩ := hCpoly.exists_simplicialComplex
  let _ : Finite Q.faces := hQfin.to_subtype
  have hQball : IsPLBall 3 Q.space := by
    rw [hQspace]
    exact ⟨g, hg⟩
  have hQ : IsCombinatorialManifoldWithBoundary 3 Q := hQball.isCombinatorialManifoldWithBoundary
  have hNL : L.space ⊆ N'.space := by
    rw [hN]
    exact subset_union_left
  have hNQ : Q.space ⊆ N'.space := by
    rw [hN, hQspace]
    exact subset_union_right
  have hLclosed : IsClosed L.space := (isPolyhedron_space L).isClosed
  have hCclosed : IsClosed C := hCpoly.isClosed
  have hLnhds : ∀ x ∈ L.space, L.space ∈ 𝓝[N'.space] x := by
    intro x hx
    have hxC : x ∉ C := fun hxC => disjoint_left.mp hdis hx hxC
    have hO : Cᶜ ∈ 𝓝 x := hCclosed.isOpen_compl.mem_nhds hxC
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hO] with y hyN hyO
    rw [hN] at hyN
    rcases hyN with hyL | hyC
    · exact hyL
    · exact (hyO hyC).elim
  have hQnhds : ∀ x ∈ Q.space, Q.space ∈ 𝓝[N'.space] x := by
    intro x hx
    have hxL : x ∉ L.space := by
      intro hxL
      exact disjoint_left.mp hdis hxL (by rwa [← hQspace])
    have hO : L.spaceᶜ ∈ 𝓝 x := hLclosed.isOpen_compl.mem_nhds hxL
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hO] with y hyN hyO
    rw [hN] at hyN
    rcases hyN with hyL | hyQ
    · exact (hyO hyL).elim
    · exact hQspace.symm ▸ hyQ
  have hQbd : (boundaryComplex 3 Q).space = g '' stdSimplexBoundary 3 := by
    simpa using (hg.image_stdSimplexBoundary_eq_boundaryComplex (m := 2) Q hQspace).symm
  ext x
  constructor
  · intro hx
    have hxN : x ∈ N'.space := boundaryComplex_space_subset 3 N' hx
    rw [hN] at hxN
    rcases hxN with hxL | hxC
    · left
      exact (mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin N' L hN' hL hNL hxL
        (hLnhds x hxL)).mpr hx
    · right
      have hxQ : x ∈ Q.space := by rwa [hQspace]
      have hxQbd := (mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin N' Q hN' hQ hNQ hxQ
        (hQnhds x hxQ)).mpr hx
      rwa [hQbd] at hxQbd
  · rintro (hxL | hxC)
    · have hxLspace : x ∈ L.space := boundaryComplex_space_subset 3 L hxL
      exact (mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin N' L hN' hL hNL hxLspace
        (hLnhds x hxLspace)).mp hxL
    · have hxQbd : x ∈ (boundaryComplex 3 Q).space := by rwa [hQbd]
      have hxQ : x ∈ Q.space := boundaryComplex_space_subset 3 Q hxQbd
      exact (mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin N' Q hN' hQ hNQ hxQ
        (hQnhds x hxQ)).mp hxQbd

end DifferentialGeometry.Topology.PiecewiseLinear

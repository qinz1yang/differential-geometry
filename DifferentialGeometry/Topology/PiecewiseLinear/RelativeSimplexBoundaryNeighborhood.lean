/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.RelativeSimplexBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Exhaustion

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_derivedNeighborhoodTriangulation_boundary_subset
    {n : ℕ} (K A C : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) (hA : A.faces ⊆ K.faces)
    (hCA : C.faces ⊆ A.faces)
    (hboundary : A.space ∩ (boundaryComplex (n + 1) K).space = C.space)
    {U : Set E} (hU : IsOpen U) (hCU : C.space ⊆ U) :
    ∃ T : DerivedNeighborhoodTriangulation K A,
      C.faces ⊆ (boundaryComplex (n + 1) T.complex).faces ∧
      (PiecewiseLinear.derivedNeighborhood (boundaryComplex (n + 1) T.complex) C).space ⊆
        (boundaryComplex (n + 1) K).space ∩ U := by
  let T := hK.derivedNeighborhoodTriangulation K A hA
  let _ : Finite T.complex.faces := T.finite_faces.to_subtype
  have hT := T.isCombinatorialManifoldWithBoundary hK
  have hTK : T.complex.space ⊆ K.space := by
    rw [T.space_eq]
    exact derivedNeighborhood_space_subset K A
  let O := (closure (K.space \ T.complex.space))ᶜ
  have hO : IsOpen O := isClosed_closure.isOpen_compl
  have hAO : A.space ⊆ O := by
    intro x hx hxcl
    have hnhds : T.complex.space ∈ 𝓝[K.space] x := by
      rw [T.space_eq]
      exact derivedNeighborhood_mem_nhdsWithin hA hx
    obtain ⟨V, hV, hVT⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hnhds
    obtain ⟨y, hyV, hyK, hyT⟩ := mem_closure_iff_nhds.mp hxcl V hV
    exact hyT (hVT ⟨hyV, hyK⟩)
  have hOT : O ∩ K.space ⊆ T.complex.space := by
    rintro x ⟨hxO, hxK⟩
    by_contra hxT
    exact hxO (subset_closure ⟨hxK, hxT⟩)
  let B := boundaryComplex (n + 1) T.complex
  let _ : Finite B.faces := (boundaryComplex_faces_finite (n + 1) T.complex).to_subtype
  let Q := B.space \ (O ∩ U)
  have hQ : IsClosed Q := (isPolyhedron_space B).isClosed.sdiff (hO.inter hU)
  have hAQ : A.space ⊆ Qᶜ := by
    rintro x hx ⟨hxB, hxOU⟩
    have hxC : x ∈ C.space := hboundary.subset
      ⟨hx, (T.mem_boundaryComplex_iff hK hA hx).mp hxB⟩
    exact hxOU ⟨hAO hx, hCU hxC⟩
  obtain ⟨R, hR, hfinR, hAR, hsmall⟩ :=
    exists_isSubdivision_regularNeighborhoodIn_subset_of_isOpen T.complex A T.faces_subset
      hQ.isOpen_compl hAQ
  let T' : DerivedNeighborhoodTriangulation K A :=
    ⟨R, hfinR, hAR, hR.space_eq.trans T.space_eq⟩
  let _ : Finite R.faces := hfinR.to_subtype
  have hRboundary : (boundaryComplex (n + 1) R).space = B.space :=
    (T'.boundaryComplex_space hK).trans (T.boundaryComplex_space hK).symm
  have hCboundary : C.space ⊆ (boundaryComplex (n + 1) K).space := by
    rw [← hboundary]
    exact inter_subset_right
  refine ⟨T', T'.faces_subset_boundaryComplex hK hA hCA hCboundary, ?_⟩
  have hNQ : (PiecewiseLinear.derivedNeighborhood (boundaryComplex (n + 1) R) C).space ⊆ Qᶜ := by
    apply derivedNeighborhood_space_subset_of_forall_face
    intro s hs t ht hst x hx
    apply hsmall
    have htR := boundaryComplex_faces_subset (n + 1) R ht
    exact (regularNeighborhoodIn R A.space).convexHull_subset_space
      ⟨htR, t, htR, Finset.Subset.refl t, s.centroid ℝ id, hst,
        A.convexHull_subset_space (hCA hs)
          (s.centroid_mem_convexHull (C.nonempty_of_mem_faces hs))⟩ hx
  intro x hx
  have hxRboundary := derivedNeighborhood_space_subset (boundaryComplex (n + 1) R) C hx
  have hxB : x ∈ B.space := hRboundary ▸ hxRboundary
  have hxOU : x ∈ O ∩ U := by
    by_contra hxOU
    exact hNQ hx ⟨hxB, hxOU⟩
  have hxT : x ∈ T.complex.space := boundaryComplex_space_subset (n + 1) T.complex hxB
  have hnhds : T.complex.space ∈ 𝓝[K.space] x :=
    Filter.mem_of_superset (inter_mem_nhdsWithin K.space (hO.mem_nhds hxOU.1))
      (fun _ hx => hOT ⟨hx.2, hx.1⟩)
  exact ⟨(mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin K T.complex hK hT
    hTK hxT hnhds).mp hxB, hxOU.2⟩

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_derivedNeighborhoodTriangulation_boundary_mem
    {n : ℕ} (K A C : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) (hA : A.faces ⊆ K.faces)
    (hCA : C.faces ⊆ A.faces)
    (hboundary : A.space ∩ (boundaryComplex (n + 1) K).space = C.space)
    {V : Set E} (hV : V ∈ 𝓝ˢ[(boundaryComplex (n + 1) K).space] C.space) :
    ∃ T : DerivedNeighborhoodTriangulation K A,
      C.faces ⊆ (boundaryComplex (n + 1) T.complex).faces ∧
      (PiecewiseLinear.derivedNeighborhood (boundaryComplex (n + 1) T.complex) C).space ⊆
        (boundaryComplex (n + 1) K).space ∩ V := by
  obtain ⟨U, hU, hCU, hUV⟩ := mem_nhdsSetWithin.mp hV
  obtain ⟨T, hCT, hsmall⟩ :=
    hK.exists_derivedNeighborhoodTriangulation_boundary_subset K A C hA hCA hboundary hU hCU
  refine ⟨T, hCT, fun x hx => ?_⟩
  have hx' := hsmall hx
  exact ⟨hx'.1, hUV ⟨hx'.2, hx'.1⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear

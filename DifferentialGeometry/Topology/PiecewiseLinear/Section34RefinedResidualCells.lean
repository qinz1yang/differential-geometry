/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34LocalResidualCells

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {d : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin d)) X] {U : Set X}

theorem LocallyFinitePLPieceIn.restrict_faces_finite_of_isCompact
    (T : LocallyFinitePLPieceIn E d X U) {P : Set E} (hP : IsCompact P)
    (hPT : P ⊆ T.complex.space) : (restrict T.complex P).faces.Finite := by
  let C : Set T.complex.space := (Subtype.val : T.complex.space → E) ⁻¹' P
  have hC : IsCompact C := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.mpr hPT]
    exact hP
  refine ((T.locallyFinite.finite_nonempty_inter_compact hC).image Subtype.val).subset ?_
  intro s hs
  have hc := s.centroid_mem_convexHull (R := ℝ) (T.complex.nonempty_of_mem_faces hs.1)
  exact ⟨⟨s, hs.1⟩, ⟨⟨s.centroid ℝ id, T.complex.convexHull_subset_space hs.1 hc⟩,
    hc, hs.2 hc⟩, rfl⟩

open Classical in
theorem LocallyFinitePLPieceIn.closure_convexHull_sdiff_derivedNeighborhood_of_subdivision
    (T : LocallyFinitePLPieceIn E d X U) {K L : Geometry.SimplicialComplex ℝ E}
    (hsub : IsSubdivision T.complex K) (hL : L.faces ⊆ T.complex.faces)
    {s : Finset E} (hs : s ∈ K.faces) :
    closure (convexHull ℝ (s : Set E) \ (derivedNeighborhood T.complex L).space) =
      ⋃ t ∈ {t : Finset E | t ∈ T.complex.faces ∧
        convexHull ℝ (t : Set E) ⊆ convexHull ℝ (s : Set E) ∧ t ∉ L.faces},
          (derivedNeighborhoodCell (restrict T.complex (convexHull ℝ (s : Set E))) t).space := by
  let S := restrict T.complex (convexHull ℝ (s : Set E))
  have hSP : S.space = convexHull ℝ (s : Set E) :=
    restrict_space_of_eq_biUnion T.complex _ (hsub.convexHull_eq_biUnion hs)
  have hSK := restrict_faces_subset T.complex (convexHull ℝ (s : Set E))
  have hP : convexHull ℝ (s : Set E) ⊆ T.complex.space :=
    (K.convexHull_subset_space hs).trans hsub.space_eq.symm.subset
  let _ : Finite S.faces :=
    (T.restrict_faces_finite_of_isCompact (s.finite_toSet.isCompact_convexHull ℝ) hP).to_subtype
  have heq : convexHull ℝ (s : Set E) \ (derivedNeighborhood T.complex L).space =
      S.space \ (derivedNeighborhood S L).space := by
    rw [← derivedNeighborhood_space_inter_subcomplex T.complex S L hSK, hSP]
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  rw [heq, closure_space_sdiff_derivedNeighborhood_space hSK hL]
  simp only [mem_restrict_faces_iff, and_assoc]

end DifferentialGeometry.Topology.PiecewiseLinear

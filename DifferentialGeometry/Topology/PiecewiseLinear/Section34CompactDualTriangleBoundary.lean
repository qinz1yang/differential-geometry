/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualTraces
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTriangleBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
theorem compactDualCutBoundary_faceDisk_eq_local
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (s : Section34CompactSimplexIndex K 3) :
    compactDualCutBoundary M K hKM (.faceDisk s) =
      (boundaryComplex 2
        (derivedNeighborhoodCell (restrict M (convexHull ℝ (s.1 : Set E3))) s.1)).space := by
  change (boundaryComplex 2
    (restrict (secondDerived M) (compactDualResidualCell M K s.1))).space = _
  rw [compactDualResidualCell_eq_derived_triangle M K hKM s]
  let S := restrict M (convexHull ℝ (s.1 : Set E3))
  have hSM : S.faces ⊆ M.faces := restrict_faces_subset M _
  have hDc : (derivedNeighborhoodCell S s.1).faces ⊆
      (@secondDerived E3 _ _ (Classical.decEq E3) M).faces :=
    (derivedNeighborhoodCell_faces_subset S s.1).trans
      (@secondDerived_faces_subset E3 _ _ (Classical.decEq E3) _ _ hSM)
  have hR : @secondDerived E3 _ _ (Classical.decEq E3) M = secondDerived M :=
    congrArg (fun d : DecidableEq E3 => @secondDerived E3 _ _ d M)
      (Subsingleton.elim _ _)
  rw [restrict_eq_of_subcomplex _ _ (hR ▸ hDc)]

open Classical in
theorem mem_compactTriangleGraph_faces_iff
    (M K : Geometry.SimplicialComplex ℝ E3) (hKM : K.faces ⊆ M.faces)
    (s : Section34CompactSimplexIndex K 3) (r : Finset E3) :
    r ∈ (restrict (restrict K (section34CompactGraphSkeleton K))
      (restrict M (convexHull ℝ (s.1 : Set E3))).space).faces ↔
      r ∈ (restrict M (convexHull ℝ (s.1 : Set E3))).faces ∧ r ≠ s.1 := by
  let S := restrict M (convexHull ℝ (s.1 : Set E3))
  let L := restrict K (section34CompactGraphSkeleton K)
  have hsM := hKM s.2.1
  have hSM : S.faces ⊆ M.faces := restrict_faces_subset _ _
  have hLM : L.faces ⊆ M.faces := (restrict_faces_subset _ _).trans hKM
  constructor
  · intro hr
    have hrS : r ∈ S.faces :=
      ((mem_restrict_faces_iff_of_faces_subset M L S hLM hSM).mp hr).2
    have hrc := card_le_two_of_mem_restrict_section34CompactGraphSkeleton hr.1
    refine ⟨hrS, fun heq => ?_⟩
    rw [heq, s.2.2] at hrc
    omega
  · rintro ⟨hrS, hrne⟩
    have hrs := ((mem_restrict_convexHull_faces_iff M hsM).mp hrS).2
    have hrK := K.down_closed s.2.1 hrs (S.nonempty_of_mem_faces hrS)
    have hrc : r.card ≤ 2 := by
      have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hrs, hrne⟩)
      rw [s.2.2] at hlt
      omega
    exact ⟨⟨hrK, convexHull_subset_section34CompactGraphSkeleton hrK hrc⟩,
      S.convexHull_subset_space hrS⟩

open Classical in
theorem compactDualFaceArc_eq_localTrace
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (a : Section34CompactArcIndex K K) :
    let S := restrict M (convexHull ℝ (a.1.1.1 : Set E3))
    let H := restrict (restrict K (section34CompactGraphSkeleton K)) S.space
    compactDualCutCell M K hKM (.faceArc a) =
      (graphDualCell S H (a.1.2.1.centroid ℝ id)).space ∩
        (derivedNeighborhoodCell S a.1.1.1).space := by
  dsimp only
  let s := a.1.1
  let w := a.1.2
  let v := w.1.centroid ℝ id
  let S := restrict M (convexHull ℝ (s.1 : Set E3))
  let L := restrict K (section34CompactGraphSkeleton K)
  let H := restrict L S.space
  have hvK : {v} ∈ K.faces := by
    rw [show ({v} : Finset E3) = w.1 from singleton_centroid_eq_compactVertexIndex w]
    exact w.2.1
  have hvConv : v ∈ convexHull ℝ (s.1 : Set E3) := a.2 (by
    change v ∈ (w.1 : Set E3)
    rw [← singleton_centroid_eq_compactVertexIndex w]
    exact Finset.mem_singleton_self _)
  have hvS : {v} ∈ S.faces := ⟨hKM hvK, by
    simpa only [Finset.coe_singleton, convexHull_singleton, singleton_subset_iff] using hvConv⟩
  have hSM : S.faces ⊆ M.faces := restrict_faces_subset _ _
  have hLM : L.faces ⊆ M.faces := (restrict_faces_subset _ _).trans hKM
  change (graphDualCell M L v).space ∩ compactDualResidualCell M K s.1 = _
  rw [compactDualResidualCell_eq_derived_triangle M K hKM s]
  calc
    _ = ((graphDualCell M L v).space ∩ S.space) ∩
        (derivedNeighborhoodCell S s.1).space := by
      ext x
      exact ⟨fun h => ⟨⟨h.1, derivedNeighborhoodCell_space_subset S s.1 h.2⟩, h.2⟩,
        fun h => ⟨h.1.1, h.2⟩⟩
    _ = _ := by
      rw [graphDualCell_space_inter_subcomplex_restrict M S L hSM hLM hvS]

open Classical in
theorem compactDualCutBoundary_faceDisk_eq_iUnion_faceArc
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (s : Section34CompactSimplexIndex K 3) :
    compactDualCutBoundary M K hKM (.faceDisk s) =
      ⋃ (a : Section34CompactArcIndex K K) (_ : a.1.1 = s),
        compactDualCutCell M K hKM (.faceArc a) := by
  let S := restrict M (convexHull ℝ (s.1 : Set E3))
  let H := restrict (restrict K (section34CompactGraphSkeleton K)) S.space
  let _ : Finite S.faces := (restrict_faces_finite M _).to_subtype
  have hsS : s.1 ∈ S.faces := ⟨hKM s.2.1, subset_rfl⟩
  have hmax : ∀ r ∈ S.faces, r ⊆ s.1 :=
    fun r hr => ((mem_restrict_convexHull_faces_iff M (hKM s.2.1)).mp hr).2
  have hH : ∀ r, r ∈ H.faces ↔ r ∈ S.faces ∧ r ≠ s.1 :=
    mem_compactTriangleGraph_faces_iff M K hKM s
  rw [compactDualCutBoundary_faceDisk_eq_local M K hKM s]
  have hB : (boundaryComplex 2 (derivedNeighborhoodCell S s.1)).space =
      (@boundaryComplex E3 _ _ (Classical.decEq E3) 2
        (derivedNeighborhoodCell S s.1)).space :=
    congrArg (fun d : DecidableEq E3 =>
      (@boundaryComplex E3 _ _ d 2 (derivedNeighborhoodCell S s.1)).space)
      (Subsingleton.elim _ _)
  rw [hB, boundaryComplex_triangleCell_eq_iUnion_graphDualCell S H hsS s.2.2 hmax hH]
  apply Subset.antisymm
  · intro x hx
    obtain ⟨v, hvs, hxv⟩ := mem_iUnion₂.mp hx
    have hvK : {v} ∈ K.faces := K.down_closed s.2.1
      (Finset.singleton_subset_iff.mpr hvs) (Finset.singleton_nonempty _)
    let w : Section34CompactVertexIndex K K := ⟨{v}, hvK, Finset.card_singleton _,
      convexHull_subset_section34CompactGraphSkeleton hvK (by simp)⟩
    have hinc : Section34Incident w.1 s.1 := by
      intro y hy
      have hyv : y = v := Finset.mem_singleton.mp hy
      subst y
      exact subset_convexHull ℝ _ hvs
    let a : Section34CompactArcIndex K K := ⟨(s, w), hinc⟩
    refine mem_iUnion₂.mpr ⟨a, rfl, ?_⟩
    rw [compactDualFaceArc_eq_localTrace M K hKM a]
    simpa only [a, w, Finset.centroid_singleton, id_eq] using hxv
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hx
    let v := a.1.2.1.centroid ℝ id
    have hvK : {v} ∈ K.faces := by
      rw [show ({v} : Finset E3) = a.1.2.1 from
        singleton_centroid_eq_compactVertexIndex a.1.2]
      exact a.1.2.2.1
    have hvConv : v ∈ convexHull ℝ (a.1.1.1 : Set E3) := a.2 (by
      rw [← singleton_centroid_eq_compactVertexIndex a.1.2]
      exact Finset.mem_singleton_self _)
    have hvs : v ∈ s.1 := by
      have hv := mem_of_mem_convexHull_of_singleton_mem K hvK a.1.1.2.1 hvConv
      simpa only [ha] using hv
    refine mem_iUnion₂.mpr ⟨v, hvs, ?_⟩
    rw [compactDualFaceArc_eq_localTrace M K hKM a] at hxa
    simpa only [ha] using hxa

end DifferentialGeometry.Topology.PiecewiseLinear

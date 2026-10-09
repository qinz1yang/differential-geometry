/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualSubcomplex
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualTetraBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem patch_incident_subset {K : Geometry.SimplicialComplex ℝ E3}
    {e s : Finset E3} (he : e ∈ K.faces) (hs : s ∈ K.faces)
    (h : Section34Incident e s) : e ⊆ s := by
  classical
  intro v hv
  have hvK := K.down_closed he (Finset.singleton_subset_iff.mpr hv)
    (Finset.singleton_nonempty v)
  exact mem_of_mem_convexHull_of_singleton_mem K hvK hs (h hv)

open Classical in
theorem compactTetraBoundary_eq_iUnion_faces
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (t : Section34CompactSimplexIndex K 4) :
    (boundaryComplex 3 (restrict M (convexHull ℝ (t.1 : Set E3)))).space =
      ⋃ (s : Section34CompactSimplexIndex K 3) (_ : Section34Incident s.1 t.1),
        convexHull ℝ (s.1 : Set E3) := by
  let dNative : DecidableEq E3 := inferInstance
  let : DecidableEq E3 := Classical.decEq E3
  let S := restrict M (convexHull ℝ (t.1 : Set E3))
  let B := boundaryComplex 3 S
  have hNativeBoundary : @boundaryComplex E3 _ _ dNative 3 S = B :=
    congrArg (fun d : DecidableEq E3 => @boundaryComplex E3 _ _ d 3 S)
      (Subsingleton.elim _ _)
  change (@boundaryComplex E3 _ _ dNative 3 S).space = _
  rw [hNativeBoundary]
  let _ : Finite S.faces := (restrict_faces_finite M _).to_subtype
  let _ : Finite B.faces := (boundaryComplex_faces_finite 3 S).to_subtype
  have hSB : B = simplexBoundary t.1 (M.indep (hKM t.2.1)) := by
    dsimp only [B, S]
    rw [restrict_convexHull_eq_simplexComplex M (hKM t.2.1)]
    exact boundaryComplex_simplexComplex (M.indep (hKM t.2.1)) t.2.2
  have hSball : IsPLBall 3 S.space := by
    rw [show S.space = convexHull ℝ (t.1 : Set E3) from restrict_convexHull_space (hKM t.2.1)]
    exact isPLBall_convexHull_of_affineIndependent t.1 (M.indep (hKM t.2.1)) t.2.2
  have hB : IsPLSphere 2 B.space := isPLSphere_boundaryComplex_space_of_isPLBall S hSball
  apply Subset.antisymm
  · intro z hz
    obtain ⟨r, hr, hzr⟩ := B.mem_space_iff.mp hz
    obtain ⟨s, hsB, hrs, hsc⟩ := exists_face_superset_card_eq_of_isPLSphere B hB hr
    have hsS := boundaryComplex_faces_subset 3 S hsB
    obtain ⟨hsne, hst⟩ := (mem_restrict_convexHull_faces_iff M (hKM t.2.1)).mp hsS
    let f : Section34CompactSimplexIndex K 3 := ⟨s, K.down_closed t.2.1 hst hsne, hsc⟩
    exact mem_iUnion₂.mpr ⟨f,
      (Finset.coe_subset.mpr hst).trans (subset_convexHull ℝ _),
      convexHull_mono (Finset.coe_subset.mpr hrs) hzr⟩
  · intro z hz
    obtain ⟨s, hst, hzs⟩ := mem_iUnion₂.mp hz
    have hsub := patch_incident_subset s.2.1 t.2.1 hst
    have hsB : s.1 ∈ B.faces := by
      rw [hSB]
      refine ⟨hsub, K.nonempty_of_mem_faces s.2.1, ?_⟩
      intro heq
      have hc := congrArg Finset.card heq
      rw [s.2.2, t.2.2] at hc
      omega
    exact B.convexHull_subset_space hsB hzs

open Classical in
theorem compactDualPatch_inter_tetraBoundary
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (x : Section34CompactPatchIndex K K) :
    compactDualCutCell M K hKM (.patch x) ∩
        (boundaryComplex 3 (restrict M (convexHull ℝ (x.1.1.1 : Set E3)))).space =
      ⋃ (a : Section34CompactArcIndex K K)
        (_ : a.1.2 = x.1.2 ∧ Section34Incident a.1.1.1 x.1.1.1),
          compactDualCutCell M K hKM (.faceArc a) := by
  let : DecidableEq E3 := Classical.decEq E3
  let t := x.1.1
  let w := x.1.2
  let v := w.1.centroid ℝ id
  let L := restrict K (section34CompactGraphSkeleton K)
  have hvM : {v} ∈ M.faces := by
    rw [show ({v} : Finset E3) = w.1 from singleton_centroid_eq_compactVertexIndex w]
    exact hKM w.2.1
  rw [compactTetraBoundary_eq_iUnion_faces M K hKM t]
  apply Subset.antisymm
  · rintro z ⟨hp, hb⟩
    obtain ⟨s, hst, hzs⟩ := mem_iUnion₂.mp hb
    have hsub := patch_incident_subset s.2.1 t.2.1 hst
    have hzR : z ∈ compactDualResidualCell M K s.1 :=
      (compactDualResidualCell_inter_convexHull M K hKM t.2.1 s.2.1 hsub) ▸ ⟨hp.1, hzs⟩
    have hvs : v ∈ s.1 := by
      have hzD := graphDualCell_space_subset_closedStar M L v hp.2
      rw [closedStar_barycentricSubdivision_eq_dualCell M hvM] at hzD
      have h := subset_of_mem_dualCell_of_mem_convexHull M hvM (hKM s.2.1) hzD hzs
      exact Finset.singleton_subset_iff.mp h
    have hws : Section34Incident w.1 s.1 := by
      rw [← singleton_centroid_eq_compactVertexIndex w]
      intro q hq
      have hqv : q = v := Finset.mem_singleton.mp hq
      subst q
      exact subset_convexHull ℝ _ hvs
    let a : Section34CompactArcIndex K K := ⟨(s, w), hws⟩
    exact mem_iUnion₂.mpr ⟨a, ⟨rfl, hst⟩, hp.2, hzR⟩
  · intro z hz
    obtain ⟨a, ⟨haw, hat⟩, hza⟩ := mem_iUnion₂.mp hz
    have hsub := patch_incident_subset a.1.1.2.1 t.2.1 hat
    have hzI : z ∈ compactDualResidualCell M K t.1 ∩
        convexHull ℝ (a.1.1.1 : Set E3) :=
      (compactDualResidualCell_inter_convexHull M K hKM t.2.1 a.1.1.2.1 hsub).symm ▸ hza.2
    refine ⟨⟨hzI.1, ?_⟩, mem_iUnion₂.mpr ⟨a.1.1, hat, hzI.2⟩⟩
    simpa only [haw] using hza.1

open Classical in
theorem compactDualCutBoundary_patch_eq_union
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (x : Section34CompactPatchIndex K K) :
    compactDualCutBoundary M K hKM (.patch x) =
      (⋃ (a : Section34CompactArcIndex K K)
        (_ : a.1.2 = x.1.2 ∧ Section34Incident a.1.1.1 x.1.1.1),
          compactDualCutCell M K hKM (.faceArc a)) ∪
      ⋃ (i : Section34CompactEdgeArcIndex K K)
        (_ : i.1.1 = x.1.1 ∧ x.1.2.1 ⊆ i.1.2.1),
          compactDualCutCell M K hKM (.edgeArc i) := by
  let : DecidableEq E3 := Classical.decEq E3
  let t := x.1.1
  let w := x.1.2
  let v := w.1.centroid ℝ id
  let L := restrict K (section34CompactGraphSkeleton K)
  let S := restrict M (convexHull ℝ (t.1 : Set E3))
  let G := restrict L S.space
  let I := {e : Finset E3 // e ∈ G.faces ∧ e.card = 2 ∧ v ∈ e}
  have hSsp : S.space = convexHull ℝ (t.1 : Set E3) := restrict_convexHull_space (hKM t.2.1)
  have hLM : L.faces ⊆ M.faces := (restrict_faces_subset K _).trans hKM
  have hLc : ∀ e ∈ L.faces, e.card ≤ 2 :=
    fun e he => card_le_two_of_mem_restrict_section34CompactGraphSkeleton he
  have hvw : v ∈ w.1 := by
    rw [← singleton_centroid_eq_compactVertexIndex w]
    exact Finset.mem_singleton_self _
  have hsplit (e : Section34CompactEdgeIndex K K) (hwe : w.1 ⊆ e.1) :
      compactDualSplitDisk M K hKM e ⊆ compactDualVertexBall M K w := by
    have hvE := hwe hvw
    obtain ⟨u, hu, huv⟩ := Finset.exists_mem_ne (by rw [e.2.2.1]; omega : 1 < e.1.card) v
    have heL : e.1 ∈ L.faces := ⟨e.2.1, e.2.2.2⟩
    have hi := graphDualCell_space_inter_of_mem M L hLM hLc heL hvE hu huv.symm
    exact hi.symm.subset.trans inter_subset_left
  obtain ⟨q, hq, hqb⟩ := exists_isPLHomeomorphOn_compactDualPatch_with_boundary M K hKM x
  have hlocal := isPLCellOn_id_of_isPLBall hq
  have hcanonical := isPLCellOn_compactDualCutCell_of_isPLBall M K hKM (.patch x) ⟨q, hq⟩
  rw [hcanonical.boundary_eq hlocal, hqb, inter_union_distrib_left,
    compactDualPatch_inter_tetraBoundary M K hKM x]
  congr 1
  change compactDualCutCell M K hKM (.patch x) ∩
      (⋃ e : I, (splittingDisk M e.1 (hKM e.2.1.1.1)).space) = _
  apply Subset.antisymm
  · rintro z ⟨hp, he⟩
    obtain ⟨e, hze⟩ := mem_iUnion.mp he
    let e' : Section34CompactEdgeIndex K K :=
      ⟨e.1, e.2.1.1.1, e.2.2.1, e.2.1.1.2⟩
    have het : Section34Incident e'.1 t.1 :=
      (subset_convexHull ℝ _).trans (e.2.1.2.trans hSsp.subset)
    let i : Section34CompactEdgeArcIndex K K := ⟨(t, e'), het⟩
    have hwe : w.1 ⊆ e'.1 := by
      rw [← singleton_centroid_eq_compactVertexIndex w]
      exact Finset.singleton_subset_iff.mpr e.2.2.2
    exact mem_iUnion₂.mpr ⟨i, ⟨rfl, hwe⟩, hp.1, hze⟩
  · intro z hz
    obtain ⟨i, ⟨hit, hwe⟩, hzi⟩ := mem_iUnion₂.mp hz
    let e := i.1.2
    have het : Section34Incident e.1 t.1 := by simpa only [hit] using i.2
    have heS : convexHull ℝ (e.1 : Set E3) ⊆ S.space := by
      rw [hSsp]
      exact convexHull_min het (convex_convexHull ℝ _)
    let e' : I := ⟨e.1, ⟨⟨e.2.1, e.2.2.2⟩, heS⟩, e.2.2.1, hwe hvw⟩
    have hzR : z ∈ compactDualResidualCell M K t.1 := by simpa only [hit] using hzi.1
    exact ⟨⟨hzR, hsplit e hwe hzi.2⟩, mem_iUnion.mpr ⟨e', hzi.2⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear

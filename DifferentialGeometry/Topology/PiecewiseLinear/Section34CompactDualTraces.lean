/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallPairTwoSimplices
import DifferentialGeometry.Topology.PiecewiseLinear.GraphDualCellSubgraph
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualSubcomplex
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactEdgeTraces
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactResidualRecognition
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexSubcomplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem subset_of_section34Incident {K : Geometry.SimplicialComplex ℝ E3}
    {e s : Finset E3} (he : e ∈ K.faces) (hs : s ∈ K.faces)
    (h : Section34Incident e s) : e ⊆ s := by
  classical
  intro v hv
  have hvK := K.down_closed he (Finset.singleton_subset_iff.mpr hv)
    (Finset.singleton_nonempty v)
  exact mem_of_mem_convexHull_of_singleton_mem K hvK hs (h hv)

open Classical in
theorem exists_subcomplex_compactDualFaceArc
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (a : Section34CompactArcIndex K K) :
    ∃ G : Geometry.SimplicialComplex ℝ E3, G.faces ⊆ (secondDerived M).faces ∧
      G.space = compactDualCutCell M K hKM (.faceArc a) ∧ IsPLBall 1 G.space := by
  let s := a.1.1
  let w := a.1.2
  let v := w.1.centroid ℝ id
  let S := restrict M (convexHull ℝ (s.1 : Set E3))
  let L := restrict K (section34CompactGraphSkeleton K)
  let H := restrict L S.space
  have hsM : s.1 ∈ M.faces := hKM s.2.1
  have hSM : S.faces ⊆ M.faces := restrict_faces_subset _ _
  have hLM : L.faces ⊆ M.faces := (restrict_faces_subset _ _).trans hKM
  have hsS : s.1 ∈ S.faces := ⟨hsM, subset_rfl⟩
  have hmax : ∀ r ∈ S.faces, r ⊆ s.1 :=
    fun r hr => ((mem_restrict_convexHull_faces_iff M hsM).mp hr).2
  have hwsub : w.1 ⊆ s.1 := subset_of_section34Incident w.2.1 s.2.1 a.2
  have hvS : {v} ∈ S.faces := by
    change {w.1.centroid ℝ id} ∈ S.faces
    rw [singleton_centroid_eq_compactVertexIndex w]
    exact (mem_restrict_convexHull_faces_iff M hsM).mpr
      ⟨K.nonempty_of_mem_faces w.2.1, hwsub⟩
  have hvs : v ∈ s.1 := hmax {v} hvS (Finset.mem_singleton_self _)
  have hH : ∀ r, r ∈ H.faces ↔ r ∈ S.faces ∧ r ≠ s.1 := by
    intro r
    constructor
    · intro hr
      have hrS : r ∈ S.faces :=
        ((mem_restrict_faces_iff_of_faces_subset M L S hLM hSM).mp hr).2
      have hrc := card_le_two_of_mem_restrict_section34CompactGraphSkeleton hr.1
      refine ⟨hrS, fun heq => ?_⟩
      rw [heq, s.2.2] at hrc
      omega
    · rintro ⟨hrS, hrne⟩
      have hrs := hmax r hrS
      have hrK := K.down_closed s.2.1 hrs (S.nonempty_of_mem_faces hrS)
      have hrc : r.card ≤ 2 := by
        have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hrs, hrne⟩)
        rw [s.2.2] at hlt
        omega
      exact ⟨⟨hrK, convexHull_subset_section34CompactGraphSkeleton hrK hrc⟩,
        S.convexHull_subset_space hrS⟩
  let G := @upperLink E3 _ _ (Classical.decEq E3) (dualCell S {v} hvS)
    {s.1.centroid ℝ id}
  have hGS : G.faces ⊆ (@secondDerived E3 _ _ (Classical.decEq E3) S).faces :=
    (@upperLink_faces_subset E3 _ _ (Classical.decEq E3) _ _).trans
      (@barycentricSubdivision_faces_subset E3 _ _ (Classical.decEq E3) _ _
        (dualCell_faces_subset S hvS))
  have hGMc := hGS.trans
    (@secondDerived_faces_subset E3 _ _ (Classical.decEq E3) _ _ hSM)
  have hR : @secondDerived E3 _ _ (Classical.decEq E3) M = secondDerived M :=
    congrArg (fun d : DecidableEq E3 => @secondDerived E3 _ _ d M)
      (Subsingleton.elim _ _)
  have hGM : G.faces ⊆ (secondDerived M).faces := hR ▸ hGMc
  let _ : Finite S.faces := (restrict_faces_finite M _).to_subtype
  have htrace : compactDualCutCell M K hKM (.faceArc a) = G.space := by
    change (graphDualCell M L v).space ∩ compactDualResidualCell M K s.1 = _
    rw [compactDualResidualCell_eq_derived_triangle M K hKM s]
    calc
      _ = ((graphDualCell M L v).space ∩ S.space) ∩
          (derivedNeighborhoodCell S s.1).space := by
        ext x
        exact ⟨fun h => ⟨⟨h.1, derivedNeighborhoodCell_space_subset S s.1 h.2⟩, h.2⟩,
          fun h => ⟨h.1.1, h.2⟩⟩
      _ = (graphDualCell S H v).space ∩ (derivedNeighborhoodCell S s.1).space := by
        rw [graphDualCell_space_inter_subcomplex_restrict M S L hSM hLM hvS]
      _ = _ := graphDualCell_inter_derivedNeighborhoodCell_eq_upperLink S H hvS hsS hH
  refine ⟨G, hGM, htrace.symm, ?_⟩
  rw [← graphDualCell_inter_derivedNeighborhoodCell_eq_upperLink S H hvS hsS hH]
  exact isPLBall_graphDualCell_inter_triangleCell S H hsS hvs s.2.2 hmax hH

open Classical in
theorem exists_subcomplex_compactDualEdgeArc
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (i : Section34CompactEdgeArcIndex K K) :
    ∃ G : Geometry.SimplicialComplex ℝ E3, G.faces ⊆ (secondDerived M).faces ∧
      G.space = compactDualCutCell M K hKM (.edgeArc i) ∧ IsPLBall 1 G.space := by
  let t := i.1.1
  let e := i.1.2
  let S := restrict M (convexHull ℝ (t.1 : Set E3))
  have htM : t.1 ∈ M.faces := hKM t.2.1
  have hSM : S.faces ⊆ M.faces := restrict_faces_subset _ _
  have htS : t.1 ∈ S.faces := ⟨htM, subset_rfl⟩
  have het : e.1 ⊆ t.1 := subset_of_section34Incident e.2.1 t.2.1 i.2
  have heS : e.1 ∈ S.faces := (mem_restrict_convexHull_faces_iff M htM).mpr
    ⟨K.nonempty_of_mem_faces e.2.1, het⟩
  have hmax : ∀ r ∈ S.faces, r ⊆ t.1 :=
    fun r hr => ((mem_restrict_convexHull_faces_iff M htM).mp hr).2
  have heB : e.1 ∈ (boundaryComplex 3 S).faces := by
    dsimp only [S]
    rw [restrict_convexHull_eq_simplexComplex M htM,
      boundaryComplex_simplexComplex (M.indep htM) t.2.2]
    refine ⟨het, K.nonempty_of_mem_faces e.2.1, ?_⟩
    intro heq
    have hc := congrArg Finset.card heq
    rw [e.2.2.1, t.2.2] at hc
    omega
  let G := @upperLink E3 _ _ (Classical.decEq E3) (dualCell S e.1 heS)
    {e.1.centroid ℝ id}
  have hGS : G.faces ⊆ (@secondDerived E3 _ _ (Classical.decEq E3) S).faces :=
    (@upperLink_faces_subset E3 _ _ (Classical.decEq E3) _ _).trans
      (@barycentricSubdivision_faces_subset E3 _ _ (Classical.decEq E3) _ _
        (dualCell_faces_subset S heS))
  have hGMc := hGS.trans
    (@secondDerived_faces_subset E3 _ _ (Classical.decEq E3) _ _ hSM)
  have hR : @secondDerived E3 _ _ (Classical.decEq E3) M = secondDerived M :=
    congrArg (fun d : DecidableEq E3 => @secondDerived E3 _ _ d M)
      (Subsingleton.elim _ _)
  have hGM : G.faces ⊆ (secondDerived M).faces := hR ▸ hGMc
  let _ : Finite S.faces := (restrict_faces_finite M _).to_subtype
  have hSball : IsPLBall 3 S.space := by
    rw [show S.space = convexHull ℝ (t.1 : Set E3) from restrict_convexHull_space htM]
    exact isPLBall_convexHull_of_affineIndependent t.1 (M.indep htM) t.2.2
  let R := (derivedNeighborhoodCell S t.1).space ∪
    ⋃ s ∈ t.1.powersetCard 3, (derivedNeighborhoodCell S s).space
  have hRS : R ⊆ S.space := union_subset (derivedNeighborhoodCell_space_subset S t.1)
    (iUnion₂_subset fun s _ => derivedNeighborhoodCell_space_subset S s)
  have htrace : compactDualCutCell M K hKM (.edgeArc i) = G.space := by
    change compactDualResidualCell M K t.1 ∩ (splittingDisk M e.1 (hKM e.2.1)).space = _
    rw [compactDualResidualCell_eq_derived_tetrahedron M K hKM t, inter_comm]
    change (splittingDisk M e.1 (hKM e.2.1)).space ∩ R = _
    calc
      _ = ((splittingDisk M e.1 (hKM e.2.1)).space ∩ S.space) ∩ R := by
        ext x
        exact ⟨fun h => ⟨⟨h.1, hRS h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
      _ = (splittingDisk S e.1 heS).space ∩ R := by
        rw [splittingDisk_space_inter_subcomplex M S hSM heS]
      _ = _ := splittingDisk_inter_tetraResidual_eq_upperLink S heS htS e.2.2.1 t.2.2 hmax
  refine ⟨G, hGM, htrace.symm, ?_⟩
  have hSman := hSball.isCombinatorialManifoldWithBoundary
  have hB : boundaryComplex 3 S = @boundaryComplex E3 _ _ (Classical.decEq E3) 3 S :=
    congrArg (fun d : DecidableEq E3 => @boundaryComplex E3 _ _ d 3 S)
      (Subsingleton.elim _ _)
  exact hSman.isPLBall_upperLink_dualCell_apex_of_mem_boundaryComplex S (hB ▸ heB)
    (k := 1) e.2.2.1

open Classical in
theorem compactDualCutCell_markedPoint_eq_singleton
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (p : Section34CompactMarkIndex K K) :
    compactDualCutCell M K hKM (.markedPoint p) =
      {({p.1.2.1.centroid ℝ id, p.1.1.1.centroid ℝ id} : Finset E3).centroid ℝ id} := by
  let s := p.1.1
  let e := p.1.2
  let S := restrict M (convexHull ℝ (s.1 : Set E3))
  have hsM : s.1 ∈ M.faces := hKM s.2.1
  have hSM : S.faces ⊆ M.faces := restrict_faces_subset _ _
  have hsS : s.1 ∈ S.faces := ⟨hsM, subset_rfl⟩
  have hes : e.1 ⊆ s.1 := subset_of_section34Incident e.2.1 s.2.1 p.2
  have heS : e.1 ∈ S.faces := (mem_restrict_convexHull_faces_iff M hsM).mpr
    ⟨K.nonempty_of_mem_faces e.2.1, hes⟩
  change (splittingDisk M e.1 (hKM e.2.1)).space ∩ compactDualResidualCell M K s.1 = _
  rw [compactDualResidualCell_eq_derived_triangle M K hKM s]
  calc
    _ = ((splittingDisk M e.1 (hKM e.2.1)).space ∩ S.space) ∩
        (derivedNeighborhoodCell S s.1).space := by
      ext x
      exact ⟨fun h => ⟨⟨h.1, derivedNeighborhoodCell_space_subset S s.1 h.2⟩, h.2⟩,
        fun h => ⟨h.1.1, h.2⟩⟩
    _ = (splittingDisk S e.1 heS).space ∩ (derivedNeighborhoodCell S s.1).space := by
      rw [splittingDisk_space_inter_subcomplex M S hSM heS]
    _ = _ := by
      have h := splittingDisk_inter_derivedNeighborhoodCell_eq_singleton S heS hsS hes
        (by rw [s.2.2, e.2.2.1])
        (fun r hr => ((mem_restrict_convexHull_faces_iff M hsM).mp hr).2)
      exact h.trans (congrArg (fun d : DecidableEq E3 =>
        letI : DecidableEq E3 := d
        ({({e.1.centroid ℝ id, s.1.centroid ℝ id} : Finset E3).centroid ℝ id} : Set E3))
        (Subsingleton.elim _ _))

open Classical in
theorem isPLCellOn_compactDualFaceArc
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (a : Section34CompactArcIndex K K) :
    IsPLCellOn 1 (compactDualCutCell M K hKM (.faceArc a))
      (compactDualCutBoundary M K hKM (.faceArc a)) := by
  obtain ⟨G, hGM, hG, hball⟩ := exists_subcomplex_compactDualFaceArc M K hKM a
  apply isPLCellOn_of_isPLBall_restrict_space (secondDerived M) (hG ▸ hball)
  rw [← hG, restrict_eq_of_subcomplex _ _ hGM]

open Classical in
theorem isPLCellOn_compactDualEdgeArc
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (i : Section34CompactEdgeArcIndex K K) :
    IsPLCellOn 1 (compactDualCutCell M K hKM (.edgeArc i))
      (compactDualCutBoundary M K hKM (.edgeArc i)) := by
  obtain ⟨G, hGM, hG, hball⟩ := exists_subcomplex_compactDualEdgeArc M K hKM i
  apply isPLCellOn_of_isPLBall_restrict_space (secondDerived M) (hG ▸ hball)
  rw [← hG, restrict_eq_of_subcomplex _ _ hGM]

open Classical in
theorem isPLCellOn_compactDualMarkedPoint
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (p : Section34CompactMarkIndex K K) :
    IsPLCellOn 0 (compactDualCutCell M K hKM (.markedPoint p))
      (compactDualCutBoundary M K hKM (.markedPoint p)) := by
  have hP := compactDualCutCell_markedPoint_eq_singleton M K hKM p
  have hball : IsPLBall 0 (compactDualCutCell M K hKM (.markedPoint p)) := by
    rw [hP]
    exact isPLBall_zero_singleton _
  exact isPLCellOn_compactDualCutCell_of_isPLBall M K hKM (.markedPoint p) hball

end DifferentialGeometry.Topology.PiecewiseLinear

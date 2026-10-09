/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualTraces
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactEdgeEndpoints

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
theorem compactDualCutBoundary_edgeArc_eq_pair
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (i : Section34CompactEdgeArcIndex K K)
    (s f : Section34CompactSimplexIndex K 3)
    (hes : Section34Incident i.1.2.1 s.1) (hef : Section34Incident i.1.2.1 f.1)
    (hst : Section34Incident s.1 i.1.1.1) (hft : Section34Incident f.1 i.1.1.1)
    (hsf : s ≠ f) :
    compactDualCutBoundary M K hKM (.edgeArc i) =
      {({i.1.2.1.centroid ℝ id, s.1.centroid ℝ id} : Finset E3).centroid ℝ id,
        ({i.1.2.1.centroid ℝ id, f.1.centroid ℝ id} : Finset E3).centroid ℝ id} := by
  have hsub {a b : Finset E3} (ha : a ∈ K.faces) (hb : b ∈ K.faces)
      (hab : Section34Incident a b) : a ⊆ b := by
    intro v hv
    have hvK := K.down_closed ha (Finset.singleton_subset_iff.mpr hv)
      (Finset.singleton_nonempty _)
    exact mem_of_mem_convexHull_of_singleton_mem K hvK hb (hab hv)
  let t := i.1.1
  let e := i.1.2
  let S := restrict M (convexHull ℝ (t.1 : Set E3))
  let _ : Finite S.faces := (restrict_faces_finite M _).to_subtype
  have htM := hKM t.2.1
  have hSM : S.faces ⊆ M.faces := restrict_faces_subset _ _
  have htS : t.1 ∈ S.faces := ⟨htM, subset_rfl⟩
  have hes' : e.1 ⊆ s.1 := hsub e.2.1 s.2.1 hes
  have hef' : e.1 ⊆ f.1 := hsub e.2.1 f.2.1 hef
  have hst' : s.1 ⊆ t.1 := hsub s.2.1 t.2.1 hst
  have hft' : f.1 ⊆ t.1 := hsub f.2.1 t.2.1 hft
  have heS : e.1 ∈ S.faces := (mem_restrict_convexHull_faces_iff M htM).mpr
    ⟨K.nonempty_of_mem_faces e.2.1, hes'.trans hst'⟩
  have hsS : s.1 ∈ S.faces := (mem_restrict_convexHull_faces_iff M htM).mpr
    ⟨K.nonempty_of_mem_faces s.2.1, hst'⟩
  have hfS : f.1 ∈ S.faces := (mem_restrict_convexHull_faces_iff M htM).mpr
    ⟨K.nonempty_of_mem_faces f.2.1, hft'⟩
  have hmax : ∀ r ∈ S.faces, r ⊆ t.1 :=
    fun r hr => ((mem_restrict_convexHull_faces_iff M htM).mp hr).2
  have hSball : IsPLBall 3 S.space := by
    rw [show S.space = convexHull ℝ (t.1 : Set E3) from restrict_convexHull_space htM]
    exact isPLBall_convexHull_of_affineIndependent t.1 (M.indep htM) t.2.2
  let G := @upperLink E3 _ _ (Classical.decEq E3) (dualCell S e.1 heS)
    {e.1.centroid ℝ id}
  let _ : Finite (dualCell S e.1 heS).faces := (dualCell_faces_finite S heS).to_subtype
  let _ : Finite G.faces :=
    (@upperLink_faces_finite E3 _ _ (Classical.decEq E3) _ _ _).to_subtype
  let R := (derivedNeighborhoodCell S t.1).space ∪
    ⋃ r ∈ t.1.powersetCard 3, (derivedNeighborhoodCell S r).space
  have hRS : R ⊆ S.space := union_subset (derivedNeighborhoodCell_space_subset S t.1)
    (iUnion₂_subset fun r _ => derivedNeighborhoodCell_space_subset S r)
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
  obtain ⟨B, -, hB, hball⟩ := exists_subcomplex_compactDualEdgeArc M K hKM i
  have hG : IsPLBall 1 G.space := (hB.trans htrace) ▸ hball
  obtain ⟨q, hq⟩ := hG
  have hlocal := isPLCellOn_id_of_isPLBall hq
  rw [hq.image_stdSimplexBoundary_eq_boundaryComplex G rfl] at hlocal
  have hglobal := isPLCellOn_compactDualEdgeArc M K hKM i
  rw [htrace] at hglobal
  rw [hglobal.boundary_eq hlocal]
  have hb := boundaryComplex_tetra_edge_trace_eq_pair S hSball.isCombinatorialManifoldWithBoundary
    heS hsS hfS htS e.2.2.1 s.2.2 f.2.2 t.2.2 hes' hef' hst' hft'
    (fun h => hsf (Subtype.ext h)) hmax
  have htransport := congrArg (fun d : DecidableEq E3 =>
    letI : DecidableEq E3 := d
    (@boundaryComplex E3 _ _ d 1 G).space =
      ({({e.1.centroid ℝ id, s.1.centroid ℝ id} : Finset E3).centroid ℝ id,
        ({e.1.centroid ℝ id, f.1.centroid ℝ id} : Finset E3).centroid ℝ id} : Set E3))
    (Subsingleton.elim (Classical.decEq E3) (inferInstance : DecidableEq E3))
  exact htransport.mp hb

end DifferentialGeometry.Topology.PiecewiseLinear

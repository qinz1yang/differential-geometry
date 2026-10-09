/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualTriangleBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTriangleEndpoints

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
theorem compactDualCutBoundary_faceArc_eq_pair
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (a : Section34CompactArcIndex K K)
    {w z : E3} (hws : w ∈ a.1.1.1) (hzs : z ∈ a.1.1.1)
    (hvw : a.1.2.1.centroid ℝ id ≠ w) (hvz : a.1.2.1.centroid ℝ id ≠ z)
    (hwz : w ≠ z) :
    compactDualCutBoundary M K hKM (.faceArc a) =
      {({({a.1.2.1.centroid ℝ id, w} : Finset E3).centroid ℝ id,
          a.1.1.1.centroid ℝ id} : Finset E3).centroid ℝ id,
        ({({a.1.2.1.centroid ℝ id, z} : Finset E3).centroid ℝ id,
          a.1.1.1.centroid ℝ id} : Finset E3).centroid ℝ id} := by
  let s := a.1.1
  let v := a.1.2.1.centroid ℝ id
  let S := restrict M (convexHull ℝ (s.1 : Set E3))
  let H := restrict (restrict K (section34CompactGraphSkeleton K)) S.space
  let _ : Finite S.faces := (restrict_faces_finite M _).to_subtype
  have hsS : s.1 ∈ S.faces := ⟨hKM s.2.1, subset_rfl⟩
  have hmax : ∀ r ∈ S.faces, r ⊆ s.1 :=
    fun r hr => ((mem_restrict_convexHull_faces_iff M (hKM s.2.1)).mp hr).2
  have hH : ∀ r, r ∈ H.faces ↔ r ∈ S.faces ∧ r ≠ s.1 :=
    mem_compactTriangleGraph_faces_iff M K hKM s
  have hvK : {v} ∈ K.faces := by
    rw [show ({v} : Finset E3) = a.1.2.1 from
      singleton_centroid_eq_compactVertexIndex a.1.2]
    exact a.1.2.2.1
  have hvConv : v ∈ convexHull ℝ (s.1 : Set E3) := a.2 (by
    rw [← singleton_centroid_eq_compactVertexIndex a.1.2]
    exact Finset.mem_singleton_self _)
  have hvS : {v} ∈ S.faces := ⟨hKM hvK, by
    simpa only [Finset.coe_singleton, convexHull_singleton, singleton_subset_iff] using hvConv⟩
  have hvs : v ∈ s.1 := hmax {v} hvS (Finset.mem_singleton_self _)
  let G := @upperLink E3 _ _ (Classical.decEq E3) (dualCell S {v} hvS)
    {s.1.centroid ℝ id}
  let _ : Finite (dualCell S {v} hvS).faces := (dualCell_faces_finite S hvS).to_subtype
  let _ : Finite G.faces :=
    (@upperLink_faces_finite E3 _ _ (Classical.decEq E3) _ _ _).to_subtype
  have htrace : compactDualCutCell M K hKM (.faceArc a) = G.space :=
    (compactDualFaceArc_eq_localTrace M K hKM a).trans
      (graphDualCell_inter_derivedNeighborhoodCell_eq_upperLink S H hvS hsS hH)
  have hball : IsPLBall 1 G.space := by
    rw [← graphDualCell_inter_derivedNeighborhoodCell_eq_upperLink S H hvS hsS hH]
    exact isPLBall_graphDualCell_inter_triangleCell S H hsS hvs s.2.2 hmax hH
  obtain ⟨q, hq⟩ := hball
  have hlocal := isPLCellOn_id_of_isPLBall hq
  rw [hq.image_stdSimplexBoundary_eq_boundaryComplex G rfl] at hlocal
  have hglobal := isPLCellOn_compactDualFaceArc M K hKM a
  rw [htrace] at hglobal
  rw [hglobal.boundary_eq hlocal]
  have hb := boundaryComplex_triangle_vertex_trace_eq_pair S H hsS s.2.2 hmax hH hvS
    hvs hws hzs hvw hvz hwz
  have htransport := congrArg (fun d : DecidableEq E3 =>
    letI : DecidableEq E3 := d
    (@boundaryComplex E3 _ _ d 1 G).space =
      ({({({v, w} : Finset E3).centroid ℝ id, s.1.centroid ℝ id} : Finset E3).centroid ℝ id,
        ({({v, z} : Finset E3).centroid ℝ id, s.1.centroid ℝ id} : Finset E3).centroid ℝ id} :
        Set E3)) (Subsingleton.elim (Classical.decEq E3) (inferInstance : DecidableEq E3))
  exact htransport.mp hb

end DifferentialGeometry.Topology.PiecewiseLinear

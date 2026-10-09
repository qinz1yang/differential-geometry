/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FaceInterior
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactResidualRecognition

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem restrict_subcomplex_space (R A : Geometry.SimplicialComplex ℝ E3)
    (hAR : A.faces ⊆ R.faces) : (restrict R A.space).space = A.space := by
  rw [restrict_space_eq_inter_of_faces_subset R R A subset_rfl hAR]
  exact inter_eq_right.mpr (space_mono_of_faces_subset hAR)

private theorem restrict_inter_space_of_restrict_space
    {R : Geometry.SimplicialComplex ℝ E3} {P Q : Set E3}
    (hP : (restrict R P).space = P) (hQ : (restrict R Q).space = Q) :
    (restrict R (P ∩ Q)).space = P ∩ Q := by
  have h := restrict_space_eq_inter_of_faces_subset R (restrict R P) (restrict R Q)
    (restrict_faces_subset R P) (restrict_faces_subset R Q)
  simpa only [hQ, restrict_restrict, hP] using h

private theorem restrict_iUnion_space_of_restrict_space
    {R : Geometry.SimplicialComplex ℝ E3} {I : Type*} {P : I → Set E3}
    (hP : ∀ i, (restrict R (P i)).space = P i) :
    (restrict R (⋃ i, P i)).space = ⋃ i, P i := by
  refine Subset.antisymm (restrict_space_subset R _) (iUnion_subset fun i => ?_)
  exact (hP i).symm.subset.trans (restrict_space_mono (subset_iUnion P i))

private theorem restrict_closure_sdiff_of_restrict_spaces
    {R : Geometry.SimplicialComplex ℝ E3} [Finite R.faces] {P Q : Set E3}
    (hP : (restrict R P).space = P) (hQ : (restrict R Q).space = Q) :
    (restrict R (closure (P \ Q))).space = closure (P \ Q) := by
  let A := restrict R P
  let B := restrict R Q
  let G := subcomplexGeneratedBy A B.facesᶜ
  let _ : Finite A.faces := (restrict_faces_finite R P).to_subtype
  have hAR : A.faces ⊆ R.faces := restrict_faces_subset R P
  have hBR : B.faces ⊆ R.faces := restrict_faces_subset R Q
  have hGR : G.faces ⊆ R.faces :=
    (subcomplexGeneratedBy_faces_subset A B.facesᶜ).trans hAR
  have hG : closure (P \ Q) = G.space := by
    rw [← hP, ← hQ]
    exact closure_space_sdiff_space_eq_subcomplexGeneratedBy R A B hAR hBR
  rw [hG]
  exact restrict_subcomplex_space R G hGR

private theorem restrict_frontier_of_restrict_space
    {R : Geometry.SimplicialComplex ℝ E3} [Finite R.faces] {P : Set E3}
    (hP : (restrict R P).space = P) :
    (restrict R (frontier P)).space = frontier P := by
  let _ : Finite (restrict R P).faces := (restrict_faces_finite R P).to_subtype
  simpa only [hP] using restrict_space_frontier_of_faces_subset R (restrict R P)
    (restrict_faces_subset R P)

theorem restrict_compactDualCutCell_space
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (l : Section34CompactLabelOf K K) :
    (restrict (secondDerived M) (compactDualCutCell M K hKM l)).space =
      compactDualCutCell M K hKM l := by
  classical
  have hR : @secondDerived E3 _ _ (Classical.decEq E3) M = secondDerived M :=
    congrArg (fun d : DecidableEq E3 => @secondDerived E3 _ _ d M)
      (Subsingleton.elim _ _)
  have hV (w : Section34CompactVertexIndex K K) :
      (restrict (secondDerived M) (compactDualVertexBall M K w)).space =
        compactDualVertexBall M K w :=
    restrict_subcomplex_space (secondDerived M) _
      (hR ▸ (graphDualCell_faces_subset M _ _).trans
        (@derivedNeighborhood_faces_subset E3 _ _ (Classical.decEq E3) M _))
  have hE (e : Section34CompactEdgeIndex K K) :
      (restrict (secondDerived M) (compactDualSplitDisk M K hKM e)).space =
        compactDualSplitDisk M K hKM e :=
    restrict_subcomplex_space (secondDerived M) _
      (hR ▸ splittingDisk_faces_subset M (hKM e.2.1))
  have hKspace : (restrict (secondDerived M) K.space).space = K.space := by
    rw [← (secondDerived_isSubdivision K).space_eq]
    exact restrict_subcomplex_space (secondDerived M) (secondDerived K)
      (secondDerived_faces_subset hKM)
  cases l with
  | vertexBall w => exact hV w
  | splitDisk e => exact hE e
  | tetraBall t => exact restrict_compactDualResidualCell_space M K hKM t.2.1
  | faceDisk s => exact restrict_compactDualResidualCell_space M K hKM s.2.1
  | patch x =>
    exact restrict_inter_space_of_restrict_space
      (restrict_compactDualResidualCell_space M K hKM x.1.1.2.1) (hV x.1.2)
  | faceArc a =>
    exact restrict_inter_space_of_restrict_space (hV a.1.2)
      (restrict_compactDualResidualCell_space M K hKM a.1.1.2.1)
  | edgeArc i =>
    exact restrict_inter_space_of_restrict_space
      (restrict_compactDualResidualCell_space M K hKM i.1.1.2.1) (hE i.1.2)
  | markedPoint p =>
    exact restrict_inter_space_of_restrict_space (hE p.1.2)
      (restrict_compactDualResidualCell_space M K hKM p.1.1.2.1)
  | outerFace o =>
    exact restrict_closure_sdiff_of_restrict_spaces
      (restrict_frontier_of_restrict_space (hV o.1))
      (restrict_union_space hKspace (restrict_iUnion_space_of_restrict_space hE))
  | outerArc q =>
    have hbd : (restrict (secondDerived M)
        (boundaryComplex 2 (splittingDisk M q.1.1 (hKM q.1.2.1))).space).space =
          (boundaryComplex 2 (splittingDisk M q.1.1 (hKM q.1.2.1))).space :=
      restrict_subcomplex_space (secondDerived M) _
        (hR ▸ (boundaryComplex_faces_subset 2 _).trans
          (splittingDisk_faces_subset M (hKM q.1.2.1)))
    exact restrict_closure_sdiff_of_restrict_spaces hbd hKspace

theorem isPLCellOn_compactDualCutCell_of_isPLBall
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (l : Section34CompactLabelOf K K)
    (hcell : IsPLBall (section34BoundedDim l) (compactDualCutCell M K hKM l)) :
    IsPLCellOn (section34BoundedDim l) (compactDualCutCell M K hKM l)
      (compactDualCutBoundary M K hKM l) :=
  isPLCellOn_of_isPLBall_restrict_space (secondDerived M) hcell
    (restrict_compactDualCutCell_space M K hKM l)

end DifferentialGeometry.Topology.PiecewiseLinear

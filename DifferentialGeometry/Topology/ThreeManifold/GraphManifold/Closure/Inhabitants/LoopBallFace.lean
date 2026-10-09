import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopRegionInteriors

/-!
The original loop ball has its genuine whole sphere face and its native ball vertex model.
The same handle meets balls only through actual boundary end disks, and the deep core is disjoint.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold DifferentialGeometry.Geometry.Boundary
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

private local instance ballFaceCharts : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

private local instance ballFaceSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

def loopBallModelVertex : Vertex (NoCuts.carrier standardThreeSphereLift.{0}) :=
  .zero (standardLoopBallHandleCycle.ball ⟨0, standardLoopBallHandleCycle.len_pos⟩)
    (.ball (standardLoopBallHandleCycle.ballModel ⟨0, standardLoopBallHandleCycle.len_pos⟩))

def loopBallWholeFace : Set SphereCarrier.{0} :=
  (standardLoopBallHandleCycle.ball ⟨0, standardLoopBallHandleCycle.len_pos⟩).map ''
    (𝓡∂ 3).boundary (standardLoopBallHandleCycle.ball
      ⟨0, standardLoopBallHandleCycle.len_pos⟩).Piece

theorem loopBallWholeFace_frontier : loopBallWholeFace = frontier
    (Set.range (standardLoopBallHandleCycle.ball
      ⟨0, standardLoopBallHandleCycle.len_pos⟩).map) := by
  let P := standardLoopBallHandleCycle.ball ⟨0, standardLoopBallHandleCycle.len_pos⟩
  exact image_boundary_eq_frontier_of_fullRank_closedEmbedding P.map P.smooth
    P.isClosedEmbedding_map (fun p => (P.mfderiv_bijective p).injective) (by simp)

private def ballBoundarySphere : ((𝓡∂ 3).boundary (ClosedCell 3))
    ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 where
  toFun q := ⟨q.val.val, by
    have hq : ‖q.val.val‖ = 1 := (Set.ext_iff.mp
      (DifferentialGeometry.Topology.Manifold.closedCell_boundary_eq_sphere 2) q.val).mp
        q.property
    exact mem_sphere_zero_iff_norm.mpr hq⟩
  invFun q := ⟨⟨q.val, by
    have hq := mem_sphere_zero_iff_norm.mp q.property
    exact hq.le⟩, by
    rw [DifferentialGeometry.Topology.Manifold.closedCell_boundary_eq_sphere 2]
    exact mem_sphere_zero_iff_norm.mp q.property⟩
  left_inv q := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv q := by apply Subtype.ext; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def ballBoundaryModel : ((𝓡∂ 3).boundary
    (standardLoopBallHandleCycle.ball ⟨0, standardLoopBallHandleCycle.len_pos⟩).Piece)
    ≃ₜ ((𝓡∂ 3).boundary (ClosedCell 3)) :=
  (standardLoopBallHandleCycle.ballModel
    ⟨0, standardLoopBallHandleCycle.len_pos⟩).toHomeomorph.sets
      ((standardLoopBallHandleCycle.ballModel
        ⟨0, standardLoopBallHandleCycle.len_pos⟩).preimage_boundary (by simp)).symm

def loopBallWholeFaceModel :
    loopBallWholeFace ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  let P := standardLoopBallHandleCycle.ball ⟨0, standardLoopBallHandleCycle.len_pos⟩
  let f : ((𝓡∂ 3).boundary P.Piece) → SphereCarrier.{0} := fun q => P.map q.val
  have hi : Topology.IsEmbedding f :=
    P.isClosedEmbedding_map.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have hr : range f = loopBallWholeFace := by
    ext p
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q.val, q.property, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩
  exact ((Homeomorph.setCongr hr.symm).trans hi.toHomeomorph.symm).trans
    (ballBoundaryModel.trans ballBoundarySphere)

theorem loopBall_handle_interiors_disjoint (k h : Fin standardLoopBallHandleCycle.len) :
    Disjoint (interior (Set.range (standardLoopBallHandleCycle.ball k).map))
      (interior (Set.range (standardLoopBallHandleCycle.handle h).map)) := by
  apply Set.disjoint_left.mpr
  intro p hb hh
  have hi : p ∈ range (standardLoopBallHandleCycle.handle h).map ∩
      range (standardLoopBallHandleCycle.ball k).map :=
    ⟨interior_subset hh, interior_subset hb⟩
  rw [standardLoopBallHandleCycle.handle_ball_inter] at hi
  have hf : p ∈ (standardLoopBallHandleCycle.ball k).map ''
      (𝓡∂ 3).boundary (standardLoopBallHandleCycle.ball k).Piece := by
    rcases hi with hs | he
    · split_ifs at hs with hk
      · subst k
        exact standardLoopBallHandleCycle.start_face h hs
      · exact False.elim hs
    · split_ifs at he with hk
      · subst k
        exact standardLoopBallHandleCycle.end_face h he
      · exact False.elim he
  let P := standardLoopBallHandleCycle.ball k
  have he := image_boundary_eq_frontier_of_fullRank_closedEmbedding P.map P.smooth
    P.isClosedEmbedding_map (fun q => (P.mfderiv_bijective q).injective) (by simp)
  rw [he] at hf
  exact hf.2 hb

theorem loopBall_core_disjoint (k : Fin standardLoopBallHandleCycle.len) :
    Disjoint (Set.range (standardLoopBallHandleCycle.ball k).map)
      (Set.range loopComplementVertex.map) := by
  apply loopComplementVertex_disjoint.symm.mono_left
  rw [← standardLoopBallHandleCycle_union]
  exact standardLoopBallHandleCycle.ball_subset_union k

theorem loopHandle_core_disjoint (k : Fin standardLoopBallHandleCycle.len) :
    Disjoint (Set.range (standardLoopBallHandleCycle.handle k).map)
      (Set.range loopComplementVertex.map) := by
  apply loopComplementVertex_disjoint.symm.mono_left
  rw [← standardLoopBallHandleCycle_union]
  exact standardLoopBallHandleCycle.handle_subset_union k

end GC.GraphManifold.Assembly

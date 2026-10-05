import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopDefiningFamily

/-!
The actual global defining functions are strictly positive inside the original ball and handle.
True native chart inverse images identify their whole closed pieces and ambient interiors.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

private theorem pieceInterior_ballSource (x : ClosedCell 3) :
    x.val ∈ loopActualBallChart.source := by
  rw [loopActualBallChart_source,Metric.mem_ball,dist_zero_right]
  linarith [x.property]

private theorem pieceInterior_handleSource (y : ClosedCell 2 × Set.Icc (0 : ℝ) 1) :
    (y.1.val,y.2.val) ∈ loopActualHandleChart.source := by
  rw [loopActualHandleChart_source]
  change ‖y.1.val‖ < 13/10 ∧ -1/4 < y.2.val ∧ y.2.val < 5/4
  constructor
  · linarith [y.1.property]
  · constructor <;> linarith [y.2.property.1,y.2.property.2]

private theorem pieceInterior_ballImage : loopActualBallChart.toOpenPartialHomeomorph.IsImage
    (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (Set.range (standardLoopBallHandleCycle.ball
      ⟨0, standardLoopBallHandleCycle.len_pos⟩).map) := by
  intro u hu
  apply Iff.symm
  change u ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 ↔
    loopActualBallChart u ∈ Set.range
      (standardLoopBallHandleCycle.ball ⟨0, standardLoopBallHandleCycle.len_pos⟩).map
  constructor
  · intro hn
    have hx : ‖u‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hn
    exact ⟨⟨u,hx⟩,(loopActualBallChart_ball ⟨u,hx⟩).symm⟩
  · rintro ⟨x,hx⟩
    have he := loopActualBallChart.injOn hu (pieceInterior_ballSource x)
      (hx.symm.trans (loopActualBallChart_ball x).symm)
    rw [he,Metric.mem_closedBall,dist_zero_right]
    exact x.property

private theorem pieceInterior_handleImage : loopActualHandleChart.toOpenPartialHomeomorph.IsImage
    (Metric.closedBall (0 : ModelPlane) 1 ×ˢ Set.Icc (0 : ℝ) 1)
    (Set.range (standardLoopBallHandleCycle.handle
      ⟨0, standardLoopBallHandleCycle.len_pos⟩).map) := by
  intro u hu
  apply Iff.symm
  change u ∈ (Metric.closedBall (0 : ModelPlane) 1 ×ˢ Set.Icc (0 : ℝ) 1) ↔
    loopActualHandleChart u ∈ Set.range
      (standardLoopBallHandleCycle.handle ⟨0, standardLoopBallHandleCycle.len_pos⟩).map
  constructor
  · rintro ⟨hn,ht⟩
    have hw : ‖u.1‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hn
    let y : ClosedCell 2 × Set.Icc (0 : ℝ) 1 := (⟨u.1,hw⟩,⟨u.2,ht⟩)
    exact ⟨y,(loopActualHandleChart_handle y).symm⟩
  · rintro ⟨y,hy⟩
    have he := loopActualHandleChart.injOn hu (pieceInterior_handleSource y)
      (hy.symm.trans (loopActualHandleChart_handle y).symm)
    rw [he]
    exact ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using y.1.property,y.2.property⟩

theorem loopBallDefining_ballInterior {z : loopCircleBase}
    (hp : loopCircleSection z ∈ interior (Set.range
      (standardLoopBallHandleCycle.ball ⟨0, standardLoopBallHandleCycle.len_pos⟩).map)) :
    0 < loopBallDefining z := by
  obtain ⟨x,hx⟩ := interior_subset hp
  have hs := pieceInterior_ballSource x
  have he : loopActualBallChart x.val = loopCircleSection z :=
    (loopActualBallChart_ball x).trans hx
  have ht : loopCircleSection z ∈ loopActualBallChart.target :=
    he ▸ loopActualBallChart.map_source hs
  have hn := (pieceInterior_ballImage.interior hs).mp (by
    change loopActualBallChart x.val ∈ _
    rw [he]
    exact hp)
  rw [interior_closedBall _ (by norm_num)] at hn
  have hnorm : ‖x.val‖ < 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hn
  rw [loopBallDefining_target ht,← he]
  have hi := loopActualBallChart.left_inv hs
  change loopActualBallChart.symm (loopActualBallChart x.val) = x.val at hi
  rw [hi,loopBallProfile_pos]
  exact hnorm

theorem loopHandleDefining_handleInterior {z : loopCircleBase}
    (hp : loopCircleSection z ∈ interior (Set.range
      (standardLoopBallHandleCycle.handle ⟨0, standardLoopBallHandleCycle.len_pos⟩).map)) :
    0 < loopHandleDefining z := by
  obtain ⟨y,hy⟩ := interior_subset hp
  have hs := pieceInterior_handleSource y
  have he : loopActualHandleChart (y.1.val,y.2.val) = loopCircleSection z :=
    (loopActualHandleChart_handle y).trans hy
  have ht : loopCircleSection z ∈ loopActualHandleChart.target :=
    he ▸ loopActualHandleChart.map_source hs
  have hn := (pieceInterior_handleImage.interior hs).mp (by
    change loopActualHandleChart (y.1.val,y.2.val) ∈ _
    rw [he]
    exact hp)
  rw [interior_prod_eq,interior_closedBall _ (by norm_num),interior_Icc] at hn
  have hnorm : ‖y.1.val‖ < 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hn.1
  rw [loopHandleDefining_target ht,← he]
  have hi := loopActualHandleChart.left_inv hs
  change loopActualHandleChart.symm (loopActualHandleChart (y.1.val,y.2.val)) = _ at hi
  rw [hi]
  rw [loopHandleProfile_middle (by linarith [y.1.property])
    ⟨by linarith [y.2.property.1],by linarith [y.2.property.2]⟩]
  linarith

end GC.GraphManifold.Assembly

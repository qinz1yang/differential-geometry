import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopDefiningFamily

/-!
The genuine global ball and handle defining functions are nonnegative on their original pieces.
The native chart inverses retain the original closed radial and time bounds.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

theorem loopBallDefining_raw {z : loopCircleBase}
    (hp : loopCircleSection z ∈ Set.range
      (standardLoopBallHandleCycle.ball ⟨0, standardLoopBallHandleCycle.len_pos⟩).map) :
    0 ≤ loopBallDefining z := by
  obtain ⟨x,hx⟩ := hp
  have hs : x.val ∈ loopActualBallChart.source := by
    rw [loopActualBallChart_source, Metric.mem_ball, dist_zero_right]
    linarith [x.property]
  have he : loopActualBallChart x.val = loopCircleSection z :=
    (loopActualBallChart_ball x).trans hx
  have ht : loopCircleSection z ∈ loopActualBallChart.target :=
    he ▸ loopActualBallChart.map_source hs
  rw [loopBallDefining_target ht]
  have hi := loopActualBallChart.left_inv hs
  change loopActualBallChart.symm (loopActualBallChart x.val) = x.val at hi
  rw [← he,hi,loopBallProfile_small (by linarith [x.property])]
  linarith [x.property]

theorem loopHandleDefining_raw {z : loopCircleBase}
    (hp : loopCircleSection z ∈ Set.range
      (standardLoopBallHandleCycle.handle ⟨0, standardLoopBallHandleCycle.len_pos⟩).map) :
    0 ≤ loopHandleDefining z := by
  obtain ⟨y,hy⟩ := hp
  let q : ModelSpace := (y.1.val,y.2.val)
  have hs : q ∈ loopActualHandleChart.source := by
    rw [loopActualHandleChart_source]
    change ‖y.1.val‖ < 13/10 ∧ -1/4 < y.2.val ∧ y.2.val < 5/4
    constructor
    · linarith [y.1.property]
    · constructor <;> linarith [y.2.property.1,y.2.property.2]
  have he : loopActualHandleChart q = loopCircleSection z :=
    (loopActualHandleChart_handle y).trans hy
  have ht : loopCircleSection z ∈ loopActualHandleChart.target :=
    he ▸ loopActualHandleChart.map_source hs
  rw [loopHandleDefining_target ht]
  have hi := loopActualHandleChart.left_inv hs
  change loopActualHandleChart.symm (loopActualHandleChart q) = q at hi
  rw [← he,hi]
  change 0 ≤ loopHandleProfile ‖y.1.val‖ y.2.val
  rw [loopHandleProfile_middle (by linarith [y.1.property])
    ⟨by linarith [y.2.property.1],by linarith [y.2.property.2]⟩]
  linarith [y.1.property]

end GC.GraphManifold.Assembly

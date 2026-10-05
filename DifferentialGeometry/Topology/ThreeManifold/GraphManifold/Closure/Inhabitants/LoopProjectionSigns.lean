import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopPositiveGeometry
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopHandleOrbit

/-!
The original closed handle retains its genuine radial defining profile under the first circle.
Positive original ball values lie in its true interior. Original handle-ball overlaps are faces.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

private theorem projectionSigns_single (k : Fin standardLoopBallHandleCycle.len) :
    k = ⟨0, standardLoopBallHandleCycle.len_pos⟩ := by
  apply Fin.ext
  have hbound : standardLoopBallHandleCycle.len ≤ 1 := by
    rw [standardLoopBallHandleCycle_len]
  have hlt := lt_of_lt_of_le k.isLt hbound
  change k.val = 0
  omega

private theorem projectionSigns_handleSource (y : ClosedCell 2 × Set.Icc (0 : ℝ) 1) :
    (y.1.val,y.2.val) ∈ loopActualHandleChart.source := by
  rw [loopActualHandleChart_source]
  change ‖y.1.val‖ < 13/10 ∧ -1/4 < y.2.val ∧ y.2.val < 5/4
  constructor
  · linarith [y.1.property]
  · constructor <;> linarith [y.2.property.1,y.2.property.2]

theorem loopHandleProjection_middle (y : ClosedCell 2 × Set.Icc (0 : ℝ) 1)
    (hd : (standardLoopBallHandleCycle.handle ⟨0, standardLoopBallHandleCycle.len_pos⟩).map y
      ∈ loopCircleDomain) :
    loopHandleDefining (loopCircleProjection
      ⟨(standardLoopBallHandleCycle.handle ⟨0, standardLoopBallHandleCycle.len_pos⟩).map y, hd⟩) =
    16*(1-‖y.1.val‖) := by
  let q : ModelSpace := (y.1.val,y.2.val)
  have hq := projectionSigns_handleSource y
  have he : loopActualHandleChart q =
      (standardLoopBallHandleCycle.handle ⟨0, standardLoopBallHandleCycle.len_pos⟩).map y :=
    loopActualHandleChart_handle y
  have hdc : loopActualHandleChart q ∈ loopCircleDomain := he.symm ▸ hd
  have ht : loopCircleSection (loopCircleProjection ⟨loopActualHandleChart q, hdc⟩)
      ∈ loopActualHandleChart.target := by
    rw [loopHandleRotation_section hq hdc]
    exact loopActualHandleChart.map_source (loopHandleRotation_source hq 1)
  have hp : loopHandleDefining (loopCircleProjection ⟨loopActualHandleChart q, hdc⟩) =
      16*(1-‖y.1.val‖) := by
    rw [loopHandleDefining_target ht,loopHandleRotation_inverse_norm hq hdc,
      loopHandleRotation_inverse_time hq hdc]
    change loopHandleProfile ‖y.1.val‖ y.2.val = _
    rw [loopHandleProfile_middle (by linarith [y.1.property])
      ⟨by linarith [y.2.property.1],by linarith [y.2.property.2]⟩]
  have hdom : (⟨loopActualHandleChart q, hdc⟩ : loopCircleDomain) =
      ⟨(standardLoopBallHandleCycle.handle ⟨0, standardLoopBallHandleCycle.len_pos⟩).map y, hd⟩ :=
    Subtype.ext he
  rwa [hdom] at hp

theorem loopBallDefining_positive_interior {z : loopCircleBase} (hp : 0 < loopBallDefining z) :
    loopCircleSection z ∈ interior (Set.range
      (standardLoopBallHandleCycle.ball ⟨0, standardLoopBallHandleCycle.len_pos⟩).map) := by
  have hh := loopBallDefining_positive hp
  have hm : loopCircleSection z ∈ loopBallPositive :=
    ⟨loopActualBallChart.symm (loopCircleSection z),hh.2,loopActualBallChart.right_inv hh.1⟩
  have hs : loopBallPositive ⊆ Set.range (standardLoopBallHandleCycle.ball
      ⟨0, standardLoopBallHandleCycle.len_pos⟩).map := by
    rintro p ⟨x,hx,he⟩
    exact ⟨⟨x,hx.le⟩,(loopActualBallChart_ball ⟨x,hx.le⟩).symm.trans he⟩
  apply interior_mono hs
  rwa [loopBallPositive_open.interior_eq]

theorem loopHandleBall_intersection_face {p : SphereCarrier.{0}}
    (hh : p ∈ Set.range (standardLoopBallHandleCycle.handle
      ⟨0, standardLoopBallHandleCycle.len_pos⟩).map)
    (hb : p ∈ Set.range (standardLoopBallHandleCycle.ball
      ⟨0, standardLoopBallHandleCycle.len_pos⟩).map) : p ∈ loopBallWholeFace := by
  let k : Fin standardLoopBallHandleCycle.len := ⟨0, standardLoopBallHandleCycle.len_pos⟩
  have hi : p ∈ Set.range (standardLoopBallHandleCycle.handle k).map ∩
      Set.range (standardLoopBallHandleCycle.ball k).map := ⟨hh,hb⟩
  rw [standardLoopBallHandleCycle.handle_ball_inter k k] at hi
  have hrot : finRotate standardLoopBallHandleCycle.len k = k := projectionSigns_single _
  rw [hrot] at hi
  change p ∈ (standardLoopBallHandleCycle.ball k).map ''
    (𝓡∂ 3).boundary (standardLoopBallHandleCycle.ball k).Piece
  rcases hi with hstart | hend
  · exact standardLoopBallHandleCycle.start_face k hstart
  · have hf := standardLoopBallHandleCycle.end_face k hend
    rwa [hrot] at hf

end GC.GraphManifold.Assembly

import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopArcOrbit
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopBallOrbit

/-!
The entire actual ball annulus retains its original latitude inverse in the genuine ball chart.
The actual first-circle section puts its base arc on the true global ball defining zero set.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

theorem loopBallAnnulus_ballInverse (θ : Circle) (t : Set.Icc (0 : ℝ) 1) :
    loopActualBallChart.symm (loopBallAnnulus (θ,t)) = (loopBallLatitudePoint θ t).val := by
  have hs : (loopBallLatitudePoint θ t).val ∈ loopActualBallChart.source := by
    rw [loopActualBallChart_source,Metric.mem_ball,dist_zero_right]
    rw [loopBallLatitudePoint_norm]
    norm_num
  change loopActualBallChart.symm ((standardLoopBallHandleCycle.ball
    ⟨0, standardLoopBallHandleCycle.len_pos⟩).map (loopBallLatitudePoint θ t)) = _
  rw [← loopActualBallChart_ball]
  exact loopActualBallChart.left_inv hs

theorem loopBallProjection_zero {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ loopActualBallChart.source) (hn : ‖x‖ = 1)
    (hd : loopActualBallChart x ∈ loopCircleDomain) :
    loopBallDefining (loopCircleProjection ⟨loopActualBallChart x, hd⟩) = 0 := by
  apply loopBallDefining_zero.mpr
  constructor
  · rw [loopBallRotation_section hx hd]
    exact loopActualBallChart.map_source (loopBallRotation_source hx 1)
  · rw [loopBallRotation_inverse_norm hx hd,hn]

theorem loopBallArcBase_ballZero (t : Set.Icc (0 : ℝ) 1) :
    loopBallDefining (loopBallArcBase t) = 0 := by
  let x := (loopBallLatitudePoint 1 t).val
  have hn : ‖x‖ = 1 := loopBallLatitudePoint_norm 1 t
  have hs : x ∈ loopActualBallChart.source := by
    rw [loopActualBallChart_source,Metric.mem_ball,dist_zero_right,hn]
    norm_num
  have hp : loopActualBallChart x = loopBallAnnulus (1,t) :=
    loopActualBallChart_ball (loopBallLatitudePoint 1 t)
  have hd : loopActualBallChart x ∈ loopCircleDomain := hp.symm ▸ loopBallAnnulus_domain 1 t
  have he : (⟨loopActualBallChart x, hd⟩ : loopCircleDomain) =
      ⟨loopBallAnnulus (1,t), loopBallAnnulus_domain 1 t⟩ := Subtype.ext hp
  have hz := loopBallProjection_zero hs hn hd
  rw [he,loopBallAnnulus_projection] at hz
  exact hz

end GC.GraphManifold.Assembly

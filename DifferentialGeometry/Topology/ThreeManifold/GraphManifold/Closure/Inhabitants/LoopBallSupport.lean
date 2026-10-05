import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopCircleSection
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopBallRimInverse

/-!
The original ball radial cutoff has genuine compact support strictly inside its actual chart.
Its closed pullback to the entire true circle base permits a smooth constant outer extension.
-/

set_option autoImplicit false
noncomputable section
open Set Metric Manifold DifferentialGeometry DifferentialGeometry.Topology GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

private theorem ballSupport_source :
    closedBall (0 : EuclideanSpace ℝ (Fin 3)) (19 / 16) ⊆ loopActualBallChart.source := by
  rw [loopActualBallChart_source]
  intro x hx
  rw [mem_closedBall_zero_iff] at hx
  rw [mem_ball_zero_iff]
  linarith

def loopBallSupport : Set SphereCarrier.{0} :=
  loopActualBallChart '' closedBall (0 : EuclideanSpace ℝ (Fin 3)) (19 / 16)

theorem loopBallSupport_compact : IsCompact loopBallSupport :=
  (isCompact_closedBall _ _).image_of_continuousOn
    (loopActualBallChart.contMDiffOn_toFun.continuousOn.mono ballSupport_source)

theorem loopBallSupport_closed : IsClosed loopBallSupport := loopBallSupport_compact.isClosed

theorem loopBallSupport_target : loopBallSupport ⊆ loopActualBallChart.target := by
  rintro p ⟨x,hx,rfl⟩
  exact loopActualBallChart.map_source (ballSupport_source hx)

def loopBallBaseSupport : Set loopCircleBase := loopCircleSection ⁻¹' loopBallSupport

theorem loopBallBaseSupport_closed : IsClosed loopBallBaseSupport :=
  loopBallSupport_closed.preimage loopCircleSection_smooth.continuous

theorem loopBallBaseSupport_target {z : loopCircleBase} (hz : z ∈ loopBallBaseSupport) :
    loopCircleSection z ∈ loopActualBallChart.target := loopBallSupport_target hz

theorem loopBallInverse_outside {z : loopCircleBase}
    (hz : z ∉ loopBallBaseSupport) (ht : loopCircleSection z ∈ loopActualBallChart.target) :
    19 / 16 < ‖loopActualBallChart.symm (loopCircleSection z)‖ := by
  by_contra hn
  apply hz
  refine ⟨loopActualBallChart.symm (loopCircleSection z), ?_, ?_⟩
  · rw [mem_closedBall_zero_iff]
    exact le_of_not_gt hn
  · exact loopActualBallChart.right_inv ht

end GC.GraphManifold.Assembly

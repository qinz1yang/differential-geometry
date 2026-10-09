import DifferentialGeometry.Topology.Manifold.BallChartRestriction
import DifferentialGeometry.Topology.ThreeManifold.CapBallChart
import DifferentialGeometry.Topology.ThreeManifold.CutCapMarkedGraphBridge

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SphericalCutCapTransition

universe u
local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

private theorem capBallChart_target_subset_componentSet (b : E.tubes.Boundary) :
    (E.capping.capBallChart b).chart.target ⊆ E.capped.componentSet (E.cutCapVertex b.1 b.2) := by
  rw [E.capping.capBallChart_target]
  rintro y ⟨x, _, rfl⟩
  exact E.capRange_subset_componentSet b.1 b.2 ⟨x, rfl⟩

def capComponentBallChart (b : E.tubes.Boundary) :
    OrientedBallChart (E.capped.component (E.cutCapVertex b.1 b.2)).toClosedOrientedManifold :=
  (E.capping.capBallChart b).component (E.cutCapVertex b.1 b.2)
    (E.capBallChart_target_subset_componentSet b)

@[simp] theorem capComponentBallChart_source (b : E.tubes.Boundary) :
    (E.capComponentBallChart b).chart.source = Metric.ball (0 : E3) 4 := by
  rw [capComponentBallChart, OrientedBallChart.component_source, E.capping.capBallChart_source]

@[simp] theorem capComponentBallChart_target (b : E.tubes.Boundary) :
    (E.capComponentBallChart b).chart.target =
      (Subtype.val : (E.capped.component (E.cutCapVertex b.1 b.2)).Carrier → E.capped.Carrier) ⁻¹'
        (E.capping.cap b '' {x : ClosedCell 3 | ‖x.val‖ < 1}) := by
  rw [capComponentBallChart, OrientedBallChart.component_target, E.capping.capBallChart_target]

theorem capComponentBallChart_apply (b : E.tubes.Boundary) {x : E3}
    (hx : x ∈ Metric.ball (0 : E3) 4) :
    ((E.capComponentBallChart b).chart x).val = (E.capping.capBallChart b).chart x := by
  apply OrientedBallChart.component_apply
  rwa [E.capping.capBallChart_source]

theorem capComponentBallChart_apply_closedBall (b : E.tubes.Boundary) {x : E3}
    (hx : x ∈ Metric.closedBall (0 : E3) 2) :
    ((E.capComponentBallChart b).chart x).val = (E.capping.capBallChart b).chart x :=
  E.capComponentBallChart_apply b (Metric.closedBall_subset_ball (by norm_num) hx)

theorem capComponentBallChart_image_closedBall (b : E.tubes.Boundary) :
    (Subtype.val : (E.capped.component (E.cutCapVertex b.1 b.2)).Carrier → E.capped.Carrier) ''
        ((E.capComponentBallChart b).chart '' Metric.closedBall (0 : E3) 2) =
      (E.capping.capBallChart b).chart '' Metric.closedBall (0 : E3) 2 := by
  erw [Set.image_image]
  apply Set.image_congr
  intro x hx
  exact E.capComponentBallChart_apply_closedBall b hx

theorem capComponentBallChart_signed_apply (b : E.tubes.Boundary) (x : E3)
    (hx : ‖(if b.2 then (1 / 4 : ℝ) else -(1 / 4 : ℝ)) • x‖ < 1) :
    ((E.capComponentBallChart b).chart x).val =
      E.capping.cap b ⟨(if b.2 then (1 / 4 : ℝ) else -(1 / 4 : ℝ)) • x, hx.le⟩ := by
  have hx4 : x ∈ Metric.ball (0 : E3) 4 := by
    rw [mem_ball_zero_iff]
    rw [norm_smul, Real.norm_eq_abs] at hx
    have habs : |if b.2 then (1 / 4 : ℝ) else -(1 / 4 : ℝ)| = 1 / 4 := by
      cases b.2 <;> norm_num
    rw [habs] at hx
    linarith
  rw [E.capComponentBallChart_apply b hx4]
  exact E.capping.capBallChart_apply b x hx

end DifferentialGeometry.Topology.SphericalCutCapTransition

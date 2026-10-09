import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SphereCapFillingIsometry

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.OrientedBallChart

universe u v
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

variable {M : ClosedOrientedManifold.{u} 3} {N : ClosedOrientedManifold.{v} 3}

def map (c : OrientedBallChart M) (F : ClosedOrientedManifold.OrientedDiffeomorph M N) :
    OrientedBallChart N where
  chart := compPartialDiffeomorph c.chart F.val
  closedBall_subset_source := c.closedBall_subset_source
  preserves_orientation := preservesOrientation_compPartialDiffeomorph c.chart
    M.orientation N.orientation F.val F.property c.preserves_orientation

theorem map_apply (c : OrientedBallChart M) (F : ClosedOrientedManifold.OrientedDiffeomorph M N) (x : E3) :
    (c.map F).chart x = F.val (c.chart x) := rfl

theorem disjoint_map_closedBall (c d : OrientedBallChart M)
    (F : ClosedOrientedManifold.OrientedDiffeomorph M N)
    (h : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2)) :
    Disjoint ((c.map F).chart '' Metric.closedBall 0 2) ((d.map F).chart '' Metric.closedBall 0 2) := by
  apply Set.disjoint_left.mpr
  rintro y ⟨x, hx, rfl⟩ ⟨z, hz, hzx⟩
  exact Set.disjoint_left.mp h ⟨x, hx, rfl⟩ ⟨z, hz, F.val.injective hzx⟩

end DifferentialGeometry.Topology.OrientedBallChart

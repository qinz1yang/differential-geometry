import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusStageCloud
import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusPacketsExamples

/-!
# Consumer: the stage-0 cloud of the example torus packet is non-empty (S-FIXTURE-C1b, R1 start)

On the packet `torC1_packets_FXC1` of the example torus the origin node `π(0, 0, 0)` is a circle
centre with `η_j(j) = 0`, so the first stage core and the stage-0 cloud `gafCloud … 0` are non-empty
(the stage clauses of the chain, which quantify over this cloud, are not vacuous).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric GC.MetricGeometry
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] torMS_FXC1

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

/-- The origin node is a centre of the circle family of the packet (statement for the family). -/
theorem torC1_stage0_cloud_nonempty_FXC1
    (oM : ManifoldOrientation 𝓘(ℝ, E3) (Tor_FXC1 torPeriodsC1_FXC1) 3) :
    (gafCloud (torC1_packets_FXC1 oM).toLocalChartFamily (torC1_packets_FXC1 oM).zero 0).Nonempty :=
  (gafCloud_zero_nonempty_FXC1 (torC1_packets_FXC1 oM).toLocalChartFamily
    (torC1_packets_FXC1 oM).zero
    (j := torPi_FXC1 torPeriodsC1_FXC1 (torNode_FXC1 1 0 0))
    ⟨(0, 0), ⟨by simp, by simp⟩, rfl⟩
    (by
      change ‖torEta_FXC1 torPeriodsC1_FXC1 1 _ _‖ ≤ 7
      rw [torEta_center_FXC1, norm_zero]
      norm_num)).2

end DifferentialGeometry.Geometry.Collapse

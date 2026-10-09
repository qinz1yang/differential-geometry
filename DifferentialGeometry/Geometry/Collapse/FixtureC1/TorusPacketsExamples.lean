import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusPacketsC14Z
import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusCircleAdaptedExamples

/-!
# Explicit consumer of the packet family of the flat torus (S-FIXTURE-C1b, F1, G5 consumer)

On the torus `ℝ³ / (N ℤ ⊕ N ℤ ⊕ 10⁻⁷ ℤ)`, `N = 8·10⁷`, at `R = 1`, `β₂ = 10⁻⁷`, `β₃ = 3/20`,
`γ = 1/10`, `b = s = 1/1000` (all other parameters of the family are free; set to `0` here):
`torC1_packets_FXC1 oM : LocalChartPacketsC14Z …` with a NON-EMPTY circle centre set, empty slim,
edge and zero centre sets, and the circle adapted centre at the origin node.
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

/-- **The packet family of the example torus**, with `γ = 1/10`, `b = s = 1/1000` and every other
parameter of the family (free for this fixture) set to `0` (`Δ = 1`). -/
def torC1_packets_FXC1
    (oM : ManifoldOrientation 𝓘(ℝ, E3) (Tor_FXC1 torPeriodsC1_FXC1) 3) :
    LocalChartPacketsC14Z (Tor_FXC1 torPeriodsC1_FXC1) (torMetric_FXC1 torPeriodsC1_FXC1)
      (torMS_hmetric_FXC1 torPeriodsC1_FXC1) (fun _ => (1 : ℝ)) (fun _ => one_pos) 0
      torBetaC1_FXC1 1 0 0 0 0 (1 / 1000) (1 / 1000) 0 0 0 0 0 0 0 (1 / 10) 0 0 0 0 0 0 0 0 oM :=
  torPacketsC14Z_FXC1 torPeriodsC1_FXC1 (R := 1) (β := torBetaC1_FXC1) one_pos
    (by simp [torBetaC1_FXC1]) (by simp [torBetaC1_FXC1])
    (by rw [torC1_L2_FXC1]; simp [torBetaC1_FXC1])
    (by rw [torC1_planePeriod_FXC1]; simp [torBetaC1_FXC1]; norm_num)
    80000000 torC1_L0_FXC1 torC1_L1_FXC1 torC1_hβ3_FXC1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) oM

variable (oM : ManifoldOrientation 𝓘(ℝ, E3) (Tor_FXC1 torPeriodsC1_FXC1) 3)

/-- **The circle family of the packet is non-empty**: the origin node is a centre. -/
theorem torC1_packets_circle_nonempty_FXC1 : (torC1_packets_FXC1 oM).circle.centres.Nonempty :=
  ⟨torPi_FXC1 torPeriodsC1_FXC1 (torNode_FXC1 1 0 0), ⟨(0, 0), ⟨by simp, by simp⟩, rfl⟩⟩

/-- The slim, edge and zero centre sets of the packet are empty. -/
theorem torC1_packets_others_empty_FXC1 :
    (torC1_packets_FXC1 oM).slim.centres = ∅ ∧ (torC1_packets_FXC1 oM).edge.centres = ∅ ∧
      (torC1_packets_FXC1 oM).zero.centres = ∅ :=
  ⟨rfl, rfl, rfl⟩

end DifferentialGeometry.Geometry.Collapse

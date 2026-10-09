import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusCircleAdapted
import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusCircleFamilyExamples

/-!
# Explicit consumer of the circle adapted centre of the flat torus (S-FIXTURE-C1b, F1, G4 consumer)

On the torus `ℝ³ / (N ℤ ⊕ N ℤ ⊕ 10⁻⁷ ℤ)`, `N = 8·10⁷`, `R = 1`, `β₂ = 10⁻⁷`, `β₃ = 3/20`,
`γ = 1/10`: the circle adapted centre at the centre `π(0, 0, 0)` of the (non-empty) circle family,
its Kleiner-Lott map has plane component `η_j`, and LFR07's residual enclosure holds there.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric GC.MetricGeometry
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] torMS_FXC1

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The circle adapted centre of the example torus at the centre `π(0, 0, 0)`, error `γ = 1/10`. -/
def torC1_adapted_FXC1 :
    CircleAdaptedCentre (Tor_FXC1 torPeriodsC1_FXC1) (torMetric_FXC1 torPeriodsC1_FXC1)
      (torMS_hmetric_FXC1 torPeriodsC1_FXC1) (fun _ => (1 : ℝ)) (fun _ => one_pos)
      torBetaC1_FXC1 (1 / 10) torC1_circleFamily_FXC1
      (torPi_FXC1 torPeriodsC1_FXC1 (torNode_FXC1 1 0 0)) torC1_origin_centre_FXC1 :=
  torCircleAdapted_FXC1 torPeriodsC1_FXC1 (R := 1) (β := torBetaC1_FXC1) one_pos
    (by simp [torBetaC1_FXC1]) (by simp [torBetaC1_FXC1])
    (by rw [torC1_L2_FXC1]; simp [torBetaC1_FXC1])
    (by rw [torC1_planePeriod_FXC1]; simp [torBetaC1_FXC1]; norm_num)
    80000000 torC1_L0_FXC1 torC1_L1_FXC1 torC1_hβ3_FXC1 (by norm_num) _ torC1_origin_centre_FXC1

/-- The plane component of the Kleiner-Lott map of the adapted centre is the chart coordinate. -/
theorem torC1_adapted_split_FXC1 (x : Tor_FXC1 torPeriodsC1_FXC1) :
    (@KleinerLottApprox.toFun (Tor_FXC1 torPeriodsC1_FXC1) (WithLp 2 (ℝ² × PUnit.{1}))
      ((torMS_FXC1 torPeriodsC1_FXC1).rescale (1 : ℝ)⁻¹ (inv_pos.mpr one_pos)) _ _ _ _
      torC1_adapted_FXC1.split x).fst =
      torEta_FXC1 torPeriodsC1_FXC1 1 (torPi_FXC1 torPeriodsC1_FXC1 (torNode_FXC1 1 0 0)) x :=
  rfl

/-- LFR07's residual enclosure at the origin centre of the example torus. -/
theorem torC1_residual_FXC1 :
    letI := (torMS_FXC1 torPeriodsC1_FXC1).rescale (1 : ℝ)⁻¹ (inv_pos.mpr one_pos)
    ∀ x ∈ ball (torPi_FXC1 torPeriodsC1_FXC1 (torNode_FXC1 1 0 0)) 200,
      ‖torEta_FXC1 torPeriodsC1_FXC1 1 (torPi_FXC1 torPeriodsC1_FXC1 (torNode_FXC1 1 0 0)) x‖ ≤ 8 →
        x ∈ ball (torPi_FXC1 torPeriodsC1_FXC1 (torNode_FXC1 1 0 0)) 10 :=
  torCircle_residual_FXC1 torPeriodsC1_FXC1 (R := 1) (β := torBetaC1_FXC1) one_pos
    (by simp [torBetaC1_FXC1]) (by simp [torBetaC1_FXC1])
    (by rw [torC1_L2_FXC1]; simp [torBetaC1_FXC1])
    (by rw [torC1_planePeriod_FXC1]; simp [torBetaC1_FXC1]; norm_num) _

end DifferentialGeometry.Geometry.Collapse

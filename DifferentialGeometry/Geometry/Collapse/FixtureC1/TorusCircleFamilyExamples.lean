import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusCircleFamily
import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusCircleExamples

/-!
# Explicit consumer of the circle family of the flat torus (S-FIXTURE-C1b, F1, G3 consumer)

On the torus `ℝ³ / (N ℤ ⊕ N ℤ ⊕ 10⁻⁷ ℤ)`, `N = 8·10⁷`, at `R = 1`, `β₂ = 10⁻⁷`, `β₃ = 3/20`:
the circle family is non-empty (the node `π(0, 0, 0)` is a centre), its cutoff at that centre equals
one at the centre, and every point of the torus is a two-stratum point (every point has rank two).
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

theorem torC1_hβ3_FXC1 : torBetaC1_FXC1 3 ≤ 3 / 20 := by simp [torBetaC1_FXC1]

/-- The circle family of the example torus. -/
def torC1_circleFamily_FXC1 :
    CircleFamily 𝓘(ℝ, E3) (Tor_FXC1 torPeriodsC1_FXC1) (fun _ => (1 : ℝ)) (fun _ => one_pos)
      torBetaC1_FXC1 :=
  torCircleFamily_FXC1 torPeriodsC1_FXC1 (R := 1) (β := torBetaC1_FXC1) one_pos
    (by simp [torBetaC1_FXC1]) (by simp [torBetaC1_FXC1])
    (by rw [torC1_L2_FXC1]; simp [torBetaC1_FXC1])
    (by rw [torC1_planePeriod_FXC1]; simp [torBetaC1_FXC1]; norm_num)
    80000000 torC1_L0_FXC1 torC1_L1_FXC1 torC1_hβ3_FXC1

/-- The node `π(0, 0, 0)` is a circle centre: the family is non-empty. -/
theorem torC1_origin_centre_FXC1 :
    torPi_FXC1 torPeriodsC1_FXC1 (torNode_FXC1 1 0 0) ∈ torC1_circleFamily_FXC1.centres :=
  ⟨(0, 0), ⟨by simp, by simp⟩, rfl⟩

/-- The cutoff of the centre `π(0, 0, 0)` is one at the centre. -/
theorem torC1_origin_cutoff_FXC1 :
    torC1_circleFamily_FXC1.cutoff (torPi_FXC1 torPeriodsC1_FXC1 (torNode_FXC1 1 0 0))
      (torPi_FXC1 torPeriodsC1_FXC1 (torNode_FXC1 1 0 0)) = 1 :=
  torC1_circleFamily_FXC1.plateau _ torC1_origin_centre_FXC1 _
    (mem_ball_self (by norm_num))

/-- Every point of the example torus is a two-stratum point (the centre set is non-empty and the
two-stratum is everything). -/
theorem torC1_stratum_two_FXC1 (p : Tor_FXC1 torPeriodsC1_FXC1) :
    p ∈ scaledSplittingStratum.{0, 0} (fun _ : Tor_FXC1 torPeriodsC1_FXC1 => (1 : ℝ))
      (fun _ => one_pos) torBetaC1_FXC1 2 := by
  rw [torStratum_two_eq_univ_FXC1 torPeriodsC1_FXC1 one_pos (β := torBetaC1_FXC1)
    (by simp [torBetaC1_FXC1]) (by simp [torBetaC1_FXC1]; norm_num) torC1_hβ3_FXC1
    (by rw [torC1_L2_FXC1]; simp [torBetaC1_FXC1])
    (by rw [torC1_planePeriod_FXC1]; simp [torBetaC1_FXC1]; norm_num)]
  exact mem_univ p

end DifferentialGeometry.Geometry.Collapse

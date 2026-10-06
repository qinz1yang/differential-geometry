import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusCircleChart
import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusCircleCentres

/-!
# Explicit consumer of the circle chart and the centre net (S-FIXTURE-C1, F1, consumer)

The torus `ℝ³ / (N ℤ ⊕ N ℤ ⊕ 10⁻⁷ ℤ)`, `N = 8·10⁷` (so `Lp = 8R/β₂` at `R = 1`, `β₂ = 10⁻⁷`):

* the LC83 chart at the centre `π(0, 0, 0)` has `center = π 0` and `η(π 0) = 0`;
* every point is within `1` of a centre; the centres `π(0,0,0)` and `π(1,0,0)` are `≥ 1` apart.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] torMS_FXC1

/-- The periods `(8·10⁷, 8·10⁷, 10⁻⁷)`. -/
def torPeriodsC1_FXC1 : TorusPeriods_FXC1 where
  L := fun i => if i = 2 then 1 / 10 ^ 7 else 80000000
  pos := fun i => by
    by_cases h : i = 2 <;> simp [h]

/-- The tolerances `β₂ = 10⁻⁷`, `β₃ = 3/20`. -/
def torBetaC1_FXC1 : ℕ → ℝ := fun k => if k = 3 then 3 / 20 else 1 / 10 ^ 7

theorem torC1_L0_FXC1 : torPeriodsC1_FXC1.L 0 = ((80000000 : ℕ) : ℝ) * 1 := by
  simp [torPeriodsC1_FXC1]

theorem torC1_L1_FXC1 : torPeriodsC1_FXC1.L 1 = ((80000000 : ℕ) : ℝ) * 1 := by
  simp [torPeriodsC1_FXC1]

theorem torC1_L2_FXC1 : torPeriodsC1_FXC1.L 2 = 1 / 10 ^ 7 := by simp [torPeriodsC1_FXC1]

theorem torC1_planePeriod_FXC1 : planePeriod_FXC1 torPeriodsC1_FXC1 = 80000000 := by
  simp [planePeriod_FXC1, torPeriodsC1_FXC1]

/-- The LC83 circle chart of the example torus at the centre `π 0` is centred there and vanishes
there. -/
theorem torC1_chart_FXC1 :
    letI := (torMS_FXC1 torPeriodsC1_FXC1).rescale (1 : ℝ)⁻¹ (inv_pos.mpr one_pos)
    (torChart_FXC1 torPeriodsC1_FXC1 (R := 1) (β := torBetaC1_FXC1) one_pos
      (by simp [torBetaC1_FXC1]) (by simp [torBetaC1_FXC1])
      (by rw [torC1_L2_FXC1]; simp [torBetaC1_FXC1])
      (by rw [torC1_planePeriod_FXC1]; simp [torBetaC1_FXC1]; norm_num)
      (torPi_FXC1 torPeriodsC1_FXC1 0)).center = torPi_FXC1 torPeriodsC1_FXC1 0 :=
  rfl

/-- Every point of the example torus is within `1` of a centre. -/
theorem torC1_cover_FXC1 (p : Tor_FXC1 torPeriodsC1_FXC1) :
    ∃ j ∈ torCentres_FXC1 torPeriodsC1_FXC1 1 80000000, dist p j ≤ 1 :=
  torCentres_cover_FXC1 torPeriodsC1_FXC1 80000000 torC1_L0_FXC1 torC1_L1_FXC1 one_pos
    (by norm_num) (by rw [torC1_L2_FXC1]; norm_num) p

/-- The centres `π(0,0,0)` and `π(1,0,0)` are at least `1` apart. -/
theorem torC1_sep_FXC1 :
    1 ≤ dist (torPi_FXC1 torPeriodsC1_FXC1 (torNode_FXC1 1 0 0))
      (torPi_FXC1 torPeriodsC1_FXC1 (torNode_FXC1 1 1 0)) :=
  torCentres_sep_FXC1 torPeriodsC1_FXC1 80000000 torC1_L0_FXC1 torC1_L1_FXC1 one_pos
    (a := 0) (b := 0) (a' := 1) (b' := 0)
    (by simp) (by simp) (by simp) (by simp) (by simp)

end DifferentialGeometry.Geometry.Collapse

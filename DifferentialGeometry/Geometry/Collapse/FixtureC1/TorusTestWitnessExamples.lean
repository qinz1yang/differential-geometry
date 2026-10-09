import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusTestWitness
import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusRegisterPacket
import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusCircleExamples

/-!
# Consumers of G10: the geodesic test has a witness on the register torus and on the C1 example
# (O-FIXTURE-C1, G10 file 2)

* `torRegPeriods_plane_ge_OFC`: the register torus (scale `1`, side `⌈8/β₂⌉₊`, `β₂ ≤ 10⁻⁷`) has
  plane period `≥ 404`; `torRegTest_witness_OFC`: the premises of the geodesic test of its circle
  adapted centres are met at the origin centre.
* `torC1Test_witness_OFC`: the same on S-FIXTURE-C1's example torus `(8·10⁷, 8·10⁷, 10⁻⁷)`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] torMS_FXC1

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The register torus has plane period at least `404` (scale `1`). -/
theorem torRegPeriods_plane_ge_OFC {D : ClosedEarlyData} {T : ClosedThresholdsV4 D}
    (R : ClosedRegisterV4 D T) (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C D))
    (hlc : T.lc18 ≤ threeSplittingExclusionThreshold.{0, 0}) :
    404 * 1 ≤ planePeriod_FXC1 (torRegPeriods_OFC R.later.excl.β₂ R.later.β₂_pos) := by
  obtain ⟨h0, h7, -⟩ := R.torus_numbers_OFC hT hlc
  rw [R.β_two_VAL6] at h0 h7
  have hp := torRegPeriods_plane_OFC R.later.β₂_pos
  have h8 : 404 * 1 ≤ 8 * 1 / R.later.excl.β₂ := by
    rw [le_div_iff₀ h0]
    nlinarith
  linarith

/-- **The geodesic test of the register torus has a witness at the origin centre.** -/
theorem torRegTest_witness_OFC {D : ClosedEarlyData} {T : ClosedThresholdsV4 D}
    (R : ClosedRegisterV4 D T) (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C D))
    (hlc : T.lc18 ≤ threeSplittingExclusionThreshold.{0, 0}) :
    type_of% (torTest_witness_OFC (torRegPeriods_OFC R.later.excl.β₂ R.later.β₂_pos) one_pos
      (torRegOrigin_OFC R) (torRegPeriods_plane_ge_OFC R hT hlc)) :=
  torTest_witness_OFC _ one_pos _ (torRegPeriods_plane_ge_OFC R hT hlc)

/-- **The geodesic test of S-FIXTURE-C1's example torus has a witness** (at every centre). -/
theorem torC1Test_witness_OFC (j : Tor_FXC1 torPeriodsC1_FXC1) :
    type_of% (torTest_witness_OFC torPeriodsC1_FXC1 one_pos j
      (by rw [torC1_planePeriod_FXC1]; norm_num)) :=
  torTest_witness_OFC _ one_pos j (by rw [torC1_planePeriod_FXC1]; norm_num)

end DifferentialGeometry.Geometry.Collapse

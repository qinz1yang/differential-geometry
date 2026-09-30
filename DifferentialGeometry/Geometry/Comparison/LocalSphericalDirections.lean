import DifferentialGeometry.Geometry.Comparison.ConeSphericalComparison
import DifferentialGeometry.Geometry.Comparison.FiniteDimensionalTangentGeometry

set_option autoImplicit false

open Set Metric Filter Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem spherical_direction_comparison_of_local_comparison_and_dimH
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    {U : Set X} (hU : IsOpen U) {n : ℕ} (hdim : dimH U ≤ n)
    (hlocal : ∀ z ∈ U, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison 1 Ω ∧ z ∈ Ω)
    {q : X} (hq : q ∈ U) :
    letI : HasAnglesAt q := by
      obtain ⟨Ω, hΩ, hcomp, hqΩ⟩ := hlocal q hq
      exact hasAnglesAt_of_local_fourPointComparison (by norm_num : (0 : ℝ) ≤ 1) hΩ hcomp hqΩ
    ∀ ξ : SpaceOfDirections q,
      fourPointSphericalComparison (ball ξ (Real.pi / 4)) := by
  let : HasAnglesAt q := by
    obtain ⟨Ω, hΩ, hcomp, hqΩ⟩ := hlocal q hq
    exact hasAnglesAt_of_local_fourPointComparison (by norm_num : (0 : ℝ) ≤ 1) hΩ hcomp hqΩ
  have hdim' : dimH U ≤ (n + 1 : ℕ) := hdim.trans (by exact_mod_cast Nat.le_succ n)
  obtain ⟨_, _, hcone, _, _⟩ := tangent_geometry_and_blowup_of_local_comparison_and_dimH
    hcurves hU (by omega : 1 ≤ n + 1) hdim' hlocal hq
  exact fun ξ => fourPointSphericalComparison_ball_of_cone_comparison hcone ξ

theorem spherical_direction_comparison_of_intrinsic_eight_comparison_and_dimH
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (p : X) {R : ℝ} (hR : 0 < R) {n : ℕ}
    (hdim : dimH (ball p (8 * R)) ≤ n)
    (hlocal : ∀ z : ball p (8 * R), ∃ Ω : Set (ball p (8 * R)),
      @IsOpen (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)) 1 Ω ∧ z ∈ Ω)
    {q : X} (hq : q ∈ ball p (8 * R)) :
    letI : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
      (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal hq
    ∀ ξ : SpaceOfDirections q,
      fourPointSphericalComparison (ball ξ (Real.pi / 4)) := by
  let : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
    (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal hq
  have hdim' : dimH (ball p (8 * R)) ≤ (n + 1 : ℕ) :=
    hdim.trans (by exact_mod_cast Nat.le_succ n)
  obtain ⟨_, _, hcone, _, _⟩ := tangent_geometry_and_blowup_of_intrinsic_eight_comparison_and_dimH
    hcurves p hR (by omega : 1 ≤ n + 1) hdim' hlocal hq
  exact fun ξ => fourPointSphericalComparison_ball_of_cone_comparison hcone ξ

end DifferentialGeometry.Geometry.Comparison.Toponogov

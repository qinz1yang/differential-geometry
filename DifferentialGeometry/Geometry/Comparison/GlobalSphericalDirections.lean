import DifferentialGeometry.Geometry.Comparison.FiniteDimensionalPiDirections
import DifferentialGeometry.Geometry.Comparison.TangentComparison
import DifferentialGeometry.Geometry.Comparison.GlobalSphericalComparison

set_option autoImplicit false

open Set Metric Filter Topology

universe u

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem global_spherical_direction_comparison_of_local_comparison_and_dimH
    {X : Type u} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    {U : Set X} (hU : IsOpen U) {n : ℕ} (hdim : dimH U ≤ n)
    (hlocal : ∀ z ∈ U, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison 1 Ω ∧ z ∈ Ω)
    {q : X} (hq : q ∈ U) :
    letI : HasAnglesAt q := by
      obtain ⟨Ω, hΩ, hcomp, hqΩ⟩ := hlocal q hq
      exact hasAnglesAt_of_local_fourPointComparison (by norm_num : (0 : ℝ) ≤ 1) hΩ hcomp hqΩ
    fourPointSphericalComparison (univ : Set (SpaceOfDirections q)) := by
  let : HasAnglesAt q := by
    obtain ⟨Ω, hΩ, hcomp, hqΩ⟩ := hlocal q hq
    exact hasAnglesAt_of_local_fourPointComparison (by norm_num : (0 : ℝ) ≤ 1) hΩ hcomp hqΩ
  have hdim' : dimH U ≤ (n + 1 : ℕ) := hdim.trans (by exact_mod_cast Nat.le_succ n)
  obtain ⟨_, hsegments⟩ := compact_pi_geodesic_directions_of_local_comparison_and_dimH
    hcurves hU (by omega : 1 ≤ n + 1) hdim' hlocal hq
  obtain ⟨Ω, hΩ, hcomp, hqΩ⟩ := hlocal q hq
  have hcone : fourPointComparison 0 (univ : Set (TangentCone q)) :=
    tangentCone_fourPointComparison_zero_of_local_fourPointComparison
      (by norm_num : (0 : ℝ) ≤ 1) hΩ hcomp hqΩ
  exact fourPointSphericalComparison_univ_of_cone_comparison SpaceOfDirections.dist_le_pi hcone hsegments

theorem global_spherical_direction_comparison_of_intrinsic_eight_comparison_and_dimH
    {X : Type u} [MetricSpace X] [CompleteSpace X]
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
    fourPointSphericalComparison (univ : Set (SpaceOfDirections q)) := by
  let : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
    (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal hq
  apply global_spherical_direction_comparison_of_local_comparison_and_dimH
    hcurves isOpen_ball hdim _ hq
  intro z hz
  exact (exists_local_fourPointComparison_intrinsicBall_iff hcurves p
    (by positivity : 0 < 8 * R) ⟨z, hz⟩).mp (hlocal ⟨z, hz⟩)

end DifferentialGeometry.Geometry.Comparison.Toponogov

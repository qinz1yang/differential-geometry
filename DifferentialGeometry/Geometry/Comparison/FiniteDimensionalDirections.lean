import DifferentialGeometry.Geometry.Metric.CompactDirections
import DifferentialGeometry.Geometry.Metric.EuclideanConeProper
import DifferentialGeometry.Geometry.Comparison.UniformSmallScaleNets
import DifferentialGeometry.Geometry.Comparison.IntrinsicGeodesicDirections

set_option autoImplicit false

open Set Metric Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem compact_directions_and_proper_tangent_of_local_comparison_and_dimH
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    {U : Set X} (hU : IsOpen U) {n : ℕ} (hn : 1 ≤ n) (hdim : dimH U ≤ n)
    (hlocal : ∀ z ∈ U, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison 1 Ω ∧ z ∈ Ω)
    {q : X} (hq : q ∈ U) :
    letI : HasAnglesAt q := by
      obtain ⟨Ω, hΩ, hcomp, hqΩ⟩ := hlocal q hq
      exact hasAnglesAt_of_local_fourPointComparison (by norm_num : (0 : ℝ) ≤ 1) hΩ hcomp hqΩ
    CompactSpace (SpaceOfDirections q) ∧ ProperSpace (TangentCone q) := by
  let : HasAnglesAt q := by
    obtain ⟨Ω, hΩ, hcomp, hqΩ⟩ := hlocal q hq
    exact hasAnglesAt_of_local_fourPointComparison (by norm_num : (0 : ℝ) ≤ 1) hΩ hcomp hqΩ
  let hcompact : CompactSpace (SpaceOfDirections q) := by
    apply compactSpace_spaceOfDirections_of_uniform_scaled_nets q
    intro ε hε
    obtain ⟨S, hS, hnet⟩ := exists_uniform_small_scale_nets_of_local_comparison_and_dimH
      hcurves hU hn hdim hlocal hq
    refine ⟨(1 + ⌈4 * (pairedChartDistortion n) ^ 2 * sqrt n * sinh 2 / ε⌉₊) ^ n, S, hS, ?_⟩
    intro s hs hsS
    obtain ⟨T, hcard, _, hT⟩ := hnet s hs hsS ε hε
    exact ⟨T, hcard, hT⟩
  exact ⟨hcompact, inferInstanceAs (ProperSpace (EuclideanCone (SpaceOfDirections q)))⟩

theorem compact_directions_and_proper_tangent_of_intrinsic_eight_comparison_and_dimH
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (p : X) {R : ℝ} (hR : 0 < R) {n : ℕ} (hn : 1 ≤ n)
    (hdim : dimH (ball p (8 * R)) ≤ n)
    (hlocal : ∀ z : ball p (8 * R), ∃ Ω : Set (ball p (8 * R)),
      @IsOpen (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)) 1 Ω ∧ z ∈ Ω)
    {q : X} (hq : q ∈ ball p (8 * R)) :
    letI : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
      (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal hq
    CompactSpace (SpaceOfDirections q) ∧ ProperSpace (TangentCone q) := by
  let : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
    (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal hq
  apply compact_directions_and_proper_tangent_of_local_comparison_and_dimH
    hcurves isOpen_ball hn hdim _ hq
  intro z hz
  exact (exists_local_fourPointComparison_intrinsicBall_iff hcurves p
    (by positivity : 0 < 8 * R) ⟨z, hz⟩).mp (hlocal ⟨z, hz⟩)

end DifferentialGeometry.Geometry.Comparison.Toponogov

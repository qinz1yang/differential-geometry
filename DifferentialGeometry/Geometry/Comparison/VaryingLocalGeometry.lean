import DifferentialGeometry.Geometry.Comparison.FiniteDimensionalLocalCompactness
import DifferentialGeometry.Geometry.Comparison.RescaleComparison
import DifferentialGeometry.Geometry.Comparison.CurvatureWeakening
import DifferentialGeometry.Geometry.Comparison.LocalBufferComparison
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleLength

set_option autoImplicit false

open Set Metric Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem locallyCompactSpace_of_nonnegative_parameter_local_comparison_and_dimH
    {X : Type*} [m : MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    {κ : ℝ} (hκ : 0 ≤ κ) {U : Set X} (hU : IsOpen U)
    {n : ℕ} (hdim : dimH U ≤ n)
    (hlocal : ∀ p ∈ U, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison κ Ω ∧ p ∈ Ω) :
    LocallyCompactSpace U := by
  rcases eq_or_lt_of_le hκ with hzero | hpos
  · have hk : κ = 0 := hzero.symm
    subst κ
    apply locallyCompactSpace_of_local_comparison_and_dimH hcurves hU hdim
    intro p hp
    obtain ⟨Ω, hΩ, hc, hpΩ⟩ := hlocal p hp
    exact ⟨Ω, hΩ, hc.of_zero zero_le_one, hpΩ⟩
  · let c := sqrt κ
    have hc : 0 < c := sqrt_pos.mpr hpos
    let m' := m.rescale c hc
    have hcomplete : @CompleteSpace X m'.toUniformSpace :=
      (m.rescale_completeSpace_iff c hc).mpr inferInstance
    have hcurves' := @MetricSpace.rescale_arbitrarily_short_curves X m hcurves c hc
    have hdim' : @dimH X m'.toEMetricSpace U ≤ n := by
      rw [MetricSpace.rescale_dimH]
      exact hdim
    have hlocal' : ∀ p ∈ U, ∃ Ω : Set X,
        @IsOpen X m'.toUniformSpace.toTopologicalSpace Ω ∧ @fourPointComparison X m' 1 Ω ∧ p ∈ Ω := by
      intro p hp
      exact (@local_fourPointComparison_rescale_sqrt_iff X m κ hpos p).mpr (hlocal p hp)
    exact @locallyCompactSpace_of_local_comparison_and_dimH X m' hcomplete
      (fun a b ε hε => hcurves' a b hε) U hU n hdim' hlocal'

theorem fourPointComparison_two_ball_of_local_comparison_and_dimH
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (o : X) {κ R : ℝ} (hκ : 0 ≤ κ) (hR : 0 < R)
    {n : ℕ} (hdim : dimH (ball o (256 * R)) ≤ n)
    (hlocal : ∀ z ∈ ball o (256 * R),
      ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison κ Ω ∧ z ∈ Ω) :
    fourPointComparison κ (ball o (2 * R)) := by
  let : LocallyCompactSpace (ball o (256 * R)) :=
    locallyCompactSpace_of_nonnegative_parameter_local_comparison_and_dimH
      hcurves hκ isOpen_ball hdim hlocal
  exact fourPointComparison_two_ball_of_local_256_buffer hcurves o hκ hR hlocal

theorem fourPointComparison_two_ball_of_intrinsic_local_comparison_and_dimH
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (o : X) {κ R : ℝ} (hκ : 0 ≤ κ) (hR : 0 < R)
    {n : ℕ} (hdim : dimH (ball o (256 * R)) ≤ n)
    (hlocal : ∀ p : ball o (256 * R), ∃ Ω : Set (ball o (256 * R)),
      @IsOpen (ball o (256 * R))
        (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 256 * R)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison (ball o (256 * R))
        (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 256 * R)) κ Ω ∧ p ∈ Ω) :
    fourPointComparison κ (ball o (2 * R)) := by
  apply fourPointComparison_two_ball_of_local_comparison_and_dimH hcurves o hκ hR hdim
  intro p hp
  exact (exists_local_fourPointComparison_intrinsicBall_iff hcurves o
    (by positivity : 0 < 256 * R) ⟨p, hp⟩).mp (hlocal ⟨p, hp⟩)

end DifferentialGeometry.Geometry.Comparison.Toponogov

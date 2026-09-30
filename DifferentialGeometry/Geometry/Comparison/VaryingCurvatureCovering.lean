import DifferentialGeometry.Geometry.Comparison.FiniteDimensionalCovering
import DifferentialGeometry.Geometry.Comparison.RescaleComparison
import DifferentialGeometry.Geometry.Comparison.CurvatureWeakening
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleLength
import DifferentialGeometry.Topology.MetricSpace.RescaleNetBound

set_option autoImplicit false

open Set Metric Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_closedBall_net_of_bounded_local_curvature_and_dimH
    {X : Type*} [m : MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (o : X) {κ R ε : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1) (hR : 0 < R) (hε : 0 < ε)
    {n : ℕ} (hn : 1 ≤ n) (hdim : dimH (ball o (256 * R)) ≤ n)
    (hlocal : ∀ z ∈ ball o (256 * R),
      ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison κ Ω ∧ z ∈ Ω) :
    ∃ T : Finset X,
      T.card ≤ (1 + ⌈4 * (pairedChartDistortion n) ^ 2 * sqrt n * sinh (2 * R) / ε⌉₊) ^ n ∧
      (T : Set X) ⊆ closedBall o R ∧ ∀ x ∈ closedBall o R, ∃ y ∈ T, dist x y < ε := by
  rcases eq_or_lt_of_le hκ with hzero | hpos
  · have hk : κ = 0 := hzero.symm
    subst κ
    apply exists_closedBall_net_of_local_comparison_and_dimH hcurves o hR hε hn hdim
    intro z hz
    obtain ⟨Ω, hΩ, hc, hp⟩ := hlocal z hz
    exact ⟨Ω, hΩ, hc.of_zero zero_le_one, hp⟩
  · let c := sqrt κ
    have hc : 0 < c := sqrt_pos.mpr hpos
    have hc1 : c ≤ 1 := sqrt_le_one.mpr hκ1
    let m' := m.rescale c hc
    have hcomplete : @CompleteSpace X m'.toUniformSpace :=
      (m.rescale_completeSpace_iff c hc).mpr inferInstance
    have hcurves' := @MetricSpace.rescale_arbitrarily_short_curves X m hcurves c hc
    have hball : @ball X m'.toPseudoMetricSpace o (256 * (c * R)) = @ball X m.toPseudoMetricSpace o (256 * R) := by
      rw [show 256 * (c * R) = c * (256 * R) by ring]
      exact m.rescale_ball c hc o (256 * R)
    have hdim' : @dimH X m'.toEMetricSpace (@ball X m'.toPseudoMetricSpace o (256 * (c * R))) ≤ n := by
      rw [hball, MetricSpace.rescale_dimH]
      exact hdim
    have hlocal' : ∀ z ∈ @ball X m'.toPseudoMetricSpace o (256 * (c * R)),
        ∃ Ω : Set X, @IsOpen X m'.toUniformSpace.toTopologicalSpace Ω ∧
          @fourPointComparison X m' 1 Ω ∧ z ∈ Ω := by
      rw [hball]
      intro z hz
      exact (@local_fourPointComparison_rescale_sqrt_iff X m κ hpos z).mpr (hlocal z hz)
    obtain ⟨T, hcard, hT, hnet⟩ := @exists_closedBall_net_of_local_comparison_and_dimH X m'
      hcomplete (fun a b η hη => hcurves' a b hη) o (c * R) (c * ε)
      (mul_pos hc hR) (mul_pos hc hε) n hn hdim' hlocal'
    refine ⟨T, hcard.trans (chart_net_bound_rescale_le hR.le hε hc hc1), ?_, ?_⟩
    · rwa [m.rescale_closedBall c hc o R] at hT
    · intro x hx
      have hx' : x ∈ @closedBall X m'.toPseudoMetricSpace o (c * R) := by
        rwa [m.rescale_closedBall c hc o R]
      obtain ⟨y, hy, hxy⟩ := hnet x hx'
      exact ⟨y, hy, (mul_lt_mul_iff_right₀ hc).mp hxy⟩

theorem exists_closedBall_net_of_bounded_intrinsic_local_curvature_and_dimH
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (o : X) {κ R ε : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1) (hR : 0 < R) (hε : 0 < ε)
    {n : ℕ} (hn : 1 ≤ n) (hdim : dimH (ball o (256 * R)) ≤ n)
    (hlocal : ∀ p : ball o (256 * R), ∃ Ω : Set (ball o (256 * R)),
      @IsOpen (ball o (256 * R))
        (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 256 * R)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison (ball o (256 * R))
        (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 256 * R)) κ Ω ∧ p ∈ Ω) :
    ∃ T : Finset X,
      T.card ≤ (1 + ⌈4 * (pairedChartDistortion n) ^ 2 * sqrt n * sinh (2 * R) / ε⌉₊) ^ n ∧
      (T : Set X) ⊆ closedBall o R ∧ ∀ x ∈ closedBall o R, ∃ y ∈ T, dist x y < ε := by
  apply exists_closedBall_net_of_bounded_local_curvature_and_dimH hcurves o hκ hκ1 hR hε hn hdim
  intro p hp
  exact (exists_local_fourPointComparison_intrinsicBall_iff hcurves o
    (by positivity : 0 < 256 * R) ⟨p, hp⟩).mp (hlocal ⟨p, hp⟩)

end DifferentialGeometry.Geometry.Comparison.Toponogov

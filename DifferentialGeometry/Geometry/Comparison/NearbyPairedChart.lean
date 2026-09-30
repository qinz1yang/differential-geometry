import DifferentialGeometry.Geometry.Comparison.CenteredPairedChart
import DifferentialGeometry.Geometry.Comparison.IntrinsicLocalComparison

set_option autoImplicit false

open Set Metric Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem one_le_pairedChartDistortion {n : ℕ} (hn : 1 ≤ n) : 1 ≤ pairedChartDistortion n := by
  simpa only [Nat.cast_one, sqrt_one] using sqrt_le_pairedChartDistortion hn

theorem exists_centered_chart_near_of_local_comparison
    {X : Type*} [MetricSpace X] [CompleteSpace X] [Nontrivial X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    {U : Set X} (hU : IsOpen U) {n : ℕ} (hn : 1 ≤ n) (hdim : dimH U ≤ n)
    {p : X} (hp : p ∈ U)
    (hlocal : ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison 1 Ω ∧ p ∈ Ω)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ n ∧ ∃ q ∈ U ∩ ball p ε,
      ∃ a : Fin m → X, range a ⊆ U ∧ ∃ r : ℝ, ∃ hr : 0 < r,
      ball q r ⊆ U ∩ ball p ε ∧
      ∃ φ : ball q r → PiLp 2 (fun _ : Fin m => ℝ),
        (∀ z, φ z = distanceCoordinates 2 a (z : X) - distanceCoordinates 2 a q) ∧
        φ ⟨q, mem_ball_self hr⟩ = 0 ∧
        (∀ x y : ball q r, (pairedChartDistortion n)⁻¹ * dist x y ≤ dist (φ x) (φ y)) ∧
        (∀ x y : ball q r, dist (φ x) (φ y) ≤ pairedChartDistortion n * dist x y) := by
  obtain ⟨Ω, hΩ, hcomp, hpΩ⟩ := hlocal
  let V := Ω ∩ (U ∩ ball p ε)
  have hV : IsOpen V := hΩ.inter (hU.inter isOpen_ball)
  have hVsub : V ⊆ U ∩ ball p ε := inter_subset_right
  have hcompV : fourPointComparison 1 V := hcomp.mono inter_subset_left
  have hpV : p ∈ V := ⟨hpΩ, hp, mem_ball_self hε⟩
  have hdimV : dimH V ≤ n := (dimH_mono (hVsub.trans inter_subset_left)).trans hdim
  obtain ⟨m, hm1, hmn, q, hq, a, ha, r, hr, hBr, W, _, e, he, hzero, hlo, hhi⟩ :=
    exists_centered_distance_chart_in_open_set hcurves hcompV (Subset.refl V) hV ⟨p, hpV⟩
      (fun z _ => ⟨1, zero_lt_one, isClosed_closedBall.isComplete⟩) hn hdimV
  exact ⟨m, hm1, hmn, q, hVsub hq, a, ha.trans (hVsub.trans inter_subset_left), r, hr,
    hBr.trans hVsub, fun z => (e z : PiLp 2 (fun _ : Fin m => ℝ)), he, hzero, hlo, hhi⟩

theorem exists_centered_chart_near_of_intrinsic_local_comparison
    {X : Type*} [MetricSpace X] [CompleteSpace X] [Nontrivial X]
    (hcurves : ∀ a b : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (o : X) {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε)
    {n : ℕ} (hn : 1 ≤ n) (hdim : dimH (ball o L) ≤ n)
    (hlocal : ∃ Ω : Set (ball o L),
      @IsOpen (ball o L) (intrinsicBallMetricSpace hcurves o hL).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison (ball o L) (intrinsicBallMetricSpace hcurves o hL) 1 Ω ∧
      (⟨o, mem_ball_self hL⟩ : ball o L) ∈ Ω) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ n ∧ ∃ q ∈ ball o L ∩ ball o ε,
      ∃ a : Fin m → X, range a ⊆ ball o L ∧ ∃ r : ℝ, ∃ hr : 0 < r,
      ball q r ⊆ ball o L ∩ ball o ε ∧
      ∃ φ : ball q r → PiLp 2 (fun _ : Fin m => ℝ),
        (∀ z, φ z = distanceCoordinates 2 a (z : X) - distanceCoordinates 2 a q) ∧
        φ ⟨q, mem_ball_self hr⟩ = 0 ∧
        (∀ x y : ball q r, (pairedChartDistortion n)⁻¹ * dist x y ≤ dist (φ x) (φ y)) ∧
        (∀ x y : ball q r, dist (φ x) (φ y) ≤ pairedChartDistortion n * dist x y) := by
  exact exists_centered_chart_near_of_local_comparison hcurves isOpen_ball hn hdim
    (mem_ball_self hL)
    ((exists_local_fourPointComparison_intrinsicBall_iff hcurves o hL
      ⟨o, mem_ball_self hL⟩).mp hlocal) hε

end DifferentialGeometry.Geometry.Comparison.Toponogov

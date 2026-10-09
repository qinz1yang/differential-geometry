import DifferentialGeometry.Geometry.Comparison.FiniteDimensionalLocalCompactness
import DifferentialGeometry.Geometry.Comparison.NearbyPairedChart
import DifferentialGeometry.Topology.MetricSpace.ChartNetBound
import DifferentialGeometry.Geometry.Comparison.EightChartCovering

set_option autoImplicit false


open Set Metric Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_closedBall_net_of_local_eight_comparison_and_dimH
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (o : X) {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n)
    (hdim : dimH (ball o (8 * R)) ≤ n)
    (hlocal : ∀ z ∈ ball o (8 * R),
      ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison 1 Ω ∧ z ∈ Ω) :
    ∃ T : Finset X,
      T.card ≤ (1 + ⌈4 * (pairedChartDistortion n) ^ 2 * sqrt n * sinh (2 * R) / ε⌉₊) ^ n ∧
      (T : Set X) ⊆ closedBall o R ∧ ∀ x ∈ closedBall o R, ∃ y ∈ T, dist x y < ε := by
  classical
  rcases subsingleton_or_nontrivial X with hsub | hnontriv
  · refine ⟨{o}, ?_, ?_, ?_⟩
    · simp only [Finset.card_singleton]
      have hpos : 0 < (1 + ⌈4 * (pairedChartDistortion n) ^ 2 * sqrt n * sinh (2 * R) / ε⌉₊) ^ n :=
        pow_pos (by omega) _
      omega
    · intro x hx
      have hx' : x = o := Finset.mem_singleton.mp hx
      subst x
      simpa only [mem_closedBall, dist_self] using hR.le
    · intro x hx
      refine ⟨o, Finset.mem_singleton_self o, ?_⟩
      rw [Subsingleton.elim x o, dist_self]
      exact hε
  · let : LocallyCompactSpace (ball o (8 * R)) :=
      locallyCompactSpace_of_local_comparison_and_dimH hcurves isOpen_ball hdim hlocal
    have ho : o ∈ ball o (8 * R) := mem_ball_self (by positivity)
    obtain ⟨m, hm1, hmn, q, hq, a, _, r, hr, _, φ, _, hzero, hlo, hhi⟩ :=
      exists_centered_chart_near_of_local_comparison hcurves isOpen_ball hn hdim ho
        (hlocal o ho) (by positivity : 0 < R / 2)
    obtain ⟨T, hcard, hT, hnet⟩ := exists_closedBall_net_of_intrinsic_8_comparison_and_chart
      hcurves o hR (fun z =>
        (exists_local_fourPointComparison_intrinsicBall_iff hcurves o
          (by positivity : 0 < 8 * R) z).mpr (hlocal z.val z.property)) hq.2 (by omega : 0 < m) (one_le_pairedChartDistortion hn)
      hr hε φ hzero hlo hhi
    exact ⟨T, hcard.trans (chart_net_bound_mono_dimension hmn hR.le hε), hT, hnet⟩

theorem exists_closedBall_net_of_intrinsic_local_eight_comparison_and_dimH
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (o : X) {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n)
    (hdim : dimH (ball o (8 * R)) ≤ n)
    (hlocal : ∀ p : ball o (8 * R), ∃ Ω : Set (ball o (8 * R)),
      @IsOpen (ball o (8 * R))
        (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 8 * R)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison (ball o (8 * R))
        (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 8 * R)) 1 Ω ∧ p ∈ Ω) :
    ∃ T : Finset X,
      T.card ≤ (1 + ⌈4 * (pairedChartDistortion n) ^ 2 * sqrt n * sinh (2 * R) / ε⌉₊) ^ n ∧
      (T : Set X) ⊆ closedBall o R ∧ ∀ x ∈ closedBall o R, ∃ y ∈ T, dist x y < ε := by
  apply exists_closedBall_net_of_local_eight_comparison_and_dimH hcurves o hR hε hn hdim
  intro p hp
  exact (exists_local_fourPointComparison_intrinsicBall_iff hcurves o
    (by positivity : 0 < 8 * R) ⟨p, hp⟩).mp (hlocal ⟨p, hp⟩)

end DifferentialGeometry.Geometry.Comparison.Toponogov

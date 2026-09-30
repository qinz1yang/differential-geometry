import DifferentialGeometry.Geometry.Comparison.EightFiniteDimensionalCovering
import DifferentialGeometry.Topology.MetricSpace.RescaleNetBound

set_option autoImplicit false

open Set Metric Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_uniform_small_scale_nets_of_local_comparison_and_dimH
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    {U : Set X} (hU : IsOpen U) {n : ℕ} (hn : 1 ≤ n) (hdim : dimH U ≤ n)
    (hlocal : ∀ z ∈ U, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison 1 Ω ∧ z ∈ Ω)
    {q : X} (hq : q ∈ U) :
    ∃ S : ℝ, 0 < S ∧ ∀ s : ℝ, 0 < s → s < S → ∀ ε : ℝ, 0 < ε →
      ∃ T : Finset X,
        T.card ≤ (1 + ⌈4 * (pairedChartDistortion n) ^ 2 * sqrt n * sinh 2 / ε⌉₊) ^ n ∧
        (T : Set X) ⊆ closedBall q s ∧
        ∀ x ∈ closedBall q s, ∃ y ∈ T, dist x y < ε * s := by
  obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hU q hq
  refine ⟨min (δ / 8) 1, lt_min (by positivity) zero_lt_one, ?_⟩
  intro s hs hsS ε hε
  have hsδ : s < δ / 8 := hsS.trans_le (min_le_left _ _)
  have hs1 : s ≤ 1 := hsS.le.trans (min_le_right _ _)
  have hsmall : ball q (8 * s) ⊆ U := by
    intro x hx
    apply hsub
    have hxd : dist x q < 8 * s := hx
    change dist x q < δ
    linarith
  obtain ⟨T, hcard, hT, hnet⟩ := exists_closedBall_net_of_local_eight_comparison_and_dimH
    hcurves q hs (mul_pos hs hε) hn ((dimH_mono hsmall).trans hdim)
    (fun z hz => hlocal z (hsmall hz))
  have hbound := chart_net_bound_rescale_le (n := n) (L := pairedChartDistortion n)
    (R := 1) (by norm_num) hε hs hs1
  simp only [mul_one] at hbound
  refine ⟨T, hcard.trans hbound, hT, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hnet x hx
  exact ⟨y, hy, by simpa only [mul_comm s ε] using hxy⟩

end DifferentialGeometry.Geometry.Comparison.Toponogov

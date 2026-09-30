import DifferentialGeometry.Geometry.Comparison.AlmostStraightTriangle
import DifferentialGeometry.Topology.MetricSpace.AlmostRadialPoint

set_option autoImplicit false

open Set Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem almost_radial_constants_pos {a A δ : ℝ} (ha : 0 < a) (haA : a ≤ A)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100) :
    let C := sinh (A + 1) / sinh (a / 2)
    let ν := min (δ ^ 2) (min ((1 - cos δ) / C) 1)
    0 < ν ∧ ν ≤ δ ^ 2 ∧ ν ≤ 1 ∧
      sinh (A + 1) * ν ≤ (1 - cos δ) * sinh (a / 2) := by
  dsimp only
  let C := sinh (A + 1) / sinh (a / 2)
  let ν := min (δ ^ 2) (min ((1 - cos δ) / C) 1)
  change 0 < ν ∧ ν ≤ δ ^ 2 ∧ ν ≤ 1 ∧ _
  have hsa : 0 < sinh (a / 2) := sinh_pos_iff.mpr (by linarith)
  have hS : 0 < sinh (A + 1) := sinh_pos_iff.mpr (by linarith)
  have hC : 0 < C := div_pos hS hsa
  have hcos : 0 < 1 - cos δ := by
    have h := cos_lt_cos_of_nonneg_of_le_pi (show (0 : ℝ) ≤ 0 by rfl)
      (show δ ≤ Real.pi by linarith [Real.two_le_pi]) hδ
    rw [cos_zero] at h
    linarith
  have hν : 0 < ν := lt_min (sq_pos_of_pos hδ) (lt_min (div_pos hcos hC) zero_lt_one)
  have hνC : ν ≤ (1 - cos δ) / C := (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨hν, min_le_left _ _, (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  have hb := (le_div_iff₀ hC).mp hνC
  have hCeq : C * sinh (a / 2) = sinh (A + 1) := div_mul_cancel₀ _ hsa.ne'
  change sinh (A + 1) * ν ≤ _
  calc
    sinh (A + 1) * ν = (ν * C) * sinh (a / 2) := by rw [mul_assoc, hCeq, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_right hb hsa.le

variable {X : Type*} [MetricSpace X]

theorem exists_almost_radial_point_with_comparison_angles
    (hcurves : ∀ p u : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = p ∧ c 1 = u ∧
        eVariationOn c univ < ENNReal.ofReal (dist p u + η))
    (p u : X) {a A t δ : ℝ} (ha : 0 < a) (har : a ≤ dist p u) (hrA : dist p u ≤ A)
    (ht : 0 < t) (ht1 : t ≤ 1) (hta : t ≤ a / 2)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100) :
    let C := sinh (A + 1) / sinh (a / 2)
    let ν := min (δ ^ 2) (min ((1 - cos δ) / C) 1)
    ∃ y : X, dist p y = t ∧
      dist p u - t ≤ dist y u ∧ dist y u < dist p u - t + ν * t ∧
      Real.pi - δ ≤ comparisonAngleNegCurvature 1 (dist y u) (dist y p) (dist u p) ∧
      comparisonAngleNegCurvature 1 (dist p u) (dist p y) (dist u y) ≤ δ ∧
      (1 - δ ^ 2) * t ≤ dist p u - dist y u ∧ dist p u - dist y u ≤ t ∧
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = p ∧ c 1 = u ∧
        eVariationOn c univ < ENNReal.ofReal (dist p u + ν * t) ∧
        ∃ s : unitInterval, c s = y ∧ ∀ v ≤ s, c v ∈ Metric.closedBall p t := by
  dsimp only
  let C := sinh (A + 1) / sinh (a / 2)
  let ν := min (δ ^ 2) (min ((1 - cos δ) / C) 1)
  obtain ⟨hν, hνδ, hν1, hνbudget⟩ := almost_radial_constants_pos ha (har.trans hrA) hδ hδ1
  change 0 < ν at hν
  change ν ≤ δ ^ 2 at hνδ
  change ν ≤ 1 at hν1
  change sinh (A + 1) * ν ≤ (1 - cos δ) * sinh (a / 2) at hνbudget
  obtain ⟨c, hc, hc0, hc1, hlen, s, hs, hslo, hshi, hbefore⟩ :=
    Metric.exists_almost_radial_point_of_arbitrarily_short_curves hcurves p u ht.le
      (by linarith : t ≤ dist p u) (mul_pos hν ht)
  have hbudget : sinh (A + 1) * (ν * t) ≤ (1 - cos δ) * (sinh (a / 2) * t) := by
    nlinarith [mul_le_mul_of_nonneg_right hνbudget ht.le]
  have hηt : ν * t ≤ t := by nlinarith
  obtain ⟨hang1, hang2⟩ := comparisonAngles_of_small_triangle_excess ha har hrA ht ht1 hta
    hηt hslo hshi.le hδ.le hbudget
  refine ⟨c s, hs, hslo, hshi, ?_, ?_, ?_, ?_, c, hc, hc0, hc1, hlen, s, rfl, hbefore⟩
  · simpa only [dist_comm (c s) p, dist_comm u p, hs] using hang1
  · simpa only [dist_comm u (c s), hs] using hang2
  · nlinarith [mul_le_mul_of_nonneg_right hνδ ht.le]
  · linarith

end DifferentialGeometry.Geometry.Comparison.Toponogov

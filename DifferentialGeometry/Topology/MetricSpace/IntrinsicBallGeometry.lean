import DifferentialGeometry.Topology.MetricSpace.IntrinsicBallCompleteness
import Mathlib.Topology.Compactness.LocallyCompact

set_option autoImplicit false

open Set Metric

namespace Metric

theorem intrinsicBall_dist_eq_on_inner_closedBall
    {X : Type*} [MetricSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (o : X) {L : ℝ} (hL : 0 < L) {x : X} {h : ℝ} (hh : 0 < h)
    (hmargin : dist x o + 4 * h < L)
    {a b : ball o L} (ha : (a : X) ∈ closedBall x h) (hb : (b : X) ∈ closedBall x h) :
    @dist (ball o L) (intrinsicBallMetricSpace hcurves o hL).toDist a b =
      dist (a : X) (b : X) := by
  rw [intrinsicBallMetricSpace_dist,
    intrinsicEDist_eq_edist_on_inner_closedBall hcurves hh hmargin ha hb,
    edist_dist, ENNReal.toReal_ofReal dist_nonneg]

theorem intrinsicBall_ball_image
    {X : Type*} [MetricSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (o : X) {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hmargin : 4 * r < L) :
    (fun y : ball o L => (y : X)) ''
      (@ball (ball o L) (intrinsicBallMetricSpace hcurves o hL).toPseudoMetricSpace
        ⟨o, by simpa only [mem_ball, dist_self] using hL⟩ r) = ball o r := by
  let p : ball o L := ⟨o, by simpa only [mem_ball, dist_self] using hL⟩
  have hLip := intrinsicBallMetricSpace_lipschitzWith_coe hcurves o hL
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    have hd := @LipschitzWith.dist_le_mul (ball o L) X
      (intrinsicBallMetricSpace hcurves o hL).toPseudoMetricSpace _ 1 _ hLip a p
    simp only [NNReal.coe_one, one_mul] at hd
    exact hd.trans_lt ha
  · intro hy
    have hy' : dist y o < r := hy
    have hymem : y ∈ ball o L := hy'.trans (by linarith)
    let a : ball o L := ⟨y, hymem⟩
    refine ⟨a, ?_, rfl⟩
    change @dist (ball o L) (intrinsicBallMetricSpace hcurves o hL).toDist a p < r
    rw [intrinsicBall_dist_eq_on_inner_closedBall hcurves o hL hr
      (by simpa only [dist_self, zero_add] using hmargin)
      (show (a : X) ∈ closedBall o r from hy'.le)
      (show (p : X) ∈ closedBall o r by
        simpa only [p, mem_closedBall, dist_self] using hr.le)]
    exact hy'

theorem intrinsicBallMetricSpace_locallyCompact
    {X : Type*} [MetricSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (o : X) {L : ℝ} (hL : 0 < L) [LocallyCompactSpace (ball o L)] :
    @LocallyCompactSpace (ball o L)
      (intrinsicBallMetricSpace hcurves o hL).toUniformSpace.toTopologicalSpace := by
  rw [intrinsicBallMetricSpace_toTopology hcurves o hL]
  infer_instance

end Metric

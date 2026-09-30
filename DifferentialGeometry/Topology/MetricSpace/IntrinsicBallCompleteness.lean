import DifferentialGeometry.Topology.MetricSpace.IntrinsicBallTopology
import DifferentialGeometry.Topology.MetricSpace.LipschitzBufferCompleteness

set_option autoImplicit false

open Set Metric

namespace Metric

theorem isComplete_intrinsicBall_closedBall
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (o : X) {L : ℝ} (hL : 0 < L) (p : ball o L) {r : ℝ}
    (hmargin : dist (p : X) o + r < L) :
    @IsComplete (ball o L) (intrinsicBallMetricSpace hcurves o hL).toUniformSpace
      (@closedBall (ball o L) (intrinsicBallMetricSpace hcurves o hL).toPseudoMetricSpace p r) := by
  exact @Topology.IsEmbedding.isComplete_closedBall_of_range_ball X (ball o L) _
    (intrinsicBallMetricSpace hcurves o hL) _ (fun y : ball o L => (y : X))
    (@Topology.IsOpenEmbedding.isEmbedding (ball o L) X (fun y : ball o L => (y : X))
      (intrinsicBallMetricSpace hcurves o hL).toUniformSpace.toTopologicalSpace inferInstance
      (intrinsicBallMetricSpace_isOpenEmbedding hcurves o hL))
    (intrinsicBallMetricSpace_lipschitzWith_coe hcurves o hL) o L Subtype.range_val p r hmargin

theorem intrinsicBall_closedBall_image
    {X : Type*} [MetricSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (o : X) {L : ℝ} (hL : 0 < L) (p : ball o L) {h : ℝ} (hh : 0 < h)
    (hmargin : dist (p : X) o + 4 * h < L) :
    (fun y : ball o L => (y : X)) ''
      (@closedBall (ball o L) (intrinsicBallMetricSpace hcurves o hL).toPseudoMetricSpace p h) =
        closedBall (p : X) h := by
  have hdist_eq (a : ball o L) (ha : dist (a : X) (p : X) ≤ h) :
      @dist (ball o L) (intrinsicBallMetricSpace hcurves o hL).toDist a p =
        dist (a : X) (p : X) := by
    rw [intrinsicBallMetricSpace_dist,
      intrinsicEDist_eq_edist_on_inner_closedBall hcurves hh hmargin
        (show (a : X) ∈ closedBall (p : X) h from ha)
        (show (p : X) ∈ closedBall (p : X) h by
          simpa only [mem_closedBall, dist_self] using hh.le),
      edist_dist, ENNReal.toReal_ofReal dist_nonneg]
  have hLip := intrinsicBallMetricSpace_lipschitzWith_coe hcurves o hL
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    have hd := @LipschitzWith.dist_le_mul (ball o L) X
      (intrinsicBallMetricSpace hcurves o hL).toPseudoMetricSpace _ 1 _ hLip a p
    simp only [NNReal.coe_one, one_mul] at hd
    exact hd.trans ha
  · intro hy
    have hy' : dist y (p : X) ≤ h := hy
    have hmem : y ∈ ball o L := by
      have hd := dist_triangle y (p : X) o
      change dist y o < L
      linarith
    let a : ball o L := ⟨y, hmem⟩
    refine ⟨a, ?_, rfl⟩
    change @dist (ball o L) (intrinsicBallMetricSpace hcurves o hL).toDist a p ≤ h
    rw [hdist_eq a hy']
    exact hy'

end Metric

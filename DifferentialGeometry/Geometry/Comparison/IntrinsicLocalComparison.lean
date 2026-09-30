import DifferentialGeometry.Geometry.Comparison.LocalMetricComparison
import DifferentialGeometry.Topology.MetricSpace.IntrinsicBallGeometry

set_option autoImplicit false

open Set Metric Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_local_fourPointComparison_intrinsicBall_iff
    {X : Type*} [MetricSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (o : X) {L κ : ℝ} (hL : 0 < L) (p : ball o L) :
    (∃ Ω : Set (ball o L),
      @IsOpen (ball o L) (intrinsicBallMetricSpace hcurves o hL).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison (ball o L) (intrinsicBallMetricSpace hcurves o hL) κ Ω ∧ p ∈ Ω) ↔
    ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison κ Ω ∧ (p : X) ∈ Ω := by
  let m := intrinsicBallMetricSpace hcurves o hL
  apply @exists_local_fourPointComparison_iff_of_isOpenEmbedding X (ball o L) _ m κ
    (fun y => (y : X)) (intrinsicBallMetricSpace_isOpenEmbedding hcurves o hL) p
  let r := (L - dist (p : X) o) / 8
  have hp : dist (p : X) o < L := p.property
  have hr : 0 < r := by dsimp only [r]; linarith
  refine ⟨r, hr, ?_⟩
  have hLip := intrinsicBallMetricSpace_lipschitzWith_coe hcurves o hL
  have hmem (a : ball o L) (ha : a ∈ @ball (ball o L) m.toPseudoMetricSpace p r) :
      (a : X) ∈ closedBall (p : X) r := by
    have hd := @LipschitzWith.dist_le_mul (ball o L) X m.toPseudoMetricSpace _ 1 _ hLip a p
    simp only [NNReal.coe_one, one_mul] at hd
    exact (hd.trans_lt ha).le
  intro a ha b hb
  exact (intrinsicBall_dist_eq_on_inner_closedBall hcurves o hL hr
    (by dsimp only [r]; linarith : dist (p : X) o + 4 * r < L)
    (hmem a ha) (hmem b hb)).symm

end DifferentialGeometry.Geometry.Comparison.Toponogov

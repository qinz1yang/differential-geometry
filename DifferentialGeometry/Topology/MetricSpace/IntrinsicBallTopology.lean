import DifferentialGeometry.Topology.MetricSpace.IntrinsicBall
import DifferentialGeometry.Topology.MetricSpace.LocalMetricTopology

set_option autoImplicit false

open Set Metric Topology
open scoped ENNReal

namespace Metric

@[instance_reducible]
noncomputable def intrinsicBallMetricSpace
    {X : Type*} [MetricSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (o : X) {L : ℝ} (hL : 0 < L) : MetricSpace (ball o L) :=
  intrinsicMetricSpace (ball o L) (fun a b =>
    (intrinsicEDist_lt_top_on_ball_of_arbitrarily_short_curves hcurves o hL a b).ne)


theorem dist_le_intrinsicMetricSpace_dist {X : Type*} [MetricSpace X]
    (hfinite : ∀ x y : X, intrinsicEDist x y ≠ ⊤) (x y : X) :
    dist x y ≤ @dist X (intrinsicMetricSpace X hfinite).toDist x y := by
  rw [intrinsicMetricSpace_dist]
  have ht := ENNReal.toReal_mono (hfinite x y) (edist_le_intrinsicEDist x y)
  rwa [edist_dist, ENNReal.toReal_ofReal dist_nonneg] at ht

theorem intrinsicBallMetricSpace_toTopology
    {X : Type*} [MetricSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (o : X) {L : ℝ} (hL : 0 < L) :
    (intrinsicBallMetricSpace hcurves o hL).toUniformSpace.toTopologicalSpace =
      (inferInstance : MetricSpace (ball o L)).toUniformSpace.toTopologicalSpace := by
  let m0 : MetricSpace (ball o L) := inferInstance
  let hfinite : ∀ a b : ball o L, intrinsicEDist a b ≠ ⊤ := fun a b =>
    (intrinsicEDist_lt_top_on_ball_of_arbitrarily_short_curves hcurves o hL a b).ne
  let m := intrinsicMetricSpace (ball o L) hfinite
  change m.toUniformSpace.toTopologicalSpace = m0.toUniformSpace.toTopologicalSpace
  symm
  apply PseudoMetricSpace.toTopology_eq_of_locally_dist_eq
    m0.toPseudoMetricSpace m.toPseudoMetricSpace
  · intro x y
    change dist (x : X) (y : X) ≤ (intrinsicEDist x y).toReal
    have ht := ENNReal.toReal_mono (hfinite x y) (edist_le_intrinsicEDist x y)
    change (edist (x : X) (y : X)).toReal ≤ (intrinsicEDist x y).toReal at ht
    rwa [edist_dist, ENNReal.toReal_ofReal dist_nonneg] at ht
  · intro x
    let r := (L - dist (x : X) o) / 8
    have hx : dist (x : X) o < L := x.property
    have hr : 0 < r := by dsimp only [r]; linarith
    refine ⟨r, hr, fun y hy => ?_⟩
    have heq := intrinsicEDist_eq_edist_on_inner_closedBall hcurves hr
      (by dsimp only [r]; linarith : dist (x : X) o + 4 * r < L)
      (a := y) (b := x) (show (y : X) ∈ closedBall (x : X) r from hy.le)
      (by simpa only [mem_closedBall, dist_self] using hr.le)
    change (intrinsicEDist y x).toReal = dist (y : X) (x : X)
    rw [heq, edist_dist, ENNReal.toReal_ofReal dist_nonneg]

theorem intrinsicBallMetricSpace_edist
    {X : Type*} [MetricSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (o : X) {L : ℝ} (hL : 0 < L) (a b : ball o L) :
    @edist (ball o L) (intrinsicBallMetricSpace hcurves o hL).toEDist a b =
      intrinsicEDist a b := rfl

theorem intrinsicBallMetricSpace_dist
    {X : Type*} [MetricSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (o : X) {L : ℝ} (hL : 0 < L) (a b : ball o L) :
    @dist (ball o L) (intrinsicBallMetricSpace hcurves o hL).toDist a b =
      (intrinsicEDist a b).toReal := rfl

theorem intrinsicBallMetricSpace_isOpenEmbedding
    {X : Type*} [MetricSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (o : X) {L : ℝ} (hL : 0 < L) :
    @IsOpenEmbedding (ball o L) X
      (intrinsicBallMetricSpace hcurves o hL).toUniformSpace.toTopologicalSpace
      inferInstance (fun y : ball o L => (y : X)) := by
  change @IsOpenEmbedding (ball o L) X
    (intrinsicBallMetricSpace hcurves o hL).toUniformSpace.toTopologicalSpace
    _ Subtype.val
  rw [intrinsicBallMetricSpace_toTopology hcurves o hL]
  exact isOpen_ball.isOpenEmbedding_subtypeVal

theorem intrinsicBallMetricSpace_lipschitzWith_coe
    {X : Type*} [MetricSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (o : X) {L : ℝ} (hL : 0 < L) :
    @LipschitzWith (ball o L) X
      (intrinsicBallMetricSpace hcurves o hL).toPseudoEMetricSpace inferInstance
      1 (fun y : ball o L => (y : X)) := by
  have hdom (a b : ball o L) : edist (a : X) (b : X) ≤ intrinsicEDist a b :=
    edist_le_intrinsicEDist a b
  apply @LipschitzWith.of_edist_le (ball o L) X
    (intrinsicBallMetricSpace hcurves o hL).toPseudoEMetricSpace inferInstance
    (fun y : ball o L => (y : X))
  intro a b
  change edist (a : X) (b : X) ≤ intrinsicEDist a b
  exact hdom a b

end Metric

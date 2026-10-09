import DifferentialGeometry.Topology.MetricSpace.LocalHopfRinow
import DifferentialGeometry.Topology.MetricSpace.SegmentConcatenation

set_option autoImplicit false

open Set Metric

namespace Metric

theorem exists_isometric_segment_in_ball_of_recentered_complete_buffer
    {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    {o p : X} {L r : ℝ} (hr : 0 < r) (hcomplete : IsComplete (closedBall o L))
    (hbuffer : dist p o + 3 * r ≤ L)
    {a b : X} (ha : a ∈ ball p r) (hb : b ∈ ball p r) :
    ∃ σ : Icc (0 : ℝ) (dist a b) → X, Isometry σ ∧
      σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = a ∧
      σ ⟨dist a b, ⟨dist_nonneg, le_rfl⟩⟩ = b ∧
      ∀ t, σ t ∈ ball p (2 * r) := by
  obtain ⟨f, _, hf0, hf1, hball, hdist⟩ :=
    exists_metric_segment_in_ball_of_recentered_complete_buffer
      hcurves hr hcomplete hbuffer ha hb
  let a' : ball p (2 * r) := ⟨a, (ha.trans_le (by linarith) : dist a p < 2 * r)⟩
  let b' : ball p (2 * r) := ⟨b, (hb.trans_le (by linarith) : dist b p < 2 * r)⟩
  let f' : unitInterval → ball p (2 * r) := fun t => ⟨f t, hball t⟩
  have h0 : f' 0 = a' := Subtype.ext hf0
  have h1 : f' 1 = b' := Subtype.ext hf1
  obtain ⟨σ, hσ, hσ0, hσ1⟩ := exists_isometric_segment_of_dist_eq_mul h0 h1 hdist
  exact ⟨fun t => (σ t : X), isometry_subtype_coe.comp hσ,
    congrArg Subtype.val hσ0, congrArg Subtype.val hσ1, fun t => (σ t).property⟩

end Metric

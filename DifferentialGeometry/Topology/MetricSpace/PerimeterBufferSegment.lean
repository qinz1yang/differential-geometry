import DifferentialGeometry.Topology.MetricSpace.LocalHopfRinow
import DifferentialGeometry.Topology.MetricSpace.SegmentConcatenation

set_option autoImplicit false

namespace Metric

open Set

theorem exists_isometric_segment_in_closedBall_of_half_perimeter_lt
    {X : Type*} [MetricSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (p : X) {L : ℝ} [LocallyCompactSpace (ball p L)]
    (hcomplete : IsComplete (closedBall p L)) {a b : X}
    (hbuffer : (dist a p + dist b p + dist a b) / 2 < L) :
    ∃ σ : Icc (0 : ℝ) (dist a b) → X, Isometry σ ∧
      σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = a ∧
      σ ⟨dist a b, ⟨dist_nonneg, le_rfl⟩⟩ = b ∧
      ∀ t, σ t ∈ closedBall p ((dist a p + dist b p + dist a b) / 2) := by
  let C := (dist a p + dist b p + dist a b) / 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  change C < L at hbuffer
  have hL : 0 < L := lt_of_le_of_lt hC hbuffer
  let r := (C + L) / 2
  have hCr : C < r := by dsimp [r]; linarith
  have hrL : r < L := by dsimp [r]; linarith
  have hK := isCompact_closedBall_of_complete_buffer hcurves p hL hcomplete hrL
  have hshort : ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        (∀ t, c t ∈ closedBall p r) ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε) := by
    intro ε hε
    let η := min ε (r - C)
    have hη : 0 < η := lt_min hε (sub_pos.mpr hCr)
    obtain ⟨c, hc, hc0, hc1, hlen⟩ := hcurves a b η hη
    refine ⟨c, hc, hc0, hc1, ?_, hlen.trans_le ?_⟩
    · intro t
      have he := (edist_add_edist_le_eVariationOn c t).trans_lt hlen
      rw [hc0, hc1, edist_dist, edist_dist,
        ← ENNReal.ofReal_add dist_nonneg dist_nonneg] at he
      have hre := (ENNReal.ofReal_lt_ofReal_iff
        (add_pos_of_nonneg_of_pos dist_nonneg hη)).mp he
      have h1 := dist_triangle (c t) a p
      have h2 := dist_triangle (c t) b p
      rw [dist_comm (c t) a] at h1
      have hηr : η ≤ r - C := min_le_right _ _
      change dist (c t) p ≤ r
      dsimp only [C] at hηr hCr
      linarith
    · exact ENNReal.ofReal_le_ofReal (by linarith [show η ≤ ε from min_le_left _ _])
  obtain ⟨f, _hf, hf0, hf1, _hfr, hfd⟩ :=
    exists_metric_segment_of_compact_arbitrarily_short_curves hK hshort
  have hfC (t : unitInterval) : f t ∈ closedBall p C :=
    dist_center_le_of_metric_segment f hf0 hf1 hfd t
  have haC : a ∈ closedBall p C := by simpa only [hf0] using hfC 0
  have hbC : b ∈ closedBall p C := by simpa only [hf1] using hfC 1
  let f' : unitInterval → closedBall p C := fun t => ⟨f t, hfC t⟩
  let a' : closedBall p C := ⟨a, haC⟩
  let b' : closedBall p C := ⟨b, hbC⟩
  obtain ⟨σ, hσ, hσ0, hσ1⟩ := exists_isometric_segment_of_dist_eq_mul
    (x := a') (y := b') (f := f') (Subtype.ext hf0) (Subtype.ext hf1) hfd
  exact ⟨fun t => (σ t : X), isometry_subtype_coe.comp hσ,
    congrArg Subtype.val hσ0, congrArg Subtype.val hσ1, fun t => (σ t).property⟩

end Metric

import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open scoped NNReal

namespace Metric

variable {X : Type*} [PseudoMetricSpace X]

theorem exists_lipschitzWith_between_iff (K : ℝ≥0) (lower upper : X → ℝ) :
    (∃ r : X → ℝ, LipschitzWith K r ∧ lower ≤ r ∧ r ≤ upper) ↔
      ∀ p q : X, lower p - K * dist p q ≤ upper q := by
  constructor
  · rintro ⟨r, hr, hl, hu⟩ p q
    have h := hr.le_add_mul p q
    linarith [hl p, hu q]
  · intro h
    let r : X → ℝ := fun q => sSup (Set.range (fun p : X => lower p - K * dist p q))
    have hb (q : X) : BddAbove (Set.range (fun p : X => lower p - K * dist p q)) := by
      refine ⟨upper q, ?_⟩
      rintro z ⟨p, rfl⟩
      exact h p q
    have hn (q : X) : (Set.range (fun p : X => lower p - K * dist p q)).Nonempty :=
      ⟨lower q - K * dist q q, ⟨q, rfl⟩⟩
    have hl : lower ≤ r := by
      intro q
      have hq := le_csSup (hb q) (Set.mem_range_self q)
      simpa only [r, dist_self, mul_zero, sub_zero] using hq
    have hu : r ≤ upper := by
      intro q
      apply csSup_le (hn q)
      rintro z ⟨p, rfl⟩
      exact h p q
    refine ⟨r, LipschitzWith.of_le_add_mul K (fun q q' => ?_), hl, hu⟩
    apply csSup_le (hn q)
    rintro z ⟨p, rfl⟩
    have hp : lower p - K * dist p q' ≤ r q' :=
      le_csSup (hb q') (Set.mem_range_self p)
    have ht := mul_le_mul_of_nonneg_left (dist_triangle p q q') K.coe_nonneg
    rw [mul_add] at ht
    linarith

theorem exists_pos_lipschitzWith_between_iff (K : ℝ≥0) (lower upper : X → ℝ)
    (hlower : ∀ x : X, 0 < lower x) :
    (∃ r : X → ℝ, LipschitzWith K r ∧ (∀ x : X, 0 < r x) ∧
      lower ≤ r ∧ r ≤ upper) ↔
      ∀ p q : X, lower p - K * dist p q ≤ upper q := by
  constructor
  · rintro ⟨r, hr, _, hl, hu⟩
    exact (exists_lipschitzWith_between_iff K lower upper).mp ⟨r, hr, hl, hu⟩
  · intro h
    obtain ⟨r, hr, hl, hu⟩ := (exists_lipschitzWith_between_iff K lower upper).mpr h
    exact ⟨r, hr, fun x => (hlower x).trans_le (hl x), hl, hu⟩

end Metric

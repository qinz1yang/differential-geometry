import Mathlib.MeasureTheory.Measure.Basic

set_option autoImplicit false

/-!
# HG09: finite-family volume budget (CH12-O15 G2)

Blueprint `lem:hyp-finite-volume-budget` (HG09): if `k` pairwise disjoint measurable sets each
carry measure at least `v/2 > 0` and the total measure is at most `V`, then `k ≤ 2V/v`.
Used by H4 (HPI05 termination) with `μ` the normalized slice volume at one common late time.
-/

open MeasureTheory
open scoped ENNReal

namespace GC.LongTime.Ch12

/-- HG09, extended-real form: `#s · v ≤ V`. -/
theorem hg09_card_mul_le_O15 {X : Type*} [MeasurableSpace X] (μ : Measure X) {ι : Type*}
    (s : Finset ι) (A : ι → Set X) (v V : ℝ≥0∞) (hA : ∀ i ∈ s, MeasurableSet (A i))
    (hdisj : (s : Set ι).PairwiseDisjoint A) (hv : ∀ i ∈ s, v ≤ μ (A i))
    (hV : μ Set.univ ≤ V) :
    (s.card : ℝ≥0∞) * v ≤ V := by
  calc (s.card : ℝ≥0∞) * v = ∑ _i ∈ s, v := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ s, μ (A i) := Finset.sum_le_sum hv
    _ = μ (⋃ i ∈ s, A i) := (measure_biUnion_finset hdisj hA).symm
    _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)
    _ ≤ V := hV

/-- HG09, real form used by HPI05: at most `2V/v` selections. -/
theorem hg09_card_le_O15 {X : Type*} [MeasurableSpace X] (μ : Measure X) {ι : Type*}
    (s : Finset ι) (A : ι → Set X) {v V : ℝ} (hv0 : 0 < v) (hV0 : 0 ≤ V)
    (hA : ∀ i ∈ s, MeasurableSet (A i)) (hdisj : (s : Set ι).PairwiseDisjoint A)
    (hv : ∀ i ∈ s, ENNReal.ofReal (v / 2) ≤ μ (A i)) (hV : μ Set.univ ≤ ENNReal.ofReal V) :
    (s.card : ℝ) ≤ 2 * V / v := by
  have h := hg09_card_mul_le_O15 μ s A (ENNReal.ofReal (v / 2)) (ENNReal.ofReal V) hA hdisj hv hV
  have hcast : (s.card : ℝ≥0∞) = ENNReal.ofReal (s.card : ℝ) := by
    rw [ENNReal.ofReal_natCast]
  rw [hcast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_le_ofReal_iff hV0] at h
  rw [le_div_iff₀ hv0]
  nlinarith
end GC.LongTime.Ch12

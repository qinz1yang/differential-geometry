import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal

namespace MeasureTheory

variable {X ι : Type*} [MeasurableSpace X]

theorem card_le_of_disjoint_measure_comparison (μ : Measure X) (I : Finset ι)
    (U V : ι → Set X) {b : ℝ} (hb : 0 ≤ b)
    (hdisjoint : (I : Set ι).PairwiseDisjoint U)
    (hU : ∀ i ∈ I, MeasurableSet (U i))
    (hpos : ∀ i ∈ I, 0 < μ.real (U i))
    (hfinite : ∀ i ∈ I, μ (V i) ≠ ∞)
    (hcontain : ∀ i ∈ I, ∀ j ∈ I, U j ⊆ V i)
    (hcomparison : ∀ i ∈ I, μ.real (V i) ≤ b * μ.real (U i)) : (I.card : ℝ) ≤ b := by
  classical
  by_cases hI : I.Nonempty
  · obtain ⟨i, hi, hmin⟩ := Set.exists_min_image (I : Set ι) (fun j => μ.real (U j))
      I.finite_toSet (by simpa using hI)
    have hsub : (⋃ j ∈ I, U j) ⊆ V i := by
      intro x hx
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
      exact hcontain i hi j hj hxj
    have hsum : (I.card : ℝ) * μ.real (U i) ≤ μ.real (V i) := by
      calc
        _ = ∑ _j ∈ I, μ.real (U i) := by simp
        _ ≤ ∑ j ∈ I, μ.real (U j) := Finset.sum_le_sum (fun j hj => hmin j hj)
        _ = μ.real (⋃ j ∈ I, U j) := (measureReal_biUnion_finset hdisjoint hU
          (fun j hj => ne_top_of_le_ne_top (hfinite i hi) (measure_mono (hcontain i hi j hj)))).symm
        _ ≤ μ.real (V i) := measureReal_mono hsub (hfinite i hi)
    exact (mul_le_mul_iff_left₀ (hpos i hi)).mp
      (by simpa only [mul_comm] using hsum.trans (hcomparison i hi))
  · have he : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    simpa only [he, Finset.card_empty, Nat.cast_zero] using hb

end MeasureTheory

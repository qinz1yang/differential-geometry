import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Interval.Set.Infinite

set_option autoImplicit false

open Filter Set
open scoped Topology

theorem exists_tendsto_forall_notMem_of_finite_diff_Icc {E : ℕ → Set ℝ} {ζ : ℕ → ℝ}
    (hζ : Tendsto ζ atTop (𝓝 0)) (hE : ∀ n, (E n \ Icc (-(ζ n)) 0).Finite) {s : ℝ}
    (hs : s ≤ 0) :
    ∃ σ : ℕ → ℝ, Tendsto σ atTop (𝓝 s) ∧ ∀ n, σ n ≤ s ∧ σ n ∉ E n := by
  have hpick (n : ℕ) : ∃ x ∈ Ioo (min s (-ζ n) - 1 / ((n : ℝ) + 1)) (min s (-ζ n)),
      x ∉ E n \ Icc (-(ζ n)) 0 := by
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact ((Ioo_infinite (by linarith)).sdiff (hE n)).nonempty
  choose σ hσ hσE using hpick
  have hmin : Tendsto (fun n => min s (-ζ n)) atTop (𝓝 s) := by
    simpa [min_eq_left hs] using (tendsto_const_nhds (x := s)).min hζ.neg
  refine ⟨σ, ?_, fun n => ⟨(hσ n).2.le.trans (min_le_left _ _), fun hn => ?_⟩⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ hmin (fun n => (hσ n).1.le)
      (fun n => (hσ n).2.le)
    simpa using hmin.sub tendsto_one_div_add_atTop_nhds_zero_nat
  · exact hσE n ⟨hn, fun h => ((hσ n).2.trans_le (min_le_right _ _)).not_ge h.1⟩

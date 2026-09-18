import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.Complete

namespace MeasureTheory.Lp

open Filter
open scoped Topology ENNReal

variable {α K : Type*} [MeasurableSpace α] [NormedAddCommGroup K]
  {μ : Measure α} [IsFiniteMeasure μ] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem tendsto_of_ae_tendsto_of_ae_norm_le
    (hp : p ≠ ∞) (F : ℕ → Lp K p μ) (f : Lp K p μ) {C : ℝ}
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto F atTop (𝓝 f) := by
  have hui : UnifIntegrable (fun n => (F n : α → K)) p μ := by
    intro ε hε
    obtain ⟨δ, hδ, hδbound⟩ :=
      (memLp_const C : MemLp (fun _ : α => C) p μ).eLpNorm_indicator_le
        Fact.out hp hε
    refine ⟨δ, hδ, fun n s hs hμs => ?_⟩
    refine le_trans ?_ (hδbound s hs hμs)
    apply eLpNorm_mono_ae
    filter_upwards [hbound n] with x hx
    by_cases hxs : x ∈ s
    · simpa only [Set.indicator_of_mem hxs, Real.norm_eq_abs] using hx.trans (le_abs_self C)
    · simp [hxs]
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' F f).2
  exact tendsto_Lp_finite_of_tendsto_ae Fact.out hp
    (fun n => Lp.aestronglyMeasurable (F n)) (Lp.memLp f) hui hlim

end MeasureTheory.Lp

import Mathlib.Topology.MetricSpace.Pseudo.Basic
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

open Filter
open scoped Topology ENNReal

namespace MeasureTheory.Lp

variable {α E F : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  {μ : Measure α} [IsFiniteMeasure μ] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem tendsto_of_tendstoInMeasure_of_ae_norm_le
    (hp : p ≠ ∞) (f : ℕ → Lp E p μ) (f0 : Lp E p μ)
    (b : ℕ → Lp F p μ) (b0 : Lp F p μ)
    (hb : Tendsto b atTop (𝓝 b0))
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ ‖b n x‖)
    (hf : TendstoInMeasure μ (fun n => f n) atTop f0) :
    Tendsto f atTop (𝓝 f0) := by
  have hub : UnifIntegrable (fun n => (b n : α → F)) p μ :=
    unifIntegrable_of_tendsto_Lp Fact.out hp (fun n => Lp.memLp (b n))
      (Lp.memLp b0) ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' b b0).mp hb)
  have huf : UnifIntegrable (fun n => (f n : α → E)) p μ := by
    intro ε hε
    obtain ⟨δ, hδ, hsmall⟩ := hub hε
    refine ⟨δ, hδ, ?_⟩
    intro n s hs hμs
    refine le_trans ?_ (hsmall n s hs hμs)
    apply eLpNorm_mono_ae
    filter_upwards [hbound n] with x hx
    by_cases hxs : x ∈ s
    · simpa only [Set.indicator_of_mem hxs] using hx
    · simpa only [Set.indicator_of_notMem hxs] using
        (show ‖(0 : E)‖ ≤ ‖(0 : F)‖ by simp)
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' f f0).mpr
  exact tendsto_Lp_finite_of_tendstoInMeasure Fact.out hp
    (fun n => Lp.aestronglyMeasurable (f n)) (Lp.memLp f0) huf hf

end MeasureTheory.Lp

open Filter MeasureTheory
open scoped Topology ENNReal

namespace MeasureTheory.Lp

theorem tendsto_top_of_tendstoUniformlyOn
    {Ω X E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {μ : Measure Ω} {l : Filter X} {s : Set Ω}
    (hs : ∀ᵐ t ∂μ, t ∈ s)
    (f : X → Lp E ∞ μ) (f0 : Lp E ∞ μ)
    (u : X → Ω → E) (u0 : Ω → E)
    (hf : ∀ x, f x =ᵐ[μ] u x) (hf0 : f0 =ᵐ[μ] u0)
    (hu : TendstoUniformlyOn u u0 l s) :
    Tendsto f l (𝓝 f0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu (ε / 2) (half_pos hε)] with x hx
  have hbound : ∀ᵐ t ∂μ, ‖(f x - f0) t‖ ≤ ε / 2 := by
    filter_upwards [hs, hf x, hf0, Lp.coeFn_sub (f x) f0] with t ht hft hf0t hsub
    rw [hsub, Pi.sub_apply, hft, hf0t, ← dist_eq_norm_sub, dist_comm]
    exact (hx t ht).le
  have hnorm : ‖f x - f0‖ ≤ ε / 2 := by
    rw [Lp.norm_def, eLpNorm_exponent_top]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (eLpNormEssSup_le_of_ae_bound hbound)).trans_eq
        (ENNReal.toReal_ofReal (half_pos hε).le)
  rw [dist_eq_norm_sub]
  exact hnorm.trans_lt (half_lt_self hε)

end MeasureTheory.Lp

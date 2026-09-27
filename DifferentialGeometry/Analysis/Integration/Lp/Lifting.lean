import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic

open scoped ENNReal

namespace MeasureTheory

private theorem aestronglyMeasurable_of_continuous_injective
    {α E F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    [NormedAddCommGroup F] {μ : Measure α} {f : α → E} {j : E → F}
    (hj : Continuous j) (hinj : Function.Injective j)
    (hf : AEStronglyMeasurable (j ∘ f) μ) : AEStronglyMeasurable f μ := by
  borelize E F
  exact ((hj.measurableEmbedding hinj).aemeasurable_comp_iff.mp hf.aemeasurable).aestronglyMeasurable

theorem exists_lp_lift_of_ae_exists_norm_le
    {α E F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    [NormedAddCommGroup F] {μ : Measure α} {p : ℝ≥0∞}
    {j : E → F} (hj : Continuous j) (hinj : Function.Injective j)
    {g : α → F} (hg : AEStronglyMeasurable g μ)
    {b : α → ℝ} (hb : MemLp b p μ)
    (h : ∀ᵐ a ∂μ, ∃ e : E, j e = g a ∧ ‖e‖ ≤ b a) :
    ∃ v : Lp E p μ, (fun a => j (v a)) =ᵐ[μ] g ∧
      ∀ᵐ a ∂μ, ‖v a‖ ≤ b a := by
  classical
  let f : α → E := fun a =>
    if h : ∃ e : E, j e = g a ∧ ‖e‖ ≤ b a then h.choose else 0
  have hf : ∀ᵐ a ∂μ, j (f a) = g a ∧ ‖f a‖ ≤ b a := by
    filter_upwards [h] with a ha
    simpa only [f, dif_pos ha] using ha.choose_spec
  have hfg : (j ∘ f) =ᵐ[μ] g := hf.mono fun _ ha => ha.1
  have hfm : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_continuous_injective hj hinj (hg.congr hfg.symm)
  have hLp : MemLp f p μ := hb.mono' hfm (hf.mono fun _ ha => ha.2)
  refine ⟨hLp.toLp f, ?_, ?_⟩
  · filter_upwards [hLp.coeFn_toLp, hf] with a ha hfa
    exact (congrArg j ha).trans hfa.1
  · filter_upwards [hLp.coeFn_toLp, hf] with a ha hfa
    simpa only [ha] using hfa.2

end MeasureTheory

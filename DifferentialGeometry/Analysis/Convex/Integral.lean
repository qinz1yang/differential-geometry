import Mathlib.Analysis.Convex.Function
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section
open MeasureTheory

theorem convexOn_integral
    {α E : Type*} [MeasurableSpace α] [AddCommMonoid E] [Module ℝ E]
    {μ : Measure α} {s : Set E} (hs : Convex ℝ s) {f : α → E → ℝ}
    (hf : ∀ᵐ z ∂μ, ConvexOn ℝ s (f z))
    (hi : ∀ x ∈ s, Integrable (fun z => f z x) μ) :
    ConvexOn ℝ s (fun x => ∫ z, f z x ∂μ) := by
  refine ⟨hs, fun x hx y hy a b ha hb hab => ?_⟩
  calc
    _ ≤ ∫ z, a • f z x + b • f z y ∂μ := by
      apply integral_mono_ae (hi _ (hs hx hy ha hb hab))
        (((hi x hx).smul a).add ((hi y hy).smul b))
      filter_upwards [hf] with z hz
      exact hz.2 hx hy ha hb hab
    _ = _ := by
      change (∫ z, (a • (fun z => f z x)) z + (b • (fun z => f z y)) z ∂μ) = _
      rw [integral_add ((hi x hx).smul a) ((hi y hy).smul b)]
      simp only [Pi.smul_apply, integral_smul]

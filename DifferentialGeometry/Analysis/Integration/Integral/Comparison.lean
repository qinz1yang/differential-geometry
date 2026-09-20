import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace MeasureTheory

theorem setIntegral_le_of_ae_eq_on_sdiff
    {P : Type*} [MeasurableSpace P] {μ : Measure P} {s t : Set P}
    (hs : MeasurableSet s) (hst : s ⊆ t) {f g : P → ℝ}
    (hf : IntegrableOn f t μ) (hg : IntegrableOn g t μ)
    (hfg : f =ᵐ[μ.restrict (t \ s)] g)
    (hle : (∫ x in t, f x ∂μ) ≤ ∫ x in t, g x ∂μ) :
    (∫ x in s, f x ∂μ) ≤ ∫ x in s, g x ∂μ := by
  have hdiff := integral_congr_ae hfg
  rw [setIntegral_sdiff hs hf hst, setIntegral_sdiff hs hg hst] at hdiff
  linarith

end MeasureTheory

end

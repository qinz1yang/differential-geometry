import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
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

open Set MeasureTheory

namespace intervalIntegral

theorem integral_ge_of_mul_sq_le {a b C : ℝ} (hab : a ≤ b)
    {f : ℝ → ℝ} (hint : IntervalIntegrable f volume a b)
    (hlower : ∀ t ∈ Ioo a b, C * t ^ 2 ≤ f t) :
    (C / 3) * (b ^ 3 - a ^ 3) ≤ ∫ t in a..b, f t := by
  have hpoly : IntervalIntegrable (fun t : ℝ => C * t ^ 2) volume a b :=
    (by fun_prop : Continuous (fun t : ℝ => C * t ^ 2)).intervalIntegrable _ _
  have hle := integral_mono_on_of_le_Ioo hab hpoly hint hlower
  have heq : (∫ t in a..b, C * t ^ 2) = (C / 3) * (b ^ 3 - a ^ 3) := by
    rw [integral_const_mul, integral_pow]
    norm_num
    ring
  rwa [heq] at hle

end intervalIntegral

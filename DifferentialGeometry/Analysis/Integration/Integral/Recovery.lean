import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Group.Continuity

section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace MeasureTheory

variable {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem tendsto_integral_of_eq_on_core_of_integral_tendsto
    {μ : Measure X} {T : ℕ → Set X} (hT : ∀ n, MeasurableSet (T n))
    {e : X → ℝ} {en : ℕ → X → ℝ} (he : Integrable e μ)
    (hen : ∀ n, Integrable (en n) μ)
    {f : X → F} {fn : ℕ → X → F} (hf : Integrable f μ)
    (hfn : ∀ n, Integrable (fn n) μ)
    {C : ℝ} (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ C * e x)
    (hboundn : ∀ n, ∀ᵐ x ∂μ, ‖fn n x‖ ≤ C * en n x)
    (hcore : ∀ n, en n =ᵐ[μ.restrict (T n)] e)
    (hcoref : ∀ n, fn n =ᵐ[μ.restrict (T n)] f)
    (henergy : Tendsto (fun n => ∫ x, en n x ∂μ) atTop (𝓝 (∫ x, e x ∂μ)))
    (htail : Tendsto (fun n => ∫ x in (T n)ᶜ, e x ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, fn n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  have htailn : Tendsto (fun n => ∫ x in (T n)ᶜ, en n x ∂μ) atTop (𝓝 0) := by
    have heq (n : ℕ) : (∫ x in (T n)ᶜ, en n x ∂μ) =
        (∫ x, en n x ∂μ) - (∫ x, e x ∂μ) + ∫ x in (T n)ᶜ, e x ∂μ := by
      have hn := integral_add_compl (hT n) (hen n)
      have h := integral_add_compl (hT n) he
      rw [integral_congr_ae (hcore n)] at hn
      linarith
    have h := (henergy.sub_const (∫ x, e x ∂μ)).add htail
    simpa only [sub_self, zero_add, ← heq] using h
  have htailfn (n : ℕ) : ‖∫ x in (T n)ᶜ, fn n x ∂μ‖ ≤
      C * ∫ x in (T n)ᶜ, en n x ∂μ := by
    calc
      _ ≤ ∫ x in (T n)ᶜ, C * en n x ∂μ :=
        norm_integral_le_of_norm_le ((hen n).restrict.const_mul C)
          (ae_restrict_of_ae (hboundn n))
      _ = _ := integral_const_mul _ _
  have htailf (n : ℕ) : ‖∫ x in (T n)ᶜ, f x ∂μ‖ ≤
      C * ∫ x in (T n)ᶜ, e x ∂μ := by
    calc
      _ ≤ ∫ x in (T n)ᶜ, C * e x ∂μ :=
        norm_integral_le_of_norm_le (he.restrict.const_mul C) (ae_restrict_of_ae hbound)
      _ = _ := integral_const_mul _ _
  have hdiff (n : ℕ) : (∫ x, fn n x ∂μ) - ∫ x, f x ∂μ =
      (∫ x in (T n)ᶜ, fn n x ∂μ) - ∫ x in (T n)ᶜ, f x ∂μ := by
    rw [← integral_add_compl (hT n) (hfn n), ← integral_add_compl (hT n) hf,
      integral_congr_ae (hcoref n)]
    abel
  have hlim : Tendsto (fun n => (∫ x, fn n x ∂μ) - ∫ x, f x ∂μ) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_)
      (show Tendsto (fun n => C * (∫ x in (T n)ᶜ, en n x ∂μ) +
        C * ∫ x in (T n)ᶜ, e x ∂μ) atTop (𝓝 0) by
        simpa only [mul_zero, add_zero] using (htailn.const_mul C).add (htail.const_mul C))
    rw [hdiff]
    exact (norm_sub_le _ _).trans (add_le_add (htailfn n) (htailf n))
  simpa only [sub_add_cancel, zero_add] using hlim.add_const (∫ x, f x ∂μ)

end MeasureTheory

end

end

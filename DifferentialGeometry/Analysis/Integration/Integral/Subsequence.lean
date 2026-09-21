import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

section

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem ae_exists_subseq_bounded_of_integral_bound
    {f : ℕ → X → ℝ} (hf : ∀ n, Integrable (f n) μ)
    (hpos : ∀ n, 0 ≤ᵐ[μ] f n) {B : ℝ} (hB : ∀ n, (∫ x, f n x ∂μ) ≤ B) :
    ∀ᵐ x ∂μ, ∃ (σ : ℕ → ℕ) (C : ℝ), StrictMono σ ∧ ∀ n, f (σ n) x ≤ C := by
  let F : ℕ → X → ℝ≥0∞ := fun n x => ENNReal.ofReal (f n x)
  have hF (n : ℕ) : AEMeasurable (F n) μ := (hf n).aemeasurable.ennreal_ofReal
  have hbound (n : ℕ) : (∫⁻ x, F n x ∂μ) ≤ ENNReal.ofReal B := by
    rw [show (∫⁻ x, F n x ∂μ) = ENNReal.ofReal (∫ x, f n x ∂μ) from
      (ofReal_integral_eq_lintegral_ofReal (hf n) (hpos n)).symm]
    exact ENNReal.ofReal_le_ofReal (hB n)
  have hi : (∫⁻ x, liminf (fun n => F n x) atTop ∂μ) ≤ ENNReal.ofReal B :=
    (lintegral_liminf_le' hF).trans ((liminf_le_limsup).trans
      (limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall hbound)))
  have hmeas : AEMeasurable (fun x => liminf (fun n => F n x) atTop) μ := by
    simp only [liminf_eq_iSup_iInf_of_nat]
    exact AEMeasurable.iSup fun n => AEMeasurable.biInf (s := {i : ℕ | n ≤ i})
      (to_countable _) (fun i _ => hF i)
  have hfinite := ae_lt_top' hmeas (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hi)
  filter_upwards [hfinite] with x hx
  let a : ℝ≥0∞ := liminf (fun n => F n x) atTop
  have ha : a ≠ ⊤ := hx.ne
  have hlt : a < ENNReal.ofReal (a.toReal + 1) := by
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one, ENNReal.ofReal_toReal ha]
    exact ENNReal.lt_add_right ha (by simp)
  have hfreq : ∃ᶠ n in atTop, F n x < ENNReal.ofReal (a.toReal + 1) :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) hlt
  obtain ⟨σ, hσ, hσbound⟩ := extraction_of_frequently_atTop hfreq
  refine ⟨σ, a.toReal + 1, hσ, ?_⟩
  intro n
  have h := hσbound n
  exact le_of_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < a.toReal + 1)).mp h)

end MeasureTheory

end

end

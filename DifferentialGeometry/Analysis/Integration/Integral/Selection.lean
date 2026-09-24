import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

open MeasureTheory Set Filter

open scoped Topology

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

theorem exists_le_integral_sum_of_ae
    {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[μ] g) {P : X → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∃ x, P x ∧ f x ≤ (∫ y, f y ∂μ) + ∫ y, g y ∂μ ∧
      g x ≤ (∫ y, f y ∂μ) + ∫ y, g y ∂μ := by
  let N : Set X := {x | ¬ (P x ∧ 0 ≤ f x ∧ 0 ≤ g x)}
  have hN : μ N = 0 := by
    apply ae_iff.mp
    filter_upwards [hP, hf0, hg0] with x hx hf' hg'
    exact ⟨hx, hf', hg'⟩
  obtain ⟨x, hxN, hx⟩ := exists_notMem_null_le_integral (hf.add hg) hN
  have hp : P x ∧ 0 ≤ f x ∧ 0 ≤ g x := by simpa only [N, mem_ofPred_eq, not_not] using hxN
  simp only [Pi.add_apply] at hx
  rw [integral_add hf hg] at hx
  exact ⟨x, hp.1, (le_add_of_nonneg_right hp.2.2).trans hx,
    (le_add_of_nonneg_left hp.2.1).trans hx⟩

theorem exists_energy_and_scaled_error_le_integral_sum
    {e d : X → ℝ} (he : Integrable e μ) (hd : Integrable d μ)
    (he0 : 0 ≤ᵐ[μ] e) (hd0 : 0 ≤ᵐ[μ] d) {P : X → Prop} (hP : ∀ᵐ x ∂μ, P x)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ x, P x ∧ e x ≤ (∫ y, e y ∂μ) + δ⁻¹ * ∫ y, d y ∂μ ∧
      d x ≤ δ * (∫ y, e y ∂μ) + ∫ y, d y ∂μ := by
  obtain ⟨x, hx, he', hd'⟩ := exists_le_integral_sum_of_ae he (hd.const_mul δ⁻¹) he0
    (hd0.mono fun x hx => mul_nonneg (inv_nonneg.mpr hδ.le) hx) hP
  rw [integral_const_mul] at he' hd'
  refine ⟨x, hx, he', ?_⟩
  have h := mul_le_mul_of_nonneg_left hd' hδ.le
  rw [← mul_assoc, mul_inv_cancel₀ hδ.ne', one_mul] at h
  calc
    d x ≤ δ * ((∫ y, e y ∂μ) + δ⁻¹ * ∫ y, d y ∂μ) := h
    _ = _ := by rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hδ.ne', one_mul]

theorem exists_tendsto_zero_and_eventually_le_of_scaled_integral
    {e d : ℕ → X → ℝ} (he : ∀ n, Integrable (e n) μ) (hd : ∀ n, Integrable (d n) μ)
    (he0 : ∀ n, 0 ≤ᵐ[μ] e n) (hd0 : ∀ n, 0 ≤ᵐ[μ] d n)
    {P : ℕ → X → Prop} (hP : ∀ n, ∀ᵐ x ∂μ, P n x)
    {B : ℝ} (hB : ∀ n, (∫ y, e n y ∂μ) ≤ B)
    {δ : ℕ → ℝ} (hδ : ∀ n, 0 < δ n) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hscaled : Tendsto (fun n => (δ n)⁻¹ * ∫ y, d n y ∂μ) atTop (𝓝 0)) :
    ∃ x : ℕ → X, (∀ n, P n (x n)) ∧
      Tendsto (fun n => d n (x n)) atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, e n (x n) ≤ B + 1 := by
  classical
  have hselect (n : ℕ) := exists_energy_and_scaled_error_le_integral_sum (he n) (hd n)
    (he0 n) (hd0 n) ((hP n).and (hd0 n)) (hδ n)
  choose x hx hxe hxd using hselect
  refine ⟨x, fun n => (hx n).1, ?_, ?_⟩
  · have hD : Tendsto (fun n => ∫ y, d n y ∂μ) atTop (𝓝 0) := by
      have h := hδ0.mul hscaled
      simpa only [← mul_assoc, mul_inv_cancel₀ (hδ _).ne', one_mul, mul_zero] using h
    have hupper : Tendsto (fun n => δ n * B + ∫ y, d n y ∂μ) atTop (𝓝 0) := by
      simpa only [zero_mul, zero_add] using (hδ0.mul_const B).add hD
    exact squeeze_zero (fun n => (hx n).2)
      (fun n => (hxd n).trans (add_le_add (mul_le_mul_of_nonneg_left (hB n)
        (hδ n).le) le_rfl)) hupper
  · filter_upwards [hscaled.eventually_le_const (show (0 : ℝ) < 1 by norm_num)] with n hn
    exact (hxe n).trans (add_le_add (hB n) hn)

theorem exists_tendsto_zero_and_eventually_le_of_integral
    {e d : ℕ → X → ℝ} (he : ∀ n, Integrable (e n) μ) (hd : ∀ n, Integrable (d n) μ)
    (he0 : ∀ n, 0 ≤ᵐ[μ] e n) (hd0 : ∀ n, 0 ≤ᵐ[μ] d n)
    {P : ℕ → X → Prop} (hP : ∀ n, ∀ᵐ x ∂μ, P n x)
    {B : ℝ} (hB : ∀ n, (∫ y, e n y ∂μ) ≤ B)
    (hD : Tendsto (fun n => ∫ y, d n y ∂μ) atTop (𝓝 0)) :
    ∃ x : ℕ → X, (∀ n, P n (x n)) ∧
      Tendsto (fun n => d n (x n)) atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, e n (x n) ≤ B + 1 := by
  let δ : ℕ → ℝ := fun n => Real.sqrt (∫ y, d n y ∂μ) + 1 / ((n : ℝ) + 1)
  have hδ (n : ℕ) : 0 < δ n := by
    exact add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (by positivity)
  have hδ0 : Tendsto δ atTop (𝓝 0) := by
    simpa only [δ, Real.sqrt_zero, zero_add] using
      hD.sqrt.add (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
  apply exists_tendsto_zero_and_eventually_le_of_scaled_integral he hd he0 hd0 hP hB hδ hδ0
  have hn (n : ℕ) : 0 ≤ ∫ y, d n y ∂μ := integral_nonneg_of_ae (hd0 n)
  apply squeeze_zero (fun n => mul_nonneg (inv_nonneg.mpr (hδ n).le) (hn n))
    (fun n => ?_) (by simpa only [Real.sqrt_zero] using hD.sqrt)
  rw [inv_mul_le_iff₀ (hδ n)]
  dsimp [δ]
  rw [add_mul, Real.mul_self_sqrt (hn n)]
  exact le_add_of_nonneg_right (by positivity)

end MeasureTheory

end

noncomputable section

open MeasureTheory Set Filter

open scoped Topology

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem exists_tendsto_zero_and_eventually_le_of_finite_integral
    [IsFiniteMeasure μ] [NeZero μ]
    {e d : ℕ → X → ℝ} (he : ∀ n, Integrable (e n) μ) (hd : ∀ n, Integrable (d n) μ)
    (he0 : ∀ n, 0 ≤ᵐ[μ] e n) (hd0 : ∀ n, 0 ≤ᵐ[μ] d n)
    {P : ℕ → X → Prop} (hP : ∀ n, ∀ᵐ x ∂μ, P n x)
    {B : ℝ} (hB : ∀ n, (∫ y, e n y ∂μ) ≤ B)
    (hD : Tendsto (fun n => ∫ y, d n y ∂μ) atTop (𝓝 0)) :
    ∃ x : ℕ → X, (∀ n, P n (x n)) ∧
      Tendsto (fun n => d n (x n)) atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, e n (x n) ≤ (μ.real univ)⁻¹ * B + 1 := by
  let ν : Measure X := (μ univ)⁻¹ • μ
  have hE (n : ℕ) : (∫ y, e n y ∂ν) ≤ (μ.real univ)⁻¹ * B := by
    change (⨍ y, e n y ∂μ) ≤ _
    rw [average_eq, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (hB n) (inv_nonneg.mpr (measureReal_nonneg))
  have hD' : Tendsto (fun n => ∫ y, d n y ∂ν) atTop (𝓝 0) := by
    change Tendsto (fun n => ⨍ y, d n y ∂μ) atTop (𝓝 0)
    simp_rw [average_eq, smul_eq_mul]
    simpa only [mul_zero] using hD.const_mul (μ.real univ)⁻¹
  exact exists_tendsto_zero_and_eventually_le_of_integral
    (fun n => (he n).to_average) (fun n => (hd n).to_average)
    (fun n => Measure.ae_smul_measure (he0 n) _) (fun n => Measure.ae_smul_measure (hd0 n) _)
    (fun n => Measure.ae_smul_measure (hP n) _) hE hD'

end MeasureTheory

end

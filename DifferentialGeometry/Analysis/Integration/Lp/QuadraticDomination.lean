import DifferentialGeometry.Analysis.Integration.Lp.Bilinear

noncomputable section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace MeasureTheory

variable {P X : Type*} [MeasurableSpace P] {μ : Measure P}
  [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem norm_integral_quadratic_le_integral_norm_sq
    (A : P → X →L[ℝ] X →L[ℝ] ℝ)
    (hA : ∀ v w, AEStronglyMeasurable (fun x => A x v w) μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖A x‖ ≤ C)
    {f : P → X} (hf : MemLp f 2 μ) :
    ‖∫ x, A x (f x) (f x) ∂μ‖ ≤ C * ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have hi := integrable_bilinear_of_apply_aestronglyMeasurable A hA hC hf hf
  have hs := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  calc
    _ ≤ ∫ x, ‖A x (f x) (f x)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, C * ‖f x‖ ^ 2 ∂μ := by
      apply integral_mono_ae hi.norm (hs.const_mul C)
      filter_upwards [hC] with x hx
      calc
        ‖A x (f x) (f x)‖ ≤ ‖A x‖ * ‖f x‖ * ‖f x‖ := (A x).le_opNorm₂ _ _
        _ ≤ C * ‖f x‖ * ‖f x‖ := by gcongr
        _ = C * ‖f x‖ ^ 2 := by ring
    _ = _ := integral_const_mul _ _

theorem norm_integral_quadratic_add_div_two_le
    (A : P → X →L[ℝ] X →L[ℝ] ℝ)
    (hA : ∀ v w, AEStronglyMeasurable (fun x => A x v w) μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖A x‖ ≤ C)
    {a b : P → X} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    ‖∫ x, (A x (a x) (a x) + A x (b x) (b x)) / 2 ∂μ‖ ≤
      C * ∫ x, (‖a x‖ ^ 2 + ‖b x‖ ^ 2) / 2 ∂μ := by
  have hia := integrable_bilinear_of_apply_aestronglyMeasurable A hA hC ha ha
  have hib := integrable_bilinear_of_apply_aestronglyMeasurable A hA hC hb hb
  have hsa := (memLp_two_iff_integrable_sq_norm ha.aestronglyMeasurable).mp ha
  have hsb := (memLp_two_iff_integrable_sq_norm hb.aestronglyMeasurable).mp hb
  rw [integral_div, integral_add hia hib, norm_div,
    Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), integral_div, integral_add hsa hsb]
  calc
    _ ≤ (‖∫ x, A x (a x) (a x) ∂μ‖ + ‖∫ x, A x (b x) (b x) ∂μ‖) / 2 := by
      gcongr
      exact norm_add_le _ _
    _ ≤ ((C * ∫ x, ‖a x‖ ^ 2 ∂μ) + C * ∫ x, ‖b x‖ ^ 2 ∂μ) / 2 := by
      gcongr
      · exact norm_integral_quadratic_le_integral_norm_sq A hA hC ha
      · exact norm_integral_quadratic_le_integral_norm_sq A hA hC hb
    _ = _ := by ring

theorem tendsto_integral_quadratic_add_div_two_of_tendsto_integral_norm_sq
    (μn : ℕ → Measure P) (A : ℕ → P → X →L[ℝ] X →L[ℝ] ℝ)
    (hA : ∀ n v w, AEStronglyMeasurable (fun x => A n x v w) (μn n))
    {C : ℝ} (hC : ∀ n, ∀ᵐ x ∂μn n, ‖A n x‖ ≤ C)
    (a b : ℕ → P → X)
    (ha : ∀ n, MemLp (a n) 2 (μn n)) (hb : ∀ n, MemLp (b n) 2 (μn n))
    (hlim : Tendsto (fun n => ∫ x, (‖a n x‖ ^ 2 + ‖b n x‖ ^ 2) / 2 ∂μn n)
      atTop (𝓝 0)) :
    Tendsto
      (fun n => ∫ x, (A n x (a n x) (a n x) + A n x (b n x) (b n x)) / 2 ∂μn n)
      atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n =>
    norm_integral_quadratic_add_div_two_le (A n) (hA n) (hC n) (ha n) (hb n))
  simpa only [mul_zero] using hlim.const_mul C

end MeasureTheory

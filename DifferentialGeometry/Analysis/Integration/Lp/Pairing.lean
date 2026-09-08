import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem continuous_integral_weight_mul_lp (c : α → ℝ) (hc : MemLp c ∞ μ)
    (f : Lp ℝ 2 μ) :
    Continuous (fun g : Lp ℝ 2 μ => ∫ z, f z * c z * g z ∂μ) := by
  have hfc : MemLp (fun z => f z * c z) 2 μ := by
    simpa only [mul_comm] using (Lp.memLp f).mul' hc
  let fc : Lp ℝ 2 μ := hfc.toLp (fun z => f z * c z)
  have heq : (fun g : Lp ℝ 2 μ => ∫ z, f z * c z * g z ∂μ) =
      (fun g : Lp ℝ 2 μ => inner ℝ fc g) := by
    funext g
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hfc.coeFn_toLp] with z hz
    simp only [Real.inner_apply, fc, hz]
  rw [heq]
  exact continuous_const.inner continuous_id

theorem integrable_weight_mul_lp (c : α → ℝ) (hc : MemLp c ∞ μ)
    (f g : Lp ℝ 2 μ) :
    Integrable (fun z => f z * c z * g z) μ := by
  have hfc : MemLp (fun z => f z * c z) 2 μ := by
    simpa only [mul_comm] using (Lp.memLp f).mul' hc
  exact hfc.integrable_mul (Lp.memLp g)

end MeasureTheory

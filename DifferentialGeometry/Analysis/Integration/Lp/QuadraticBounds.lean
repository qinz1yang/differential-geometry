import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.MeasureTheory.Function.L1Space.Integrable

section

open MeasureTheory
open scoped BigOperators ENNReal

namespace MeasureTheory

variable {α ι F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
  {μ : Measure α}

theorem integrable_finset_sum_norm_sq
    (s : Finset ι) {v : ι → α → F} (hv : ∀ j ∈ s, MemLp (v j) 2 μ) (C : ℝ) :
    Integrable (fun x => C * ∑ j ∈ s, ‖v j x‖ ^ 2) μ := by
  refine (integrable_finsetSum s fun j hj => ?_).const_mul C
  exact (hv j hj).integrable_norm_pow (by decide)

theorem integrable_finset_sum_quadratic_bound
    (s : Finset ι) {v w : ι → α → F}
    (hv : ∀ j ∈ s, MemLp (v j) 2 μ) (hw : ∀ j ∈ s, MemLp (w j) 2 μ)
    (C P : ℝ) :
    Integrable (fun x => C * ∑ j ∈ s,
      (P * (‖v j x‖ + ‖w j x‖) ^ 2 + 2 * ‖w j x‖ * (‖v j x‖ + ‖w j x‖))) μ := by
  refine (integrable_finsetSum s fun j hj => ?_).const_mul C
  have hsum : MemLp (fun x => ‖v j x‖ + ‖w j x‖) 2 μ :=
    (hv j hj).norm.add (hw j hj).norm
  have hsq : Integrable (fun x => (‖v j x‖ + ‖w j x‖) ^ 2) μ := by
    have hmul' := hsum.integrable_mul hsum
    convert hmul' using 1
    ext x
    simp only [Pi.mul_apply, pow_two]
  have hmul : Integrable (fun x => ‖w j x‖ * (‖v j x‖ + ‖w j x‖)) μ :=
    (hw j hj).norm.integrable_mul hsum
  have hadd := (hsq.const_mul P).add (hmul.const_mul 2)
  convert hadd using 1
  ext x
  simp only [Pi.add_apply, mul_assoc]

theorem integrable_sum_norm_sq
    [Fintype ι] {v : ι → α → F} (hv : ∀ j, MemLp (v j) 2 μ) (C : ℝ) :
    Integrable (fun x => C * ∑ j, ‖v j x‖ ^ 2) μ :=
  integrable_finset_sum_norm_sq Finset.univ (fun j _ => hv j) C

theorem integrable_sum_quadratic_bound
    [Fintype ι] {v w : ι → α → F}
    (hv : ∀ j, MemLp (v j) 2 μ) (hw : ∀ j, MemLp (w j) 2 μ) (C P : ℝ) :
    Integrable (fun x => C * ∑ j,
      (P * (‖v j x‖ + ‖w j x‖) ^ 2 + 2 * ‖w j x‖ * (‖v j x‖ + ‖w j x‖))) μ :=
  integrable_finset_sum_quadratic_bound Finset.univ (fun j _ => hv j) (fun j _ => hw j) C P

end MeasureTheory

end

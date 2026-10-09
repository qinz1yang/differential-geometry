import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open scoped BigOperators
namespace ContinuousLinearMap

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]

theorem norm_le_sqrt_sum_block_bounds (T : E →L[ℝ] PiLp 2 F) (b : ι → ℝ)
    (hT : ∀ x i, ‖T x i‖ ≤ b i * ‖x‖) :
    ‖T‖ ≤ Real.sqrt (∑ i, b i ^ 2) := by
  have hs : 0 ≤ ∑ i, b i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  apply T.opNorm_le_bound (Real.sqrt_nonneg _)
  intro x
  have hsum : ‖T x‖ ^ 2 ≤ (∑ i, b i ^ 2) * ‖x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have h := hT x i
    nlinarith [norm_nonneg (T x i)]
  have hroot := Real.sq_sqrt hs
  have hp := mul_nonneg (Real.sqrt_nonneg (∑ i, b i ^ 2)) (norm_nonneg x)
  nlinarith [sq_nonneg (Real.sqrt (∑ i, b i ^ 2) * ‖x‖ - ‖T x‖), norm_nonneg (T x)]

theorem norm_le_sqrt_active_blocks (T : E →L[ℝ] PiLp 2 F) (s : Finset ι)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x i, i ∈ s → ‖T x i‖ ≤ B * ‖x‖)
    (hzero : ∀ x i, i ∉ s → T x i = 0) :
    ‖T‖ ≤ Real.sqrt (s.card : ℝ) * B := by
  classical
  have h := T.norm_le_sqrt_sum_block_bounds (fun i => if i ∈ s then B else 0)
    (by
      intro x i
      by_cases hi : i ∈ s
      · simpa only [ite_eq_left hi] using hbound x i hi
      · simp only [ite_eq_right hi, hzero x i hi, norm_zero, zero_mul, le_refl])
  have heq : (∑ i, (if i ∈ s then B else 0) ^ 2) = (s.card : ℝ) * B ^ 2 := by
    simp only [ite_pow, zero_pow (by decide : 2 ≠ 0)]
    rw [Finset.sum_ite_mem]
    simp
  rw [heq, Real.sqrt_mul (by positivity), Real.sqrt_sq hB] at h
  exact h

end ContinuousLinearMap

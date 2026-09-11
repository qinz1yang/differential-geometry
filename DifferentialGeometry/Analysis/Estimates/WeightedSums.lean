import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Operations

noncomputable section

open scoped ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Estimates

theorem sum_le_of_le_ofReal_mul
    {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) (C : ι → ℝ) (A : ℝ≥0∞)
    (hC : ∀ j ∈ s, 0 ≤ C j)
    (hbd : ∀ j ∈ s, f j ≤ ENNReal.ofReal (C j) * A) :
    ∑ j ∈ s, f j ≤ ENNReal.ofReal (∑ j ∈ s, C j) * A := by
  classical
  calc ∑ j ∈ s, f j
      ≤ ∑ j ∈ s, ENNReal.ofReal (C j) * A := Finset.sum_le_sum hbd
    _ = (∑ j ∈ s, ENNReal.ofReal (C j)) * A := by rw [Finset.sum_mul]
    _ = ENNReal.ofReal (∑ j ∈ s, C j) * A := by
        rw [ENNReal.ofReal_sum_of_nonneg hC]

theorem weight_sum_bound
    {A : Type*} [Fintype A] (K : A → ℝ) (hK : ∀ a, 0 ≤ K a)
    (v : A → ℝ≥0∞) :
    (∑ a, ENNReal.ofReal (K a) * v a) ≤
      ENNReal.ofReal (∑ a, K a) * ∑ a, v a := by
  calc
    (∑ a, ENNReal.ofReal (K a) * v a) ≤
        ∑ a, ENNReal.ofReal (∑ b, K b) * v a := by
      refine Finset.sum_le_sum ?_
      intro a ha
      simpa only [mul_comm] using mul_le_mul_right
        (ENNReal.ofReal_le_ofReal
          (Finset.single_le_sum (fun b _ => hK b) ha)) (v a)
    _ = ENNReal.ofReal (∑ b, K b) * ∑ a, v a := by
      rw [Finset.mul_sum]

theorem weight_sum_pos
    {A : Type*} [Fintype A] [Nonempty A] (K : A → ℝ)
    (hK : ∀ a, 0 < K a) :
    0 < ∑ a, K a := by
  classical
  let a : A := Classical.choice inferInstance
  exact Finset.sum_pos' (fun b _ => (hK b).le)
    ⟨a, Finset.mem_univ a, hK a⟩

end Estimates

namespace Sobolev
namespace Tensor

alias weight_sum_bound := Estimates.weight_sum_bound
alias weight_sum_pos := Estimates.weight_sum_pos

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry

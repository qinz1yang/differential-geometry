import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.ENNReal.Operations

/-!
# Finite weighted bounds for fine tensor arrays

This is the elementary finite-sum step used to turn coordinatewise Sobolev
reassembly estimates into one operator bound.
-/

noncomputable section

open scoped ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Tensor

/-- A finite family of nonnegative real weights is dominated by its sum in
an `ENNReal`-weighted finite sum. -/
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
      exact mul_le_mul_of_nonneg_right
        (ENNReal.ofReal_le_ofReal
          (Finset.single_le_sum (fun b _ => hK b) ha)) (zero_le _)
    _ = ENNReal.ofReal (∑ b, K b) * ∑ a, v a := by
      rw [Finset.mul_sum]

/-- The sum of a nonempty finite family of strictly positive weights is
strictly positive. -/
theorem weight_sum_pos
    {A : Type*} [Fintype A] [Nonempty A] (K : A → ℝ)
    (hK : ∀ a, 0 < K a) :
    0 < ∑ a, K a := by
  classical
  let a : A := Classical.choice inferInstance
  exact Finset.sum_pos' (fun b _ => (hK b).le)
    ⟨a, Finset.mem_univ a, hK a⟩

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry

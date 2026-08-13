import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator

namespace DifferentialGeometry
namespace Analysis

variable {n : Type*} [DecidableEq n]

omit [DecidableEq n] in
theorem hasDerivAt_matrix
    [Finite n]
    (A : ℝ → Matrix n n ℝ) (A' : Matrix n n ℝ) (t : ℝ)
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t) :
    HasDerivAt A A' t := by
  letI : Fintype n := Fintype.ofFinite n
  exact hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => hA i j

variable [Fintype n]

omit [DecidableEq n] in
theorem hasDerivAt_trace
    (A : ℝ → Matrix n n ℝ) (A' : Matrix n n ℝ) (t : ℝ)
    (hA : HasDerivAt A A' t) :
    HasDerivAt (fun s => trace (A s)) (trace A') t := by
  simpa only [trace, Matrix.diag_apply] using
    (HasDerivAt.fun_sum fun i (_ : i ∈ Finset.univ) =>
      hasDerivAt_pi.mp (hasDerivAt_pi.mp hA i) i)

theorem hasDerivAt_inv_mul
    (G B : ℝ → Matrix n n ℝ) (G' B' : Matrix n n ℝ) (t : ℝ)
    (hG : HasDerivAt G G' t) (hB : HasDerivAt B B' t)
    (hunit : IsUnit (G t)) :
    HasDerivAt (fun s => (G s)⁻¹ * B s)
      (-((G t)⁻¹ * G' * (G t)⁻¹) * B t + (G t)⁻¹ * B') t := by
  obtain ⟨u, hu⟩ := hunit
  have hinvF :
      HasFDerivAt (Ring.inverse : Matrix n n ℝ → Matrix n n ℝ)
        (-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℝ)
          (↑u⁻¹ : Matrix n n ℝ) (↑u⁻¹ : Matrix n n ℝ)) (G t) := by
    rw [← hu]
    exact hasFDerivAt_ringInverse u
  have hinv :
      HasDerivAt (fun s => Ring.inverse (G s))
        (-((G t)⁻¹ * G' * (G t)⁻¹)) t := by
    simpa [Function.comp_def, hu, ContinuousLinearMap.mulLeftRight_apply,
      Matrix.nonsing_inv_eq_ringInverse] using hinvF.comp_hasDerivAt t hG
  simpa [Matrix.nonsing_inv_eq_ringInverse, Matrix.mul_assoc] using hinv.mul hB

theorem trace_inv_mul_conj
    (G A : Matrix n n ℝ) (hdet : IsUnit G.det) :
    trace (G⁻¹ * (A * G)) = trace A := by
  rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle,
    Matrix.mul_nonsing_inv G hdet, Matrix.one_mul]

theorem trace_sq_le_mul
    (A : Matrix n n ℝ) (hA : A.IsSymm) :
    (trace A) ^ 2 ≤ (Fintype.card n : ℝ) * trace (A ^ 2) := by
  have hdiag :
      (∑ i : n, A i i) ^ 2 ≤
        (Fintype.card n : ℝ) * ∑ i : n, (A i i) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (α := ℝ)
      (s := (Finset.univ : Finset n)) (f := fun i => A i i)
    simpa [Finset.card_univ] using h
  have hrow (i : n) : (A i i) ^ 2 ≤ ∑ j : n, (A i j) ^ 2 := by
    exact Finset.single_le_sum (fun j _ => sq_nonneg (A i j)) (Finset.mem_univ i)
  have hsum : ∑ i : n, (A i i) ^ 2 ≤ ∑ i : n, ∑ j : n, (A i j) ^ 2 :=
    Finset.sum_le_sum fun i _ => hrow i
  have hcard : (0 : ℝ) ≤ Fintype.card n := by positivity
  have htraceSq : trace (A ^ 2) = ∑ i : n, ∑ j : n, (A i j) ^ 2 := by
    simp only [trace, Matrix.diag_apply, pow_two, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hA.apply i j]
  rw [trace, htraceSq]
  exact hdiag.trans (mul_le_mul_of_nonneg_left hsum hcard)

theorem hasDerivAt_riccati
    (G M : ℝ → Matrix n n ℝ) (Q : Matrix n n ℝ) (t : ℝ)
    (hG : HasDerivAt G ((2 : ℝ) • M t) t)
    (hM : HasDerivAt M (Q + M t * (G t)⁻¹ * M t) t)
    (hunit : IsUnit (G t)) :
    HasDerivAt (fun s => trace ((G s)⁻¹ * M s))
      (trace ((G t)⁻¹ * Q) - trace (((G t)⁻¹ * M t) ^ 2)) t := by
  have hprod := hasDerivAt_inv_mul G M ((2 : ℝ) • M t)
    (Q + M t * (G t)⁻¹ * M t) t hG hM hunit
  refine (hasDerivAt_trace _ _ t hprod).congr_deriv ?_
  simp only [Matrix.mul_smul, Matrix.trace_add, Matrix.mul_add, pow_two,
    smul_mul_assoc, neg_mul, Matrix.trace_neg, Matrix.trace_smul]
  simp only [Matrix.mul_assoc]
  simp only [smul_eq_mul]
  ring

end Analysis
end DifferentialGeometry

end

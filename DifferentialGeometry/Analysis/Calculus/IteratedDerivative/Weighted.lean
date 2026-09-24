import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

open Filter
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis

noncomputable def weightedDeriv (w f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => w x * deriv f x

private theorem exists_iteratedDeriv_mul_bound {α : Type*} (n : ℕ)
    (x : α → ℝ) (v q : α → ℝ → ℝ)
    (hv : ∀ a, ContDiffAt ℝ n (v a) (x a))
    (hq : ∀ a, ContDiffAt ℝ n (q a) (x a))
    (hvb : ∀ i ≤ n, ∃ C : ℝ, 0 ≤ C ∧ ∀ a, ‖iteratedDeriv i (v a) (x a)‖ ≤ C)
    (hqb : ∀ i ≤ n, ∃ C : ℝ, 0 ≤ C ∧ ∀ a, ‖iteratedDeriv i (q a) (x a)‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a, ‖iteratedDeriv n (fun y => v a y * q a y) (x a)‖ ≤ C := by
  classical
  have hA (i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
      (i ≤ n → ∀ a, ‖iteratedDeriv i (v a) (x a)‖ ≤ C) := by
    by_cases hi : i ≤ n
    · obtain ⟨C, hC, hbound⟩ := hvb i hi
      exact ⟨C, hC, fun _ => hbound⟩
    · exact ⟨0, le_rfl, fun h => (hi h).elim⟩
  have hB (i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
      (i ≤ n → ∀ a, ‖iteratedDeriv i (q a) (x a)‖ ≤ C) := by
    by_cases hi : i ≤ n
    · obtain ⟨C, hC, hbound⟩ := hqb i hi
      exact ⟨C, hC, fun _ => hbound⟩
    · exact ⟨0, le_rfl, fun h => (hi h).elim⟩
  choose A hA hAv using hA
  choose B hB hBq using hB
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A i * B (n - i), ?_, ?_⟩
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB _)
  · intro a
    rw [iteratedDeriv_fun_mul (hv a) (hq a)]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [norm_mul, norm_mul, Real.norm_natCast]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hAv i (by simpa using hi) a)
      (Nat.cast_nonneg _)) (hBq (n - i) (Nat.sub_le _ _) a)
      (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hA i))

theorem contDiffAt_weightedDeriv {w f : ℝ → ℝ} {x : ℝ} {n : ℕ∞ω}
    (hw : ContDiffAt ℝ n w x) (hf : ContDiffAt ℝ (n + 1) f x) :
    ContDiffAt ℝ n (weightedDeriv w f) x :=
  hw.mul (hf.derivWithin le_rfl)

theorem exists_iteratedDeriv_bound_of_weightedDeriv {α : Type*} (n : ℕ)
    (x : α → ℝ) (v q : α → ℝ → ℝ)
    (hv : ∀ a, ContDiffAt ℝ ((n - 1 : ℕ) : ℕ∞ω) (v a) (x a))
    (hq : ∀ a, ContDiffAt ℝ n (q a) (x a))
    (hvn : ∀ a, v a (x a) ≠ 0)
    (hvb : ∀ i < n, ∃ C : ℝ, 0 ≤ C ∧ ∀ a, ‖iteratedDeriv i (v a) (x a)‖ ≤ C)
    (hqb : ∀ k ≤ n, ∃ C : ℝ, 0 ≤ C ∧ ∀ a,
      ‖((weightedDeriv (fun y => (v a y)⁻¹))^[k] (q a)) (x a)‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a, ‖iteratedDeriv n (q a) (x a)‖ ≤ C := by
  induction n using Nat.strong_induction_on generalizing q with
  | h n ih =>
    cases n with
    | zero => simpa using hqb 0 le_rfl
    | succ n =>
      let r : α → ℝ → ℝ := fun a => weightedDeriv (fun y => (v a y)⁻¹) (q a)
      have hvr (a : α) : ContDiffAt ℝ n (v a) (x a) := by simpa using hv a
      have hr (a : α) : ContDiffAt ℝ n (r a) (x a) :=
        contDiffAt_weightedDeriv ((hvr a).inv (hvn a)) (by simpa using hq a)
      have hrb (j : ℕ) (hj : j ≤ n) :
          ∃ C : ℝ, 0 ≤ C ∧ ∀ a, ‖iteratedDeriv j (r a) (x a)‖ ≤ C := by
        apply ih j (by omega) r
          (fun a => (hv a).of_le (by exact_mod_cast (show j - 1 ≤ n + 1 - 1 by omega)))
          (fun a => (hr a).of_le (by exact_mod_cast hj))
        · intro i hi
          exact hvb i (by omega)
        · intro k hk
          simpa only [r, ← Function.iterate_succ_apply] using hqb (k + 1) (by omega)
      obtain ⟨C, hC, hbound⟩ := exists_iteratedDeriv_mul_bound n x v r
        (fun a => by simpa using hv a) hr
        (fun i hi => hvb i (by omega)) hrb
      refine ⟨C, hC, fun a => ?_⟩
      have heq : deriv (q a) =ᶠ[𝓝 (x a)] (fun y => v a y * r a y) := by
        filter_upwards [(hv a).continuousAt.eventually_ne (hvn a)] with y hy
        simp only [r, weightedDeriv]
        rw [← mul_assoc, mul_inv_cancel₀ hy, one_mul]
      rw [iteratedDeriv_succ', heq.iteratedDeriv_eq n]
      exact hbound a

end DifferentialGeometry.Analysis

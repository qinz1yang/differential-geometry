import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.InterpolationStep_O26
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# CH12-O26 L2b: the interpolation step for iterated derivatives

`‖D^{j+1} u (x)‖ ≤ 2 sup_{B̄(x,t)} ‖D^j u‖ / t + t sup_{B̄(x,t)} ‖D^{j+2} u‖` for `u` smooth on an
open set containing `closedBall x t`.  Iterating over `j` gives "small `C⁰` + bounded `C^{k+1}`
⇒ small `C^k`" for the chart displacement of the single-model core `L1` (`[FROZEN] CH12-O26`).
-/

set_option autoImplicit false

open Metric Set
open scoped ContDiff

namespace GC.LongTime.Ch12

/-- **Interpolation step for `iteratedFDeriv`.** -/
theorem norm_iteratedFDeriv_succ_le_interp_O26 {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {u : E → F} {s : Set E}
    (hs : IsOpen s) (hu : ContDiffOn ℝ ∞ u s) {x : E} {t S M : ℝ} (ht : 0 < t)
    (hball : closedBall x t ⊆ s) (j : ℕ)
    (hS : ∀ y ∈ closedBall x t, ‖iteratedFDeriv ℝ j u y‖ ≤ S)
    (hM : ∀ y ∈ closedBall x t, ‖iteratedFDeriv ℝ (j + 2) u y‖ ≤ M) :
    ‖iteratedFDeriv ℝ (j + 1) u x‖ ≤ 2 * S / t + t * M := by
  have hd : ∀ (i : ℕ), ∀ y ∈ closedBall x t, DifferentiableAt ℝ (iteratedFDeriv ℝ i u) y :=
    fun i y hy => (hu.contDiffAt (hs.mem_nhds (hball hy))).differentiableAt_iteratedFDeriv
      (by exact_mod_cast ENat.natCast_lt_top i)
  have hfd : fderiv ℝ (iteratedFDeriv ℝ j u) =
      continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F ∘
        iteratedFDeriv ℝ (j + 1) u := fderiv_iteratedFDeriv
  have hdd : ∀ y ∈ closedBall x t,
      DifferentiableAt ℝ (fderiv ℝ (iteratedFDeriv ℝ j u)) y := fun y hy => by
    rw [hfd]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F).differentiable.differentiableAt.comp
      y (hd (j + 1) y hy)
  have hnorm : ∀ y, ‖fderiv ℝ (fderiv ℝ (iteratedFDeriv ℝ j u)) y‖ =
      ‖iteratedFDeriv ℝ (j + 2) u y‖ := fun y => by
    rw [hfd, LinearIsometryEquiv.comp_fderiv, ← norm_fderiv_iteratedFDeriv]
    exact LinearIsometry.norm_toContinuousLinearMap_comp
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F).toLinearIsometry
  have key := norm_fderiv_le_interp_O26 (g := iteratedFDeriv ℝ j u)
    (g' := fderiv ℝ (iteratedFDeriv ℝ j u))
    (g'' := fderiv ℝ (fderiv ℝ (iteratedFDeriv ℝ j u))) ht
    (fun y hy => (hd j y hy).hasFDerivAt.hasFDerivWithinAt)
    (fun y hy => (hdd y hy).hasFDerivAt.hasFDerivWithinAt) hS
    (fun y hy => (hnorm y).le.trans (hM y hy))
  rwa [norm_fderiv_iteratedFDeriv] at key

/-- **L3: small `C⁰` + bounded `C^{k+1}` ⇒ small `C^k`** (uniform: `η` depends only on
`k, c, B, j, ε`).  At a point `y` with `closedBall y (j * c) ⊆ s`. -/
theorem small_iteratedFDeriv_of_C0_O26 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ) {c B : ℝ} (hc : 0 < c) (hB : 0 ≤ B) :
    ∀ j : ℕ, j ≤ k → ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ (u : E → F) (s : Set E), IsOpen s →
      ContDiffOn ℝ ∞ u s → (∀ i : ℕ, i ≤ k + 1 → ∀ z ∈ s, ‖iteratedFDeriv ℝ i u z‖ ≤ B) →
      (∀ z ∈ s, ‖u z‖ ≤ η) → ∀ y : E, closedBall y (j * c) ⊆ s →
      ‖iteratedFDeriv ℝ j u y‖ < ε := by
  intro j
  induction j with
  | zero =>
    intro _ ε hε
    refine ⟨ε / 2, by positivity, fun u s _ _ _ hη y hy => ?_⟩
    have hys : y ∈ s := hy (mem_closedBall_self (by simp))
    rw [norm_iteratedFDeriv_zero]
    linarith [hη y hys]
  | succ j ih =>
    intro hj ε hε
    set t : ℝ := min c (ε / (2 * (B + 1))) with ht_def
    have ht : 0 < t := lt_min hc (by positivity)
    have htc : t ≤ c := min_le_left _ _
    have htB : t * B < ε / 2 := by
      have h1 : t ≤ ε / (2 * (B + 1)) := min_le_right _ _
      have h2 : ε / (2 * (B + 1)) * B < ε / 2 := by
        rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      exact (mul_le_mul_of_nonneg_right h1 hB).trans_lt h2
    obtain ⟨η, hη, hP⟩ := ih (by omega) (ε * t / 8) (by positivity)
    refine ⟨η, hη, fun u s hs hu hBd hηb y hy => ?_⟩
    have hjc : ((j + 1 : ℕ) : ℝ) * c = j * c + c := by push_cast; ring
    have hj0 : 0 ≤ (j : ℝ) * c := mul_nonneg (Nat.cast_nonneg j) hc.le
    have hball : closedBall y t ⊆ s :=
      (closedBall_subset_closedBall (by rw [hjc]; linarith)).trans hy
    have hsub : ∀ z ∈ closedBall y t, closedBall z (j * c) ⊆ s := fun z hz =>
      (closedBall_subset_closedBall' (by rw [hjc]; rw [mem_closedBall] at hz; linarith)).trans hy
    have key := norm_iteratedFDeriv_succ_le_interp_O26 hs hu ht hball j
      (S := ε * t / 8) (M := B) (fun z hz => (hP u s hs hu hBd hηb z (hsub z hz)).le)
      (fun z hz => hBd (j + 2) (by omega) z (hball hz))
    have h3 : 2 * (ε * t / 8) / t = ε / 4 := by field_simp; ring
    rw [h3] at key
    linarith

end GC.LongTime.Ch12

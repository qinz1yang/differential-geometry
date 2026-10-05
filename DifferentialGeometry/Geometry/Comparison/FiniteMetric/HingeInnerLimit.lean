import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
Two-sided quadratic bounds for the same bilinear forms imply mixed inner-product convergence
along two genuinely varying vectors. Scalar squeezing and polarization need no chart choices.
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace DifferentialGeometry.Geometry.FiniteComparison

theorem tendsto_bilin_of_quadratic_bounds
    {E : Type*} [normE : NormedAddCommGroup E] [spaceE : NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (BSeq : ℕ → E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ u v, B u v = B v u)
    (hSeq : ∀ n u v, BSeq n u v = BSeq n v u)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ n w, (1 - ε n) ^ 2 * B w w ≤ BSeq n w w ∧
      BSeq n w w ≤ (1 + ε n) ^ 2 * B w w)
    (uSeq vSeq : ℕ → E) (u v : E)
    (hu : Tendsto uSeq atTop (𝓝 u)) (hv : Tendsto vSeq atTop (𝓝 v)) :
    Tendsto (fun n => BSeq n (uSeq n) (vSeq n)) atTop (𝓝 (B u v)) := by
  have hd {wSeq : ℕ → E} {w : E} (hw : Tendsto wSeq atTop (𝓝 w)) :
      Tendsto (fun n => BSeq n (wSeq n) (wSeq n)) atTop (𝓝 (B w w)) := by
    have hc : Tendsto (fun n => B (wSeq n) (wSeq n)) atTop (𝓝 (B w w)) :=
      B.continuous₂.continuousAt.tendsto.comp (hw.prodMk_nhds hw)
    have h1 : Tendsto (fun n : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hl : Tendsto (fun n => (1 - ε n) ^ 2 * B (wSeq n) (wSeq n))
        atTop (𝓝 (B w w)) := by simpa using ((h1.sub hε).pow 2).mul hc
    have hr : Tendsto (fun n => (1 + ε n) ^ 2 * B (wSeq n) (wSeq n))
        atTop (𝓝 (B w w)) := by simpa using ((h1.add hε).pow 2).mul hc
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl hr
      (fun n => (hbound n (wSeq n)).1) (fun n => (hbound n (wSeq n)).2)
  have hp (C : E →L[ℝ] E →L[ℝ] ℝ) (hC : ∀ x y, C x y = C y x) (x y : E) :
      C x y = (C (x + y) (x + y) - C x x - C y y) / 2 := by
    simp only [map_add, add_apply, hC y x]
    ring
  have h := (((hd (hu.add hv)).sub (hd hu)).sub (hd hv)).div_const 2
  have heq : (fun n => BSeq n (uSeq n) (vSeq n)) = fun n =>
      (BSeq n (uSeq n + vSeq n) (uSeq n + vSeq n) -
        BSeq n (uSeq n) (uSeq n) - BSeq n (vSeq n) (vSeq n)) / 2 := by
    funext n
    exact hp (BSeq n) (hSeq n) (uSeq n) (vSeq n)
  rw [heq, hp B hB u v]
  exact h

end DifferentialGeometry.Geometry.FiniteComparison

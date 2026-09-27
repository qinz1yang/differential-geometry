import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

set_option autoImplicit false
open Set
open scoped ContDiff

namespace DifferentialGeometry.Analysis

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]

theorem contDiffWithinAt_derivWithin_tower
    {f : ℕ → 𝕜 → V} {s : Set 𝕜} {x : 𝕜} (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s)
    (hzero : ContDiffWithinAt 𝕜 ∞ (f 0) s x)
    (hstep : ∀ q y, y ∈ s → f (q + 1) y = derivWithin (f q) s y)
    (q : ℕ) : ContDiffWithinAt 𝕜 ∞ (f q) s x := by
  induction q with
  | zero => exact hzero
  | succ q ih =>
    exact (ih.derivWithin hs (by simp) hx).congr_of_mem (hstep q) hx

theorem derivWithin_tower_eq {s : Set 𝕜} (f g : ℕ → 𝕜 → V)
    (hf : ∀ q x, x ∈ s → f (q + 1) x = derivWithin (f q) s x)
    (hg : ∀ q x, x ∈ s → g (q + 1) x = derivWithin (g q) s x)
    (hzero : EqOn (f 0) (g 0) s) : ∀ q, EqOn (f q) (g q) s := by
  intro q
  induction q with
  | zero => exact hzero
  | succ q ih =>
    intro x hx
    rw [hf q x hx, hg q x hx]
    exact derivWithin_congr ih (ih hx)

theorem iteratedDerivWithin_eq_of_hasDerivWithinAt {s : Set 𝕜}
    (hs : UniqueDiffOn 𝕜 s) (f : 𝕜 → V) (g : ℕ → 𝕜 → V)
    (hg : ∀ q x, x ∈ s → HasDerivWithinAt (g q) (g (q + 1) x) s x)
    (hzero : EqOn f (g 0) s) : ∀ q, EqOn (iteratedDerivWithin q f s) (g q) s := by
  apply derivWithin_tower_eq (fun q => iteratedDerivWithin q f s) g
    (fun q x _ => congrFun (iteratedDerivWithin_succ (n := q)) x)
    (fun q x hx => ((hg q x hx).derivWithin (hs x hx)).symm)
  exact hzero

end DifferentialGeometry.Analysis

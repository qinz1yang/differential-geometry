import Mathlib.Analysis.Calculus.ContDiff.Deriv

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

end DifferentialGeometry.Analysis

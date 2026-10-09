import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimEndProfile
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# FC39 GROUP G, RIMBOX R3 kernel: consumer

Lane FC39-G-RIMBOX. The end-profile kernel applied to `q = sin` (smooth, `sin 0 = 0`,
`sin' 0 = 1`): for the square `[-2, 2]` and every small scale there is a global smooth profile with
`sin (τ y) = l y` on `[0, 2]`, `τ 0 = 0`, `τ' > 0` on `[0, 2)` and `0 ≤ τ < 1` there.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace GC.GraphManifold.Assembly.FC39P0

/-- **The sine end profile.** -/
theorem exists_sinEndProfile_GRIM :
    ∃ l₀ : ℝ, 0 < l₀ ∧ ∀ l, 0 < l → l ≤ l₀ → ∃ τ : ℝ → ℝ, ContDiff ℝ ∞ τ ∧ τ 0 = 0 ∧
      (∀ y ∈ Ico 0 2, 0 < deriv τ y) ∧
      ∀ y ∈ Icc 0 2, Real.sin (τ y) = l * y ∧ 0 ≤ τ y ∧ τ y < 1 :=
  exists_endProfile_rim_GRIM one_pos le_rfl Real.contDiff_sin.contDiffOn Real.sin_zero
    (by rw [Real.deriv_sin, Real.cos_zero]; exact one_pos) two_pos

end GC.GraphManifold.Assembly.FC39P0

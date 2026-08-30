import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow

theorem false_of_hamiltonIvey_lower_bound_for_all_ages
    (scalar q : Real)
    (hq : 0 < q)
    (hbound : ∀ age : Real, 0 < age →
      scalar ≥ q * (Real.log (age * q) - 3)) :
    False := by
  let age : Real := Real.exp (scalar / q + 4) / q
  have hage : 0 < age := by
    dsimp [age]
    positivity
  have harg : age * q = Real.exp (scalar / q + 4) := by
    dsimp [age]
    field_simp
  have hlog : Real.log (age * q) = scalar / q + 4 := by
    rw [harg, Real.log_exp]
  have hmain := hbound age hage
  rw [hlog] at hmain
  have hquot : q * (scalar / q) = scalar := by
    field_simp
  have hrewrite : q * (scalar / q + 4 - 3) = scalar + q := by
    rw [show scalar / q + 4 - 3 = scalar / q + 1 by ring]
    rw [mul_add, hquot]
    ring
  rw [hrewrite] at hmain
  linarith

theorem nonnegative_of_hamiltonIvey_lower_bound_for_all_ages
    (scalar leastEigenvalue : Real → Real)
    (hbound : ∀ age : Real, 0 < age →
      ∀ x, leastEigenvalue x < 0 →
        scalar x ≥ (-leastEigenvalue x) *
          (Real.log (age * (-leastEigenvalue x)) - 3)) :
    ∀ x, 0 ≤ leastEigenvalue x := by
  intro x
  by_contra hnonneg
  have hnegative : leastEigenvalue x < 0 := lt_of_not_ge hnonneg
  let q : Real := -leastEigenvalue x
  have hq : 0 < q := by
    dsimp [q]
    linarith
  apply false_of_hamiltonIvey_lower_bound_for_all_ages
    (scalar x) q hq
  intro age hage
  simpa [q] using hbound age hage x hnegative

end DifferentialGeometry.PDE.RicciFlow

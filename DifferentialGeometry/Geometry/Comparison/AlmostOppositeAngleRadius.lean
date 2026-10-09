import DifferentialGeometry.Geometry.Comparison.AlmostOppositeAngle

/-!
# LC26 with the blueprint's radius bound

Blueprint 207A, LC26 (`lem:collapse-model-opposite-angle`, A:21027–21064) assumes `0 < r ≤ b` and
`κ b ≤ 1/3`. The existing kernel `one_add_cos_comparisonAngle_double_le` needs only `κ r ≤ 1/3`;
this file records the blueprint form.
-/

set_option autoImplicit false

open Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

/-- LC26 in the blueprint's form: for `0 < r ≤ b`, `0 ≤ μ ≤ 1`, `r ≤ ℓ ≤ (1 + μ) r`, `κ ≥ 0`
and `κ b ≤ 1/3`, the model angle `ϑ = Θ_{-κ²}(r, ℓ, 2r)` has `0 ≤ 1 + cos ϑ ≤ 6 μ`, and
`ϑ > π - τ` whenever `0 ≤ τ` and `6 μ < 1 - cos τ`. -/
theorem comparisonAngle_double_bounds_of_le_radius
    {κ r ℓ μ b : ℝ} (hκ : 0 ≤ κ) (hr : 0 < r) (hrb : r ≤ b)
    (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) (hrℓ : r ≤ ℓ) (hℓ : ℓ ≤ (1 + μ) * r) (hκb : κ * b ≤ 1 / 3) :
    (0 ≤ 1 + cos (comparisonAngleNegCurvature (κ ^ 2) r ℓ (2 * r)) ∧
      1 + cos (comparisonAngleNegCurvature (κ ^ 2) r ℓ (2 * r)) ≤ 6 * μ) ∧
    ∀ τ : ℝ, 0 ≤ τ → 6 * μ < 1 - cos τ →
      Real.pi - τ < comparisonAngleNegCurvature (κ ^ 2) r ℓ (2 * r) := by
  have hκr : κ * r ≤ 1 / 3 := (mul_le_mul_of_nonneg_left hrb hκ).trans hκb
  exact ⟨one_add_cos_comparisonAngle_double_le hκ hr hμ hμ1 hrℓ hℓ hκr,
    fun τ hτ hbudget => pi_sub_lt_comparisonAngle_double hκ hr hμ hμ1 hrℓ hℓ hκr hτ hbudget⟩

end DifferentialGeometry.Geometry.Comparison.Toponogov

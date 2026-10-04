import DifferentialGeometry.Analysis.InnerProductSpace.DirectionalSaturation

/-!
# Pointwise asymmetric derivative tests (FC22 pointwise; EGP04, TCP03, SGP03)

Blueprint `master207B.tex`: FC15 (`lem:fibration-directional-comparison`, lines 934–983), FC22
(`lem:fibration-asymmetric-tests`, 1451–1503), EGP04 (`lem:fibration-edge-actual-comparison`,
4943–5040), TCP03 (5370–5440), SGP03 (4483–4600).

At one point, two adapted derivative tests along the SAME unit initial vector `w` of a minimizing
segment give saturation of both covectors, and the Riesz calculation of FC15 (in the tree as
`ContinuousLinearMap.norm_sub_le_of_common_unit_saturation`) bounds their difference:

* `saturation_of_test_gain`: `|α - G/ℓ| ≤ ς`, raw gain `G ≥ ℓ - e`, length `ℓ ≥ ℓ₀ > 0` give
  `α ≥ 1 - (ς + e/ℓ₀)`.
* `short_gain_of_long_tests` (FC22's scalar step): a long raw gain `Ψ y - Ψ x ≥ ℓ - β`, the coarse
  bound `Ψ y - Ψ z ≤ ℓ - t + δ` at the intermediate point `z`, and the affine alignment
  `|Ψ - (U + b)| ≤ E` only at `x, z` give the short gain `U z - U x ≥ t - (β + δ + 2E)`.
* `norm_sub_le_of_asymmetric_tests`: both tests on the same `w`, with lengths at least `ℓ₀` and gain
  defects at most `e`, give `‖f - g‖ ≤ 2 √(4ε + ε²)` with `ε = ς + e/ℓ₀`.
* `abs_affine_value_error_le`: the value clause of (EC)/(TC)/(SC): separate value errors `v` of the two
  smooth coordinates and the raw alignment `E` give `|s ηⱼ - (a ηᵢ + c)| ≤ s v + E + v` for `|a| = 1`.
-/

set_option autoImplicit false

open scoped InnerProductSpace

namespace ContinuousLinearMap

/-- A derivative test with an almost maximal raw gain saturates the covector on its direction. -/
theorem saturation_of_test_gain {α G ℓ ℓ₀ ς e : ℝ} (hℓ₀ : 0 < ℓ₀) (hℓ : ℓ₀ ≤ ℓ) (he : 0 ≤ e)
    (htest : |α - G / ℓ| ≤ ς) (hgain : ℓ - e ≤ G) : 1 - (ς + e / ℓ₀) ≤ α := by
  have hℓpos : 0 < ℓ := hℓ₀.trans_le hℓ
  have h1 : 1 - e / ℓ ≤ G / ℓ := by
    have hid : 1 - e / ℓ = (ℓ - e) / ℓ := by field_simp
    rw [hid]
    exact div_le_div_of_nonneg_right hgain hℓpos.le
  have h2 : e / ℓ ≤ e / ℓ₀ := div_le_div_of_nonneg_left he hℓ₀ hℓ
  linarith [(abs_le.mp htest).1]

/-- FC22's scalar step: the long gain transfers to the short segment through the alignment at
`x` and `z` only. -/
theorem short_gain_of_long_tests {Ψx Ψy Ψz Ux Uz b ℓ t β δ E : ℝ}
    (hlong : ℓ - β ≤ Ψy - Ψx) (hcoarse : Ψy - Ψz ≤ ℓ - t + δ)
    (hx : |Ψx - (Ux + b)| ≤ E) (hz : |Ψz - (Uz + b)| ≤ E) :
    t - (β + δ + 2 * E) ≤ Uz - Ux := by
  have h1 := abs_le.mp hx
  have h2 := abs_le.mp hz
  linarith [h1.1, h1.2, h2.1, h2.2]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- FC22 at one point: two derivative tests on the same unit direction. -/
theorem norm_sub_le_of_asymmetric_tests (f g : StrongDual ℝ E) (w : E) (hw : ‖w‖ = 1)
    {ς e ℓ₀ ℓ₁ ℓ₂ G₁ G₂ : ℝ} (hς : 0 ≤ ς) (he : 0 ≤ e) (hℓ₀ : 0 < ℓ₀)
    (hf : ‖f‖ ≤ 1 + ς) (hg : ‖g‖ ≤ 1 + ς) (hℓ₁ : ℓ₀ ≤ ℓ₁) (hℓ₂ : ℓ₀ ≤ ℓ₂)
    (htest₁ : |f w - G₁ / ℓ₁| ≤ ς) (hgain₁ : ℓ₁ - e ≤ G₁)
    (htest₂ : |g w - G₂ / ℓ₂| ≤ ς) (hgain₂ : ℓ₂ - e ≤ G₂) :
    ‖f - g‖ ≤ 2 * Real.sqrt (4 * (ς + e / ℓ₀) + (ς + e / ℓ₀) ^ 2) := by
  have hε : 0 ≤ e / ℓ₀ := div_nonneg he hℓ₀.le
  exact norm_sub_le_of_common_unit_saturation f g (by positivity) (by linarith) (by linarith) w hw
    (saturation_of_test_gain hℓ₀ hℓ₁ he htest₁ hgain₁)
    (saturation_of_test_gain hℓ₀ hℓ₂ he htest₂ hgain₂)

end ContinuousLinearMap

/-- The value clause of EGP04 (EC), TCP03 (TC) and SGP03 (SC). -/
theorem abs_affine_value_error_le {ηj ηi uj ui s a c v E : ℝ} (hs : 0 ≤ s) (ha : |a| = 1)
    (hj : |ηj - uj| ≤ v) (hi : |ηi - ui| ≤ v) (hraw : |s * uj - a * ui - c| ≤ E) :
    |s * ηj - (a * ηi + c)| ≤ s * v + E + v := by
  have he : s * ηj - (a * ηi + c) = s * (ηj - uj) + (s * uj - a * ui - c) - a * (ηi - ui) := by
    ring
  rw [he]
  calc _ ≤ |s * (ηj - uj) + (s * uj - a * ui - c)| + |a * (ηi - ui)| := abs_sub _ _
    _ ≤ |s * (ηj - uj)| + |s * uj - a * ui - c| + |a * (ηi - ui)| := by
        gcongr; exact abs_add_le _ _
    _ ≤ s * v + E + v := by
        rw [abs_mul, abs_mul, abs_of_nonneg hs, ha, one_mul]
        gcongr

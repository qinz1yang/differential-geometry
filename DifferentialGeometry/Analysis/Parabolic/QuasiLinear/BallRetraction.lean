import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Radial retraction onto a closed ball

For a real inner-product space `X` and a radius `R ≥ 0`, the radial retraction
`ballRetraction R x = (min 1 (R / ‖x‖)) • x` rescales any point outside the closed `R`-ball
back onto its boundary while fixing every point inside. It is the metric projection onto the
closed ball, hence nonexpansive. We record three properties:

* `ballRetraction_mem_closedBall` — the image lands in the closed `R`-ball;
* `ballRetraction_eq_self_of_mem` — the map fixes the closed `R`-ball;
* `lipschitzWith_ballRetraction` — the map is `1`-Lipschitz.

The `1`-Lipschitz bound is proved directly: there is no ready-made nonexpansiveness lemma for the
metric projection onto a general convex set in Mathlib (only onto closed subspaces). The proof
reduces, via the polarisation identity, to the elementary fact that `t ↦ min t R` is `1`-Lipschitz
on `ℝ`.
-/

open scoped InnerProductSpace

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- The radial retraction onto the closed ball of radius `R` centred at the origin:
points inside the ball are fixed, points outside are rescaled radially onto the boundary.
At the origin (`‖x‖ = 0`) the scalar `min 1 (R / ‖x‖)` is applied to `0`, giving `0`, so the map
is total and continuous. -/
noncomputable def ballRetraction (R : ℝ) (x : X) : X := (min 1 (R / ‖x‖)) • x

/-- The scaling factor lies in `[0, 1]` when `R ≥ 0`. -/
private theorem ballRetraction_factor_nonneg {R : ℝ} (hR : 0 ≤ R) (x : X) :
    0 ≤ min 1 (R / ‖x‖) :=
  le_min zero_le_one (div_nonneg hR (norm_nonneg x))

/-- The scaling factor times the norm equals `min ‖x‖ R`. -/
private theorem ballRetraction_factor_mul_norm {R : ℝ} (hR : 0 ≤ R) (x : X) :
    (min 1 (R / ‖x‖)) * ‖x‖ = min ‖x‖ R := by
  rcases eq_or_lt_of_le (norm_nonneg x) with hx | hx
  · rw [← hx]; simp [min_eq_left hR]
  · rw [min_mul_of_nonneg _ _ (le_of_lt hx), one_mul, div_mul_cancel₀]
    exact ne_of_gt hx

/-- The radial retraction lands in the closed ball of radius `R`. -/
theorem ballRetraction_mem_closedBall {R : ℝ} (hR : 0 ≤ R) (x : X) :
    ‖ballRetraction R x‖ ≤ R := by
  rw [ballRetraction, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (ballRetraction_factor_nonneg hR x), ballRetraction_factor_mul_norm hR]
  exact min_le_right _ _

/-- The radial retraction fixes every point of the closed ball of radius `R`. -/
theorem ballRetraction_eq_self_of_mem {R : ℝ} {x : X} (hx : ‖x‖ ≤ R) :
    ballRetraction R x = x := by
  rw [ballRetraction]
  rcases eq_or_lt_of_le (norm_nonneg x) with hx0 | hx0
  · simp [norm_eq_zero.1 hx0.symm]
  · have : (1 : ℝ) ≤ R / ‖x‖ := (one_le_div hx0).2 hx
    rw [min_eq_left this, one_smul]

/-- The radial retraction onto a closed ball is `1`-Lipschitz. -/
theorem lipschitzWith_ballRetraction {R : ℝ} (hR : 0 ≤ R) :
    LipschitzWith 1 (ballRetraction (X := X) R) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (norm_nonneg (x - y))]
  refine Real.sqrt_le_sqrt ?_
  set a : ℝ := min 1 (R / ‖x‖) with ha
  set b : ℝ := min 1 (R / ‖y‖) with hb
  have ha0 : 0 ≤ a := ballRetraction_factor_nonneg hR x
  have hb0 : 0 ≤ b := ballRetraction_factor_nonneg hR y
  have ha1 : a ≤ 1 := min_le_left _ _
  have hb1 : b ≤ 1 := min_le_left _ _
  have hax : a * ‖x‖ = min ‖x‖ R := ballRetraction_factor_mul_norm hR x
  have hby : b * ‖y‖ = min ‖y‖ R := ballRetraction_factor_mul_norm hR y
  rw [ballRetraction, ballRetraction, ← ha, ← hb, norm_sub_sq_real, norm_sub_sq_real,
    norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg ha0, abs_of_nonneg hb0, real_inner_smul_left, real_inner_smul_right]
  have hp0 : 0 ≤ ‖x‖ := norm_nonneg x
  have hq0 : 0 ≤ ‖y‖ := norm_nonneg y
  have hcs : ⟪x, y⟫_ℝ ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
  have hab : 0 ≤ 1 - a * b := by nlinarith [mul_le_one₀ ha1 hb0 hb1]
  have hmin : (a * ‖x‖ - b * ‖y‖) ^ 2 ≤ (‖x‖ - ‖y‖) ^ 2 := by
    rw [hax, hby]
    have hlip : LipschitzWith 1 (fun t : ℝ => min t R) := (LipschitzWith.id).min_const R
    have h1 : |min ‖x‖ R - min ‖y‖ R| ≤ |‖x‖ - ‖y‖| := by
      have := hlip.dist_le_mul ‖x‖ ‖y‖
      simpa [Real.dist_eq, NNReal.coe_one, one_mul] using this
    nlinarith [abs_nonneg (min ‖x‖ R - min ‖y‖ R), abs_nonneg (‖x‖ - ‖y‖),
      sq_abs (min ‖x‖ R - min ‖y‖ R), sq_abs (‖x‖ - ‖y‖),
      mul_self_le_mul_self (abs_nonneg (min ‖x‖ R - min ‖y‖ R)) h1]
  nlinarith [hmin, hab, hcs, mul_nonneg hp0 hq0,
    mul_nonneg hab (sub_nonneg.2 hcs)]

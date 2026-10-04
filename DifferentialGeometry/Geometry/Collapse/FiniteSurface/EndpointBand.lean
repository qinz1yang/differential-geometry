import DifferentialGeometry.Geometry.Comparison.Toponogov.ComparisonAngle
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# LFR23 kernels: the metric content of the endpoint disk band

Blueprint LFR23 (master207A:26745). `(Z, z₀)` is a metric space and `q : B̄(z₀,10) → [0,10]`
is a based map, `q z₀ = 0`, with distortion at most `δ`. This file proves the metric and
algebraic steps of the proof, for an arbitrary metric space:

* `endpoint_triangle_bounds`: with `x⁺` at distance `19/2` and `r(x) ≤ 37/4`, the numbers
  `a = r(x)`, `b = d(x,x⁺)` satisfy `|b - (19/2 - a)| ≤ 3δ`, `0 ≤ a + b - 19/2 ≤ 3δ`, `b > 6/25`;
* `one_add_cos_metricComparisonAngle_lt`: hence the comparison angle at `x` of the triangle
  `(z₀, x, x⁺)` satisfies `1 + cos ∠̃ < 300 δ` (the right-hand side of (LFR23.1));
* `norm_add_sq_lt_of_one_add_inner_lt`, `norm_sub_lt_of_one_add_inner_lt`,
  `inner_neg_lt_of_one_add_inner_lt`: the direction algebra (`‖v + w‖² < 600δ`, any two inward
  directions within `2√(600δ)`, `⟪-v, v'⟫ < -7/8` once `δ ≤ 1/9600`);
* `dist_le_three_mul_of_level`: two points of one distance level are within `3δ`;
* `half_le_three_mul_of_equilateral`: an interval contains no `δ`-approximation of an equilateral
  triangle of side `1/2` unless `1/2 ≤ 3δ` (the flat-torus exclusion).

The Riemannian binding (hinge comparison for the `C^m` metric, which turns the comparison angle into
the angle between ACTUAL minimizing directions) is blocked: see `build-logs/resume/sheet-W4-F7c.md`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Comparison.Toponogov

section Metric

variable {Z : Type*} [PseudoMetricSpace Z]

/-- **LFR23, the distortion bookkeeping.** -/
theorem endpoint_triangle_bounds {z₀ x x' : Z} {q : Z → ℝ} {δ : ℝ} (hq0 : q z₀ = 0)
    (hqnn : ∀ y ∈ closedBall z₀ 10, 0 ≤ q y)
    (hdist : ∀ y ∈ closedBall z₀ 10, ∀ y' ∈ closedBall z₀ 10,
      |dist (q y) (q y') - dist y y'| ≤ δ)
    (hx' : dist z₀ x' = 19 / 2) (hx₂ : dist z₀ x ≤ 37 / 4) :
    |dist x x' - (19 / 2 - dist z₀ x)| ≤ 3 * δ ∧ 0 ≤ dist z₀ x + dist x x' - 19 / 2 ∧
      dist z₀ x + dist x x' - 19 / 2 ≤ 3 * δ ∧ 6 / 25 < dist x x' := by
  have hz₀ : z₀ ∈ closedBall z₀ 10 := mem_closedBall_self (by norm_num)
  have hxB : x ∈ closedBall z₀ 10 := by
    rw [mem_closedBall, dist_comm]; linarith
  have hx'B : x' ∈ closedBall z₀ 10 := by
    rw [mem_closedBall, dist_comm]; linarith
  have hqx := abs_le.mp (hdist z₀ hz₀ x hxB)
  have hqx' := abs_le.mp (hdist z₀ hz₀ x' hx'B)
  have hqxx' := abs_le.mp (hdist x hxB x' hx'B)
  rw [hq0, Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg (hqnn x hxB)] at hqx
  rw [hq0, Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg (hqnn x' hx'B)] at hqx'
  rw [Real.dist_eq] at hqxx'
  have htri : dist z₀ x' ≤ dist z₀ x + dist x x' := dist_triangle _ _ _
  have hupper : dist x x' ≤ 19 / 2 - dist z₀ x + 3 * δ := by
    have habs : |q x - q x'| ≤ 19 / 2 - dist z₀ x + 2 * δ := by
      rw [abs_le]; constructor <;> linarith
    linarith [hqxx'.2]
  refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, by linarith, by linarith, by linarith⟩

/-- **(LFR23.1), comparison side, arithmetic form.** -/
theorem one_add_comparisonCosine_lt {a b δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 1000)
    (ha : 1 / 2 ≤ a) (hb : 6 / 25 < b) (hs₀ : 0 ≤ a + b - 19 / 2) (hs₁ : a + b - 19 / 2 ≤ 3 * δ) :
    1 + (a ^ 2 + b ^ 2 - (19 / 2) ^ 2) / (2 * a * b) < 300 * δ := by
  have hab : 0 < 2 * a * b := by positivity
  have hnum : 1 + (a ^ 2 + b ^ 2 - (19 / 2) ^ 2) / (2 * a * b) =
      ((a + b - 19 / 2) * (a + b + 19 / 2)) / (2 * a * b) := by
    field_simp
    ring
  rw [hnum, div_lt_iff₀ hab]
  have hsum : a + b + 19 / 2 ≤ 19 + 3 * δ := by linarith
  have hprod : (a + b - 19 / 2) * (a + b + 19 / 2) ≤ 3 * δ * (19 + 3 * δ) :=
    mul_le_mul hs₁ hsum (by linarith) (by linarith)
  have hab' : 6 / 25 ≤ 2 * a * b := by nlinarith
  nlinarith

/-- **(LFR23.1), comparison side.** The comparison angle at `x` of `(z₀, x, x⁺)` is almost `π`. -/
theorem one_add_cos_metricComparisonAngle_lt {z₀ x x' : Z} {q : Z → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hδ' : δ < 1 / 1000) (hq0 : q z₀ = 0) (hqnn : ∀ y ∈ closedBall z₀ 10, 0 ≤ q y)
    (hdist : ∀ y ∈ closedBall z₀ 10, ∀ y' ∈ closedBall z₀ 10,
      |dist (q y) (q y') - dist y y'| ≤ δ)
    (hx' : dist z₀ x' = 19 / 2) (hx₁ : 1 / 2 ≤ dist z₀ x) (hx₂ : dist z₀ x ≤ 37 / 4) :
    1 + Real.cos (metricComparisonAngle z₀ x x') < 300 * δ := by
  obtain ⟨-, hs₀, hs₁, hb⟩ := endpoint_triangle_bounds hq0 hqnn hdist hx' hx₂
  have ha : 0 < dist x z₀ := by rw [dist_comm]; linarith
  have hb' : 0 < dist x x' := by linarith
  have hlow : |dist x z₀ - dist x x'| ≤ dist z₀ x' := by
    rw [abs_le]; constructor
    · linarith [dist_triangle x z₀ x', dist_comm z₀ x]
    · linarith [dist_triangle z₀ x' x, dist_comm x' x, dist_comm z₀ x]
  have hup : dist z₀ x' ≤ dist x z₀ + dist x x' := by
    linarith [dist_triangle z₀ x x', dist_comm z₀ x]
  rw [metricComparisonAngle, cos_comparisonAngle ha hb' hlow hup, hx', dist_comm x z₀]
  exact one_add_comparisonCosine_lt hδ hδ' hx₁ hb (by linarith) (by linarith)

/-- **LFR23, connectedness step.** Two points on one distance level `ρ ≤ 10` are within `3δ`. -/
theorem dist_le_three_mul_of_level {z₀ x y : Z} {q : Z → ℝ} {δ ρ : ℝ} (hq0 : q z₀ = 0)
    (hqnn : ∀ y ∈ closedBall z₀ 10, 0 ≤ q y)
    (hdist : ∀ y ∈ closedBall z₀ 10, ∀ y' ∈ closedBall z₀ 10,
      |dist (q y) (q y') - dist y y'| ≤ δ)
    (hρ : ρ ≤ 10) (hx : dist z₀ x = ρ) (hy : dist z₀ y = ρ) : dist x y ≤ 3 * δ := by
  have hz₀ : z₀ ∈ closedBall z₀ 10 := mem_closedBall_self (by linarith [dist_nonneg (x := z₀) (y := x)])
  have hxB : x ∈ closedBall z₀ 10 := by rw [mem_closedBall, dist_comm]; linarith
  have hyB : y ∈ closedBall z₀ 10 := by rw [mem_closedBall, dist_comm]; linarith
  have hqx := abs_le.mp (hdist z₀ hz₀ x hxB)
  have hqy := abs_le.mp (hdist z₀ hz₀ y hyB)
  have hqxy := abs_le.mp (hdist x hxB y hyB)
  rw [hq0, Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg (hqnn x hxB)] at hqx
  rw [hq0, Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg (hqnn y hyB)] at hqy
  rw [Real.dist_eq] at hqxy
  have habs : |q x - q y| ≤ 2 * δ := by rw [abs_le]; constructor <;> linarith
  linarith [hqxy.1]

end Metric

/-- **LFR23, flat-torus exclusion.** If three points with pairwise distances `1/2` are mapped into
`ℝ` with distortion at most `δ`, then `1/2 ≤ 3δ`: the largest of three distances on a line is the
sum of the other two. -/
theorem half_le_three_mul_of_equilateral {X : Type*} [PseudoMetricSpace X] {y₁ y₂ y₃ : X}
    {q : X → ℝ} {δ : ℝ} (h₁₂ : dist y₁ y₂ = 1 / 2) (h₁₃ : dist y₁ y₃ = 1 / 2)
    (h₂₃ : dist y₂ y₃ = 1 / 2) (d₁₂ : |dist (q y₁) (q y₂) - dist y₁ y₂| ≤ δ)
    (d₁₃ : |dist (q y₁) (q y₃) - dist y₁ y₃| ≤ δ) (d₂₃ : |dist (q y₂) (q y₃) - dist y₂ y₃| ≤ δ) :
    1 / 2 ≤ 3 * δ := by
  rw [h₁₂, Real.dist_eq] at d₁₂
  rw [h₁₃, Real.dist_eq] at d₁₃
  rw [h₂₃, Real.dist_eq] at d₂₃
  have e₁₂ := abs_le.mp d₁₂
  have e₁₃ := abs_le.mp d₁₃
  have e₂₃ := abs_le.mp d₂₃
  rcases le_total (q y₁) (q y₂) with a | a <;> rcases le_total (q y₂) (q y₃) with b | b <;>
    rcases le_total (q y₁) (q y₃) with c | c <;>
    simp only [abs_of_nonneg (sub_nonneg.mpr a), abs_of_nonpos (sub_nonpos.mpr a),
      abs_of_nonneg (sub_nonneg.mpr b), abs_of_nonpos (sub_nonpos.mpr b),
      abs_of_nonneg (sub_nonneg.mpr c), abs_of_nonpos (sub_nonpos.mpr c)] at e₁₂ e₁₃ e₂₃ <;>
    linarith [e₁₂.1, e₁₂.2, e₁₃.1, e₁₃.2, e₂₃.1, e₂₃.2]

section Directions

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `‖v + w‖² = 2 (1 + ⟪v,w⟫)` for unit vectors, so `1 + ⟪v,w⟫ < c` gives `‖v + w‖² < 2c`. -/
theorem norm_add_sq_lt_of_one_add_inner_lt {v w : V} {c : ℝ} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (h : 1 + inner ℝ v w < c) : ‖v + w‖ ^ 2 < 2 * c := by
  rw [norm_add_sq_real, hv, hw]
  linarith

/-- **LFR23, direction diameter.** Two unit vectors almost opposite to one unit vector `w`
(`1 + ⟪v,w⟫ < c`, `1 + ⟪v',w⟫ < c`) are within `2√(2c)`; with `c = 300δ` this is `2√(600δ)`. -/
theorem norm_sub_lt_of_one_add_inner_lt {v v' w : V} {c : ℝ} (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1)
    (hw : ‖w‖ = 1) (h : 1 + inner ℝ v w < c) (h' : 1 + inner ℝ v' w < c) :
    ‖v - v'‖ < 2 * Real.sqrt (2 * c) := by
  have h₁ : ‖v + w‖ < Real.sqrt (2 * c) :=
    Real.lt_sqrt_of_sq_lt (norm_add_sq_lt_of_one_add_inner_lt hv hw h)
  have h₂ : ‖v' + w‖ < Real.sqrt (2 * c) :=
    Real.lt_sqrt_of_sq_lt (norm_add_sq_lt_of_one_add_inner_lt hv' hw h')
  have hsub : v - v' = (v + w) - (v' + w) := by abel
  rw [hsub]
  linarith [norm_sub_le (v + w) (v' + w)]

/-- **LFR23, the negated direction.** Under the same hypotheses with `c ≤ 1/32` (i.e. `δ ≤ 1/9600`
for `c = 300δ`), `⟪-v, v'⟫ < -7/8`. -/
theorem inner_neg_lt_of_one_add_inner_lt {v v' w : V} {c : ℝ} (hc : c ≤ 1 / 32) (hv : ‖v‖ = 1)
    (hv' : ‖v'‖ = 1) (hw : ‖w‖ = 1) (h : 1 + inner ℝ v w < c) (h' : 1 + inner ℝ v' w < c) :
    inner ℝ (-v) v' < -(7 / 8) := by
  have hlt := norm_sub_lt_of_one_add_inner_lt hv hv' hw h h'
  have hc0 : 0 ≤ 2 * c := by
    have := norm_add_sq_lt_of_one_add_inner_lt hv hw h
    nlinarith [sq_nonneg ‖v + w‖]
  have hsq : ‖v - v'‖ ^ 2 < 8 * c := by
    have h0 : 0 ≤ ‖v - v'‖ := norm_nonneg _
    have hs := Real.sq_sqrt hc0
    nlinarith
  rw [norm_sub_sq_real, hv, hv'] at hsq
  rw [inner_neg_left]
  linarith

end Directions

end DifferentialGeometry.Geometry.Collapse

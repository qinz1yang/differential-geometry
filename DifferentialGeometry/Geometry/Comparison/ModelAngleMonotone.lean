import DifferentialGeometry.Geometry.Comparison.CurvatureWeakening
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Monotonicity of the model angle in the curvature

`comparisonAngleNegCurvature κ a b c` is the angle opposite the side `c` in the model plane of
constant curvature `-κ`. For fixed side lengths it is antitone in `κ ∈ [0, ∞)`: a more negative
model curvature gives a smaller comparison angle.

The hypotheses are only `0 ≤ κ ≤ κ'` and `0 < a`, `0 < b` (or `0 ≤ a * b` in the general form);
no triangle inequality is needed, because outside `|a - b| ≤ |c| ≤ a + b` the clamped `arccos`
is `0` or `π` at every curvature. Both hypotheses are necessary for the definition as written:
for `κ < 0` the value is `π / 2` for all sides, and for `a < 0 < b` the angle is
`π` minus the angle of `(|a|, b, c)`, hence monotone in the other direction.

Proof: with `s = √κ`, `P = (c + a - b) / 2`, `Q = (c - a + b) / 2`,
`1 - cos θ = 2 (sinh (sP) / sinh (sa)) (sinh (sQ) / sinh (sb))`, and `s ↦ sinh (s p) / sinh (s a)`
is antitone for `0 ≤ p ≤ a` because `u ↦ u coth u` is monotone. The Euclidean endpoint is
`comparisonAngleNegCurvature_le_comparisonAngle`.
-/

set_option autoImplicit false

open Set

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

/-- `u ↦ u cosh u / sinh u` is monotone on `(0, ∞)`. -/
private theorem monotoneOn_mul_cosh_div_sinh :
    MonotoneOn (fun u : ℝ => u * Real.cosh u / Real.sinh u) (Ioi 0) := by
  have hderiv : ∀ u ∈ Ioi (0 : ℝ), HasDerivAt (fun u : ℝ => u * Real.cosh u / Real.sinh u)
      (((1 * Real.cosh u + u * Real.sinh u) * Real.sinh u -
        u * Real.cosh u * Real.cosh u) / Real.sinh u ^ 2) u := fun u hu =>
    ((hasDerivAt_id' u).mul (Real.hasDerivAt_cosh u)).div (Real.hasDerivAt_sinh u)
      (Real.sinh_pos_iff.2 hu).ne'
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 0)
    (f' := fun u => ((1 * Real.cosh u + u * Real.sinh u) * Real.sinh u -
      u * Real.cosh u * Real.cosh u) / Real.sinh u ^ 2)
  · exact fun u hu => (hderiv u hu).continuousAt.continuousWithinAt
  · intro u hu
    rw [interior_Ioi] at hu
    exact (hderiv u hu).hasDerivWithinAt
  · intro u hu
    rw [interior_Ioi] at hu
    apply div_nonneg _ (sq_nonneg _)
    have h2 := Real.self_le_sinh_iff.2 (by linarith [hu.out] : (0 : ℝ) ≤ 2 * u)
    rw [Real.sinh_two_mul] at h2
    have hnum : (1 * Real.cosh u + u * Real.sinh u) * Real.sinh u -
        u * Real.cosh u * Real.cosh u = Real.sinh u * Real.cosh u - u := by
      linear_combination (-u) * Real.cosh_sq_sub_sinh_sq u
    rw [hnum]
    linarith

private theorem mul_cosh_mul_sinh_le {p a s : ℝ} (hp : 0 ≤ p) (hpa : p ≤ a) (hs : 0 < s) :
    p * Real.cosh (s * p) * Real.sinh (s * a) ≤
      a * Real.cosh (s * a) * Real.sinh (s * p) := by
  rcases hp.eq_or_lt with rfl | hp
  · simp
  have hsp : 0 < s * p := mul_pos hs hp
  have hsa : 0 < s * a := mul_pos hs (hp.trans_le hpa)
  have hk := monotoneOn_mul_cosh_div_sinh hsp hsa (mul_le_mul_of_nonneg_left hpa hs.le)
  simp only at hk
  rw [div_le_div_iff₀ (Real.sinh_pos_iff.2 hsp) (Real.sinh_pos_iff.2 hsa)] at hk
  have h : s * (p * Real.cosh (s * p) * Real.sinh (s * a)) ≤
      s * (a * Real.cosh (s * a) * Real.sinh (s * p)) := by linarith
  exact le_of_mul_le_mul_left h hs

/-- For `0 ≤ p ≤ a` with `0 < a`, `s ↦ sinh (s p) / sinh (s a)` is antitone on `(0, ∞)`. -/
private theorem antitoneOn_sinh_mul_div_sinh_mul {p a : ℝ} (hp : 0 ≤ p) (hpa : p ≤ a)
    (ha : 0 < a) :
    AntitoneOn (fun s : ℝ => Real.sinh (s * p) / Real.sinh (s * a)) (Ioi 0) := by
  have hderiv : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivAt (fun s : ℝ => Real.sinh (s * p) / Real.sinh (s * a))
        ((Real.cosh (s * p) * (1 * p) * Real.sinh (s * a) -
          Real.sinh (s * p) * (Real.cosh (s * a) * (1 * a))) / Real.sinh (s * a) ^ 2) s :=
    fun s hs => (((hasDerivAt_id' s).mul_const p).sinh).div
      (((hasDerivAt_id' s).mul_const a).sinh) (Real.sinh_pos_iff.2 (mul_pos hs ha)).ne'
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
    (f' := fun s => (Real.cosh (s * p) * (1 * p) * Real.sinh (s * a) -
      Real.sinh (s * p) * (Real.cosh (s * a) * (1 * a))) / Real.sinh (s * a) ^ 2)
  · exact fun s hs => (hderiv s hs).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ioi] at hs
    exact (hderiv s hs).hasDerivWithinAt
  · intro s hs
    rw [interior_Ioi] at hs
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    have h := mul_cosh_mul_sinh_le hp hpa hs
    linarith

private theorem hyperbolicCosine_eq_one_sub {s a b c : ℝ} (hs : 0 < s) (ha : 0 < a)
    (hb : 0 < b) :
    (Real.cosh (s * a) * Real.cosh (s * b) - Real.cosh (s * c)) /
        (Real.sinh (s * a) * Real.sinh (s * b)) =
      1 - 2 * (Real.sinh (s * ((c + a - b) / 2)) / Real.sinh (s * a)) *
        (Real.sinh (s * ((c - a + b) / 2)) / Real.sinh (s * b)) := by
  have hA : Real.sinh (s * a) ≠ 0 := (Real.sinh_pos_iff.2 (mul_pos hs ha)).ne'
  have hB : Real.sinh (s * b) ≠ 0 := (Real.sinh_pos_iff.2 (mul_pos hs hb)).ne'
  have e1 : Real.cosh (s * c) =
      Real.cosh (s * ((c + a - b) / 2)) * Real.cosh (s * ((c - a + b) / 2)) +
        Real.sinh (s * ((c + a - b) / 2)) * Real.sinh (s * ((c - a + b) / 2)) := by
    rw [← Real.cosh_add]
    congr 1
    ring
  have e2 : Real.cosh (s * a) * Real.cosh (s * b) - Real.sinh (s * a) * Real.sinh (s * b) =
      Real.cosh (s * ((c + a - b) / 2)) * Real.cosh (s * ((c - a + b) / 2)) -
        Real.sinh (s * ((c + a - b) / 2)) * Real.sinh (s * ((c - a + b) / 2)) := by
    rw [← Real.cosh_sub, ← Real.cosh_sub]
    congr 1
    ring
  have halg (X Y : ℝ) : (1 - 2 * (X / Real.sinh (s * a)) * (Y / Real.sinh (s * b))) *
      (Real.sinh (s * a) * Real.sinh (s * b)) =
        Real.sinh (s * a) * Real.sinh (s * b) - 2 * X * Y := by
    field_simp
  rw [div_eq_iff (mul_ne_zero hA hB), halg]
  linear_combination e2 - e1

/-- The hyperbolic cosine expression of the model angle is monotone in the scale `s = √κ`
for side lengths satisfying the triangle inequalities. -/
private theorem hyperbolicCosine_le_of_le {s t a b c : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (ha : 0 < a) (hb : 0 < b) (hlower : |a - b| ≤ c) (hupper : c ≤ a + b) :
    (Real.cosh (s * a) * Real.cosh (s * b) - Real.cosh (s * c)) /
        (Real.sinh (s * a) * Real.sinh (s * b)) ≤
      (Real.cosh (t * a) * Real.cosh (t * b) - Real.cosh (t * c)) /
        (Real.sinh (t * a) * Real.sinh (t * b)) := by
  have ht : 0 < t := hs.trans_le hst
  have hab := abs_le.1 hlower
  have hP : 0 ≤ (c + a - b) / 2 := by linarith
  have hPa : (c + a - b) / 2 ≤ a := by linarith
  have hQ : 0 ≤ (c - a + b) / 2 := by linarith
  have hQb : (c - a + b) / 2 ≤ b := by linarith
  rw [hyperbolicCosine_eq_one_sub hs ha hb, hyperbolicCosine_eq_one_sub ht ha hb]
  have hrP := antitoneOn_sinh_mul_div_sinh_mul hP hPa ha hs ht hst
  have hrQ := antitoneOn_sinh_mul_div_sinh_mul hQ hQb hb hs ht hst
  simp only at hrP hrQ
  have hnonneg {u p q : ℝ} (hu : 0 < u) (hp : 0 ≤ p) (hq : 0 < q) :
      0 ≤ Real.sinh (u * p) / Real.sinh (u * q) :=
    div_nonneg (Real.sinh_nonneg_iff.2 (mul_nonneg hu.le hp))
      (Real.sinh_pos_iff.2 (mul_pos hu hq)).le
  have h := mul_le_mul hrP hrQ (hnonneg ht hQ hb) (hnonneg hs hP ha)
  linarith

/-- The model angle only depends on `|c|`. -/
theorem comparisonAngleNegCurvature_abs (κ a b c : ℝ) :
    comparisonAngleNegCurvature κ a b |c| = comparisonAngleNegCurvature κ a b c := by
  unfold comparisonAngleNegCurvature
  split
  · simp only [comparisonAngle, comparisonCosine, sq_abs]
  · have h : Real.cosh (Real.sqrt κ * |c|) = Real.cosh (Real.sqrt κ * c) := by
      rw [← Real.cosh_abs (Real.sqrt κ * c), abs_mul, abs_of_nonneg (Real.sqrt_nonneg κ)]
    rw [h]

/-- A degenerate triangle with `a + b ≤ c` has model angle `π` at every curvature `-κ ≤ 0`. -/
theorem comparisonAngleNegCurvature_eq_pi_of_add_le {κ a b c : ℝ} (hκ : 0 ≤ κ)
    (ha : 0 < a) (hb : 0 < b) (hc : a + b ≤ c) :
    comparisonAngleNegCurvature κ a b c = Real.pi := by
  rcases hκ.eq_or_lt with rfl | hκ
  · rw [comparisonAngleNegCurvature_zero, comparisonAngle, Real.arccos_eq_pi,
      comparisonCosine, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul hc hc (by positivity) (by linarith)]
  · have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
    have hden : 0 < Real.sinh (Real.sqrt κ * a) * Real.sinh (Real.sqrt κ * b) :=
      mul_pos (Real.sinh_pos_iff.2 (mul_pos hs ha)) (Real.sinh_pos_iff.2 (mul_pos hs hb))
    rw [comparisonAngleNegCurvature, ite_eq_right hκ.ne', Real.arccos_eq_pi, div_le_iff₀ hden]
    have hcosh : Real.cosh (Real.sqrt κ * a + Real.sqrt κ * b) ≤
        Real.cosh (Real.sqrt κ * c) := by
      rw [Real.cosh_le_cosh, abs_of_pos (by positivity),
        abs_of_pos (mul_pos hs (by linarith))]
      nlinarith
    rw [Real.cosh_add] at hcosh
    linarith

/-- A degenerate triangle with `0 ≤ c ≤ |a - b|` has model angle `0` at every curvature
`-κ ≤ 0`. -/
theorem comparisonAngleNegCurvature_eq_zero_of_le_abs_sub {κ a b c : ℝ} (hκ : 0 ≤ κ)
    (ha : 0 < a) (hb : 0 < b) (hc0 : 0 ≤ c) (hc : c ≤ |a - b|) :
    comparisonAngleNegCurvature κ a b c = 0 := by
  rcases hκ.eq_or_lt with rfl | hκ
  · rw [comparisonAngleNegCurvature_zero, comparisonAngle, Real.arccos_eq_zero,
      comparisonCosine, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul hc hc hc0 (abs_nonneg _), sq_abs (a - b)]
  · have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
    have hden : 0 < Real.sinh (Real.sqrt κ * a) * Real.sinh (Real.sqrt κ * b) :=
      mul_pos (Real.sinh_pos_iff.2 (mul_pos hs ha)) (Real.sinh_pos_iff.2 (mul_pos hs hb))
    rw [comparisonAngleNegCurvature, ite_eq_right hκ.ne', Real.arccos_eq_zero, le_div_iff₀ hden]
    have hcosh : Real.cosh (Real.sqrt κ * c) ≤
        Real.cosh (Real.sqrt κ * a - Real.sqrt κ * b) := by
      rw [Real.cosh_le_cosh, ← mul_sub, abs_mul, abs_mul, abs_of_pos hs, abs_of_nonneg hc0]
      exact mul_le_mul_of_nonneg_left hc hs.le
    rw [Real.cosh_sub] at hcosh
    linarith

/-- **Monotonicity of the model angle in the curvature.** For `0 ≤ κ ≤ κ'` and positive sides
`a`, `b`, the comparison angle in curvature `-κ'` is at most the one in curvature `-κ`, for every
`c` (no triangle inequality needed). -/
theorem comparisonAngleNegCurvature_le_of_le {κ κ' a b c : ℝ} (hκ : 0 ≤ κ) (hκκ' : κ ≤ κ')
    (ha : 0 < a) (hb : 0 < b) :
    comparisonAngleNegCurvature κ' a b c ≤ comparisonAngleNegCurvature κ a b c := by
  have hκ' : 0 ≤ κ' := hκ.trans hκκ'
  rw [← comparisonAngleNegCurvature_abs κ' a b c, ← comparisonAngleNegCurvature_abs κ a b c]
  have hc : 0 ≤ |c| := abs_nonneg c
  generalize |c| = d at hc ⊢
  by_cases hup : a + b ≤ d
  · rw [comparisonAngleNegCurvature_eq_pi_of_add_le hκ ha hb hup]
    exact (comparisonAngleNegCurvature_mem_Icc _ _ _ _).2
  by_cases hlo : d ≤ |a - b|
  · rw [comparisonAngleNegCurvature_eq_zero_of_le_abs_sub hκ' ha hb hc hlo]
    exact (comparisonAngleNegCurvature_mem_Icc _ _ _ _).1
  rw [not_le] at hup hlo
  rcases hκ.eq_or_lt with rfl | hκpos
  · rw [comparisonAngleNegCurvature_zero]
    exact comparisonAngleNegCurvature_le_comparisonAngle hκ' ha hb hlo.le hup.le
  · have hκ'pos : 0 < κ' := hκpos.trans_le hκκ'
    simp only [comparisonAngleNegCurvature, ite_eq_right hκpos.ne', ite_eq_right hκ'pos.ne']
    exact Real.arccos_le_arccos (hyperbolicCosine_le_of_le (Real.sqrt_pos.2 hκpos)
      (Real.sqrt_le_sqrt hκκ') ha hb hlo.le hup.le)

/-- The model angle with sides `a`, `b > 0` is antitone in `κ` on `[0, ∞)`. -/
theorem antitoneOn_comparisonAngleNegCurvature {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (c : ℝ) :
    AntitoneOn (fun κ => comparisonAngleNegCurvature κ a b c) (Ici 0) :=
  fun _ hκ _ _ hκκ' => comparisonAngleNegCurvature_le_of_le hκ hκκ' ha hb

private theorem comparisonAngleNegCurvature_zero_left (κ b c : ℝ) :
    comparisonAngleNegCurvature κ 0 b c = Real.pi / 2 := by
  unfold comparisonAngleNegCurvature
  split
  · simp [comparisonAngle, comparisonCosine, Real.arccos_zero]
  · simp [Real.arccos_zero]

private theorem comparisonAngleNegCurvature_neg_neg (κ a b c : ℝ) :
    comparisonAngleNegCurvature κ (-a) (-b) c = comparisonAngleNegCurvature κ a b c := by
  unfold comparisonAngleNegCurvature
  split
  · simp only [comparisonAngle, comparisonCosine]
    congr 1
    ring
  · simp only [mul_neg, neg_mul, neg_neg, Real.cosh_neg, Real.sinh_neg]

/-- **Monotonicity of the model angle, sharp form.** The comparison angle is antitone in
`κ ∈ [0, ∞)` whenever `a` and `b` do not have opposite signs; for `a < 0 < b` it fails. -/
theorem comparisonAngleNegCurvature_le_of_le_of_mul_nonneg {κ κ' a b c : ℝ} (hκ : 0 ≤ κ)
    (hκκ' : κ ≤ κ') (hab : 0 ≤ a * b) :
    comparisonAngleNegCurvature κ' a b c ≤ comparisonAngleNegCurvature κ a b c := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [comparisonAngleNegCurvature_zero_left, comparisonAngleNegCurvature_zero_left]
  rcases eq_or_ne b 0 with rfl | hb
  · rw [comparisonAngleNegCurvature_comm κ', comparisonAngleNegCurvature_comm κ,
      comparisonAngleNegCurvature_zero_left, comparisonAngleNegCurvature_zero_left]
  rcases lt_or_gt_of_ne ha with ha | ha
  · have hb' : b < 0 := by
      rcases lt_or_gt_of_ne hb with hb | hb
      · exact hb
      · nlinarith [mul_neg_of_neg_of_pos ha hb]
    rw [← comparisonAngleNegCurvature_neg_neg κ', ← comparisonAngleNegCurvature_neg_neg κ]
    exact comparisonAngleNegCurvature_le_of_le hκ hκκ' (neg_pos.2 ha) (neg_pos.2 hb')
  · have hb' : 0 < b := by
      rcases lt_or_gt_of_ne hb with hb | hb
      · nlinarith [mul_neg_of_pos_of_neg ha hb]
      · exact hb
    exact comparisonAngleNegCurvature_le_of_le hκ hκκ' ha hb'

end DifferentialGeometry.Geometry.Comparison.Toponogov

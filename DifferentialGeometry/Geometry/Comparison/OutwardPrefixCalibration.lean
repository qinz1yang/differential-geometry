import DifferentialGeometry.Geometry.Comparison.AngleShortening
import DifferentialGeometry.Analysis.SpecialFunctions.Trigonometric.HyperbolicEstimates
import DifferentialGeometry.Analysis.SpecialFunctions.Trigonometric.HyperbolicSlope

/-!
# The original center calibrates the outward prefixes (LC69, metric kernel)

Blueprint `master207A.tex`, LC69 (`lem:collapse-original-radial-calibration`, lines 24073–24117).
Let `(q; p, z)` have equal legs `d(q,p) = d(q,z) = D`, comparison angle at `q` above `π - θ`
at curvature `-κ²` with `0 < θ ≤ π/2` and `κ D ≤ 1`, and let four-point comparison at
curvature `-κ²` hold on a set containing `p, q, z, w`, where `w` lies on a minimizing segment
from `q` to `z` at distance `t > 0` from `q`. Then the original center `p` calibrates the
prefix: `0 ≤ D + t - d(p,w) < 2 t (1 - cos θ)`. After multiplying the distance by any `λ > 0`,
the centered radial function `u = λ d(p, ·) - λ d(p, q)` satisfies
`T - 2 T (1 - cos θ) < u(w) ≤ T` with `T = λ t`, with no factor `λ δ` and no upper bound on `λ`.
On an inward prefix of a minimizing segment from `q` to `p` the function `u` equals minus the
normalized prefix length exactly.

The proof is the blueprint's: AC64 shortening of the `z` leg to `t`
(`comparisonAngleNegCurvature_le_of_shortening_right`), the hyperbolic cosine law, `d(p,w) ≥ D`
from the obtuse angle, the tangent-line bound for `cosh` on `[κ d(p,w), κ (D + t)]`, and
`sinh x ≤ x cosh x ≤ 2 x` on `[0, 1]`.
-/

set_option autoImplicit false

open Set Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

/-- The tangent-line lower bound for `cosh` on the nonnegative half-line. -/
theorem sinh_mul_sub_le_cosh_sub_cosh {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    sinh u * (v - u) ≤ cosh v - cosh u := by
  have hv : v = u + (v - u) := by ring
  have hcv : cosh v = cosh u * cosh (v - u) + sinh u * sinh (v - u) := by
    conv_lhs => rw [hv]
    rw [cosh_add]
  have h1 : 0 ≤ cosh u * (cosh (v - u) - 1) :=
    mul_nonneg (cosh_pos u).le (by linarith [one_le_cosh (v - u)])
  have h2 : sinh u * (v - u) ≤ sinh u * sinh (v - u) :=
    mul_le_mul_of_nonneg_left (self_le_sinh_iff.mpr (by linarith)) (sinh_nonneg_iff.mpr hu)
  rw [hcv]
  nlinarith

/-- **LC69 (metric kernel).** The original center calibrates an outward prefix. -/
theorem outward_prefix_calibration {X : Type*} [MetricSpace X] {κ θ : ℝ} (hκ : 0 < κ)
    {Ω : Set X} (hcomp : fourPointComparison (κ ^ 2) Ω) {p q z w : X}
    (hp : p ∈ Ω) (hq : q ∈ Ω) (hz : z ∈ Ω) (hw : w ∈ Ω)
    (hqz : dist q z = dist q p) (hκD : κ * dist q p ≤ 1)
    (hθ : 0 < θ) (hθpi : θ ≤ π / 2)
    (hangle : π - θ < comparisonAngleNegCurvature (κ ^ 2) (dist q p) (dist q z) (dist p z))
    (ht : 0 < dist q w) (hwz : dist q w + dist w z = dist q z) :
    0 ≤ dist q p + dist q w - dist p w ∧
      dist q p + dist q w - dist p w < 2 * dist q w * (1 - cos θ) := by
  set D := dist q p with hD
  set t := dist q w with ht'
  set c := dist p w with hc
  have htD : t ≤ D := by
    have := dist_nonneg (x := w) (y := z)
    linarith
  have hDpos : 0 < D := ht.trans_le htD
  have hpq : p ≠ q := by
    intro h
    rw [h, dist_self] at hD
    linarith
  have htri1 : c ≤ D + t := by
    have h := dist_triangle p q w
    rw [dist_comm p q] at h
    linarith
  have htri2 : |D - t| ≤ c := by
    apply abs_le.mpr
    constructor
    · have h := dist_triangle q p w
      linarith
    · have h := dist_triangle q w p
      rw [dist_comm w p] at h
      linarith
  refine ⟨by linarith, ?_⟩
  -- AC64: shorten the `z` leg to `t`.
  have hsh := comparisonAngleNegCurvature_le_of_shortening_right (sq_nonneg κ) hcomp hq hw hz hp
    ht hpq (by rw [← hwz])
  have hA : π - θ < comparisonAngleNegCurvature (κ ^ 2) D t c := hangle.trans_le hsh
  -- The hyperbolic cosine law.
  have hcos := cos_comparisonAngleNegCurvature_of_pos (pow_pos hκ 2) hDpos ht htri2 htri1
  rw [sqrt_sq hκ.le] at hcos
  have hlt : cos (comparisonAngleNegCurvature (κ ^ 2) D t c) < cos (π - θ) :=
    cos_lt_cos_of_nonneg_of_le_pi (by linarith [pi_pos])
      (comparisonAngleNegCurvature_mem_Icc _ _ _ _).2 hA
  rw [cos_pi_sub, hcos] at hlt
  have hsD : 0 < sinh (κ * D) := sinh_pos_iff.mpr (mul_pos hκ hDpos)
  have hst : 0 < sinh (κ * t) := sinh_pos_iff.mpr (mul_pos hκ ht)
  have hS : 0 < sinh (κ * D) * sinh (κ * t) := mul_pos hsD hst
  rw [div_lt_iff₀ hS] at hlt
  have hcosθ : 0 ≤ cos θ := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hθpi⟩
  have hadd : cosh (κ * (D + t)) = cosh (κ * D) * cosh (κ * t) +
      sinh (κ * D) * sinh (κ * t) := by rw [mul_add, cosh_add]
  have hkey : cosh (κ * (D + t)) - cosh (κ * c) <
      (1 - cos θ) * (sinh (κ * D) * sinh (κ * t)) := by nlinarith
  -- `c > D` from the obtuse angle.
  have hcD : D < c := by
    have h1 : cosh (κ * D) * cosh (κ * t) ≤ cosh (κ * c) := by nlinarith
    have h2 : cosh (κ * D) ≤ cosh (κ * D) * cosh (κ * t) :=
      le_mul_of_one_le_right (cosh_pos _).le (one_le_cosh _)
    have h3 : cosh (κ * D) < cosh (κ * c) ∨ cosh (κ * D) = cosh (κ * c) := lt_or_eq_of_le
      (h2.trans h1)
    by_contra hle
    push Not at hle
    -- Then `c ≤ D`, so the cosine law forces a nonobtuse angle, a contradiction.
    have hc0 : 0 ≤ c := dist_nonneg
    have hcc : cosh (κ * c) ≤ cosh (κ * D) := cosh_le_cosh.mpr (by
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hle hκ.le)
    have hct : 1 < cosh (κ * t) := by
      have := cosh_lt_cosh.mpr (show |(0 : ℝ)| < |κ * t| by
        rw [abs_zero, abs_of_pos (mul_pos hκ ht)]; exact mul_pos hκ ht)
      rwa [cosh_zero] at this
    have hstrict : cosh (κ * D) < cosh (κ * D) * cosh (κ * t) :=
      lt_mul_of_one_lt_right (cosh_pos _) hct
    rcases h3 with h3 | h3 <;> linarith
  -- The tangent-line bound on `[κ c, κ (D + t)]`.
  have htan := sinh_mul_sub_le_cosh_sub_cosh (by positivity : 0 ≤ κ * c)
    (mul_le_mul_of_nonneg_left htri1 hκ.le)
  have hsinh_cD : sinh (κ * D) ≤ sinh (κ * c) :=
    sinh_le_sinh.mpr (mul_le_mul_of_nonneg_left hcD.le hκ.le)
  have hex : 0 ≤ D + t - c := by linarith
  have hlow : sinh (κ * D) * (κ * (D + t - c)) ≤ cosh (κ * (D + t)) - cosh (κ * c) := by
    have : κ * (D + t) - κ * c = κ * (D + t - c) := by ring
    rw [this] at htan
    exact (mul_le_mul_of_nonneg_right hsinh_cD (by positivity)).trans htan
  have hmain : κ * (D + t - c) < (1 - cos θ) * sinh (κ * t) := by
    have h := hlow.trans_lt hkey
    have e : (1 - cos θ) * (sinh (κ * D) * sinh (κ * t)) =
        sinh (κ * D) * ((1 - cos θ) * sinh (κ * t)) := by ring
    have h' : sinh (κ * D) * (κ * (D + t - c)) < sinh (κ * D) * ((1 - cos θ) * sinh (κ * t)) := by
      linarith
    exact lt_of_mul_lt_mul_left h' hsD.le
  -- `sinh x ≤ x cosh x ≤ 2 x` for `0 ≤ x ≤ 1`.
  have hκt1 : κ * t ≤ 1 := (mul_le_mul_of_nonneg_left htD hκ.le).trans hκD
  have hcosh2 : cosh (κ * t) ≤ 2 := by
    have h := cosh_sub_one_le_sq (mul_pos hκ ht).le hκt1
    have hsq : (κ * t) ^ 2 ≤ 1 := by
      have h0 := (mul_pos hκ ht).le
      nlinarith
    linarith
  have hsinh := sinh_le_self_mul_cosh (mul_pos hκ ht).le (le_refl (κ * t))
  have hsinh2 : sinh (κ * t) ≤ κ * (2 * t) := by
    have h := mul_le_mul_of_nonneg_left hcosh2 (mul_pos hκ ht).le
    linarith
  have hfin : κ * (D + t - c) < κ * (2 * t * (1 - cos θ)) := by
    have hcθ1 : 0 ≤ 1 - cos θ := by linarith [cos_le_one θ]
    have := mul_le_mul_of_nonneg_left hsinh2 hcθ1
    nlinarith
  exact lt_of_mul_lt_mul_left hfin hκ.le

/-- **LC69, normalized form.** With `T = λ t` and `u = λ d(p, ·) - λ d(p, q)`:
`T - 2 T (1 - cos θ) < u(w) ≤ T`. -/
theorem outward_prefix_calibration_scaled {X : Type*} [MetricSpace X] {κ θ : ℝ} (hκ : 0 < κ)
    {Ω : Set X} (hcomp : fourPointComparison (κ ^ 2) Ω) {p q z w : X}
    (hp : p ∈ Ω) (hq : q ∈ Ω) (hz : z ∈ Ω) (hw : w ∈ Ω)
    (hqz : dist q z = dist q p) (hκD : κ * dist q p ≤ 1)
    (hθ : 0 < θ) (hθpi : θ ≤ π / 2)
    (hangle : π - θ < comparisonAngleNegCurvature (κ ^ 2) (dist q p) (dist q z) (dist p z))
    (ht : 0 < dist q w) (hwz : dist q w + dist w z = dist q z) {lam : ℝ} (hlam : 0 < lam) :
    lam * dist q w - 2 * (lam * dist q w) * (1 - cos θ) <
        lam * dist p w - lam * dist p q ∧
      lam * dist p w - lam * dist p q ≤ lam * dist q w := by
  obtain ⟨h1, h2⟩ := outward_prefix_calibration hκ hcomp hp hq hz hw hqz hκD hθ hθpi hangle ht
    hwz
  rw [dist_comm q p] at h1 h2
  constructor <;> nlinarith

/-- **LC69, inward prefixes.** On a minimizing segment from `q` to `p`, the centered radial
function decreases by exactly the traversed length. -/
theorem inward_prefix_radial_eq {X : Type*} [MetricSpace X] {p q w : X}
    (hw : dist q w + dist w p = dist q p) (lam : ℝ) :
    lam * dist p w - lam * dist p q = -(lam * dist q w) := by
  rw [dist_comm p w, dist_comm p q, ← hw]
  ring

end DifferentialGeometry.Geometry.Comparison.Toponogov

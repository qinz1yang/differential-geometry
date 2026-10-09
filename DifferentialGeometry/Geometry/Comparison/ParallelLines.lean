import DifferentialGeometry.Geometry.Comparison.CalibratedLine

set_option autoImplicit false

open Set

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X]

theorem lineCoordinate_eq_sub_of_calibrated_line
    (hs : fourPointComparison 0 (univ : Set X)) {γ ℓ : ℝ → X}
    (hγ : Isometry γ) (hℓ : Isometry ℓ)
    (hb : ∀ t, lineCoordinate γ (ℓ t) = lineCoordinate γ (ℓ 0) + t) (x : X) :
    lineCoordinate ℓ x = lineCoordinate γ x - lineCoordinate γ (ℓ 0) := by
  let d := lineCoordinate γ x - lineCoordinate γ (ℓ 0)
  let δ := lineCoordinate ℓ x - d
  let C := dist x (ℓ 0) ^ 2 - d ^ 2
  have hnonneg (t : ℝ) : 0 ≤ C - 2 * t * δ := by
    have hlip := (lipschitzWith_lineCoordinate hs hγ).dist_le_mul x (ℓ t)
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlip
    rw [hb t] at hlip
    have hsq := mul_self_le_mul_self (abs_nonneg _) hlip
    have h := sq_dist_isometry_line hs hℓ x t
    dsimp [C, δ, d]
    nlinarith [sq_abs (lineCoordinate γ x - (lineCoordinate γ (ℓ 0) + t))]
  have hδ : δ = 0 := by
    by_contra h
    have heq : 2 * ((C + 1) / (2 * δ)) * δ = C + 1 := by field_simp
    have hh := hnonneg ((C + 1) / (2 * δ))
    rw [heq] at hh
    linarith
  dsimp [δ, d] at hδ
  linarith

theorem sq_dist_calibrated_line
    (hs : fourPointComparison 0 (univ : Set X)) {γ ℓ : ℝ → X}
    (hγ : Isometry γ) (hℓ : Isometry ℓ)
    (hb : ∀ t, lineCoordinate γ (ℓ t) = lineCoordinate γ (ℓ 0) + t)
    (x : X) (t : ℝ) :
    dist x (ℓ t) ^ 2 = t ^ 2 -
      2 * t * (lineCoordinate γ x - lineCoordinate γ (ℓ 0)) + dist x (ℓ 0) ^ 2 := by
  rw [sq_dist_isometry_line hs hℓ, lineCoordinate_eq_sub_of_calibrated_line hs hγ hℓ hb]

theorem sq_dist_calibrated_lines
    (hs : fourPointComparison 0 (univ : Set X)) {γ ℓ k : ℝ → X}
    (hγ : Isometry γ) (hℓ : Isometry ℓ) (hk : Isometry k)
    (hℓb : ∀ t, lineCoordinate γ (ℓ t) = lineCoordinate γ (ℓ 0) + t)
    (hkb : ∀ t, lineCoordinate γ (k t) = lineCoordinate γ (k 0) + t)
    (s t : ℝ) :
    dist (ℓ s) (k t) ^ 2 =
      (lineCoordinate γ (ℓ 0) + s - lineCoordinate γ (k 0) - t) ^ 2 +
      dist (ℓ 0) (k 0) ^ 2 - (lineCoordinate γ (ℓ 0) - lineCoordinate γ (k 0)) ^ 2 := by
  have h₁ := sq_dist_calibrated_line hs hγ hk hkb (ℓ s) t
  have h₂ := sq_dist_calibrated_line hs hγ hℓ hℓb (k 0) s
  rw [hℓb s] at h₁
  rw [dist_comm (k 0) (ℓ s), dist_comm (k 0) (ℓ 0)] at h₂
  nlinarith

theorem calibrated_line_unique
    (hs : fourPointComparison 0 (univ : Set X)) {γ ℓ k : ℝ → X}
    (hγ : Isometry γ) (hℓ : Isometry ℓ) (hk : Isometry k)
    (hℓb : ∀ t, lineCoordinate γ (ℓ t) = lineCoordinate γ (ℓ 0) + t)
    (hkb : ∀ t, lineCoordinate γ (k t) = lineCoordinate γ (k 0) + t)
    (hzero : ℓ 0 = k 0) : ℓ = k := by
  funext t
  apply dist_eq_zero.mp
  have h := sq_dist_calibrated_lines hs hγ hℓ hk hℓb hkb t t
  rw [hzero, dist_self] at h
  nlinarith [dist_nonneg (x := ℓ t) (y := k t)]

end DifferentialGeometry.Geometry.Comparison.Toponogov

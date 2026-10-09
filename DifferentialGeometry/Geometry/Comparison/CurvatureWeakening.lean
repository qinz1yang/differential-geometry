import DifferentialGeometry.Analysis.Convex.Hyperbolic
import DifferentialGeometry.Geometry.Comparison.FourPoint

set_option autoImplicit false

open Set

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

private theorem hyperbolic_cosine_ge_euclidean {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hlower : |a - b| ≤ c) (hupper : c ≤ a + b) :
    (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) ≤
      (Real.cosh a * Real.cosh b - Real.cosh c) / (Real.sinh a * Real.sinh b) := by
  let v := (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b)
  have hv : v ∈ Icc (-1 : ℝ) 1 := comparison_cosine_mem_Icc ha hb hlower hupper
  have hc : 0 ≤ c := (abs_nonneg _).trans hlower
  have hconv := Real.convexOn_cosh_sqrt.2 (sq_nonneg (a - b)) (sq_nonneg (a + b))
    (show 0 ≤ (1 + v) / 2 by linarith [hv.1])
    (show 0 ≤ (1 - v) / 2 by linarith [hv.2])
    (show (1 + v) / 2 + (1 - v) / 2 = 1 by ring)
  simp only [smul_eq_mul] at hconv
  have harg : (1 + v) / 2 * (a - b) ^ 2 + (1 - v) / 2 * (a + b) ^ 2 = c ^ 2 := by
    dsimp [v]
    field_simp
    ring
  rw [harg, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
    abs_of_nonneg hc, Real.cosh_abs, Real.cosh_abs, Real.cosh_sub, Real.cosh_add] at hconv
  have hden : 0 < Real.sinh a * Real.sinh b :=
    mul_pos (Real.sinh_pos_iff.mpr ha) (Real.sinh_pos_iff.mpr hb)
  change v ≤ _
  rw [le_div_iff₀ hden]
  nlinarith

theorem comparisonAngleNegCurvature_le_comparisonAngle {κ a b c : ℝ}
    (hκ : 0 ≤ κ) (ha : 0 < a) (hb : 0 < b)
    (hlower : |a - b| ≤ c) (hupper : c ≤ a + b) :
    comparisonAngleNegCurvature κ a b c ≤ comparisonAngle a b c := by
  by_cases hk : κ = 0
  · simp [hk]
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.mpr (lt_of_le_of_ne hκ (Ne.symm hk))
  have hlo : |Real.sqrt κ * a - Real.sqrt κ * b| ≤ Real.sqrt κ * c := by
    rw [← mul_sub, abs_mul, abs_of_pos hs]
    exact mul_le_mul_of_nonneg_left hlower hs.le
  have hup : Real.sqrt κ * c ≤ Real.sqrt κ * a + Real.sqrt κ * b := by
    simpa [mul_add] using mul_le_mul_of_nonneg_left hupper hs.le
  have hcos := hyperbolic_cosine_ge_euclidean (mul_pos hs ha) (mul_pos hs hb) hlo hup
  have hangle := Real.arccos_le_arccos hcos
  change Real.arccos _ ≤ comparisonAngle (Real.sqrt κ * a) (Real.sqrt κ * b)
    (Real.sqrt κ * c) at hangle
  rw [comparisonAngle_scale a b c hs] at hangle
  simpa only [comparisonAngleNegCurvature, ite_eq_right hk] using hangle

theorem fourPointComparison.of_zero {X : Type*} [MetricSpace X] {s : Set X}
    (h : fourPointComparison 0 s) {κ : ℝ} (hκ : 0 ≤ κ) : fourPointComparison κ s := by
  intro x hx a ha b hb c hc hax hbx hcx
  have hangle (u v : X) (hu : u ≠ x) (hv : v ≠ x) :
      comparisonAngleNegCurvature κ (dist x u) (dist x v) (dist u v) ≤
        comparisonAngle (dist x u) (dist x v) (dist u v) := by
    apply comparisonAngleNegCurvature_le_comparisonAngle hκ
      (dist_pos.mpr hu.symm) (dist_pos.mpr hv.symm)
    · simpa only [dist_comm x u, dist_comm x v] using abs_dist_sub_le u v x
    · simpa only [dist_comm u x] using dist_triangle u x v
  have hh := h x hx a ha b hb c hc hax hbx hcx
  simp only [comparisonAngleNegCurvature_zero] at hh
  linarith [hangle a b hax hbx, hangle b c hbx hcx, hangle c a hcx hax]

end DifferentialGeometry.Geometry.Comparison.Toponogov

import DifferentialGeometry.Geometry.Comparison.EqualRadiusStrainerMargin
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

private theorem norm_opposite_signed_axes {k : ℕ} (j : Fin k) :
    ‖(PiLp.single 2 j (1 : ℝ) : EuclideanSpace ℝ (Fin k)) - PiLp.single 2 j (-1)‖ = 2 := by
  rw [← PiLp.single_sub, PiLp.norm_single]
  norm_num

private theorem norm_different_signed_axes {k : ℕ} {j l : Fin k} (hjl : j ≠ l) (b c : Bool) :
    ‖(PiLp.single 2 j (if b then (1 : ℝ) else -1) : EuclideanSpace ℝ (Fin k)) -
      PiLp.single 2 l (if c then (1 : ℝ) else -1)‖ = Real.sqrt 2 := by
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg 2)).mp
  rw [Real.sq_sqrt (by norm_num)]
  cases b <;> cases c <;>
    norm_num [norm_sub_sq_real, EuclideanSpace.inner_single_left, hjl, hjl.symm]

theorem equal_radius_strainer_angles_of_chord_errors
    {X : Type*} [MetricSpace X] {k : ℕ} {p : X} {r α D : ℝ}
    (hr : 0 < r) (hα : 0 < α) (hαone : α ≤ 1)
    (a : Fin k × Bool → X) (hrad : ∀ v, dist p (a v) = r)
    (hD : D < equalRadiusStrainerMargin r α)
    (herror : ∀ v w, |dist (a v) (a w) - r *
      ‖(PiLp.single 2 v.1 (if v.2 then (1 : ℝ) else -1) : EuclideanSpace ℝ (Fin k)) -
        PiLp.single 2 w.1 (if w.2 then (1 : ℝ) else -1)‖| ≤ D) :
    (∀ j, Real.pi - α < metricComparisonAngle (a (j, true)) p (a (j, false))) ∧
    (∀ j l, j ≠ l → ∀ b c : Bool,
      Real.pi / 2 - α < metricComparisonAngle (a (j, b)) p (a (l, c))) ∧
    Function.Injective a ∧ ∀ v, a v ≠ p := by
  have hupper (v w : Fin k × Bool) : dist (a v) (a w) ≤ 2 * r := by
    have hh := dist_triangle (a v) p (a w)
    rw [dist_comm (a v) p, hrad, hrad] at hh
    linarith
  have hopp (j : Fin k) : 0 < dist (a (j, true)) (a (j, false)) ∧
      Real.pi - α < metricComparisonAngle (a (j, true)) p (a (j, false)) := by
    have hh := opposite_angle_of_equal_radius_chord_error hr hα hαone dist_nonneg
      (hupper (j, true) (j, false)) hD
      (by simpa only [Bool.false_eq_true, ↓reduceIte, norm_opposite_signed_axes, mul_comm r 2] using
        herror (j, true) (j, false))
    simpa only [metricComparisonAngle, hrad] using hh
  have hcross (j l : Fin k) (hjl : j ≠ l) (b c : Bool) :
      0 < dist (a (j, b)) (a (l, c)) ∧
      Real.pi / 2 - α < metricComparisonAngle (a (j, b)) p (a (l, c)) := by
    have hh := cross_angle_of_equal_radius_chord_error hr hα hαone dist_nonneg
      (hupper (j, b) (l, c)) hD
      (by simpa only [norm_different_signed_axes hjl b c, mul_comm r (Real.sqrt 2)] using
        herror (j, b) (l, c))
    simpa only [metricComparisonAngle, hrad] using hh
  refine ⟨fun j => (hopp j).2, fun j l hjl b c => (hcross j l hjl b c).2, ?_, ?_⟩
  · rintro ⟨j, b⟩ ⟨l, c⟩ hac
    by_cases hjl : j = l
    · subst l
      by_cases hbc : b = c
      · subst c
        rfl
      · cases b <;> cases c
        · exact False.elim (hbc rfl)
        · exact False.elim ((dist_pos.mp (hopp j).1).symm hac)
        · exact False.elim ((dist_pos.mp (hopp j).1) hac)
        · exact False.elim (hbc rfl)
    · exact False.elim ((dist_pos.mp (hcross j l hjl b c).1) hac)
  · intro v hav
    have hh := hrad v
    rw [hav, dist_self] at hh
    linarith

end GC.MetricGeometry

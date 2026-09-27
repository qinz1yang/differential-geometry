import Mathlib.Analysis.Calculus.ContDiff.Defs

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

theorem normalChristoffelFirstJet_repeated
    (A : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] F)
    (hsymm : ∀ x y z, A x y z = A x z y)
    (hdiag : ∀ x, A x x x = 0)
    (a b : E) :
    A a a b = -(1 / 3 : ℝ) • (A b a a - A a b a) := by
  have hp := hdiag (a + b)
  have hm := hdiag (a - b)
  have ha := hdiag a
  have hb := hdiag b
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply] at hp hm
  rw [hsymm a b a] at hp hm
  rw [hsymm b b a] at hp hm
  have htwice : (2 : ℝ) • ((2 : ℝ) • A a a b + A b a a) = 0 := by
    linear_combination (norm := module) hp - hm - hb - hb
  have hsum : (2 : ℝ) • A a a b + A b a a = 0 :=
    (smul_eq_zero.mp htwice).resolve_left two_ne_zero
  have hY : A b a a = -(2 : ℝ) • A a a b := by
    linear_combination (norm := module) hsum
  rw [hsymm a b a]
  rw [hY]
  module

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

import DifferentialGeometry.Geometry.Curvature.Algebraic.Form

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Curvature.IsAlgCurvForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  {A : V → V → V → V → ℝ}

private theorem smul_second (hA : IsAlgCurvForm A) (a : ℝ) (u v w z : V) :
    A u (a • v) w z = a * A u v w z := by
  rw [hA.anti_first u, hA.smul_left, hA.anti_first v]
  ring

private theorem smul_third (hA : IsAlgCurvForm A) (a : ℝ) (u v w z : V) :
    A u v (a • w) z = a * A u v w z := by
  rw [hA.pair_swap u v, hA.smul_left, hA.pair_swap w z]

private theorem sectional_sub_smul (hA : IsAlgCurvForm A) (u v : V) (a : ℝ) :
    A u (v - a • u) (v - a • u) u = A u v v u := by
  have hfirst (w z : V) : A u u w z = 0 := by
    have h := hA.anti_first u u w z
    linarith
  have hlast (w z : V) : A w z u u = 0 := by
    have h := hA.anti_last w z u u
    linarith
  simp only [sub_eq_add_neg, ← neg_smul, hA.add_two, hA.add_three,
    smul_second hA, smul_third hA, hfirst, hlast, mul_zero, add_zero]

theorem sectional_lower_bound_of_orthogonal
    (hA : IsAlgCurvForm A) (G g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hGpos : ∀ u, u ≠ 0 → 0 < G u u)
    (hgsym : ∀ u v, g u v = g v u) {c : ℝ}
    (h : ∀ u v, G u v = 0 →
      c * (g u u * g v v - (g u v) ^ 2) ≤ A u v v u) :
    ∀ u v, c * (g u u * g v v - (g u v) ^ 2) ≤ A u v v u := by
  intro u v
  by_cases hu : u = 0
  · subst u
    exact h 0 v (by simp)
  · let a : ℝ := G u v / G u u
    let w : V := v - a • u
    have horth : G u w = 0 := by
      dsimp only [w, a]
      simp only [map_sub, map_smul, smul_eq_mul,
        div_mul_cancel₀ _ (hGpos u hu).ne', sub_self]
    have hgram : g u u * g w w - (g u w) ^ 2 =
        g u u * g v v - (g u v) ^ 2 := by
      dsimp only [w]
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
        smul_eq_mul, hgsym v u]
      ring
    have hcurv : A u w w u = A u v v u := sectional_sub_smul hA u v a
    simpa only [hgram, hcurv] using h u w horth

end DifferentialGeometry.Geometry.Curvature.IsAlgCurvForm

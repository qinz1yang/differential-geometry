import DifferentialGeometry.Geometry.Comparison.FiniteRadialComparison

set_option autoImplicit false

open Set Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem dist_radial_points_lower_including_zero_arms
    {X : Type*} [MetricSpace X] {Ω : Set X} (hcomp : fourPointComparison 1 Ω)
    {q x y u v : X} (hq : q ∈ Ω) (hx : x ∈ Ω) (hy : y ∈ Ω) (hu : u ∈ Ω) (hv : v ∈ Ω)
    {D t : ℝ} (hD : 0 < D) (hrD : dist q x ≤ D) (hsD : dist q y ≤ D)
    (ht : t ∈ Ioo 0 1)
    (hqu : dist q u = t * dist q x) (hux : dist u x = (1 - t) * dist q x)
    (hqv : dist q v = t * dist q y) (hvy : dist v y = (1 - t) * dist q y) :
    (t * D / sinh D) * dist x y ≤ dist u v := by
  have hcoef : t * D / sinh D ≤ t := by
    apply (div_le_iff₀ (sinh_pos_iff.mpr hD)).mpr
    exact mul_le_mul_of_nonneg_left (self_le_sinh_iff.mpr hD.le) ht.1.le
  by_cases hqx : q = x
  · subst x
    have huq : u = q := by
      have hz : dist q u = 0 := by simpa only [dist_self, mul_zero] using hqu
      exact (dist_eq_zero.mp hz).symm
    subst u
    rw [hqv]
    exact mul_le_mul_of_nonneg_right hcoef dist_nonneg
  by_cases hqy : q = y
  · subst y
    have hvq : v = q := by
      have hz : dist q v = 0 := by simpa only [dist_self, mul_zero] using hqv
      exact (dist_eq_zero.mp hz).symm
    subst v
    rw [dist_comm x q, dist_comm u q, hqu]
    exact mul_le_mul_of_nonneg_right hcoef dist_nonneg
  exact dist_radial_points_lower_of_fourPointComparison hcomp hq hx hy hu hv
    (dist_pos.mpr hqx) (dist_pos.mpr hqy) hrD hsD ht hqu hux hqv hvy

end DifferentialGeometry.Geometry.Comparison.Toponogov

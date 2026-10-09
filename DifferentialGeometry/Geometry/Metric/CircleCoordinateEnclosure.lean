import DifferentialGeometry.Geometry.Metric.L2Product
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Original two-stratum enlargement lies in its comparison ball (TCP01, last clause)

Blueprint `master207B.tex`, TCP01 (`lem:fibration-first-comparison-list`, lines 5250–5309): LFR07's
original residual bound and value error `< 1/10` give `d(p_i, q)/R_i < √((8 + 1/10)² + 1) + 1/10 < 10`
whenever `|η_i(q)| ≤ 8`. Kernel form, in `R_i` units: a product map `F = (u, v)` to
`ℝ² × Y` based at `p` (`u p = 0`), with distortion `< 1/10` between `q` and `p`, residual distance at most
`1` and smooth coordinate within `1/10` of `u` at `q`.
-/

set_option autoImplicit false

namespace GC.MetricGeometry

theorem dist_lt_ten_of_circle_coordinate {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (F : X → WithLp 2 (EuclideanSpace ℝ (Fin 2) × Y)) (η : X → EuclideanSpace ℝ (Fin 2))
    {p q : X} (hp : (F p).fst = 0)
    (hdist : |dist (F q) (F p) - dist q p| < 1 / 10)
    (hres : dist (F q).snd (F p).snd ≤ 1) (hval : ‖η q - (F q).fst‖ < 1 / 10)
    (hq : ‖η q‖ ≤ 8) : dist q p < 10 := by
  have hsq := WithLp.prod_dist_sq_eq_add_sq (F q) (F p)
  rw [hp, dist_zero_right] at hsq
  have hfst : ‖(F q).fst‖ < 8 + 1 / 10 := by
    have h := norm_sub_norm_le (F q).fst (η q)
    rw [norm_sub_rev] at h
    linarith
  have h1 : dist (F q) (F p) ^ 2 < 81 := by
    have hres2 : dist (F q).snd (F p).snd ^ 2 ≤ 1 := by
      nlinarith [dist_nonneg (x := (F q).snd) (y := (F p).snd)]
    have hfst2 : ‖(F q).fst‖ ^ 2 < (8 + 1 / 10) ^ 2 :=
      pow_lt_pow_left₀ hfst (norm_nonneg _) (by norm_num)
    nlinarith
  have h2 : dist (F q) (F p) < 9 := by
    nlinarith [dist_nonneg (x := F q) (y := F p)]
  linarith [(abs_lt.mp hdist).1]

end GC.MetricGeometry

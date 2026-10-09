import DifferentialGeometry.Geometry.Metric.EuclideanCone

set_option autoImplicit false

open Set Metric
open scoped NNReal

namespace Metric.EuclideanCone

theorem exists_angular_midpoint_of_cone_midpoint
    {Y : Type*} [MetricSpace Y] {a b : Y} (hab : dist a b < Real.pi)
    (z : EuclideanCone Y)
    (ha : dist (mk 1 a) z = dist (mk 1 a) (mk 1 b) / 2)
    (hb : dist (mk 1 b) z = dist (mk 1 a) (mk 1 b) / 2) :
    0 < radius z ∧ ∃ u : Y,
      z = mk ⟨radius z, radius_nonneg z⟩ u ∧
      dist a u = dist a b / 2 ∧ dist b u = dist a b / 2 := by
  let d := dist a b
  let D := dist (mk 1 a) (mk 1 b)
  have hd : 0 ≤ d := dist_nonneg
  have hdpi : d < Real.pi := hab
  have hD : 0 ≤ D := dist_nonneg
  have hDsq : D ^ 2 = 2 - 2 * Real.cos d := by
    dsimp [D]
    rw [dist_mk, coneDistance_sq (by norm_num) (by norm_num)]
    simp only [NNReal.coe_one, one_pow, min_eq_right hab.le]
    dsimp [d]
    ring
  have hcos : -1 < Real.cos d := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi hd (le_refl Real.pi) hdpi
    simpa only [Real.cos_pi] using h
  have hDlt : D < 2 := by nlinarith
  have hrad : 0 < radius z := by
    have h := dist_triangle (mk 1 a) z tip
    rw [dist_tip, radius_mk, NNReal.coe_one, dist_tip, ha] at h
    change (1 : ℝ) ≤ D / 2 + radius z at h
    linarith
  refine ⟨hrad, ?_⟩
  have hz : z ≠ tip := by
    intro h
    rw [h, radius_tip] at hrad
    exact hrad.false
  obtain ⟨r, u, hr, hzu⟩ := (eq_tip_or_eq_mk z).resolve_left hz
  have hrpos : 0 < (r : ℝ) := hr
  have hang (x : Y) (hx : dist (mk 1 x) z = D / 2) : dist x u ≤ d / 2 := by
    let α := min Real.pi (dist x u)
    have hα : α ∈ Icc (0 : ℝ) Real.pi :=
      ⟨le_min Real.pi_pos.le dist_nonneg, min_le_left _ _⟩
    have hh : d / 2 ∈ Icc (0 : ℝ) Real.pi := ⟨by positivity, by linarith [Real.pi_pos]⟩
    have hs := coneDistance_sq (x := ((1 : ℝ), x)) (y := ((r : ℝ), u))
      (by norm_num) r.property
    have hdist : coneDistance ((1 : ℝ), x) ((r : ℝ), u) = D / 2 := by
      simpa only [hzu, dist_mk, NNReal.coe_one] using hx
    rw [hdist] at hs
    change (D / 2) ^ 2 = 1 ^ 2 + (r : ℝ) ^ 2 - 2 * 1 * r * Real.cos α at hs
    have hdouble := Real.cos_two_mul (d / 2)
    rw [show 2 * (d / 2) = d by ring] at hdouble
    have hc : Real.cos (d / 2) ≤ Real.cos α := by
      nlinarith [sq_nonneg ((r : ℝ) - Real.cos (d / 2))]
    have hαhalf : α ≤ d / 2 := (Real.strictAntiOn_cos.le_iff_ge hh hα).mp hc
    by_contra hxu
    have hdist : d / 2 < dist x u := lt_of_not_ge hxu
    have hlt : d / 2 < α := lt_min (by linarith [Real.pi_pos]) hdist
    linarith
  have hau := hang a ha
  have hbu := hang b hb
  have ht := dist_triangle a u b
  rw [dist_comm u b] at ht
  refine ⟨u, ?_, ?_, ?_⟩
  · exact hzu.trans (congrArg (fun s : ℝ≥0 => mk s u)
      (Subtype.ext ((congrArg radius hzu).trans (radius_mk r u)).symm))
  · change dist a u = d / 2
    dsimp [d] at *
    linarith
  · change dist b u = d / 2
    dsimp [d] at *
    linarith

end Metric.EuclideanCone

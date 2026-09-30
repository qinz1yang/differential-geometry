import DifferentialGeometry.Geometry.Metric.Approximation.StrongEdgePoint
import DifferentialGeometry.Geometry.Metric.Approximation.IsometricKleinerLottApproximation
import DifferentialGeometry.Geometry.Metric.L2Product
import Mathlib.Tactic.Linter

set_option autoImplicit false
open Set Metric GC.MetricGeometry

private abbrev Interval := Icc (0 : ℝ) 501
private def intervalOrigin : Interval := ⟨0, by norm_num⟩
private noncomputable def intervalMark : Interval := ⟨1 / 8, by norm_num⟩
private def rayOrigin : Ici (0 : ℝ) := ⟨0, by norm_num⟩
private noncomputable def rayMark : Ici (0 : ℝ) := ⟨1 / 8, by norm_num⟩

example :
    let X := WithLp 2 (ℝ × Interval)
    let a : X := WithLp.toLp 2 ((2 : ℝ), intervalOrigin)
    let : MetricSpace X := (inferInstance : MetricSpace X).rescale (3 / 2) (by norm_num)
    isEdgePoint.{0, 0} a 1 (1 / 1000) (1 / 1000) := by
  let X := WithLp 2 (ℝ × Interval)
  let p : X := WithLp.toLp 2 ((0 : ℝ), intervalMark)
  let a : X := WithLp.toLp 2 ((2 : ℝ), intervalOrigin)
  let F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), intervalMark)) (1 / 10^8) :=
    (IsometryEquiv.refl X).toKleinerLottApprox rfl (by norm_num) (by norm_num)
  let G : KleinerLottApprox intervalMark intervalMark (1 / 10^7) :=
    (IsometryEquiv.refl Interval).toKleinerLottApprox rfl (by norm_num) (by norm_num)
  have ha : dist a p ≤ 13 * (1 : ℝ) := by
    let mid : X := WithLp.toLp 2 ((0 : ℝ), intervalOrigin)
    have h1 : dist a mid = dist (2 : ℝ) 0 :=
      (WithLp.isometry_prodMk_right (E := ℝ) intervalOrigin).dist_eq 2 0
    have h2 : dist mid p = dist intervalOrigin intervalMark :=
      (WithLp.isometry_prodMk_left (Y := Interval) (0 : ℝ)).dist_eq intervalOrigin intervalMark
    have hh := dist_triangle a mid p
    rw [h1, h2] at hh
    norm_num [intervalOrigin, intervalMark, Subtype.dist_eq, Real.dist_eq] at hh ⊢
    linarith only [hh]
  exact isEdgePoint_of_marked_interval_model (βE := 1 / 1000) (s := 1 / 1000)
    (c := 3 / 2) (e := 1 / 10^6) (θ := 1 / 10^6) F G
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ha (by norm_num [intervalMark]) (by norm_num) (by norm_num)
    (by change (0 : ℝ) ≤ 2 * (1 / 10^6) + 1 / 10^6; norm_num)

example :
    let X := WithLp 2 (ℝ × Ici (0 : ℝ))
    let a : X := WithLp.toLp 2 ((2 : ℝ), rayOrigin)
    let : MetricSpace X := (inferInstance : MetricSpace X).rescale (3 / 2) (by norm_num)
    isEdgePoint.{0, 0} a 1 (1 / 1000) (1 / 1000) := by
  let X := WithLp 2 (ℝ × Ici (0 : ℝ))
  let p : X := WithLp.toLp 2 ((0 : ℝ), rayMark)
  let a : X := WithLp.toLp 2 ((2 : ℝ), rayOrigin)
  let F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), rayMark)) (1 / 10^8) :=
    (IsometryEquiv.refl X).toKleinerLottApprox rfl (by norm_num) (by norm_num)
  let G : KleinerLottApprox rayMark rayMark (1 / 10^7) :=
    (IsometryEquiv.refl (Ici (0 : ℝ))).toKleinerLottApprox rfl (by norm_num) (by norm_num)
  have ha : dist a p ≤ 13 * (1 : ℝ) := by
    let mid : X := WithLp.toLp 2 ((0 : ℝ), rayOrigin)
    have h1 : dist a mid = dist (2 : ℝ) 0 :=
      (WithLp.isometry_prodMk_right (E := ℝ) rayOrigin).dist_eq 2 0
    have h2 : dist mid p = dist rayOrigin rayMark :=
      (WithLp.isometry_prodMk_left (Y := Ici (0 : ℝ)) (0 : ℝ)).dist_eq rayOrigin rayMark
    have hh := dist_triangle a mid p
    rw [h1, h2] at hh
    norm_num [rayOrigin, rayMark, Subtype.dist_eq, Real.dist_eq] at hh ⊢
    linarith only [hh]
  exact isEdgePoint_of_ray_model (βE := 1 / 1000) (s := 1 / 1000)
    (c := 3 / 2) (e := 1 / 10^6) (θ := 1 / 10^6) F G
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ha (by norm_num [rayMark]) (by norm_num) (by norm_num)
    (by change (0 : ℝ) ≤ 2 * (1 / 10^6) + 1 / 10^6; norm_num)


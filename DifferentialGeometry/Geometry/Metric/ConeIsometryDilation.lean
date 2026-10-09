import DifferentialGeometry.Geometry.Metric.EuclideanCone
import Mathlib.Analysis.InnerProductSpace.Basic

set_option autoImplicit false

open Metric
open scoped NNReal

namespace Metric.EuclideanCone

variable {Y : Type*} [MetricSpace Y]

theorem dist_dilate_self (c : ℝ≥0) (x : EuclideanCone Y) :
    dist (dilate c x) x = |(c : ℝ) - 1| * radius x := by
  rcases eq_tip_or_eq_mk x with rfl | ⟨r, u, _, rfl⟩
  · simp
  · rw [dilate_mk, dist_mk, coneDistance_same_direction, radius_mk, NNReal.coe_mul]
    rw [show (c : ℝ) * r - r = ((c : ℝ) - 1) * r by ring,
      abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (r : ℝ) from r.property)]

theorem map_dilate_of_isometry
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : EuclideanCone Y → E} (hf : Isometry f) (hzero : f tip = 0)
    (c : ℝ≥0) (x : EuclideanCone Y) :
    f (dilate c x) = (c : ℝ) • f x := by
  have hn (z : EuclideanCone Y) : ‖f z‖ = radius z := by
    simpa only [hzero, dist_zero_right, dist_tip] using hf.dist_eq z tip
  have hdist : ‖f (dilate c x) - f x‖ = |(c : ℝ) - 1| * radius x := by
    simpa only [dist_eq_norm, dist_dilate_self] using hf.dist_eq (dilate c x) x
  have hinner : inner ℝ (f (dilate c x)) (f x) = (c : ℝ) * radius x ^ 2 := by
    have h := norm_sub_sq_real (f (dilate c x)) (f x)
    rw [hdist, hn, hn, radius_dilate] at h
    simp only [mul_pow, sq_abs] at h
    nlinarith
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have h := norm_sub_sq_real (f (dilate c x)) ((c : ℝ) • f x)
  rw [hn, radius_dilate, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (show (0 : ℝ) ≤ (c : ℝ) from c.property), hn, inner_smul_right, hinner] at h
  have hz : ‖f (dilate c x) - (c : ℝ) • f x‖ ^ 2 = 0 := by nlinarith [h]
  exact (sq_eq_zero_iff.mp hz)

theorem symm_map_smul_of_isometryEquiv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : EuclideanCone Y ≃ᵢ E) (hzero : e tip = 0)
    (c : ℝ≥0) (v : E) :
    e.symm ((c : ℝ) • v) = dilate c (e.symm v) := by
  apply e.injective
  rw [e.apply_symm_apply, map_dilate_of_isometry e.isometry hzero,
    e.apply_symm_apply]

end Metric.EuclideanCone

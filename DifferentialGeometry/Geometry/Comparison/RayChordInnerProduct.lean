import DifferentialGeometry.Geometry.Comparison.RayChord
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-!
# Ray chords in a real inner product space

The concrete consumer of `RayChord` (Tits-cone tier T1). A real inner product space `V` satisfies
`fourPointComparison 0 univ` (`fourPointComparison_zero_of_innerProductSpace`): the Euclidean
comparison angle is the angle of the difference vectors (`metricComparisonAngle_eq_angle_sub`), and
three angles at a point sum to at most `2π` by the triangle inequality for angles.

For unit vectors `v, w` the maps `t ↦ q + t • v` are rays from `q` (`isometry_lineRay`). Applying
the general results of `RayChord` to them:
* the limit chord is `‖v - w‖` (`rayChordLimit_lineRay`, through `tendsto_dist_div_rayChordLimit`);
* I3 returns the Euclidean cosine law `‖a v - b w‖ = √((a - b)² + a b ‖v - w‖²)`
  (`norm_smul_sub_smul_eq_sqrt`);
* the limit angle `arccos (1 - ρ∞² / 2)` is the actual angle `∠(v, w)`
  (`tendsto_metricComparisonAngle_lineRay`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter InnerProductGeometry
open scoped NNReal Topology

namespace GC.MetricGeometry

open DifferentialGeometry.Geometry.Comparison.Toponogov

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- In a real inner product space the Euclidean comparison angle at `o` is the angle between
`x - o` and `y - o`. -/
theorem metricComparisonAngle_eq_angle_sub (x o y : V) :
    metricComparisonAngle x o y = angle (x - o) (y - o) := by
  rw [metricComparisonAngle, comparisonAngle, comparisonCosine, angle,
    real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
    sub_sub_sub_cancel_right, dist_comm o x, dist_comm o y, dist_eq_norm, dist_eq_norm,
    dist_eq_norm]
  congr 1
  ring

/-- A real inner product space satisfies the four-point comparison at curvature `0`. -/
theorem fourPointComparison_zero_of_innerProductSpace : fourPointComparison 0 (univ : Set V) := by
  rintro x - a - b - c - - - -
  simp only [comparisonAngleNegCurvature_zero]
  have hab := metricComparisonAngle_eq_angle_sub a x b
  have hbc := metricComparisonAngle_eq_angle_sub b x c
  have hca := metricComparisonAngle_eq_angle_sub c x a
  simp only [metricComparisonAngle] at hab hbc hca
  rw [hab, hbc, hca]
  have h := angle_le_angle_add_angle (a - x) (-(c - x)) (b - x)
  rw [angle_neg_right, angle_neg_left] at h
  have h1 := angle_comm (b - x) (c - x)
  have h2 := angle_comm (c - x) (a - x)
  linarith

/-- For a unit vector `v`, `t ↦ q + t • v` is a ray from `q`. -/
theorem isometry_lineRay (q v : V) (hv : ‖v‖ = 1) :
    Isometry (fun t : ℝ≥0 => q + (t : ℝ) • v) ∧ (fun t : ℝ≥0 => q + (t : ℝ) • v) 0 = q := by
  refine ⟨Isometry.of_dist_eq fun s t => ?_, by simp⟩
  rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, hv, mul_one, Real.norm_eq_abs,
    NNReal.dist_eq]

/-- The limit chord of two rays `t ↦ q + t • v`, `t ↦ q + t • w` is `‖v - w‖`. -/
theorem rayChordLimit_lineRay (q v w : V) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    rayChordLimit (fun t : ℝ≥0 => q + (t : ℝ) • v) (fun t : ℝ≥0 => q + (t : ℝ) • w) =
      ‖v - w‖ := by
  refine tendsto_nhds_unique (tendsto_dist_div_rayChordLimit
    fourPointComparison_zero_of_innerProductSpace (isometry_lineRay q v hv)
    (isometry_lineRay q w hw)) (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_gt_atTop 0] with t ht
  have htR : (0 : ℝ) < t := ht
  change ‖v - w‖ = dist (q + (t : ℝ) • v) (q + (t : ℝ) • w) / t
  rw [dist_add_left, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos htR,
    mul_div_cancel_left₀ _ htR.ne']

/-- I3 applied to two rays of an inner product space is the Euclidean cosine law. -/
theorem norm_smul_sub_smul_eq_sqrt (v w : V) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (a b : ℝ≥0) :
    ‖(a : ℝ) • v - (b : ℝ) • w‖ = Real.sqrt (((a : ℝ) - b) ^ 2 + a * b * ‖v - w‖ ^ 2) := by
  have hI3 := tendsto_dist_mul_div_of_ray fourPointComparison_zero_of_innerProductSpace
    (isometry_lineRay 0 v hv) (isometry_lineRay 0 w hw) a b
  rw [rayChordLimit_lineRay 0 v w hv hw] at hI3
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hI3
  filter_upwards [eventually_gt_atTop 0] with t ht
  have htR : (0 : ℝ) < t := ht
  change ‖(a : ℝ) • v - (b : ℝ) • w‖ =
    dist (0 + ((a * t : ℝ≥0) : ℝ) • v) (0 + ((b * t : ℝ≥0) : ℝ) • w) / t
  rw [dist_add_left, dist_eq_norm, NNReal.coe_mul, NNReal.coe_mul, mul_comm (a : ℝ),
    mul_comm (b : ℝ), mul_smul, mul_smul, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos htR, mul_div_cancel_left₀ _ htR.ne']

/-- For unit vectors, `arccos (1 - ‖v - w‖² / 2)` is the angle between `v` and `w`. -/
theorem arccos_one_sub_norm_sub_sq_div_two {v w : V} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    Real.arccos (1 - ‖v - w‖ ^ 2 / 2) = angle v w := by
  rw [angle, real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two, hv, hw]
  congr 1
  ring

/-- The limit angle of two rays of an inner product space is the actual angle of their
directions. -/
theorem tendsto_metricComparisonAngle_lineRay (q v w : V) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    {a b : ℝ≥0} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun t : ℝ≥0 => metricComparisonAngle (q + ((a * t : ℝ≥0) : ℝ) • v) q
      (q + ((b * t : ℝ≥0) : ℝ) • w)) atTop (𝓝 (angle v w)) := by
  have h := tendsto_metricComparisonAngle_of_ray fourPointComparison_zero_of_innerProductSpace
    (isometry_lineRay q v hv) (isometry_lineRay q w hw) ha hb
  rwa [rayChordLimit_lineRay q v w hv hw, arccos_one_sub_norm_sub_sq_div_two hv hw] at h

end GC.MetricGeometry

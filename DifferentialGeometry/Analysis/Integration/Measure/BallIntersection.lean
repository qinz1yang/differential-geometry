import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.MetricSpace.Bounded

noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ball_subset_ball_inter_ball_of_mem_closedBall
    {c x : E} {R r : ℝ} (hR : 0 < R) (hx : x ∈ closedBall c R)
    (hr : 0 < r) (hrR : r ≤ 2 * R) :
    ball (c + (1 - r / (2 * R)) • (x - c)) (r / 2) ⊆ ball c R ∩ ball x r := by
  let t := r / (2 * R)
  have ht : 0 ≤ t := div_nonneg hr.le (by positivity)
  have ht1 : t ≤ 1 := (div_le_one (by positivity : 0 < 2 * R)).mpr hrR
  have htR : t * R = r / 2 := by dsimp only [t]; field_simp
  have hxc : ‖x - c‖ ≤ R := by simpa only [mem_closedBall, dist_eq_norm] using hx
  have hcenter : dist (c + (1 - t) • (x - c)) c ≤ R - r / 2 := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ht1)]
    calc
      (1 - t) * ‖x - c‖ ≤ (1 - t) * R :=
        mul_le_mul_of_nonneg_left hxc (sub_nonneg.mpr ht1)
      _ = R - r / 2 := by rw [sub_mul, one_mul, htR]
  have hcenterx : dist (c + (1 - t) • (x - c)) x ≤ r / 2 := by
    have heq : c + (1 - t) • (x - c) - x = -t • (x - c) := by module
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg ht]
    exact (mul_le_mul_of_nonneg_left hxc ht).trans_eq htR
  intro y hy
  change dist y (c + (1 - t) • (x - c)) < r / 2 at hy
  constructor
  · change dist y c < R
    exact (dist_triangle y _ c).trans_lt (by linarith)
  · change dist y x < r
    exact (dist_triangle y _ x).trans_lt (by linarith)

theorem ball_inter_ball_geometry
    {c x : E} {R r : ℝ} (hr : 0 ≤ r) :
    IsOpen (ball c R ∩ ball x r) ∧ Convex ℝ (ball c R ∩ ball x r) ∧
      diam (ball c R ∩ ball x r) ≤ 2 * r := by
  refine ⟨isOpen_ball.inter isOpen_ball, (convex_ball c R).inter (convex_ball x r), ?_⟩
  exact diam_le_of_subset_closedBall hr (inter_subset_right.trans ball_subset_closedBall)

theorem addHaar_real_ball_inter_ball_lower_bound
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {c x : E} {R r : ℝ} (hR : 0 < R) (hx : x ∈ closedBall c R)
    (hr : 0 < r) (hrR : r ≤ 2 * R) :
    (r / 2) ^ Module.finrank ℝ E * μ.real (ball (0 : E) 1) ≤
      μ.real (ball c R ∩ ball x r) := by
  have hsub := ball_subset_ball_inter_ball_of_mem_closedBall hR hx hr hrR
  have hfinite : μ (ball c R ∩ ball x r) ≠ ∞ :=
    (measure_mono inter_subset_left).trans_lt measure_ball_lt_top |>.ne
  have h := measureReal_mono (μ := μ) hsub hfinite
  rw [Measure.real, Measure.addHaar_ball_of_pos μ _ (half_pos hr), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg (half_pos hr).le _)] at h
  exact h

theorem volume_real_ball_inter_ball_fin_two_lower_bound
    {c x : EuclideanSpace ℝ (Fin 2)} {R r : ℝ} (hR : 0 < R)
    (hx : x ∈ closedBall c R) (hr : 0 < r) (hrR : r ≤ 2 * R) :
    Real.pi * r ^ 2 / 4 ≤ volume.real (ball c R ∩ ball x r) := by
  have h := addHaar_real_ball_inter_ball_lower_bound volume hR hx hr hrR
  have hunit : volume.real (ball (0 : EuclideanSpace ℝ (Fin 2)) 1) = Real.pi := by
    simp [Measure.real, EuclideanSpace.volume_ball_fin_two, Real.pi_pos.le]
  rw [finrank_euclideanSpace_fin, hunit] at h
  convert h using 1
  ring

end DifferentialGeometry.Analysis

end

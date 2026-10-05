import DifferentialGeometry.Geometry.Measure.Area.EuclideanDisk
import DifferentialGeometry.Analysis.Calculus.DiskTraceApproximation
import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.Normed.Group.Uniform

section

set_option autoImplicit false

noncomputable section

open Set Metric
open DifferentialGeometry.Topology
open scoped Topology NNReal

namespace DifferentialGeometry.Geometry

private theorem norm_diskRetraction_of_one_le_norm (z : ℂ) (hz : 1 ≤ ‖z‖) :
    ‖(diskRetraction z : ℂ)‖ = 1 := by
  let w : ℂ := diskRetraction z
  have hw : ‖w‖ ≤ 1 := by
    simpa only [w, Metric.mem_closedBall, dist_zero_right] using (diskRetraction z).property
  apply le_antisymm hw
  by_contra hn
  have hwlt : ‖w‖ < 1 := lt_of_not_ge hn
  have hd : z - w ≠ 0 := by
    intro he
    have hzw := sub_eq_zero.mp he
    rw [hzw] at hz
    exact (not_lt_of_ge hz) hwlt
  let t : ℝ := (1 - ‖w‖) / (2 * (‖z - w‖ + 1))
  have hden : 0 < 2 * (‖z - w‖ + 1) := by positivity
  have ht : 0 < t := div_pos (sub_pos.mpr hwlt) hden
  have htmul : t * (2 * (‖z - w‖ + 1)) = 1 - ‖w‖ := by
    exact div_mul_cancel₀ _ (ne_of_gt hden)
  have htnorm : ‖w‖ + t * ‖z - w‖ < 1 := by
    nlinarith [norm_nonneg (z - w)]
  have hy : w + t • (z - w) ∈ closedDisk := by
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖w + t • (z - w)‖ ≤ ‖w‖ + ‖t • (z - w)‖ := norm_add_le _ _
      _ = ‖w‖ + t * ‖z - w‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      _ ≤ 1 := htnorm.le
  have hvar := convexProjection_variational
    (E := ℂ) ⟨0, by simp⟩ isClosed_closedBall.isComplete (convex_closedBall (0 : ℂ) 1)
    z ⟨w + t • (z - w), hy⟩
  change inner ℝ (z - w) (w + t • (z - w) - w) ≤ 0 at hvar
  rw [add_sub_cancel_left, real_inner_smul_right, real_inner_self_eq_norm_sq] at hvar
  exact (not_le_of_gt (mul_pos ht (sq_pos_of_pos (norm_pos_iff.mpr hd)))) hvar

variable {Y : Type*} [PseudoMetricSpace Y]

theorem diskExtension_dist_le_of_one_le_norm
    (u : C(closedDisk, Y)) (p : Y) {R : ℝ}
    (hboundary : ∀ θ : loopCircle, dist (u (diskBoundary θ)) p ≤ R)
    (z : ℂ) (hz : 1 ≤ ‖z‖) : dist (diskExtension u z) p ≤ R := by
  obtain ⟨θ, hθ⟩ := exists_diskBoundary_eq_of_norm_eq_one
    (norm_diskRetraction_of_one_le_norm z hz)
  have he : diskBoundary θ = diskRetraction z := Subtype.ext hθ
  change dist (u (diskRetraction z)) p ≤ R
  rw [← he]
  exact hboundary θ

theorem tsupport_diskExtension_dist_excess_subset_ball
    (u : C(closedDisk, Y)) (p : Y) {R R' : ℝ} (hRR' : R < R')
    (hboundary : ∀ θ : loopCircle, dist (u (diskBoundary θ)) p ≤ R) :
    tsupport (fun z : ℂ => max (dist (diskExtension u z) p - R') 0) ⊆
      Metric.ball (0 : ℂ) 1 := by
  have hc : Continuous (fun z : ℂ => dist (diskExtension u z) p) :=
    (u.continuous.comp diskRetraction_lipschitz.continuous).dist continuous_const
  have hsub : tsupport (fun z : ℂ => max (dist (diskExtension u z) p - R') 0) ⊆
      {z | R' ≤ dist (diskExtension u z) p} := by
    apply closure_minimal
    · intro z hz
      by_contra hn
      have hlt : dist (diskExtension u z) p < R' := lt_of_not_ge hn
      exact hz (max_eq_right (sub_nonpos.mpr hlt.le))
    · exact isClosed_le continuous_const hc
  intro z hz
  rw [Metric.mem_ball, dist_zero_right]
  by_contra hn
  have hge : 1 ≤ ‖z‖ := le_of_not_gt hn
  have hlo := hsub hz
  have hhi := diskExtension_dist_le_of_one_le_norm u p hboundary z hge
  exact (not_le_of_gt hRR') (hlo.trans hhi)

theorem hasCompactSupport_diskExtension_dist_excess
    (u : C(closedDisk, Y)) (p : Y) {R R' : ℝ} (hRR' : R < R')
    (hboundary : ∀ θ : loopCircle, dist (u (diskBoundary θ)) p ≤ R) :
    HasCompactSupport (fun z : ℂ => max (dist (diskExtension u z) p - R') 0) := by
  apply (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset (isClosed_tsupport _)
  exact (tsupport_diskExtension_dist_excess_subset_ball u p hRR' hboundary).trans
    Metric.ball_subset_closedBall

theorem lipschitzWith_diskExtension_dist_excess
    (u : closedDisk → Y) (p : Y) {L : ℝ≥0}
    (hu : LipschitzWith L u) (R' : ℝ) :
    LipschitzWith L (fun z : ℂ => max (dist (diskExtension u z) p - R') 0) := by
  have hd : LipschitzWith L (fun z : ℂ => dist (diskExtension u z) p) := by
    simpa only [one_mul, Function.comp_def] using
      (LipschitzWith.dist_left p).comp (diskExtension_lipschitz hu)
  simpa only [add_zero] using (hd.sub (LipschitzWith.const R')).max_const 0

end DifferentialGeometry.Geometry

end

end

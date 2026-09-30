import DifferentialGeometry.Geometry.Metric.Distance.Ball

set_option autoImplicit false
open scoped Manifold ContDiff
open DifferentialGeometry

namespace GC.MetricGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem normalized_closedBall (g : SmoothRiemannianMetric I M) (p : M)
    (r : ℝ) (hr : 0 < r) :
    riemannianClosedBallOf (scaleMetric ((r⁻¹)^2) (sq_pos_of_pos (inv_pos.mpr hr)) g) p 1 =
      riemannianClosedBallOf g p r := by
  have h := riemannianClosedBallOf_scaleMetric ((r⁻¹)^2)
    (sq_pos_of_pos (inv_pos.mpr hr)) g p r
  simpa only [Real.sqrt_sq_eq_abs, abs_of_pos (inv_pos.mpr hr),
    inv_mul_cancel₀ (ne_of_gt hr)] using h

theorem normalized_buffer_ball (g : SmoothRiemannianMetric I M) (p : M)
    (r : ℝ) (hr : 0 < r) (R : ℝ) :
    riemannianClosedBallOf (scaleMetric ((r⁻¹)^2) (sq_pos_of_pos (inv_pos.mpr hr)) g) p R =
      riemannianClosedBallOf g p (r * R) := by
  have h := riemannianClosedBallOf_scaleMetric ((r⁻¹)^2)
    (sq_pos_of_pos (inv_pos.mpr hr)) g p (r * R)
  simpa only [Real.sqrt_sq_eq_abs, abs_of_pos (inv_pos.mpr hr),
    ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hr), one_mul] using h

theorem normalized_buffer_inclusion (g : SmoothRiemannianMetric I M) (p : M)
    (r : ℝ) (hr : 0 < r) {R S : ℝ} (hRS : R ≤ S) :
    riemannianClosedBallOf (scaleMetric ((r⁻¹)^2) (sq_pos_of_pos (inv_pos.mpr hr)) g) p R ⊆
      riemannianClosedBallOf g p (r * S) := by
  rw [normalized_buffer_ball g p r hr R]
  exact riemannianClosedBallOf_mono g p (mul_le_mul_of_nonneg_left hRS hr.le)

#check DifferentialGeometry.edistOf_scale
#check DifferentialGeometry.riemannianClosedBallOf_scaleMetric
#check normalized_closedBall
#check normalized_buffer_inclusion

end GC.MetricGeometry

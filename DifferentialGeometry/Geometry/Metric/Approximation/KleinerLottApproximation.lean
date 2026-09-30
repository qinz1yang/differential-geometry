import DifferentialGeometry.Geometry.Metric.Approximation.PointedBallApproximation
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option autoImplicit false

namespace GC.MetricGeometry

universe u v
variable {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]

structure KleinerLottApprox (p : X) (q : Y) (δ : ℝ) where
  error_pos : 0 < δ
  error_lt_one : δ < 1
  toFun : X → Y
  basepoint : toFun p = q
  distortion : ∀ x ∈ Metric.ball p δ⁻¹, ∀ x' ∈ Metric.ball p δ⁻¹,
    |dist (toFun x) (toFun x') - dist x x'| ≤ δ
  coverage : ∀ y : Y, dist y q < δ⁻¹ - δ →
    Metric.infDist y (toFun '' Metric.ball p δ⁻¹) ≤ δ

namespace KleinerLottApprox

variable {p : X} {q : Y} {δ R : ℝ}

theorem image_nonempty (f : KleinerLottApprox p q δ) :
    (f.toFun '' Metric.ball p δ⁻¹).Nonempty := by
  exact ⟨q, ⟨p, Metric.mem_ball_self (inv_pos.mpr f.error_pos), f.basepoint⟩⟩

theorem radial_error (f : KleinerLottApprox p q δ)
    (x : X) (hx : x ∈ Metric.ball p δ⁻¹) :
    |dist (f.toFun x) q - dist x p| ≤ δ := by
  simpa only [f.basepoint] using
    f.distortion x hx p (Metric.mem_ball_self (inv_pos.mpr f.error_pos))

theorem coverage_witness (f : KleinerLottApprox p q δ)
    (y : Y) (hy : dist y q < δ⁻¹ - δ) :
    ∃ x ∈ Metric.ball p δ⁻¹, dist y (f.toFun x) < 2 * δ := by
  have h : Metric.infDist y (f.toFun '' Metric.ball p δ⁻¹) < 2 * δ := by
    linarith [f.coverage y hy, f.error_pos]
  obtain ⟨z, ⟨x, hx, rfl⟩, hz⟩ := (Metric.infDist_lt_iff f.image_nonempty).mp h
  exact ⟨x, hx, hz⟩

def toClosedBall (f : KleinerLottApprox p q δ)
    (hδR : 3 * δ < R) (hR : R < δ⁻¹) : PointedBallApprox p q R (3 * δ) where
  error_pos := by linarith [f.error_pos]
  error_lt_radius := hδR
  toFun x := f.toFun x.val
  basepoint := f.basepoint
  distortion x x' := by
    have h := f.distortion x.val (lt_of_le_of_lt x.property hR)
      x'.val (lt_of_le_of_lt x'.property hR)
    linarith [f.error_pos]
  coverage y hy := by
    obtain ⟨x, hx, hxy⟩ := f.coverage_witness y (by linarith [f.error_pos])
    have hrad := (abs_le.mp (f.radial_error x hx)).1
    have htri := dist_triangle (f.toFun x) y q
    rw [dist_comm (f.toFun x) y] at htri
    have hxs : dist x p ≤ R := by linarith
    refine ⟨⟨x, hxs⟩, ?_⟩
    change dist y (f.toFun x) < 3 * δ
    linarith [f.error_pos]

end KleinerLottApprox

namespace PointedBallApprox

variable {p : X} {q : Y} {δ : ℝ}

noncomputable def toKleinerLott
    (f : PointedBallApprox p q (δ⁻¹ + δ) (δ / 4))
    (hδ : 0 < δ) (hδone : δ < 1) : KleinerLottApprox p q δ := by
  classical
  let F : X → Y := fun x => if hx : dist x p < δ⁻¹ then
    f.toFun ⟨x, by linarith⟩ else q
  have hF (x : X) (hx : dist x p < δ⁻¹) :
      F x = f.toFun ⟨x, by linarith⟩ := by
    simp only [F, dite_eq_left hx]
  refine ⟨hδ, hδone, F, ?_, ?_, ?_⟩
  · rw [hF p (by simpa using inv_pos.mpr hδ)]
    exact f.basepoint
  · intro x hx x' hx'
    change dist x p < δ⁻¹ at hx
    change dist x' p < δ⁻¹ at hx'
    rw [hF x hx, hF x' hx']
    have h := f.distortion ⟨x, by linarith⟩ ⟨x', by linarith⟩
    dsimp at h
    linarith
  · intro y hy
    obtain ⟨x, hx⟩ := f.coverage y (by linarith)
    have hrad := f.radial_lower x
    have htri := dist_triangle (f.toFun x) y q
    rw [dist_comm (f.toFun x) y] at htri
    have hxs : dist x.val p < δ⁻¹ := by linarith
    have hfx : F x.val = f.toFun x := hF x.val hxs
    have hmem : f.toFun x ∈ F '' Metric.ball p δ⁻¹ := ⟨x.val, hxs, hfx⟩
    exact (Metric.infDist_le_dist_of_mem hmem).trans (by linarith)

end PointedBallApprox
end GC.MetricGeometry

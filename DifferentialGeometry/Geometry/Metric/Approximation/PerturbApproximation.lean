import DifferentialGeometry.Geometry.Metric.Approximation.PointedBallApproximation
import Mathlib.Topology.MetricSpace.Isometry

namespace GC.MetricGeometry.PointedBallApprox

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
variable {p : X} {q : Y} {R ε ρ : ℝ}

def mapTargetIsometry (f : PointedBallApprox p q R ε) (e : Y ≃ᵢ Z) :
    PointedBallApprox p (e q) R ε where
  error_pos := f.error_pos
  error_lt_radius := f.error_lt_radius
  toFun x := e (f.toFun x)
  basepoint := congrArg e f.basepoint
  distortion x y := by simpa only [e.dist_eq] using f.distortion x y
  coverage y hy := by
    have hd : dist (e.symm y) q = dist y (e q) := by
      simpa only [e.symm_apply_apply] using e.symm.dist_eq y (e q)
    obtain ⟨x, hx⟩ := f.coverage (e.symm y) (by rwa [hd])
    exact ⟨x, by simpa only [e.apply_symm_apply] using (e.dist_eq (e.symm y) (f.toFun x)).trans_lt hx⟩

def perturb (f : PointedBallApprox p q R ε) (g : BallCarrier p R → Y)
    (hg : g ⟨p, by simpa using (f.error_pos.trans f.error_lt_radius).le⟩ = q)
    (hclose : ∀ x, dist (g x) (f.toFun x) ≤ ρ) (hE : ε + 2 * ρ < R) :
    PointedBallApprox p q R (ε + 2 * ρ) := by
  have hρ : 0 ≤ ρ := dist_nonneg.trans (hclose ⟨p, by simpa using (f.error_pos.trans f.error_lt_radius).le⟩)
  refine ⟨by linarith [f.error_pos], hE, g, hg, ?_, ?_⟩
  · intro x y
    have hf := abs_lt.mp (f.distortion x y)
    have ht := dist_triangle4 (g x) (f.toFun x) (f.toFun y) (g y)
    have hs := dist_triangle4 (f.toFun x) (g x) (g y) (f.toFun y)
    rw [dist_comm (f.toFun y) (g y)] at ht
    rw [dist_comm (f.toFun x) (g x)] at hs
    exact abs_lt.mpr ⟨by linarith [hclose x, hclose y], by linarith [hclose x, hclose y]⟩
  · intro y hy
    obtain ⟨x, hx⟩ := f.coverage y (by linarith)
    have ht := dist_triangle y (f.toFun x) (g x)
    rw [dist_comm (f.toFun x) (g x)] at ht
    exact ⟨x, by linarith [hclose x]⟩

end GC.MetricGeometry.PointedBallApprox

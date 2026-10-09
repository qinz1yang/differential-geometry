import DifferentialGeometry.Geometry.Metric.Approximation.PointedBallApproximation

set_option autoImplicit false

namespace GC.MetricGeometry

universe u v
variable {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]

structure PointedOpenBallApprox (p : X) (q : Y) (R ε : ℝ) where
  error_pos : 0 < ε
  error_lt_radius : ε < R
  toFun : Metric.ball p R → Y
  basepoint : toFun ⟨p, by simpa using (lt_trans error_pos error_lt_radius)⟩ = q
  distortion : ∀ x x', |dist (toFun x) (toFun x') - dist x.val x'.val| < ε
  coverage : ∀ y : Y, dist y q < R - ε → ∃ x, dist y (toFun x) < ε

namespace PointedOpenBallApprox

variable {p : X} {q : Y} {R ε s : ℝ}

theorem radial_error (f : PointedOpenBallApprox p q R ε) (x : Metric.ball p R) :
    |dist (f.toFun x) q - dist x.val p| < ε := by
  simpa only [f.basepoint] using f.distortion x
    ⟨p, by simpa using (lt_trans f.error_pos f.error_lt_radius)⟩

theorem radial_lower (f : PointedOpenBallApprox p q R ε) (x : Metric.ball p R) :
    dist x.val p < dist (f.toFun x) q + ε := by
  have h := (abs_lt.mp (f.radial_error x)).1
  linarith

def toClosedBall (f : PointedOpenBallApprox p q R ε)
    (hs : 2 * ε < s) (hsR : s < R) : PointedBallApprox p q s (2 * ε) where
  error_pos := by linarith [f.error_pos]
  error_lt_radius := hs
  toFun x := f.toFun ⟨x.val, lt_of_le_of_lt x.property hsR⟩
  basepoint := f.basepoint
  distortion x x' := by
    have h := f.distortion ⟨x.val, lt_of_le_of_lt x.property hsR⟩
      ⟨x'.val, lt_of_le_of_lt x'.property hsR⟩
    dsimp at h ⊢
    linarith [f.error_pos]
  coverage y hy := by
    obtain ⟨x, hx⟩ := f.coverage y (by linarith [f.error_pos])
    have hrad := f.radial_lower x
    have htri := dist_triangle (f.toFun x) y q
    rw [dist_comm (f.toFun x) y] at htri
    have hxs : dist x.val p ≤ s := by linarith
    refine ⟨⟨x.val, hxs⟩, ?_⟩
    change dist y (f.toFun x) < 2 * ε
    linarith [f.error_pos]

end PointedOpenBallApprox

namespace PointedBallApprox

variable {p : X} {q : Y} {R ε s : ℝ}

def toOpenBall (f : PointedBallApprox p q R ε)
    (hs : 2 * ε < s) (hsR : s < R) : PointedOpenBallApprox p q s (2 * ε) where
  error_pos := by linarith [f.error_pos]
  error_lt_radius := hs
  toFun x := f.toFun ⟨x.val, le_of_lt (lt_trans x.property hsR)⟩
  basepoint := f.basepoint
  distortion x x' := by
    have h := f.distortion ⟨x.val, le_of_lt (lt_trans x.property hsR)⟩
      ⟨x'.val, le_of_lt (lt_trans x'.property hsR)⟩
    dsimp at h ⊢
    linarith [f.error_pos]
  coverage y hy := by
    obtain ⟨x, hx⟩ := f.coverage y (by linarith [f.error_pos])
    have hrad := f.radial_lower x
    have htri := dist_triangle (f.toFun x) y q
    rw [dist_comm (f.toFun x) y] at htri
    have hxs : dist x.val p < s := by linarith
    refine ⟨⟨x.val, hxs⟩, ?_⟩
    change dist y (f.toFun x) < 2 * ε
    linarith [f.error_pos]

end PointedBallApprox
end GC.MetricGeometry

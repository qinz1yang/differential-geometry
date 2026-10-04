import DifferentialGeometry.Geometry.Metric.Approximation.PointedBallApproximation

set_option autoImplicit false
namespace GC.MetricGeometry.PointedBallApprox

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  {p : X} {q : Y} {R ε : ℝ}

theorem dist_image_lt_add_error (f : PointedBallApprox p q R ε)
    (x y : BallCarrier p R) : dist (f.toFun x) (f.toFun y) < dist x.val y.val + ε := by
  have h := (abs_lt.mp (f.distortion x y)).2
  linarith

theorem dist_lt_image_add_error (f : PointedBallApprox p q R ε)
    (x y : BallCarrier p R) : dist x.val y.val < dist (f.toFun x) (f.toFun y) + ε := by
  have h := (abs_lt.mp (f.distortion x y)).1
  linarith

end GC.MetricGeometry.PointedBallApprox

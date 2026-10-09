import DifferentialGeometry.Geometry.Metric.Scaling.Rescale
import Mathlib.Topology.MetricSpace.Isometry

set_option autoImplicit false

namespace IsometryEquiv

def rescale {X Y : Type*} [mX : MetricSpace X] [mY : MetricSpace Y]
    (e : X ≃ᵢ Y) (c : ℝ) (hc : 0 < c) :
    letI : MetricSpace X := mX.rescale c hc
    letI : MetricSpace Y := mY.rescale c hc
    X ≃ᵢ Y := by
  let f : X ≃ Y := e.toEquiv
  have hd (x y : X) : dist (f x) (f y) = dist x y := e.dist_eq x y
  letI : MetricSpace X := mX.rescale c hc
  letI : MetricSpace Y := mY.rescale c hc
  refine ⟨f, Isometry.of_dist_eq (fun x y => ?_)⟩
  exact congrArg (c * ·) (hd x y)

end IsometryEquiv

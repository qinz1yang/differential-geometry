import DifferentialGeometry.Geometry.Metric.Euclidean
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import DifferentialGeometry.Topology.Manifold.EuclideanHalfSpace.Instances

set_option autoImplicit false
noncomputable section
open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry

variable (n : ℕ) [NeZero n]

local notation "Ehs" => EuclideanSpace ℝ (Fin n)
local notation "Hhs" => EuclideanHalfSpace n
local notation "Ihs" => (𝓡∂ n)

def euclideanHalfSpaceMetric : SmoothRiemannianMetric Ihs Hhs :=
  (euclideanMetric (E := Ehs)).pullback Ihs (Ihs).contMDiff (fun _ => by
    rw [(Ihs).hasMFDerivAt.mfderiv]
    exact Function.injective_id)

theorem euclideanHalfSpaceMetric_inner (p : Hhs) (v w : Ehs) :
    (euclideanHalfSpaceMetric n).inner p v w = inner ℝ v w := by
  unfold euclideanHalfSpaceMetric
  erw [SmoothRiemannianMetric.pullback_inner, (Ihs).hasMFDerivAt.mfderiv,
    euclideanMetric_inner]
  rfl

end DifferentialGeometry

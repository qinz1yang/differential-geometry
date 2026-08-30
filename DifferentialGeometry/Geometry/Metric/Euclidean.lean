import DifferentialGeometry.Geometry.Metric.Basic
import Mathlib.Geometry.Manifold.Riemannian.Basic

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]

noncomputable def euclideanMetric : SmoothRiemannianMetric 𝓘(Real, E) E where
  inner := (riemannianMetricVectorSpace E).inner
  symm := (riemannianMetricVectorSpace E).symm
  pos := (riemannianMetricVectorSpace E).pos
  isVonNBounded := (riemannianMetricVectorSpace E).isVonNBounded
  contMDiff := (riemannianMetricVectorSpace E).contMDiff.of_le le_top

omit [FiniteDimensional Real E] in
@[simp] theorem euclideanMetric_inner
    (x : E) (v w : TangentSpace 𝓘(Real, E) x) :
    euclideanMetric.inner x v w = inner Real v w := by
  rfl

end DifferentialGeometry

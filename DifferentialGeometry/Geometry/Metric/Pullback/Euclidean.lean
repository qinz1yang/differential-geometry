import DifferentialGeometry.Geometry.Metric.Euclidean
import DifferentialGeometry.Geometry.Metric.Pullback

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry

open Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem LinearIsometryEquiv.pullbackMetric_euclidean (e : E ≃ₗᵢ[Real] E) :
    Diffeomorph.pullbackMetric (euclideanMetric (E := E))
        e.toContinuousLinearEquiv.toDiffeomorph =
      euclideanMetric := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [Diffeomorph.pullbackMetric_inner,
    DifferentialGeometry.euclideanMetric_inner,
    DifferentialGeometry.euclideanMetric_inner]
  change inner Real
      (mfderiv 𝓘(Real, E) 𝓘(Real, E) (e : E → E) x v)
      (mfderiv 𝓘(Real, E) 𝓘(Real, E) (e : E → E) x w) =
    inner Real v w
  rw [mfderiv_eq_fderiv]
  change inner Real
      ((fderiv Real e.toContinuousLinearEquiv.toContinuousLinearMap x) v)
      ((fderiv Real e.toContinuousLinearEquiv.toContinuousLinearMap x) w) =
    inner Real v w
  rw [ContinuousLinearMap.fderiv]
  exact e.inner_map_map v w

end DifferentialGeometry

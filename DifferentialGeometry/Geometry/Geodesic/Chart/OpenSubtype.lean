import DifferentialGeometry.Geometry.Geodesic.Equation.Basic

noncomputable section

open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem chartChristoffelContraction_opens_basepoint_eq
    (U : TopologicalSpace.Opens F) (G : SmoothRiemannianMetric 𝓘(ℝ, F) U)
    (α β : U) (v w y : F) :
    chartChristoffelContraction G α v w y =
      chartChristoffelContraction G β v w y := by
  rfl

end DifferentialGeometry.Geometry.Riemannian.Geodesic

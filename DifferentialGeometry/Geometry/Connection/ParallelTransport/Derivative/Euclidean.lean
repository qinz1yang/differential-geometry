import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeAlong
import DifferentialGeometry.Geometry.Connection.LeviCivita.Christoffel.Euclidean

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

open DifferentialGeometry.Geometry.Connection

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

set_option backward.isDefEq.respectTransparency false in
theorem covDerivAlong_euclideanMetric_eq_deriv (γ : ℝ → V)
    (W : ℝ → V) (t : ℝ) :
    covDerivAlong (euclideanMetric (E := V)) γ W t = deriv W t := by
  have hrep : chartRepAt (I := 𝓘(ℝ, V)) γ W t = fun s => W s := by
    funext s
    rw [chartRepAt_apply, TangentBundle.continuousLinearMapAt_model_space]
    rfl
  rw [covDerivAlong_def, DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCovDerivAlong_def,
    hrep, chartChristoffelContraction_euclideanMetric, add_zero,
    TangentBundle.symmL_model_space]
  rfl

end DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

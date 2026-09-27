import DifferentialGeometry.Geometry.Geodesic.Equation.Basic
import DifferentialGeometry.Geometry.Metric.Euclidean

open scoped Manifold

namespace DifferentialGeometry.Geometry.Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates
open Riemannian.Geodesic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

private theorem chartGramOnE_euclideanMetric (x : V) (i j : Fin (Module.finrank ℝ V)) :
    chartGramOnE (euclideanMetric (E := V)) x i j =
      fun _ => inner ℝ ((chartModelBasis V) i) ((chartModelBasis V) j) := by
  funext y
  rw [chartGramOnE_def, chartGramMatrix_apply, euclideanMetric_inner]
  simp only [chartBasisVecFiber, TangentBundle.symmL_model_space]
  rfl

theorem chartChristoffel_euclideanMetric (x : V) (i j k : Fin (Module.finrank ℝ V)) :
    chartChristoffel (euclideanMetric (E := V)) x i j k = 0 := by
  funext y
  rw [chartChristoffel_def]
  simp_rw [chartGramOnE_euclideanMetric]
  simp [partialDeriv]

theorem chartChristoffelContraction_euclideanMetric (x u v y : V) :
    chartChristoffelContraction (euclideanMetric (E := V)) x u v y = 0 := by
  rw [chartChristoffelContraction_def]
  simp_rw [chartChristoffel_euclideanMetric]
  simp

end DifferentialGeometry.Geometry.Connection

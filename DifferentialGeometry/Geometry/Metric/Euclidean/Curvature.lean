import DifferentialGeometry.Geometry.Metric.Euclidean
import DifferentialGeometry.Geometry.Curvature.Coordinates.RiemannTensorBridge

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Connection Curvature Operator
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]

private lemma euclideanMetric_chartGramOnE
    (x : E) (i j : Fin (Module.finrank Real E)) :
    chartGramOnE (I := 𝓘(Real, E)) (euclideanMetric (E := E)) x i j =
      fun _ => inner Real (chartModelBasis E i) (chartModelBasis E j) := by
  funext y
  simp only [chartGramOnE, chartGramMatrix, Matrix.of_apply,
    chartBasisVecFiber]
  simp only [TangentBundle.symmL_model_space]
  rw [DifferentialGeometry.euclideanMetric_inner]
  change inner Real ((1 : E →L[Real] E) (chartModelBasis E i))
      ((1 : E →L[Real] E) (chartModelBasis E j)) = _
  rfl

theorem euclideanMetric_chartChristoffel_eq_zero
    (x : E) (i j k : Fin (Module.finrank Real E)) :
    chartChristoffel (I := 𝓘(Real, E)) (euclideanMetric (E := E)) x i j k = 0 := by
  funext y
  rw [chartChristoffel_def]
  simp_rw [euclideanMetric_chartGramOnE]
  simp [partialDeriv]

private lemma euclideanMetric_chartRiemannTensor
    (x : E) (i j k l : Fin (Module.finrank Real E)) :
    chartRiemannTensor (I := 𝓘(Real, E)) (euclideanMetric (E := E)) x i j k l = 0 := by
  funext y
  rw [chartRiemannTensor_def]
  simp_rw [euclideanMetric_chartChristoffel_eq_zero]
  simp [partialDeriv]

theorem euclideanMetric_metricRm04At_eq_zero (x : E) :
    metricRm04At (I := 𝓘(Real, E)) (euclideanMetric (E := E)) x = 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  ext v
  have hv : v = vec4 (I := 𝓘(Real, E)) (v 0) (v 1) (v 2) (v 3) := by
    ext i
    fin_cases i <;> rfl
  rw [hv]
  change metricRm04StandardAt (I := 𝓘(Real, E)) (euclideanMetric (E := E)) x
    (v 0) (v 1) (v 2) (v 3) = 0
  rw [metricRm04StandardAt_eq_chartRiemannCLM,
    chartRiemannCLM_apply]
  simp only [euclideanMetric_chartRiemannTensor, Pi.zero_apply, mul_zero, zero_smul,
    Finset.sum_const_zero, map_zero]

theorem euclideanMetric_ricciTensor
    (x : E) (v w : TangentSpace 𝓘(Real, E) x) :
    ricciTensor (I := 𝓘(Real, E)) (euclideanMetric (E := E)) x v w = 0 := by
  rw [Connection.ricciTensor_eq_chartRicciSwap_of_basis_identity
    (euclideanMetric (E := E)) x
    (Connection.chartRiemannBasisIdentity_holds
      (euclideanMetric (E := E)) x)]
  simp only [chartRicciTensor_def, euclideanMetric_chartRiemannTensor]
  simp

theorem euclideanMetric_scalarCurvature (x : E) :
    metricScalarAt (I := 𝓘(Real, E)) (euclideanMetric (E := E)) x = 0 := by
  exact metricScalarAt_eq_zero_of_metricRm04At_eq_zero
    (euclideanMetric (E := E)) x (euclideanMetric_metricRm04At_eq_zero x)

end DifferentialGeometry.Geometry

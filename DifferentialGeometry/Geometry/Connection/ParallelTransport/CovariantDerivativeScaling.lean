import DifferentialGeometry.Geometry.Connection.ParallelTransport.CovariantDerivativeAlong
import DifferentialGeometry.Geometry.Metric.Scaling

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem chartGram_scale
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x₀ x : M) :
    DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (scaleMetric (I := I) c hc g) x₀ x =
      c • DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x₀ x := by
  ext i j
  simp [DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply, scaleMetric_inner]

private theorem chartInvGram_scale
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x₀ x : M) :
    chartInvGramMatrix (I := I) (scaleMetric (I := I) c hc g) x₀ x =
      c⁻¹ • chartInvGramMatrix (I := I) g x₀ x := by
  let A := DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x₀ x
  have hc₀ : c ≠ 0 := ne_of_gt hc
  change (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (scaleMetric (I := I) c hc g) x₀ x)⁻¹ =
    c⁻¹ • A⁻¹
  rw [chartGram_scale (I := I) c hc g x₀ x]
  by_cases hA : IsUnit A.det
  · let : Invertible c := invertibleOfNonzero hc₀
    simpa only [invOf_eq_inv] using Matrix.inv_smul A c hA
  · have hscaled : ¬IsUnit (c • A).det := by
      simpa [Matrix.det_smul, isUnit_iff_ne_zero, hc₀] using hA
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hscaled,
      Matrix.nonsing_inv_apply_not_isUnit _ hA, smul_zero]

private theorem partialDeriv_const_mul_ne
    (c : Real) (hc : c ≠ 0) (u : E → Real)
    (i : Fin (Module.finrank Real E)) (y : E) :
    partialDeriv (E := E) i (fun z => c * u z) y =
      c * partialDeriv (E := E) i u y := by
  unfold partialDeriv
  by_cases hu : DifferentiableAt Real u y
  · rw [fderiv_const_mul hu c]
    simp
  · have hcu : ¬DifferentiableAt Real (fun z => c * u z) y := by
      intro h
      have hinv : DifferentiableAt Real (fun z => c⁻¹ * (c * u z)) y :=
        h.const_mul c⁻¹
      have heq : (fun z => c⁻¹ * (c * u z)) = u := by
        funext z
        field_simp [hc]
      exact hu (by simpa only [heq] using hinv)
    rw [fderiv_zero_of_not_differentiableAt hu,
      fderiv_zero_of_not_differentiableAt hcu]
    simp

private theorem chartGramOnE_scale
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (x₀ : M) (i j : Fin (Module.finrank Real E)) :
    chartGramOnE (I := I) (scaleMetric (I := I) c hc g) x₀ i j =
      fun y => c * chartGramOnE (I := I) g x₀ i j y := by
  funext y
  simp [chartGramOnE, DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply, scaleMetric_inner]

private theorem chartChristoffel_scale
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (x₀ : M) (i j k : Fin (Module.finrank Real E)) (y : E) :
    chartChristoffel (I := I) (scaleMetric (I := I) c hc g) x₀ i j k y =
      chartChristoffel (I := I) g x₀ i j k y := by
  classical
  have hc₀ : c ≠ 0 := ne_of_gt hc
  rw [chartChristoffel_def, chartChristoffel_def]
  apply congrArg ((1 / 2 : Real) * ·)
  apply Finset.sum_congr rfl
  intro l _hl
  rw [chartInvGram_scale (I := I) c hc g]
  rw [chartGramOnE_scale (I := I) c hc g x₀ l j,
    chartGramOnE_scale (I := I) c hc g x₀ l i,
    chartGramOnE_scale (I := I) c hc g x₀ i j]
  rw [partialDeriv_const_mul_ne c hc₀,
    partialDeriv_const_mul_ne c hc₀,
    partialDeriv_const_mul_ne c hc₀]
  simp only [Matrix.smul_apply, smul_eq_mul]
  field_simp [hc₀]

private theorem chartChristoffelContraction_scale
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (x₀ : M) (v w y : E) :
    Geodesic.chartChristoffelContraction (I := I)
        (scaleMetric (I := I) c hc g) x₀ v w y =
      Geodesic.chartChristoffelContraction (I := I) g x₀ v w y := by
  classical
  unfold Geodesic.chartChristoffelContraction
  simp_rw [chartChristoffel_scale (I := I) c hc g]

theorem covDerivAlong_scale
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (gamma : Real → M) (V : ∀ t, TangentSpace I (gamma t)) (t : Real) :
    covDerivAlong (I := I) (scaleMetric (I := I) c hc g) gamma V t =
      covDerivAlong (I := I) g gamma V t := by
  rw [covDerivAlong_def, covDerivAlong_def]
  congr 1
  rw [chartCovDerivAlong_def, chartCovDerivAlong_def]
  rw [chartChristoffelContraction_scale (I := I) c hc g]

end DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

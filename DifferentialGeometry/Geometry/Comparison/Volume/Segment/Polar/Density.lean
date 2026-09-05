import DifferentialGeometry.Analysis.Integration.Measure.Parametric.Density
import DifferentialGeometry.Geometry.Comparison.Variation.Jacobi.Gram
import DifferentialGeometry.Geometry.Exponential.Variation.Jacobi
import DifferentialGeometry.Geometry.Exponential.Variation.EndpointShape
import DifferentialGeometry.Geometry.Exponential.Smoothness.AwayFromZero.Intrinsic
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Set Function Filter Bundle Manifold MeasureTheory
open scoped Topology Manifold ContDiff ENNReal Matrix

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
variable [riemannianBundle : RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

omit riemannianBundle
  [NeZero (Module.finrank ℝ E)]
  [CompleteSpace E]
  [I.Boundaryless]
  [T2Space M]
  [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] in
theorem mfderiv_chartBasis
    (f : E → M) {w : E} (hf : MDifferentiableAt 𝓘(ℝ, E) I f w)
    (y₀ : M) (hx : f w ∈ (trivializationAt E (TangentSpace I) y₀).baseSet)
    (i : Fin (Module.finrank ℝ E)) :
    mfderiv 𝓘(ℝ, E) I f w ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) =
      ∑ k, (LinearMap.toMatrix (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E)
            (fderiv ℝ (fun u : E => extChartAt I y₀ (f u)) w).toLinearMap) k i •
        DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) y₀ k (f w) := by
  exact DifferentialGeometry.Tensor.Coordinates.mfderiv_chartModelBasis_eq_sum
    (I := I) f hf y₀ hx i

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit riemannianBundle
  [NeZero (Module.finrank ℝ E)]
  [CompleteSpace E]
  [I.Boundaryless]
  [T2Space M]
  [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] in
theorem gramDiff_det
    (g : SmoothRiemannianMetric I M)
    (f : E → M) {w : E} (hf : MDifferentiableAt 𝓘(ℝ, E) I f w)
    (y₀ : M) (hx : f w ∈ (trivializationAt E (TangentSpace I) y₀).baseSet) :
    (Matrix.of fun i j =>
        g.inner (f w) (mfderiv 𝓘(ℝ, E) I f w ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
          (mfderiv 𝓘(ℝ, E) I f w ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j))).det =
      (fderiv ℝ (fun u : E => extChartAt I y₀ (f u)) w).det ^ 2
        * (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g y₀ (f w)).det := by
  exact paramGramMatrix_det_eq_sq_det_mul (I := I) g f hf y₀ hx

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E]
  [T2Space (TangentBundle I M)] in
theorem exp_density_curve
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (v : E) (y₀ : M)
    (hy : expMapIntrinsic (I := I) g hEnorm x (show TangentSpace I x from v)
      ∈ (chartAt H y₀).source) :
    chartDensity g y₀
          (expMapIntrinsic (I := I) g hEnorm x (show TangentSpace I x from v))
        * |(fderiv ℝ (fun b : E => extChartAt I y₀
            (expMapIntrinsic (I := I) g hEnorm x (show TangentSpace I x from b))) v).det|
      = curveDensity (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm x (show TangentSpace I x from v))
          (fun (i : Fin (Module.finrank ℝ E)) (t : ℝ) =>
            intrinsicJacobi g hEnorm x (show TangentSpace I x from v)
              (show TangentSpace I x from (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)) t) 1 := by
  classical
  set F : E → M := fun b : E =>
    expMapIntrinsic (I := I) g hEnorm x (show TangentSpace I x from b) with hF
  have hFdiff : MDifferentiableAt 𝓘(ℝ, E) I F v :=
    (intrinsicFiber_smooth (I := I) g hEnorm x).contMDiffAt.mdifferentiableAt (by decide)
  have hxbase : F v ∈ (trivializationAt E (TangentSpace I) y₀).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source (I := I) y₀]
    exact hy
  have hcol : ∀ i : Fin (Module.finrank ℝ E),
      intrinsicJacobi g hEnorm x (show TangentSpace I x from v)
          (show TangentSpace I x from (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)) 1
        = mfderiv 𝓘(ℝ, E) I F v ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) := by
    intro i
    exact intrinsic_jacobi_one (I := I) g hEnorm x v ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
  have hgram :
      curveGram (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm x (show TangentSpace I x from v))
          (fun (i : Fin (Module.finrank ℝ E)) (t : ℝ) =>
            intrinsicJacobi g hEnorm x (show TangentSpace I x from v)
              (show TangentSpace I x from (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)) t) 1
        = Matrix.of fun i j =>
            g.inner (F v) (mfderiv 𝓘(ℝ, E) I F v ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
              (mfderiv 𝓘(ℝ, E) I F v ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)) := by
    ext i j
    simp only [curveGram, Matrix.of_apply]
    rw [hcol i, hcol j]
    rfl
  rw [curveDensity, hgram, gramDiff_det (I := I) g F hFdiff y₀ hxbase,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  rw [chartDensity]
  ring

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

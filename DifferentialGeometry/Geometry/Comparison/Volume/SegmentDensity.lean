import DifferentialGeometry.Analysis.Integration.Measure.ParamEvaluation
import DifferentialGeometry.Geometry.Comparison.Variation.JacobiGram
import DifferentialGeometry.Geometry.Exponential.JacobiVariation
import DifferentialGeometry.Geometry.Exponential.EndpointShape
import DifferentialGeometry.Geometry.Exponential.Smoothness.IntrinsicOffZero
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
    mfderiv 𝓘(ℝ, E) I f w ((chartModelBasis E) i) =
      ∑ k, (LinearMap.toMatrix (chartModelBasis E) (chartModelBasis E)
            (fderiv ℝ (fun u : E => extChartAt I y₀ (f u)) w).toLinearMap) k i •
        chartBasisVecFiber (I := I) y₀ k (f w) := by
  have hxchart : f w ∈ (chartAt H y₀).source := by
    simpa [trivializationAt_baseSet_eq_chartAt_source (I := I) y₀] using hx
  have hchartdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I y₀) (f w) :=
    mdifferentiableAt_extChartAt (I := I) (x := y₀) (y := f w) hxchart
  have hchain_f :
      fderiv ℝ (fun u : E => extChartAt I y₀ (f u)) w =
        (mfderiv I 𝓘(ℝ, E) (extChartAt I y₀) (f w)).comp
          (mfderiv 𝓘(ℝ, E) I f w) := by
    have hchain :
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun u : E => extChartAt I y₀ (f u)) w =
          (mfderiv I 𝓘(ℝ, E) (extChartAt I y₀) (f w)).comp
            (mfderiv 𝓘(ℝ, E) I f w) := by
      simpa [Function.comp_def] using
        (mfderiv_comp (I := 𝓘(ℝ, E)) (I' := I) (I'' := 𝓘(ℝ, E))
          (g := extChartAt I y₀) (f := f) (x := w) hchartdiff hf)
    simpa [mfderiv_eq_fderiv] using hchain
  set T₀ : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) y₀ with hT₀
  apply (T₀.continuousLinearEquivAt ℝ (f w) hx).injective
  have hrepr :
      (fderiv ℝ (fun u : E => extChartAt I y₀ (f u)) w) ((chartModelBasis E) i) =
        ∑ k, (LinearMap.toMatrix (chartModelBasis E) (chartModelBasis E)
              (fderiv ℝ (fun u : E => extChartAt I y₀ (f u)) w).toLinearMap) k i •
          (chartModelBasis E) k := by
    simpa [LinearMap.toMatrix_apply] using
      (((chartModelBasis E).sum_repr
        ((fderiv ℝ (fun u : E => extChartAt I y₀ (f u)) w)
          ((chartModelBasis E) i))).symm)
  calc
    T₀.continuousLinearEquivAt ℝ (f w) hx
        (mfderiv 𝓘(ℝ, E) I f w ((chartModelBasis E) i))
        = (fderiv ℝ (fun u : E => extChartAt I y₀ (f u)) w) ((chartModelBasis E) i) := by
          rw [Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ) T₀ hx]
          rw [TangentBundle.continuousLinearMapAt_trivializationAt
            (I := I) (x₀ := y₀) (x := f w) hxchart]
          rw [hchain_f]
          rfl
    _ = ∑ k, (LinearMap.toMatrix (chartModelBasis E) (chartModelBasis E)
          (fderiv ℝ (fun u : E => extChartAt I y₀ (f u)) w).toLinearMap) k i •
            (chartModelBasis E) k := hrepr
    _ = T₀.continuousLinearEquivAt ℝ (f w) hx
          (∑ k, (LinearMap.toMatrix (chartModelBasis E) (chartModelBasis E)
              (fderiv ℝ (fun u : E => extChartAt I y₀ (f u)) w).toLinearMap) k i •
            chartBasisVecFiber (I := I) y₀ k (f w)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [map_smul]
          have hbasis :
              chartBasisVecFiber (I := I) y₀ k (f w) =
                (T₀.continuousLinearEquivAt ℝ (f w) hx).symm
                  ((chartModelBasis E) k) := by
            change T₀.symm (f w) ((chartModelBasis E) k) =
              (T₀.continuousLinearEquivAt ℝ (f w) hx).symm ((chartModelBasis E) k)
            rfl
          rw [hbasis]
          rw [ContinuousLinearEquiv.apply_symm_apply]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)]
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
        g.inner (f w) (mfderiv 𝓘(ℝ, E) I f w ((chartModelBasis E) i))
          (mfderiv 𝓘(ℝ, E) I f w ((chartModelBasis E) j))).det =
      (fderiv ℝ (fun u : E => extChartAt I y₀ (f u)) w).det ^ 2
        * (chartGramMatrix g y₀ (f w)).det := by
  set J : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    LinearMap.toMatrix (chartModelBasis E) (chartModelBasis E)
      (fderiv ℝ (fun u : E => extChartAt I y₀ (f u)) w).toLinearMap with hJ
  have hmul :
      (Matrix.of fun i j =>
          g.inner (f w) (mfderiv 𝓘(ℝ, E) I f w ((chartModelBasis E) i))
            (mfderiv 𝓘(ℝ, E) I f w ((chartModelBasis E) j)))
        = Jᵀ * chartGramMatrix g y₀ (f w) * J := by
    ext i j
    have hsum :
        g.inner (f w) (mfderiv 𝓘(ℝ, E) I f w ((chartModelBasis E) i))
            (mfderiv 𝓘(ℝ, E) I f w ((chartModelBasis E) j))
          = ∑ k, ∑ l, J k i * J l j * chartGramMatrix g y₀ (f w) k l := by
      rw [mfderiv_chartBasis f hf y₀ hx i, mfderiv_chartBasis f hf y₀ hx j]
      have hL :
          g.inner (f w)
              (∑ k, J k i • chartBasisVecFiber (I := I) y₀ k (f w))
            = ∑ k, J k i •
                g.inner (f w) (chartBasisVecFiber (I := I) y₀ k (f w)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [map_smul]
      rw [hL, ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [ContinuousLinearMap.smul_apply]
      have hR :
          g.inner (f w) (chartBasisVecFiber (I := I) y₀ k (f w))
              (∑ l, J l j • chartBasisVecFiber (I := I) y₀ l (f w))
            = ∑ l, J l j *
                g.inner (f w) (chartBasisVecFiber (I := I) y₀ k (f w))
                  (chartBasisVecFiber (I := I) y₀ l (f w)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl ?_
        intro l _
        rw [map_smul, smul_eq_mul]
      rw [hR, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro l _
      rw [chartGramMatrix_apply]
      ring
    rw [Matrix.of_apply, hsum]
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro k _
    ring
  rw [hmul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hJdet : J.det = (fderiv ℝ (fun u : E => extChartAt I y₀ (f u)) w).det := by
    rw [hJ, LinearMap.det_toMatrix]
  rw [hJdet]
  ring

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [CompleteSpace E]
  [T2Space (TangentBundle I M)] in
theorem exp_density_curve
    [ConnectedSpace M] [PseudoEMetricSpace M]
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
              (show TangentSpace I x from (chartModelBasis E i)) t) 1 := by
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
          (show TangentSpace I x from (chartModelBasis E i)) 1
        = mfderiv 𝓘(ℝ, E) I F v ((chartModelBasis E) i) := by
    intro i
    exact intrinsic_jacobi_one (I := I) g hEnorm x v ((chartModelBasis E) i)
  have hgram :
      curveGram (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm x (show TangentSpace I x from v))
          (fun (i : Fin (Module.finrank ℝ E)) (t : ℝ) =>
            intrinsicJacobi g hEnorm x (show TangentSpace I x from v)
              (show TangentSpace I x from (chartModelBasis E i)) t) 1
        = Matrix.of fun i j =>
            g.inner (F v) (mfderiv 𝓘(ℝ, E) I F v ((chartModelBasis E) i))
              (mfderiv 𝓘(ℝ, E) I F v ((chartModelBasis E) j)) := by
    ext i j
    simp only [curveGram, Matrix.of_apply]
    rw [hcol i, hcol j]
    rfl
  rw [curveDensity, hgram, gramDiff_det (I := I) g F hFdiff y₀ hxbase,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  rw [chartDensity]
  ring

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

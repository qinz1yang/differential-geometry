import DifferentialGeometry.Geometry.Operator.Gradient.SpacetimeQuadraticForm
import DifferentialGeometry.Geometry.Operator.Hessian.Trace.ChartInverseGramDerivative
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

namespace DifferentialGeometry.Geometry.Operator

open Filter Set MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [I.Boundaryless] in
theorem chartGradientBilin_eq_sum_inverse_gram_transpose
    (g : SmoothRiemannianMetric I M) (alpha : M) (z : E)
    (u v : E →L[ℝ] ℝ) :
    chartGradientBilin g alpha ((extChartAt I alpha).symm z) u v =
      ∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        chartInvGramOnE g alpha ij.1 ij.2 z *
          u (chartModelBasis E ij.1) * v (chartModelBasis E ij.2) := by
  rw [chartGradientBilin_apply, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← chartInvGramOnE_def, chartInvGramOnE_symm g alpha j i z]

theorem chart_laplacian_residual_eq_gradient
    (g : SmoothRiemannianMetric I M) (alpha : M)
    (f : M → ℝ → ℝ) (test : ℝ × E → ℝ) (z : E × ℝ)
    (hz : z.1 ∈ (extChartAt I alpha).target)
    (hf : DifferentiableAt ℝ
      (fun v : E × ℝ => f ((extChartAt I alpha).symm v.1) v.2) z)
    (htest : DifferentiableAt ℝ test z.swap) (c r : ℝ) :
    let d := (fderiv ℝ
      (fun v : E × ℝ => f ((extChartAt I alpha).symm v.1) v.2) z).comp
        (ContinuousLinearMap.inl ℝ E ℝ)
    let e := (fderiv ℝ (fun v : E × ℝ => test v.swap) z).comp
      (ContinuousLinearMap.inl ℝ E ℝ)
    chartDensityOnE g alpha z.1 *
        (c * normGradSqFun g (fun y => f y z.2) ((extChartAt I alpha).symm z.1) + r) *
          test z.swap +
      (∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        (chartDensityOnE g alpha z.1 * chartInvGramOnE g alpha ij.1 ij.2 z.1) *
          fderiv ℝ (scalarOnE (I := I) alpha (fun y => f y z.2)) z.1
            (chartModelBasis E ij.1) *
          fderiv ℝ test z.swap (0, chartModelBasis E ij.2)) =
      chartDensityOnE g alpha z.1 *
        ((c * chartGradientBilin g alpha ((extChartAt I alpha).symm z.1) d d + r) *
          test z.swap + chartGradientBilin g alpha ((extChartAt I alpha).symm z.1) d e) := by
  dsimp only
  have hsource : (extChartAt I alpha).symm z.1 ∈ (chartAt H alpha).source := by
    simpa only [extChartAt_source] using (extChartAt I alpha).map_target hz
  have hchart : extChartAt I alpha ((extChartAt I alpha).symm z.1) = z.1 :=
    (extChartAt I alpha).right_inv hz
  have hnorm := normGradSqFun_eq_chartGradientBilin_comp_inl
    (g := g) (f := f) (alpha := alpha) (x := (extChartAt I alpha).symm z.1)
    (t := z.2) hsource (by simpa only [hchart, Prod.eta] using hf)
  have hslice := hf.hasFDerivAt.comp z.1
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) z.1 z.2)
  have hdf : fderiv ℝ (scalarOnE (I := I) alpha (fun y => f y z.2)) z.1 =
      (fderiv ℝ (fun v : E × ℝ => f ((extChartAt I alpha).symm v.1) v.2) z).comp
        (ContinuousLinearMap.inl ℝ E ℝ) := hslice.fderiv
  have hswap : DifferentiableAt ℝ (fun v : E × ℝ => test v.swap) z :=
    htest.comp z (differentiableAt_snd.prodMk differentiableAt_fst)
  have hold := htest.hasFDerivAt.comp z.1
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.2 z.1)
  have hnew := hswap.hasFDerivAt.comp z.1
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) z.1 z.2)
  have hde (v : E) : fderiv ℝ test z.swap (0, v) =
      ((fderiv ℝ (fun w : E × ℝ => test w.swap) z).comp
        (ContinuousLinearMap.inl ℝ E ℝ)) v := by
    have hmaps := hold.fderiv.symm.trans hnew.fderiv
    exact congrArg (fun L : E →L[ℝ] ℝ => L v) hmaps
  rw [hchart] at hnorm
  rw [hnorm, hdf]
  simp_rw [hde]
  have hflux := chartGradientBilin_eq_sum_inverse_gram_transpose g alpha z.1
    ((fderiv ℝ (fun v : E × ℝ => f ((extChartAt I alpha).symm v.1) v.2) z).comp
      (ContinuousLinearMap.inl ℝ E ℝ))
    ((fderiv ℝ (fun v : E × ℝ => test v.swap) z).comp
      (ContinuousLinearMap.inl ℝ E ℝ))
  rw [hflux]
  conv_rhs => rw [mul_add, Finset.mul_sum]
  simp only [mul_assoc]

theorem integral_chart_laplacian_residual_eq_setIntegral_gradient
    [MeasurableSpace E] (μ : Measure E) [SFinite μ]
    (g : ℝ → SmoothRiemannianMetric I M) (alpha : M)
    (f : M → ℝ → ℝ) (test : ℝ × E → ℝ) (c : ℝ) (r : ℝ × E → ℝ)
    {K : Set E} {T : Set ℝ} (hK : MeasurableSet K) (hT : MeasurableSet T)
    (hKt : K ⊆ (extChartAt I alpha).target)
    (htest : Differentiable ℝ test) (hsupport : tsupport test ⊆ T ×ˢ K)
    (hf : ∀ᵐ z ∂μ.prod (volume : Measure ℝ), z ∈ K ×ˢ T →
      DifferentiableAt ℝ
        (fun v : E × ℝ => f ((extChartAt I alpha).symm v.1) v.2) z) :
    let d := fun z : E × ℝ => (fderiv ℝ
      (fun v : E × ℝ => f ((extChartAt I alpha).symm v.1) v.2) z).comp
        (ContinuousLinearMap.inl ℝ E ℝ)
    let e := fun z : E × ℝ =>
      (fderiv ℝ (fun v : E × ℝ => test v.swap) z).comp
        (ContinuousLinearMap.inl ℝ E ℝ)
    (∫ p : ℝ × E,
      chartDensityOnE (g p.1) alpha p.2 *
          (c * normGradSqFun (g p.1) (fun y => f y p.1)
            ((extChartAt I alpha).symm p.2) + r p) * test p +
        (∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          (chartDensityOnE (g p.1) alpha p.2 *
            chartInvGramOnE (g p.1) alpha ij.1 ij.2 p.2) *
            fderiv ℝ (scalarOnE (I := I) alpha (fun y => f y p.1)) p.2
              (chartModelBasis E ij.1) *
            fderiv ℝ test p (0, chartModelBasis E ij.2)) ∂volume.prod μ) =
      ∫ z in K ×ˢ T,
        chartDensityOnE (g z.2) alpha z.1 *
          ((c * chartGradientBilin (g z.2) alpha ((extChartAt I alpha).symm z.1)
              (d z) (d z) + r z.swap) * test z.swap +
            chartGradientBilin (g z.2) alpha ((extChartAt I alpha).symm z.1)
              (d z) (e z)) ∂μ.prod volume := by
  dsimp only
  let S : ℝ × E → ℝ := fun p =>
    chartDensityOnE (g p.1) alpha p.2 *
        (c * normGradSqFun (g p.1) (fun y => f y p.1)
          ((extChartAt I alpha).symm p.2) + r p) * test p +
      ∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        (chartDensityOnE (g p.1) alpha p.2 *
          chartInvGramOnE (g p.1) alpha ij.1 ij.2 p.2) *
          fderiv ℝ (scalarOnE (I := I) alpha (fun y => f y p.1)) p.2
            (chartModelBasis E ij.1) *
          fderiv ℝ test p (0, chartModelBasis E ij.2)
  have hzero : ∀ p, p ∉ T ×ˢ K → S p = 0 := by
    intro p hp
    have hnot : p ∉ tsupport test := fun h => hp (hsupport h)
    have hval : test p = 0 := image_eq_zero_of_notMem_tsupport hnot
    have hder : fderiv ℝ test p = 0 := fderiv_of_notMem_tsupport ℝ hnot
    simp only [S, hval, hder, zero_apply, mul_zero,
      Finset.sum_const_zero, add_zero]
  change (∫ p, S p ∂volume.prod μ) = _
  calc
    _ = ∫ p in T ×ˢ K, S p ∂volume.prod μ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ = ∫ z in K ×ˢ T, S z.swap ∂μ.prod volume :=
      (setIntegral_prod_swap T K S).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hf, ae_restrict_mem (hK.prod hT)] with z hz hmem
      exact chart_laplacian_residual_eq_gradient (g z.2) alpha f test z
        (hKt hmem.1) (hz hmem) (htest z.swap) c (r z.swap)

end DifferentialGeometry.Geometry.Operator

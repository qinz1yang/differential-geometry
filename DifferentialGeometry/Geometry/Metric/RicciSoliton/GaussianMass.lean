import DifferentialGeometry.Geometry.Metric.RicciSoliton.GaussianRigidity
import DifferentialGeometry.Analysis.Integration.Measure.PullbackCross
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Euclidean
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open MeasureTheory
open scoped Manifold ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

omit [SigmaCompactSpace M] in
theorem isGaussianGradientRicciSoliton_exists_isometry_of_hamiltonNormalized
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (hGaussian : isGaussianGradientRicciSoliton (E := E) g f 1)
    (hnormal : hamiltonNormalized g f 1) :
    ∃ e : M ≃ₘ⟮I, 𝓘(ℝ, E)⟯ E,
      Diffeomorph.pullbackMetricCross euclideanMetric e = g ∧
        f = gaussianPotential.comp e.toContMDiffMap := by
  obtain ⟨hone, e, b, hg, hf⟩ := hGaussian
  have hg' : Diffeomorph.pullbackMetricCross euclideanMetric e = g := by
    rw [hg]
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    simp only [scaleMetric_inner, one_mul]
  have hpot (x : M) : f x + b = ‖e x‖ ^ 2 / 4 := by
    have hx := congrArg (fun q : C^∞⟮I, M; ℝ⟯ => q x) hf
    exact hx
  have hzero : f (e.symm 0) + b = 0 := by
    simpa only [e.apply_symm_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, zero_div] using hpot (e.symm 0)
  have hmin : IsMinOn (f : M → ℝ) Set.univ (e.symm 0) := by
    intro x _
    change f (e.symm 0) ≤ f x
    have hx := hpot x
    nlinarith [sq_nonneg ‖e x‖]
  have hgrad := Operator.gradientFun_eq_zero_at_spatial_min g
    (hmin.isLocalMin (isOpen_univ.mem_nhds (Set.mem_univ _)))
    (f.contMDiff.mdifferentiableAt (by simp))
  have hscalar : metricScalarAt g (e.symm 0) = 0 :=
    isGaussianGradientRicciSoliton_scalarCurvature_eq_zero ⟨hone, e, b, hg, hf⟩ _
  have hvalue := hnormal (e.symm 0)
  rw [Connection.gradient_eq_gradFun] at hgrad
  rw [hscalar, hgrad] at hvalue
  simp only [map_zero, zero_add, one_mul] at hvalue
  have hb : b = 0 := by linarith
  refine ⟨e, hg', ?_⟩
  apply ContMDiffMap.ext
  intro x
  change f x = gaussianPotential (e x)
  simpa only [hb, add_zero, gaussianPotential_apply] using hpot x

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

theorem isGaussianGradientRicciSoliton_lintegral_exp_neg_of_hamiltonNormalized
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (hGaussian : isGaussianGradientRicciSoliton (E := E) g f 1)
    (hnormal : hamiltonNormalized g f 1) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-f x)) 
      ∂DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g =
      ENNReal.ofReal ((4 * Real.pi) ^ ((Module.finrank ℝ E : ℝ) / 2)) := by
  obtain ⟨e, hg, hf⟩ :=
    isGaussianGradientRicciSoliton_exists_isometry_of_hamiltonNormalized hGaussian hnormal
  rw [← hg, riemannianVolumeMeasure_pullback_cross, riemannianVolumeMeasure_euclideanMetric]
  have hmeas : Measurable (fun x : M => ENNReal.ofReal (Real.exp (-f x))) := by
    fun_prop
  rw [MeasureTheory.lintegral_map hmeas e.symm.contMDiff.continuous.measurable]
  have hfun : (fun x : E => ENNReal.ofReal (Real.exp (-f (e.symm x)))) =
      fun x => ENNReal.ofReal (Real.exp (-(1 / 4 : ℝ) * ‖x‖ ^ 2)) := by
    funext x
    rw [hf]
    change ENNReal.ofReal (Real.exp (-gaussianPotential (e (e.symm x)))) = _
    rw [e.apply_symm_apply, gaussianPotential_apply]
    congr 2
    ring
  rw [hfun]
  have hi : Integrable (fun x : E => Real.exp (-(1 / 4 : ℝ) * ‖x‖ ^ 2)) := by
    have hc := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (V := E) (b := (1 / 4 : ℂ)) (by norm_num) 0 (0 : E)
    refine hc.norm.congr (Filter.Eventually.of_forall fun x => ?_)
    norm_num [Complex.norm_exp, ← Complex.ofReal_pow, Complex.mul_re]
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le),
    GaussianFourier.integral_rexp_neg_mul_sq_norm (by norm_num : (0 : ℝ) < 1 / 4)]
  congr 2
  ring

theorem normalizedGradientRicciSoliton_lintegral_exp_neg_of_scalar_eq_zero
    [ConnectedSpace M] [NeZero (Module.finrank ℝ E)]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (h : normalizedGradientRicciSoliton g f)
    {x : M} (hx : metricScalarAt g x = 0) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (-f y)) 
      ∂DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g =
      ENNReal.ofReal ((4 * Real.pi) ^ ((Module.finrank ℝ E : ℝ) / 2)) :=
  isGaussianGradientRicciSoliton_lintegral_exp_neg_of_hamiltonNormalized
    (normalizedGradientRicciSoliton_isGaussian_of_scalar_eq_zero h hx)
    (normalizedGradientRicciSoliton_hamilton_normalized h)

end DifferentialGeometry.Geometry

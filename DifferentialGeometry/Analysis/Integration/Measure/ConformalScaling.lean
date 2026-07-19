import DifferentialGeometry.Geometry.Metric.Conformal
import DifferentialGeometry.Analysis.Integration.Measure.Invariance
import DifferentialGeometry.Analysis.Integration.Measure.RiemannianMeasure

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace DifferentialGeometry.Integral.Measure

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private theorem sqrt_pow (c : Real) (hc : 0 ≤ c) (n : Nat) :
    Real.sqrt (c ^ n) = Real.sqrt c ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Real.sqrt_mul (pow_nonneg hc n), ih, pow_succ]


theorem chartGram_conformal
    (f : M → Real) (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (g : SmoothRiemannianMetric I M) (x₀ x : M) :
    chartGramMatrix (conformalMetric f hf g) x₀ x =
      Real.exp (2 * f x) • chartGramMatrix g x₀ x := by
  ext i j
  simp [chartGramMatrix_apply, conformalMetric_inner]


theorem chartDensity_conformal
    (f : M → Real) (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (g : SmoothRiemannianMetric I M) (x₀ x : M) :
    chartDensity (conformalMetric f hf g) x₀ x =
      Real.exp ((Module.finrank Real E) * f x) * chartDensity g x₀ x := by
  unfold chartDensity
  rw [chartGram_conformal (I := I) f hf g x₀ x, Matrix.det_smul]
  simp only [Fintype.card_fin]
  rw [Real.sqrt_mul (pow_nonneg (Real.exp_pos _).le _)]
  congr 1
  rw [sqrt_pow (Real.exp (2 * f x)) (Real.exp_pos _).le (Module.finrank Real E)]
  have hsq : Real.exp (2 * f x) = Real.exp (f x) ^ 2 := by
    rw [two_mul, Real.exp_add, sq]
  rw [hsq, Real.sqrt_sq (Real.exp_pos _).le, ← Real.exp_nat_mul]


theorem measurable_conformalDensity
    (f : M → Real) (hf : ContMDiff I 𝓘(Real, Real) ∞ f) :
    Measurable
      (fun x : M => ENNReal.ofReal (Real.exp ((Module.finrank Real E) * f x))) := by
  have hcont : Continuous
      (fun x : M => Real.exp ((Module.finrank Real E : ℝ) * f x)) :=
    Real.continuous_exp.comp (continuous_const.mul hf.continuous)
  exact ENNReal.measurable_ofReal.comp hcont.measurable


theorem riemMeasure_conformal
    (f : M → Real) (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M Set.univ) :
    riemannianMeasure (conformalMetric f hf g) ρ =
      (riemannianMeasure g ρ).withDensity
        (fun x : M => ENNReal.ofReal (Real.exp ((Module.finrank Real E) * f x))) := by
  set D : M → ℝ≥0∞ :=
    fun x : M => ENNReal.ofReal (Real.exp ((Module.finrank Real E) * f x)) with hDdef
  have hD : Measurable D := measurable_conformalDensity (I := I) f hf
  have key : ∀ (F : M → ℝ≥0∞), Measurable F →
      ∫⁻ x, F x ∂(riemannianMeasure (conformalMetric f hf g) ρ) =
        ∫⁻ x, F x ∂((riemannianMeasure g ρ).withDensity D) := by
    intro F hF
    rw [lintegral_withDensity_eq_lintegral_mul (riemannianMeasure g ρ) hD hF]
    simp only [Pi.mul_apply]
    rw [riemannianMeasure_lintegral_eq (conformalMetric f hf g) ρ hF,
      riemannianMeasure_lintegral_eq g ρ (hD.mul hF)]
    refine tsum_congr (fun α => ?_)
    have hρα : Measurable (fun x : M => ENNReal.ofReal (ρ α x)) :=
      measurable_ofReal_pou_weight ρ α
    rw [chartLocalMeasure_lintegral (conformalMetric f hf g) α (hρα.mul hF),
      chartLocalMeasure_lintegral g α (hρα.mul (hD.mul hF))]
    refine lintegral_congr (fun y => ?_)
    rw [chartDensity_conformal (I := I) f hf g α ((extChartAt I α).symm y),
      ENNReal.ofReal_mul (Real.exp_pos _).le]
    simp only [hDdef]
    ring
  refine Measure.ext fun s hs => ?_
  rw [← lintegral_indicator_one hs, ← lintegral_indicator_one hs]
  exact key (s.indicator 1) (measurable_const.indicator hs)


theorem volume_conformal [T2Space M] [SigmaCompactSpace M]
    (f : M → Real) (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (g : SmoothRiemannianMetric I M) :
    riemannianVolumeMeasure (I := I) (M := M) (conformalMetric f hf g) =
      (riemannianVolumeMeasure (I := I) (M := M) g).withDensity
        (fun x : M => ENNReal.ofReal (Real.exp ((Module.finrank Real E) * f x))) := by
  rw [riemannianVolumeMeasure_def, riemannianVolumeMeasure_def]
  exact riemMeasure_conformal (I := I) f hf g (chartAtlasPOU I M)


theorem lintegral_volume_conformal [T2Space M] [SigmaCompactSpace M]
    (f : M → Real) (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (g : SmoothRiemannianMetric I M)
    {F : M → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) (conformalMetric f hf g)) =
      ∫⁻ x, ENNReal.ofReal (Real.exp ((Module.finrank Real E) * f x)) * F x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [volume_conformal (I := I) f hf g,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_conformalDensity (I := I) f hf) hF]
  simp only [Pi.mul_apply]

end

end DifferentialGeometry.Integral.Measure

import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensity
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open MeasureTheory Filter
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.Integral.Measure
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem integrable_riemannianVolumeMeasure_iff
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (q h : SmoothRiemannianMetric I M) (f : M → F) :
    Integrable f (riemannianVolumeMeasure (I := I) (M := M) h) ↔
      Integrable (fun x => riemannianVolumeDensity q h x • f x) (riemannianVolumeMeasure (I := I) (M := M) q) := by
  rw [riemannianVolumeMeasure_eq_withDensity q h]
  have hρ := (riemannianVolumeDensity_contMDiff q h).continuous.measurable.ennreal_ofReal
  have ht : ∀ᵐ x ∂riemannianVolumeMeasure (I := I) (M := M) q,
      ENNReal.ofReal (riemannianVolumeDensity q h x) < ⊤ := Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [integrable_withDensity_iff_integrable_smul' hρ ht]
  simp only [ENNReal.toReal_ofReal (riemannianVolumeDensity_pos q h _).le]

theorem integrable_prod_volumeDensity_smul_iff
    {P F : Type*} [MeasurableSpace P] (μ : MeasureTheory.Measure P)
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (q : SmoothRiemannianMetric I M) (g : P → SmoothRiemannianMetric I M)
    (f : P × M → F)
    (hf : AEStronglyMeasurable (fun p => riemannianVolumeDensity q (g p.1) p.2 • f p)
      (μ.prod (riemannianVolumeMeasure (I := I) (M := M) q))) :
    Integrable (fun p => riemannianVolumeDensity q (g p.1) p.2 • f p)
        (μ.prod (riemannianVolumeMeasure (I := I) (M := M) q)) ↔
      (∀ᵐ t ∂μ, Integrable (fun x => f (t, x)) (riemannianVolumeMeasure (I := I) (M := M) (g t))) ∧
        Integrable (fun t => ∫ x, ‖f (t, x)‖ ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) μ := by
  let _ := riemannianVolumeMeasure_sigmaFinite q
  have hnorm (t : P) :
      (∫ x, ‖riemannianVolumeDensity q (g t) x • f (t, x)‖
        ∂riemannianVolumeMeasure (I := I) (M := M) q) =
      ∫ x, ‖f (t, x)‖ ∂riemannianVolumeMeasure (I := I) (M := M) (g t) := by
    rw [integral_riemannianVolumeMeasure_eq_integral_volumeDensity_smul q (g t)]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (riemannianVolumeDensity_pos q (g t) x), smul_eq_mul]
  rw [integrable_prod_iff hf]
  have hfiber (t : P) := integrable_riemannianVolumeMeasure_iff q (g t) (fun x => f (t, x))
  simp_rw [← hfiber, hnorm]

theorem integrable_prod_volumeDensity_smul_of_lintegral_norm_le
    {P F : Type*} [MeasurableSpace P] (μ : MeasureTheory.Measure P) [IsFiniteMeasure μ]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (q : SmoothRiemannianMetric I M) (g : P → SmoothRiemannianMetric I M)
    (f : P × M → F)
    (hf : AEStronglyMeasurable (fun p => riemannianVolumeDensity q (g p.1) p.2 • f p)
      (μ.prod (riemannianVolumeMeasure (I := I) (M := M) q)))
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hmass : ∀ᵐ t ∂μ, (∫⁻ x, ENNReal.ofReal ‖f (t, x)‖
      ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) ≤ C) :
    Integrable (fun p => riemannianVolumeDensity q (g p.1) p.2 • f p)
      (μ.prod (riemannianVolumeMeasure (I := I) (M := M) q)) := by
  let _ := riemannianVolumeMeasure_sigmaFinite q
  refine ⟨hf, ?_⟩
  rw [hasFiniteIntegral_iff_norm, lintegral_prod _ hf.norm.aemeasurable.ennreal_ofReal]
  have heq (t : P) :
      (∫⁻ x, ENNReal.ofReal ‖riemannianVolumeDensity q (g t) x • f (t, x)‖
        ∂riemannianVolumeMeasure (I := I) (M := M) q) =
      ∫⁻ x, ENNReal.ofReal ‖f (t, x)‖ ∂riemannianVolumeMeasure (I := I) (M := M) (g t) := by
    rw [riemannianVolumeMeasure_eq_withDensity q (g t),
      lintegral_withDensity_eq_lintegral_mul_non_measurable _
        (riemannianVolumeDensity_contMDiff q (g t)).continuous.measurable.ennreal_ofReal
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply lintegral_congr
    intro x
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (riemannianVolumeDensity_pos q (g t) x)]
    exact ENNReal.ofReal_mul (riemannianVolumeDensity_pos q (g t) x).le
  simp_rw [heq]
  apply lt_of_le_of_lt (lintegral_mono_ae hmass)
  rw [lintegral_const]
  exact ENNReal.mul_lt_top hC.lt_top (measure_lt_top μ Set.univ)

end DifferentialGeometry.Integral.Measure

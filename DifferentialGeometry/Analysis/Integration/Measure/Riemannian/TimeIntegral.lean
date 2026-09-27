import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensityContinuity
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

namespace DifferentialGeometry.Integral.Measure

open Set MeasureTheory
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {T : Type*} [MeasurableSpace T]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem aestronglyMeasurable_integral_riemannianVolumeMeasure
    (q : SmoothRiemannianMetric I M) (g : T → SmoothRiemannianMetric I M)
    (μ : Measure T) {f : T × M → V}
    (hf : AEStronglyMeasurable
      (fun z : T × M => riemannianVolumeDensity q (g z.1) z.2 • f z)
      (μ.prod (riemannianVolumeMeasure (I := I) (M := M) q))) :
    AEStronglyMeasurable
      (fun t => ∫ x, f (t, x) ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) μ := by
  let : SigmaFinite (riemannianVolumeMeasure (I := I) (M := M) q) :=
    riemannianVolumeMeasure_sigmaFinite q
  have heq (t : T) :=
    integral_riemannianVolumeMeasure_eq_integral_volumeDensity_smul q (g t)
      (fun x => f (t, x))
  exact hf.integral_prod_right'.congr (Filter.Eventually.of_forall fun t => (heq t).symm)


theorem aestronglyMeasurable_integral_riemannianVolumeMeasure_of_continuous_chartGram
    [TopologicalSpace T] [OpensMeasurableSpace T]
    (q : SmoothRiemannianMetric I M) (g : T → SmoothRiemannianMetric I M)
    (μ : Measure T) {f : T × M → V}
    (hgram : ∀ (alpha : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn (fun z : T × M =>
        DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g z.1) alpha z.2 i j)
        (univ ×ˢ (trivializationAt E (TangentSpace I) alpha).baseSet))
    (hf : AEStronglyMeasurable f
      (μ.prod (riemannianVolumeMeasure (I := I) (M := M) q))) :
    AEStronglyMeasurable
      (fun t => ∫ x, f (t, x) ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) μ := by
  let : SecondCountableTopology H := I.secondCountableTopology
  let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  have hrho : Continuous
      (fun z : T × M => riemannianVolumeDensity q (g z.1) z.2) := by
    rw [← continuousOn_univ]
    simpa only [univ_prod_univ] using
      riemannianVolumeDensity_family_continuousOn q g hgram
  exact aestronglyMeasurable_integral_riemannianVolumeMeasure q g μ
    (hrho.aestronglyMeasurable.smul hf)

theorem integrable_integral_riemannianVolumeMeasure_of_integral_norm_le
    (q : SmoothRiemannianMetric I M) (g : T → SmoothRiemannianMetric I M)
    (μ : Measure T) {f : T × M → V}
    (hf : AEStronglyMeasurable
      (fun z : T × M => riemannianVolumeDensity q (g z.1) z.2 • f z)
      (μ.prod (riemannianVolumeMeasure (I := I) (M := M) q)))
    {B : T → ℝ} (hB : Integrable B μ)
    (hbound : ∀ᵐ t ∂μ,
      (∫ x, ‖f (t, x)‖ ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) ≤ B t) :
    Integrable
      (fun t => ∫ x, f (t, x) ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) μ ∧
      ‖∫ t, ∫ x, f (t, x) ∂riemannianVolumeMeasure (I := I) (M := M) (g t) ∂μ‖ ≤
        ∫ t, B t ∂μ := by
  have hnorm : ∀ᵐ t ∂μ,
      ‖∫ x, f (t, x) ∂riemannianVolumeMeasure (I := I) (M := M) (g t)‖ ≤ B t := by
    filter_upwards [hbound] with t ht
    exact (norm_integral_le_integral_norm _).trans ht
  exact ⟨hB.mono' (aestronglyMeasurable_integral_riemannianVolumeMeasure q g μ hf) hnorm,
    norm_integral_le_of_norm_le hB hnorm⟩

theorem integrable_integral_riemannianVolumeMeasure_of_uniform_integral_norm_bound
    (q : SmoothRiemannianMetric I M) (g : T → SmoothRiemannianMetric I M)
    (μ : Measure T) [IsFiniteMeasure μ] {f : T × M → V}
    (hf : AEStronglyMeasurable
      (fun z : T × M => riemannianVolumeDensity q (g z.1) z.2 • f z)
      (μ.prod (riemannianVolumeMeasure (I := I) (M := M) q)))
    {C : ℝ} (hbound : ∀ᵐ t ∂μ,
      (∫ x, ‖f (t, x)‖ ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) ≤ C) :
    Integrable
      (fun t => ∫ x, f (t, x) ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) μ ∧
      ‖∫ t, ∫ x, f (t, x) ∂riemannianVolumeMeasure (I := I) (M := M) (g t) ∂μ‖ ≤
        C * μ.real univ := by
  obtain ⟨hi, hb⟩ := integrable_integral_riemannianVolumeMeasure_of_integral_norm_le
    q g μ hf (integrable_const C) hbound
  exact ⟨hi, by simpa only [integral_const, smul_eq_mul, mul_comm] using hb⟩

end DifferentialGeometry.Integral.Measure

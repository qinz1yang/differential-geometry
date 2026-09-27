import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.TimeIntegral
import DifferentialGeometry.Analysis.Integration.Measure.GradientPairingFamily

noncomputable section

namespace DifferentialGeometry.Integral.Measure

open Set MeasureTheory
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {T : Type*} [TopologicalSpace T] [MeasurableSpace T] [OpensMeasurableSpace T]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem integrable_integral_mul_inner_gradientFun_family
    (q : SmoothRiemannianMetric I M) (g : T → SmoothRiemannianMetric I M)
    (μ : Measure T) (f h : T → M → ℝ) (w : T × M → ℝ)
    (hf : Continuous (Function.uncurry f)) (hh : Continuous (Function.uncurry h))
    (hgram : ∀ (alpha : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn (fun z : T × M => chartGramMatrix (g z.1) alpha z.2 i j)
        (univ ×ˢ (chartAt H alpha).source))
    (hw : AEStronglyMeasurable w
      (μ.prod (riemannianVolumeMeasure (I := I) (M := M) q)))
    {B : T → ℝ} (hB : Integrable B μ)
    (hbound : ∀ᵐ t ∂μ,
      (∫ x, |w (t, x) * (g t).inner x
        (gradientFun (g t) (f t) x) (gradientFun (g t) (h t) x)|
        ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) ≤ B t) :
    Integrable (fun t => ∫ x, w (t, x) * (g t).inner x
      (gradientFun (g t) (f t) x) (gradientFun (g t) (h t) x)
      ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) μ ∧
      |∫ t, ∫ x, w (t, x) * (g t).inner x
        (gradientFun (g t) (f t) x) (gradientFun (g t) (h t) x)
        ∂riemannianVolumeMeasure (I := I) (M := M) (g t) ∂μ| ≤ ∫ t, B t ∂μ := by
  let : SecondCountableTopology H := I.secondCountableTopology
  let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  have hrho : Continuous
      (fun z : T × M => riemannianVolumeDensity q (g z.1) z.2) := by
    rw [← continuousOn_univ]
    simpa only [univ_prod_univ, trivializationAt_baseSet_eq_chartAt_source] using
      riemannianVolumeDensity_family_continuousOn q g (J := (univ : Set T))
        (fun alpha i j => by
          simpa only [trivializationAt_baseSet_eq_chartAt_source] using hgram alpha i j)
  have hpair := measurable_inner_gradientFun_family g f h hf hh hgram
  have hflux := hw.mul hpair.aestronglyMeasurable
  simpa only [Real.norm_eq_abs, Pi.mul_apply] using
    integrable_integral_riemannianVolumeMeasure_of_integral_norm_le q g μ
      (hrho.aestronglyMeasurable.smul hflux) hB hbound

end DifferentialGeometry.Integral.Measure

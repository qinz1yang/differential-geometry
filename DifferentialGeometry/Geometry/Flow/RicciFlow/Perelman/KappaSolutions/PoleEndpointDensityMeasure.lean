import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RegularPoleRescalings
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Measure


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

private local instance endpointDensityComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.sigmaCompact PointedFlowData.t2
private local instance endpointDensityMeasurable : MeasurableSpace F.M := borel F.M
private local instance endpointDensityBorel : BorelSpace F.M := ⟨rfl⟩

theorem poleRescaledFlowSeq_redDensityMeasure_eq_endpoint_withDensity
    (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b) (i : ℕ) (p : F.M) (t : ℝ) :
    redDensityMeasure
      ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S
      0 p (1 - t) =
      Measure.withDensity
        (riemannianVolumeMeasure (I := I) (M := F.M)
          (((poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S.base.metric t))
        (fun y => ENNReal.ofReal (redDensity
          ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S
          0 p y (1 - t))) := by
  have htime : (0 : ℝ) - (1 - t) = t - 1 := by ring
  unfold redDensityMeasure
  rw [poleEndpointRescaledFlowSeq_metric_eq_shift, htime]
  rfl

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.ClosedIntervalRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.MetricGauge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.ClosedIntervalDerivative

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [NeZero (Module.finrank ℝ E)]

theorem ricciSharp_family_contMDiffOn_closed
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : Icc a b ⊆ D.carrier) (hregular : Ioo a b ⊆ D.regular) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : ℝ × M => (⟨p.2, ricciSharp (I := I) (S.base.metric p.1) p.2⟩ :
        TotalSpace (E →L[ℝ] E)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x)))
      (Icc c b ×ˢ (univ : Set M)) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hg := solution_metric_tensor_contMDiffOn_closed S hS hac hcb hslab hregular
  have hv := metricGaugeVelocityWithin_contMDiffOn hg (uniqueDiffOn_Icc hcb)
  apply hv.congr
  intro p hp
  congr 1
  symm
  apply metricGaugeVelocityWithin_eq_ricciSharp_of_hasDerivWithinAt S.base.metric
    (uniqueDiffOn_Icc hcb p.1 hp.1) p.2 ((hg p hp).of_le (by simp))
  intro v w
  simpa only [SolutionOn.ricciAt, SolutionFamily.ricciAt,
    metricRicciAt_apply_eq_ricciTensor, SolutionOn.family_metric] using
    metric_inner_hasDerivWithinAt_on_closed_interval S hS hcb
      (fun t ht => hslab ⟨hac.le.trans ht.1, ht.2⟩)
      (fun t ht => hregular ⟨hac.trans ht.1, ht.2⟩) hp.1 p.2 v w

end DifferentialGeometry.PDE.RicciFlow

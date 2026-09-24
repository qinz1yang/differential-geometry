import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TowerInductionStep
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCorePresentation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff

noncomputable section
open Set
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

variable {P : OrientedThreeStage.{u}} {H : RetainedCoreHistory P}
  (T : ℝ) (hT : H.horizon ≤ T)
  (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
  (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount))

private def IncomingBackwardNeck.extendHorizon
    {i : Fin H.eventCount} {δ r : ℝ} {k : ℕ}
    {neck : NormalizedNeck (H.toHistory.event i).terminal.metric δ k}
    (N : IncomingBackwardNeck H.toHistory i neck r) :
    IncomingBackwardNeck (H.extendHorizon T hT S hS).toHistory i neck r := by
  cases N
  constructor <;> assumption

protected def GeometricCutoffRecord.extendHorizon
    {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H.toHistory i p) :
    GeometricCutoffRecord (H.extendHorizon T hT S hS).toHistory i p := by
  exact { R with backward := fun α => IncomingBackwardNeck.extendHorizon T hT S hS (R.backward α) }

theorem RetainedCoreHistory.boundaryFrameReversing_extendHorizon
    (hbfr : ∀ i : Fin H.eventCount, (H.coreEvent i).transition.boundaryFrameReversing) :
    ∀ i : Fin (H.extendHorizon T hT S hS).eventCount,
      ((H.extendHorizon T hT S hS).coreEvent i).transition.boundaryFrameReversing := hbfr

theorem RetainedCoreHistory.poincareStandardDiscarded_extendHorizon
    (hctrl : ∀ i : Fin H.eventCount, (H.coreEvent i).toMetricCutCapEvent.poincareStandardDiscarded) :
    ∀ i : Fin (H.extendHorizon T hT S hS).eventCount,
      ((H.extendHorizon T hT S hS).coreEvent i).toMetricCutCapEvent.poincareStandardDiscarded := hctrl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

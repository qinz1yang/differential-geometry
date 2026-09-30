import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.SlabCompatibility
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TowerBookkeeping
set_option autoImplicit false
noncomputable section
open Set
namespace GC.GeneralFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

theorem marking_of_actual_prefix {P : OrientedThreeStage.{u}} {g : P.Metric}
    {H K : ObservedHistory.{u}} (A : InitialIdentification P g H)
    (hp : H.IsPrefixOf K) : ∃ A' : InitialIdentification P g K, A.IsPrefixOf A' := by
  have hs : K.stage 0 = H.stage 0 := by
    simpa only [Fin.cast_zero,ObservedHistory.restrict_stage_zero]
      using hp.presentation.stage_eq 0
  have hm : HEq (K.initialMetric 0) (H.initialMetric 0) := by
    simpa only [Fin.cast_zero,ObservedHistory.restrict_initialMetric_zero,
      ObservedHistory.restrict_stage_zero] using hp.presentation.initialMetric_heq 0
  exact ⟨A.ofStageZero hs hm, hp, (A.map_of_stageZero_heq hs hm).symm⟩

theorem marked_singular_event_extension {P Q : OrientedThreeStage.{u}} {g : P.Metric}
    (H : RetainedCoreHistory.{u}) (A : InitialIdentification P g H.toHistory) {s : ℝ}
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hi : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (hs : E.incoming.SingularEndpoint) :
    ∃ A' : InitialIdentification P g (H.appendEvent E.incoming.lt E hi).toHistory,
      A.IsPrefixOf A' :=
  marking_of_actual_prefix A (actual_singular_event_preserves_prefix H E hi hs)

theorem marked_closed_extension {P : OrientedThreeStage.{u}} {g : P.Metric}
    (H : RetainedCoreHistory.{u}) (A : InitialIdentification P g H.toHistory)
    {T : ℝ} (hT : H.horizon ≤ T)
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab
      (H.time (Fin.last H.eventCount)) T)
    (hi : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    ∃ A' : InitialIdentification P g (H.extendHorizon T hT S hi).toHistory,
      A.IsPrefixOf A' :=
  marking_of_actual_prefix A (actual_closed_extension_preserves_prefix H hT S hi)

end GC.GeneralFlow

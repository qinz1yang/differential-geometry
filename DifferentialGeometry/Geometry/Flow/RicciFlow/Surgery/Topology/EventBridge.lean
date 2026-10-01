import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import DifferentialGeometry.Topology.ThreeManifold.Surgery.CutCap.CappingRealization
import DifferentialGeometry.Topology.ThreeManifold.Surgery.CutCap.StandardConnectedSum
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingSum
import DifferentialGeometry.Topology.ThreeManifold.OrientedStage
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FiniteHistory
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.History
import DifferentialGeometry.Topology.Embedding.Diffeomorph
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import DifferentialGeometry.Topology.ThreeManifold.Surgery.CutCap.Defs
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandard

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def _root_.DifferentialGeometry.Topology.ClosedOrientedManifold.IncomingSlab.toSurgery {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) :
    DifferentialGeometry.PDE.RicciFlow.Surgery.IncomingSlab
      P a s where
  lt := G.lt
  flow := G.flow
  equation := G.equation
  smoothUpTo := G.smoothUpTo

def _root_.DifferentialGeometry.Topology.ClosedOrientedManifold.IncomingSlab.TerminalLimitMetric.toSurgery
    {P : OrientedThreeStage.{u}} {a s : ℝ}
    {G : P.IncomingSlab a s} (L : G.TerminalLimitMetric) :
    (G.toSurgery).TerminalLimitMetric where
  metric := L.metric
  converges := L.converges

theorem _root_.DifferentialGeometry.Topology.ClosedOrientedManifold.IncomingSlab.toSurgery_lt {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : (G.toSurgery).lt = G.lt := rfl

theorem _root_.DifferentialGeometry.Topology.ClosedOrientedManifold.IncomingSlab.toSurgery_flow {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : (G.toSurgery).flow = G.flow := rfl

theorem _root_.DifferentialGeometry.Topology.ClosedOrientedManifold.IncomingSlab.toSurgery_equation {P : OrientedThreeStage.{u}}
    {a s : ℝ} (G : P.IncomingSlab a s) : (G.toSurgery).equation = G.equation := rfl

theorem _root_.DifferentialGeometry.Topology.ClosedOrientedManifold.IncomingSlab.TerminalLimitMetric.toSurgery_metric
    {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}
    (L : G.TerminalLimitMetric) : (L.toSurgery).metric = L.metric := rfl

theorem _root_.DifferentialGeometry.Topology.ClosedOrientedManifold.IncomingSlab.toSurgery_terminalRegularRegion
    {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) :
    (G.toSurgery).terminalRegularRegion = G.terminalRegularRegion := rfl

theorem _root_.DifferentialGeometry.Topology.ClosedOrientedManifold.IncomingSlab.toSurgery_terminalRegularOpen
    {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) :
    (G.toSurgery).terminalRegularOpen = G.terminalRegularOpen := rfl


def ObservedHistory.toSurgeryFiniteSurgeryHistory (H : ObservedHistory.{u})
    (hn : 0 < H.eventCount)
    (hev : (i : Fin H.eventCount) →
      DifferentialGeometry.PDE.RicciFlow.Surgery.MetricCutCapEvent
        (H.stage i.castSucc)
        (H.stage i.succ)
        (H.time i.castSucc) (H.time i.succ))
    (hev_initial : ∀ i : Fin H.eventCount,
      (hev i).incoming.flow.base.metric (H.time i.castSucc) = H.initialMetric i.castSucc)
    (hev_output : ∀ i : Fin H.eventCount,
      (hev i).outputMetric = H.initialMetric i.succ) :
    DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.{u} where
  eventCount := H.eventCount
  eventCount_pos := hn
  time := H.time
  time_strictMono := H.time_strictMono
  time_zero := H.time_zero
  stage := fun i => (H.stage i)
  initialMetric := fun i => H.initialMetric i
  event := hev
  event_initial := hev_initial
  event_output := hev_output



namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ}

theorem surgeryPresentation_coreInclusion (E : MetricCutCapEvent P Q a s)
    (hc : SmoothCutCapCompletion E.transition) (x : E.old) :
    (SphericalCutCapTransition.ofSmoothCutCapTransition E.transition hc).presentation
        ((SphericalCutCapTransition.ofSmoothCutCapTransition E.transition hc).capping.coreInclusion
          x.1) =
      Sum.inl (E.oldOutput x) := by
  rw [SphericalCutCapTransition.ofSmoothCutCapTransition_presentation,
    SphericalCutCapTransition.ofSmoothCutCapTransition_coreInclusion,
    E.transition.presentation_eq, E.oldOutput_eq]
  rfl

theorem surgeryRetainedCore (E : MetricCutCapEvent P Q a s) (hc : SmoothCutCapCompletion E.transition) :
    E.old ⊆ (SphericalCutCapTransition.ofSmoothCutCapTransition E.transition hc).retainedCore :=
  fun _ hx =>
    (SphericalCutCapTransition.retainedCore_iff E.transition hc _).mpr (E.old_retained hx)

theorem surgeryContainsOutside (E : MetricCutCapEvent P Q a s) (hc : SmoothCutCapCompletion E.transition)
    (x : (SphericalCutCapTransition.ofSmoothCutCapTransition E.transition hc).tubes.core)
    (hx : x ∈
      (SphericalCutCapTransition.ofSmoothCutCapTransition E.transition hc).retainedCore)
    (hnot : x.1 ∉
      (SphericalCutCapTransition.ofSmoothCutCapTransition E.transition hc).tubes.surgeryRegion) :
    x ∈ (E.old : Set ↑(SphericalCutCapTransition.ofSmoothCutCapTransition E.transition
      hc).tubes.core) :=
  E.old_contains_outside x
    ((SphericalCutCapTransition.retainedCore_iff E.transition hc x).mp hx)
    (fun i hi => hnot (Set.mem_iUnion.mpr ⟨i, hi⟩))

noncomputable def toSurgery (E : MetricCutCapEvent P Q a s)
    (hc : SmoothCutCapCompletion E.transition)
    (hout : letI : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
      IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
        (fun x : E.old => E.transition.trace.capping.coreInclusion x.1)) :
    DifferentialGeometry.PDE.RicciFlow.Surgery.MetricCutCapEvent
      P Q a s := by
  letI : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
  letI : IsManifold (𝓡∂ 3) ∞ E.old := E.oldSmooth
  exact
  { transition := SphericalCutCapTransition.ofSmoothCutCapTransition E.transition hc
    incoming := E.incoming.toSurgery
    terminal := E.terminal.toSurgery
    outputMetric := E.outputMetric
    unchanged := E.old
    unchanged_compact := E.old_compact
    unchanged_retained := surgeryRetainedCore E hc
    unchangedCharts := E.oldCharts
    unchangedSmooth := E.oldSmooth
    unchanged_induced := E.old_induced
    terminalInclusion := E.oldTerminal
    terminalInclusion_eq := E.oldTerminal_eq
    terminalInclusion_smooth := by
      refine DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen (𝓡∂ 3) ThreeModel
        _ E.oldTerminal ?_
      convert E.old_induced using 1
      funext x
      exact E.oldTerminal_eq x
    outputInclusion := E.oldOutput
    outputInclusion_eq := surgeryPresentation_coreInclusion E hc
    outputInclusion_smooth := by
      have hG : IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
          (fun x : E.old =>
            E.transition.presentation (E.transition.trace.capping.coreInclusion x.1)) :=
        hout.diffeomorph_comp E.transition.presentation
      have hG' : IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
          ((Sum.inl : Q.Carrier → Q.Carrier ⊕ E.discarded.Carrier) ∘
            (fun x : E.old => E.oldOutput x)) := by
        convert hG using 1
        funext x
        rw [Function.comp_apply, E.transition.presentation_eq, E.oldOutput_eq]
      exact isSmoothEmbedding_of_comp_sumInl (fun x : E.old => E.oldOutput x) hG'
    unchanged_metric_eq := E.old_metric_eq
    unchanged_contains_outside := surgeryContainsOutside E hc
    every_component_meets_unchanged := E.every_child_meets_old }

end MetricCutCapEvent

namespace ObservedHistory

variable (H : ObservedHistory.{u})

noncomputable def toSurgeryEvents
    (hc : (i : Fin H.eventCount) → SmoothCutCapCompletion (H.event i).transition)
    (hout : (i : Fin H.eventCount) →
      letI : ChartedSpace (EuclideanHalfSpace 3) (H.event i).old := (H.event i).oldCharts
      IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
        (fun x : (H.event i).old => (H.event i).transition.trace.capping.coreInclusion x.1)) :
    (i : Fin H.eventCount) →
      DifferentialGeometry.PDE.RicciFlow.Surgery.MetricCutCapEvent
        (H.stage i.castSucc)
        (H.stage i.succ)
        (H.time i.castSucc) (H.time i.succ) :=
  fun i => MetricCutCapEvent.toSurgery (H.event i) (hc i) (hout i)

theorem toSurgeryEvents_initial
    (hc : (i : Fin H.eventCount) → SmoothCutCapCompletion (H.event i).transition)
    (hout : (i : Fin H.eventCount) →
      letI : ChartedSpace (EuclideanHalfSpace 3) (H.event i).old := (H.event i).oldCharts
      IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
        (fun x : (H.event i).old => (H.event i).transition.trace.capping.coreInclusion x.1))
    (i : Fin H.eventCount) :
    ((H.toSurgeryEvents hc hout) i).incoming.flow.base.metric (H.time i.castSucc) =
      H.initialMetric i.castSucc :=
  H.event_initial i

theorem toSurgeryEvents_output
    (hc : (i : Fin H.eventCount) → SmoothCutCapCompletion (H.event i).transition)
    (hout : (i : Fin H.eventCount) →
      letI : ChartedSpace (EuclideanHalfSpace 3) (H.event i).old := (H.event i).oldCharts
      IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
        (fun x : (H.event i).old => (H.event i).transition.trace.capping.coreInclusion x.1))
    (i : Fin H.eventCount) :
    ((H.toSurgeryEvents hc hout) i).outputMetric = H.initialMetric i.succ :=
  H.event_output i

noncomputable def toSurgeryFiniteSurgeryHistoryOfCutCapCompletion (H : ObservedHistory.{u})
    (hn : 0 < H.eventCount)
    (hc : (i : Fin H.eventCount) → SmoothCutCapCompletion (H.event i).transition)
    (hout : (i : Fin H.eventCount) →
      letI : ChartedSpace (EuclideanHalfSpace 3) (H.event i).old := (H.event i).oldCharts
      IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
        (fun x : (H.event i).old => (H.event i).transition.trace.capping.coreInclusion x.1)) :
    DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.{u} :=
  H.toSurgeryFiniteSurgeryHistory hn (H.toSurgeryEvents hc hout)
    (H.toSurgeryEvents_initial hc hout) (H.toSurgeryEvents_output hc hout)

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

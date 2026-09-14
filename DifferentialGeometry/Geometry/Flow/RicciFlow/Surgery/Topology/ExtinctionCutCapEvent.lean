import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedSlabProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ExtinctEventModelConstruction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ExtinctionFrontierSatisfiability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LocalClassRealizationLocality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MasterFlowCompatibility
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTerminalConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SmoothCutCapTransitionInstance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalRegularRegionTail
import DifferentialGeometry.Topology.Manifold.Components
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandard
import DifferentialGeometry.Topology.ThreeManifold.StandardSphere

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_incomingSlab_terminalLimitMetric (P : OrientedThreeStage.{u}) (g : P.Metric)
    (a : ℝ) :
    ∃ b : ℝ, a < b ∧ ∃ G : P.IncomingSlab a b,
      Nonempty G.TerminalLimitMetric ∧ G.flow.base.metric a = g := by
  obtain ⟨b, hab, S, hinit⟩ := exists_closedSlab_of_metric P g a
  exact ⟨b, hab, S.restrictIncoming le_rfl hab le_rfl,
    ⟨OrientedThreeStage.ClosedSlab.endpointTerminalLimitMetric P S⟩, hinit⟩

theorem nonempty_metricCutCapEvent_of_isEmpty_output
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N) [IsEmpty Q.Carrier]
    (g : P.Metric) (a : ℝ) :
    ∃ b : ℝ, a < b ∧ Nonempty (MetricCutCapEvent P Q a b) := by
  obtain ⟨b, hab, G, hL, -⟩ := exists_incomingSlab_terminalLimitMetric P g a
  exact ⟨b, hab,
    (MetricCutCapEvent.nonempty_iff_of_isEmpty_output (P := P) (Q := Q) (a := a) (s := b)).mpr
      ⟨D, N, X, G, hL, SmoothCutCapTransition.retainedCore_eq_empty_of_isEmpty X⟩⟩

theorem nonempty_retainedCoreEvent_of_isEmpty_output
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N) [IsEmpty Q.Carrier]
    (g : P.Metric) (a : ℝ) :
    ∃ b : ℝ, a < b ∧ Nonempty (RetainedCoreEvent P Q a b) := by
  obtain ⟨b, hab, G, hL, -⟩ := exists_incomingSlab_terminalLimitMetric P g a
  exact ⟨b, hab,
    (RetainedCoreEvent.nonempty_iff_of_isEmpty_output (P := P) (Q := Q) (a := a) (s := b)).mpr
      ⟨D, N, X, G, hL, SmoothCutCapTransition.retainedCore_eq_empty_of_isEmpty X⟩⟩

namespace RetainedCoreEvent

theorem exists_extinctHistory {P Q : OrientedThreeStage.{u}} {g : P.Metric} {s : ℝ} (hs : 0 < s)
    (hQ : IsEmpty Q.Carrier) (E : RetainedCoreEvent P Q 0 s)
    (hm : E.incoming.flow.base.metric 0 = g)
    (hbfr : E.transition.boundaryFrameReversing)
    (hctrl : E.toMetricCutCapEvent.poincareStandardDiscarded) :
    ∃ (H : RetainedCoreHistory P) (_ : InitialIdentification P g H.toHistory),
      H.eventCount = 1 ∧
      (∀ i : Fin H.eventCount, (H.coreEvent i).transition.boundaryFrameReversing) ∧
      (∀ i : Fin H.eventCount,
        (H.coreEvent i).toMetricCutCapEvent.poincareStandardDiscarded) ∧
      IsEmpty (H.stage (Fin.last H.eventCount)).Carrier := by
  refine ⟨extinctionHistory hs E, ?_, rfl, ?_, ?_, ?_⟩
  · refine ⟨Diffeomorph.refl ThreeModel P.Carrier ∞,
      preservesTangentOrientation_refl P.orientation, ?_⟩
    intro x v w
    change (E.incoming.flow.base.metric 0).inner x
      (mfderiv ThreeModel ThreeModel (id : P.Carrier → P.Carrier) x v)
      (mfderiv ThreeModel ThreeModel (id : P.Carrier → P.Carrier) x w) = g.inner x v w
    rw [mfderiv_id, hm]
    rfl
  · intro i
    fin_cases i
    exact hbfr
  · intro i
    fin_cases i
    exact hctrl
  · rw [extinctionHistory_stage_last]
    exact hQ

end RetainedCoreEvent

def HasExtinctCutCapTransition (P : OrientedThreeStage.{u}) : Prop :=
  ∃ (Q D N : OrientedThreeStage.{u}) (X : SmoothCutCapTransition P Q D N),
    IsEmpty Q.Carrier ∧ X.boundaryFrameReversing ∧
      ∀ q : ConnectedComponents D.Carrier,
        DifferentialGeometry.Topology.isPoincareStandard
          (D.toClosedOrientedManifold.component q).Carrier

theorem hasExtinctRetainedCoreHistory_of_hasExtinctCutCapTransition
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (h : HasExtinctCutCapTransition
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold)) :
    HasExtinctRetainedCoreHistory M g := by
  obtain ⟨Q, D, N, X, hQ, hbfr, hdisc⟩ := h
  obtain ⟨b, hab, G, hL, hinit⟩ :=
    exists_incomingSlab_terminalLimitMetric
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g 0
  let E : RetainedCoreEvent
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) Q 0 b :=
    @RetainedCoreEvent.ofEmptyOutput
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) Q D N 0 b X hQ
      G hL.some (@OrientedThreeStage.metricOfIsEmpty Q hQ)
  have hctrl : E.toMetricCutCapEvent.poincareStandardDiscarded := hdisc
  obtain ⟨H, A, -, hbfrH, hctrlH, hempty⟩ :=
    RetainedCoreEvent.exists_extinctHistory hab hQ E hinit hbfr hctrl
  exact ⟨H, A, hbfrH, hctrlH, hempty⟩

namespace RetainedCoreHistory

variable {P : OrientedThreeStage.{u}}

theorem appendEventCompatible_of_finalSlab_eq_closedPrefix (H : RetainedCoreHistory P)
    {Q : OrientedThreeStage.{u}} {s : ℝ}
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hhor : H.horizon < s)
    (hcap : ∀ hh : H.time (Fin.last H.eventCount) < H.horizon,
      H.finalSlab hh = E.incoming.closedPrefix H.horizon hh hhor) :
    H.appendEventCompatible E := by
  intro hh τ _
  rw [hcap hh]
  rfl

theorem nonempty_eventMasterFlow_of_finalSlab_eq_closedPrefix (H : RetainedCoreHistory P)
    {Q : OrientedThreeStage.{u}} {s : ℝ}
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hne : H.time (Fin.last H.eventCount) < H.horizon) (hhor : H.horizon < s)
    (hcap : ∀ hh : H.time (Fin.last H.eventCount) < H.horizon,
      H.finalSlab hh = E.incoming.closedPrefix H.horizon hh hhor) :
    Nonempty (H.eventMasterFlow E) :=
  exists_eventMasterFlow_of_appendEventCompatible H E hne
    (H.appendEventCompatible_of_finalSlab_eq_closedPrefix E hhor hcap)

end RetainedCoreHistory

def HasExtinctCoreEvent (P : OrientedThreeStage.{u}) (g : P.Metric) : Prop :=
  ∃ (Q : OrientedThreeStage.{u}) (s : ℝ), 0 < s ∧ IsEmpty Q.Carrier ∧
    ∃ E : RetainedCoreEvent P Q 0 s,
      E.incoming.flow.base.metric 0 = g ∧
      E.transition.boundaryFrameReversing ∧
      E.toMetricCutCapEvent.poincareStandardDiscarded

theorem hasExtinctCoreEvent_iff_hasExtinctCutCapTransition (P : OrientedThreeStage.{u})
    (g : P.Metric) :
    HasExtinctCoreEvent P g ↔ HasExtinctCutCapTransition P := by
  constructor
  · rintro ⟨Q, s, -, hQ, E, -, hbfr, hctrl⟩
    exact ⟨Q, E.discarded, E.capped, E.transition, hQ, hbfr, hctrl⟩
  · rintro ⟨Q, D, N, X, hQ, hbfr, hdisc⟩
    obtain ⟨s, hs, G, hL, hinit⟩ :=
      exists_incomingSlab_terminalLimitMetric P g 0
    exact ⟨Q, s, hs, hQ,
      @RetainedCoreEvent.ofEmptyOutput P Q D N 0 s X hQ G hL.some
        (@OrientedThreeStage.metricOfIsEmpty Q hQ),
      hinit, hbfr, hdisc⟩

theorem not_hasExtinctCutCapTransition_of_isEmpty (P : OrientedThreeStage.{u})
    [IsEmpty P.Carrier] : ¬ HasExtinctCutCapTransition P := by
  rintro ⟨Q, D, N, X, -, -, -⟩
  exact (isEmpty_iff.mp inferInstance) X.source_nonempty.some

private instance sphereStagePreconnectedSpace :
    PreconnectedSpace sphereStage.toClosedOrientedManifold.Carrier :=
  inferInstanceAs (PreconnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))

private theorem sphereStage_isPoincareStandard :
    DifferentialGeometry.Topology.isPoincareStandard sphereStage.Carrier :=
  DifferentialGeometry.Topology.isPoincareStandard_of_diffeomorph
    DifferentialGeometry.Topology.standardThreeSphereLiftDiffeomorph
    DifferentialGeometry.Topology.isPoincareStandard_sphere

private theorem sphereStage_component_isPoincareStandard :
    ∀ q : ConnectedComponents sphereStage.Carrier,
      DifferentialGeometry.Topology.isPoincareStandard
        (sphereStage.toClosedOrientedManifold.component q).Carrier :=
  fun q => DifferentialGeometry.Topology.isPoincareStandard_of_diffeomorph
    (DifferentialGeometry.Topology.ClosedOrientedManifold.componentDiffeomorph
      sphereStage.toClosedOrientedManifold q).symm sphereStage_isPoincareStandard

theorem hasExtinctCutCapTransition_sphereThreeEmptyStage :
    HasExtinctCutCapTransition sphereThreeEmptyStage :=
  ⟨emptyStage, sphereStage, sphereThreeEmptyStage, smoothCutCapTransitionInstance,
    inferInstanceAs (IsEmpty emptyStage.Carrier),
    @OrientedThreeStage.SmoothCutCapTransition.boundaryFrameReversing_of_isEmpty_index
      sphereThreeEmptyStage emptyStage sphereStage sphereThreeEmptyStage
      smoothCutCapTransitionInstance sphereThreeEmptyTubes_index_isEmpty,
    sphereStage_component_isPoincareStandard⟩

theorem exists_hasExtinctCutCapTransition :
    ∃ P : OrientedThreeStage.{0}, Nonempty P.Carrier ∧ HasExtinctCutCapTransition P :=
  ⟨sphereThreeEmptyStage, ⟨Sum.inr sphereThreeStage_nonempty.some⟩,
    hasExtinctCutCapTransition_sphereThreeEmptyStage⟩

theorem smoothPoincareConjecture_of_hasExtinctCutCapTransition
    (hsum : ∀ (H : DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.{u})
      (i : Fin H.eventCount),
      (H.cutCapTrace.transition i).componentConnectedSumDecomposition)
    (h : ∀ (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
      [SimplyConnectedSpace M.Carrier]
      (_ : SmoothRiemannianMetric (𝓡 3) M.Carrier),
      HasExtinctCutCapTransition
        (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold)) :
    smoothPoincareConjecture.{u} :=
  smoothPoincareConjecture_of_hasExtinctRetainedCoreHistory hsum fun M _ g =>
    hasExtinctRetainedCoreHistory_of_hasExtinctCutCapTransition M g (h M g)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

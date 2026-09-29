import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FiniteHorizonContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordHorizonExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreExtinctHistory
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.ExtinctionTimeBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.InitialScalarBarrier

noncomputable section
open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Extinction.Families
open DifferentialGeometry.PDE.RicciFlow.Extinction.Width
universe u

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

private theorem ObservedHistory.isExtinctAtHorizon_of_initialScalarBarrier
    {P : OrientedThreeStage.{u}} [SimplyConnectedSpace P.Carrier]
    {g : P.Metric} (H : ObservedHistory.{u}) (A : InitialIdentification P g H)
    (parameters : CutoffParameters)
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
    {c : ℝ} (hc : 0 < c) (hscalar : InitialScalarBarrier g c)
    (hthr : extinctionThreshold c (canonicalWidth g P.orientation) < H.horizon) :
    H.IsExtinctAtHorizon := by
  let h0 := initialIdentification_components_simplyConnected P g H A
  apply H.isExtinctAtHorizon_of_historyWidth h0 parameters records hc
    (canonicalWidth_nonneg g P.orientation) (A.historyScalarLowerBound records hc hscalar)
    _ hthr
  intro terminal
  exact le_of_eq (historyWidth_initial_eq_of_isometry g P.orientation H h0 A.map.toHomeomorph
    (initialIdentification_riemannianEDist_eq P g H A)
    (initialIdentification_fundamentalClass P g H A) terminal)

theorem RetainedCoreHistory.exists_poincare_controlled_extinction_of_initialScalarBarrier
    {P : OrientedThreeStage.{u}} [SimplyConnectedSpace P.Carrier]
    {g : P.Metric} (H : RetainedCoreHistory.{u}) (A : InitialIdentification P g H.toHistory)
    (parameters : CutoffParameters)
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i parameters)
    (hbfr : ∀ i : Fin H.eventCount, (H.coreEvent i).transition.boundaryFrameReversing)
    (hctrl : ∀ i : Fin H.eventCount,
      (H.coreEvent i).toMetricCutCapEvent.poincareStandardDiscarded)
    {c : ℝ} (hc : 0 < c) (hscalar : InitialScalarBarrier g c)
    (hthr : extinctionThreshold c (canonicalWidth g P.orientation) < H.horizon) :
    Nonempty (PoincareControlledExtinction P.toClosedOrientedManifold g) := by
  have hempty := H.toHistory.isExtinctAtHorizon_of_initialScalarBarrier A
    parameters records hc hscalar hthr
  exact exists_poincare_controlled_extinction_of_observedHistory P g H.toHistory A
    (fun i => ((H.coreEvent i).toMetricCutCapEvent_hasCutCapCompletion (hbfr i)).some)
    (fun i => (H.coreEvent i).toMetricCutCapEvent_coreInclusionIsSmoothEmbedding)
    hctrl hempty

theorem prefix_initial_stage {H K : ObservedHistory.{u}} (h : H.IsPrefixOf K) :
    K.stage 0 = H.stage 0 := by
  have hh := h.presentation.stage_eq 0
  simpa only [Fin.cast_zero, ObservedHistory.restrict_stage_zero] using hh

private theorem prefix_initial_metric {H K : ObservedHistory.{u}} (h : H.IsPrefixOf K) :
    HEq (K.initialMetric 0) (H.initialMetric 0) := by
  have hh := h.presentation.initialMetric_heq 0
  simpa only [Fin.cast_zero, ObservedHistory.restrict_initialMetric_zero,
    ObservedHistory.restrict_stage_zero] using hh

theorem RetainedCoreHistory.exists_poincare_controlled_extinction_of_history_volume_debit
    {P : OrientedThreeStage.{u}} [SimplyConnectedSpace P.Carrier]
    {g : P.Metric} (H : RetainedCoreHistory.{u})
    (A : InitialIdentification P g H.toHistory)
    (S : Set (RetainedCoreHistory.{u})) (hH : H ∈ S)
    {B v : ℝ} (hv : 0 < v)
    (hprefix : ∀ K ∈ S, H.toHistory.IsPrefixOf K.toHistory)
    (hhorizon : ∀ K ∈ S, K.horizon ≤ B)
    (hend : ∀ K ∈ S, K.time (Fin.last K.eventCount) = K.horizon)
    (hdebit : ∀ K ∈ S, ∀ i : Fin K.eventCount,
      ∃ F : Set (K.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
        riemannianVolumeMeasure ThreeModel (K.stage i.succ).Carrier
          (K.coreEvent i).outputMetric univ +
            ENNReal.ofReal ((Nat.card (K.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
        riemannianVolumeMeasure ThreeModel (K.coreEvent i).incoming.terminalRegularOpen
          (K.coreEvent i).terminal.metric F)
    (hproduce : ∀ K ∈ S, K.horizon < B →
      ∀ (s : ℝ) (G : (K.stage (Fin.last K.eventCount)).IncomingSlab
        (K.time (Fin.last K.eventCount)) s),
      s ≤ B →
      G.flow.base.metric (K.time (Fin.last K.eventCount)) =
        K.initialMetric (Fin.last K.eventCount) → G.SingularEndpoint →
      ∃ (Q : OrientedThreeStage.{u})
        (E : RetainedCoreEvent (K.stage (Fin.last K.eventCount)) Q
          (K.time (Fin.last K.eventCount)) s)
        (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric
          (K.time (Fin.last K.eventCount)) = K.initialMetric (Fin.last K.eventCount)),
        E.incoming = G ∧ K.appendEvent E.incoming.lt E hinit ∈ S)
    (parameters : ∀ K ∈ S, CutoffParameters)
    (records : ∀ K hK, ∀ i : Fin K.eventCount,
      GeometricCutoffRecord K.toHistory i (parameters K hK))
    (hbfr : ∀ K ∈ S, ∀ i : Fin K.eventCount,
      (K.coreEvent i).transition.boundaryFrameReversing)
    (hctrl : ∀ K ∈ S, ∀ i : Fin K.eventCount,
      (K.coreEvent i).toMetricCutCapEvent.poincareStandardDiscarded)
    {c : ℝ} (hc : 0 < c) (hscalar0 : InitialScalarBarrier g c)
    (hthr : extinctionThreshold c (canonicalWidth g P.orientation) < B) :
    Nonempty (PoincareControlledExtinction P.toClosedOrientedManifold g) := by
  have hscalar : ∀ K ∈ S, ∀ i : Fin K.eventCount,
      ∀ t ∈ Ico (K.time i.castSucc) (K.time i.succ),
      ∀ x : (K.stage i.castSucc).Carrier,
        -(3 / (2 * c)) ≤ metricScalarAt ((K.coreEvent i).incoming.flow.base.metric t) x := by
    intro K hK i t ht x
    let A' := A.ofStageZero (prefix_initial_stage (hprefix K hK))
      (prefix_initial_metric (hprefix K hK))
    have hstage := DifferentialGeometry.PDE.RicciFlow.stageInitial_scalarLowerBound_of_history
      (records K hK) hc (A'.stageZero_scalarLowerBound hscalar0)
    have hinit : ∀ y : (K.stage i.castSucc).Carrier,
        -3 / (2 * (K.time i.castSucc + c)) ≤
          metricScalarAt ((K.coreEvent i).incoming.flow.base.metric (K.time i.castSucc)) y := by
      intro y
      change -3 / (2 * (K.time i.castSucc + c)) ≤
        metricScalarAt ((K.coreEvent i).toMetricCutCapEvent.incoming.flow.base.metric
          (K.time i.castSucc)) y
      rw [K.event_initial i]
      exact hstage i.castSucc y
    have hbound := DifferentialGeometry.PDE.RicciFlow.incomingSlab_scalarLowerBarrier_le
      (K.toHistory.time_nonneg i.castSucc) hc (K.coreEvent i).incoming hinit ht x
    have ht0 : 0 ≤ t := (K.toHistory.time_nonneg i.castSucc).trans ht.1
    have hd : 3 / (2 * (t + c)) ≤ 3 / (2 * c) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
    have hneg : -(3 / (2 * c)) ≤ -3 / (2 * (t + c)) := by
      simpa only [neg_div] using neg_le_neg hd
    exact hneg.trans hbound
  obtain ⟨J, hJ, hJB | ⟨hB, G, hG, hp⟩⟩ :=
    H.exists_closedSlab_extension_to_horizon_of_volume_debit S hH (by positivity : 0 ≤ 3 / (2 * c)) hv hprefix hhorizon
      hend hscalar hdebit hproduce
  · let A' := A.ofStageZero (prefix_initial_stage (hprefix J hJ))
      (prefix_initial_metric (hprefix J hJ))
    exact J.exists_poincare_controlled_extinction_of_initialScalarBarrier A' (parameters J hJ)
      (records J hJ) (hbfr J hJ) (hctrl J hJ) hc hscalar0 (hJB ▸ hthr)
  · let K := J.extendHorizon B hB G hG
    let A' := A.ofStageZero (prefix_initial_stage hp) (prefix_initial_metric hp)
    exact K.exists_poincare_controlled_extinction_of_initialScalarBarrier A' (parameters J hJ)
      (fun i => GeometricCutoffRecord.extendHorizon B hB G hG (records J hJ i))
      (hbfr J hJ) (hctrl J hJ) hc hscalar0 hthr

theorem RetainedCoreHistory.exists_poincare_controlled_extinction_of_volume_debit
    {P : OrientedThreeStage.{u}} [SimplyConnectedSpace P.Carrier]
    {g : P.Metric} (H : RetainedCoreHistory.{u})
    (A : InitialIdentification P g H.toHistory)
    (S : Set (RetainedCoreHistory.{u})) (hH : H ∈ S)
    {B v : ℝ} (hv : 0 < v)
    (hprefix : ∀ K ∈ S, H.toHistory.IsPrefixOf K.toHistory)
    (hhorizon : ∀ K ∈ S, K.horizon ≤ B)
    (hend : ∀ K ∈ S, K.time (Fin.last K.eventCount) = K.horizon)
    (hdebit : ∀ K ∈ S, ∀ i : Fin K.eventCount,
      ∃ F : Set (K.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
        riemannianVolumeMeasure ThreeModel (K.stage i.succ).Carrier
          (K.coreEvent i).outputMetric univ +
            ENNReal.ofReal ((Nat.card (K.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
        riemannianVolumeMeasure ThreeModel (K.coreEvent i).incoming.terminalRegularOpen
          (K.coreEvent i).terminal.metric F)
    (hproduce : ∀ K ∈ S, K.horizon < B →
      ∀ (s : ℝ) (G : (K.stage (Fin.last K.eventCount)).IncomingSlab
        (K.time (Fin.last K.eventCount)) s),
      s ≤ B →
      G.flow.base.metric (K.time (Fin.last K.eventCount)) =
        K.initialMetric (Fin.last K.eventCount) → G.SingularEndpoint →
      ∃ (Q : OrientedThreeStage.{u})
        (E : RetainedCoreEvent (K.stage (Fin.last K.eventCount)) Q
          (K.time (Fin.last K.eventCount)) s)
        (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric
          (K.time (Fin.last K.eventCount)) = K.initialMetric (Fin.last K.eventCount)),
        E.incoming = G ∧ K.appendEvent E.incoming.lt E hinit ∈ S)
    (parameters : CutoffParameters)
    (records : ∀ K ∈ S, ∀ i : Fin K.eventCount,
      GeometricCutoffRecord K.toHistory i parameters)
    (hbfr : ∀ K ∈ S, ∀ i : Fin K.eventCount,
      (K.coreEvent i).transition.boundaryFrameReversing)
    (hctrl : ∀ K ∈ S, ∀ i : Fin K.eventCount,
      (K.coreEvent i).toMetricCutCapEvent.poincareStandardDiscarded)
    {c : ℝ} (hc : 0 < c) (hscalar0 : InitialScalarBarrier g c)
    (hthr : extinctionThreshold c (canonicalWidth g P.orientation) < B) :
    Nonempty (PoincareControlledExtinction P.toClosedOrientedManifold g) := by
  exact H.exists_poincare_controlled_extinction_of_history_volume_debit A S hH hv
    hprefix hhorizon hend hdebit hproduce (fun _ _ => parameters) records hbfr hctrl
    hc hscalar0 hthr

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.CompactTerminalMetricEvent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryMetricEventMetricAlignment

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Contract
open scoped ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

universe u

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

private theorem compact_volume_of_terminal_heq
    {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (G G' : P.IncomingSlab a s) (L : G.TerminalLimitMetric) (L' : G'.TerminalLimitMetric)
    (hG : G = G') (hL : HEq L L') (g : Q.Metric)
    (hvol : ∃ F : Set G'.terminalRegularOpen, IsCompact F ∧
      riemannianVolumeMeasure ThreeModel Q.Carrier g univ ≤
        riemannianVolumeMeasure ThreeModel G'.terminalRegularOpen L'.metric F) :
    ∃ F : Set G.terminalRegularOpen, IsCompact F ∧
      riemannianVolumeMeasure ThreeModel Q.Carrier g univ ≤
        riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric F := by
  cases hG
  cases eq_of_heq hL
  exact hvol

theorem exists_extension_of_compact_low_components
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (H : RetainedCoreHistory.{u}) (A : InitialIdentification P g H.toHistory)
    (htime : H.time (Fin.last H.eventCount) = H.horizon)
    (D : OneStepIncoming.{u})
    (hstage : H.stage (Fin.last H.eventCount) = D.stage)
    (hstart : H.time (Fin.last H.eventCount) = D.startTime)
    (hinit : HEq (D.slab.flow.base.metric D.startTime) (H.initialMetric (Fin.last H.eventCount)))
    (hcompact : ∀ x : D.slab.terminalRegularOpen,
      metricScalarAt D.terminal.metric x ≤
        ((D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime) ^ 2)⁻¹ →
      IsCompact (connectedComponent x)) :
    ∃ (Q : OrientedThreeStage.{u}) (E : MetricCutCapEvent D.stage Q D.startTime D.endTime)
      (hOld : E.old = E.transition.trace.retainedCore),
      E.incoming = D.slab ∧ HEq E.terminal D.terminal ∧
      IsEmpty E.transition.trace.tubes.Index ∧ E.transition.boundaryFrameReversing ∧
      (∀ x : D.slab.terminalRegularOpen,
        metricScalarAt D.terminal.metric x ≤
          ((D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime) ^ 2)⁻¹ →
        x.val ∈ interior ((Subtype.val : E.transition.trace.tubes.core → D.stage.Carrier) '' E.old)) ∧
      (∀ c : ConnectedComponents E.transition.trace.tubes.core,
        (∃ y : E.transition.trace.tubes.core,
          ConnectedComponents.mk y = c ∧ y ∈ E.transition.trace.retainedCore) →
        ∃ x : D.slab.terminalRegularOpen, ∃ hx : x.val ∈ E.transition.trace.tubes.core,
          ConnectedComponents.mk ⟨x.val, hx⟩ = c ∧
            metricScalarAt D.terminal.metric x ≤
              ((D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime) ^ 2)⁻¹) ∧
      ∃ (K : RetainedCoreHistory.{u}) (B : InitialIdentification P g K.toHistory)
        (i : Fin K.eventCount),
        A.IsPrefixOf B ∧ D.endTime < K.horizon ∧ K.eventCount = H.eventCount + 1 ∧
        K.time (Fin.last K.eventCount) = D.endTime ∧ K.stage (Fin.last K.eventCount) = Q ∧
        HEq (K.initialMetric (Fin.last K.eventCount)) E.outputMetric ∧
        i.val = H.eventCount ∧ K.stage i.castSucc = D.stage ∧ K.time i.castSucc = D.startTime ∧
        K.stage i.succ = Q ∧ K.time i.succ = D.endTime ∧
        HEq (K.coreEvent i) (E.toRetainedCoreEvent hOld) ∧
        HEq (K.initialMetric i.castSucc) (D.slab.flow.base.metric D.startTime) ∧
        HEq (K.initialMetric i.succ) E.outputMetric ∧
        ∃ F : Set (K.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
          riemannianVolumeMeasure ThreeModel (K.stage i.succ).Carrier
              (K.coreEvent i).outputMetric univ ≤
            riemannianVolumeMeasure ThreeModel (K.coreEvent i).incoming.terminalRegularOpen
              (K.coreEvent i).terminal.metric F ∧
          (∀ b : ℝ, 0 < b →
            (∀ x, InFixedHamiltonIveyRegion (K.coreEvent i).terminal.metric b x) →
            ∀ x, InFixedHamiltonIveyRegion (K.coreEvent i).outputMetric b x) ∧
          (∀ L : ℝ, L ≤ 0 →
            (∀ x, L ≤ metricScalarAt (K.coreEvent i).terminal.metric x) →
            ∀ x, L ≤ metricScalarAt (K.coreEvent i).outputMetric x) := by
  cases D with
  | mk stage startTime endTime hnonneg hlt slab terminal singular parameters =>
    cases hstage
    cases hstart
    let D : OneStepIncoming := ⟨_, _, endTime, hnonneg, hlt, slab, terminal, singular, parameters⟩
    obtain ⟨Q, E, hG, hL, hempty, hOld, hbfr, hcurvature, hscalar, hprotected, hmeets, hvol⟩ :=
      exists_metricCutCapEvent_of_compact_low_components D hcompact
    have hvolE := compact_volume_of_terminal_heq E.incoming D.slab E.terminal D.terminal
      hG hL E.outputMetric hvol
    obtain ⟨F, hF, hvolF⟩ := hvolE
    have hinitE : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
        H.initialMetric (Fin.last H.eventCount) := by
      rw [hG]
      exact eq_of_heq hinit
    have hdebit : riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric univ +
        ENNReal.ofReal ((Nat.card E.transition.trace.tubes.Index : ℝ) * 0) ≤
          riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen E.terminal.metric F := by
      simpa using hvolF
    obtain ⟨K, B, i, hprefix, hhorizon, hcount, hend, hout, hmetric, hi, hsource, htimeSource,
      htarget, htimeTarget, hevent, hmetricSource, hmetricTarget, F', hF'eq, hF', hdebit',
      hcurvature', hscalar'⟩ :=
      H.exists_extension_after_metricCutCapEvent_preserving_debit_with_metric_alignment
        A htime E hOld hinitE 0 F hF hdebit hcurvature hscalar
    refine ⟨Q, E, hOld, hG, hL, hempty, hbfr, hprotected, hmeets,
      K, B, i, hprefix, hhorizon, hcount, hend, hout, hmetric, hi, hsource, htimeSource,
      htarget, htimeTarget, hevent, ?_, hmetricTarget, F', hF', ?_, hcurvature', hscalar'⟩
    · have hGmetric : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
          slab.flow.base.metric (H.time (Fin.last H.eventCount)) := by
        exact congrArg (fun G => G.flow.base.metric (H.time (Fin.last H.eventCount))) hG
      exact hmetricSource.trans (heq_of_eq hGmetric)
    · simpa using hdebit'

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

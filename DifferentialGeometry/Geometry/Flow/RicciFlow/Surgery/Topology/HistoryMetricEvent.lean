import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreMetricEvent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PinchingDatum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TowerBookkeeping
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MasterFlowCompatibility

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open scoped ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

private theorem compact_debit_preservation_of_heq
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    (E : RetainedCoreEvent P Q a s) (E' : RetainedCoreEvent P' Q' a' s')
    (hE : HEq E' E) (v : ℝ) (F : Set E.incoming.terminalRegularOpen)
    (hF : IsCompact F)
    (hdebit : riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric univ +
      ENNReal.ofReal ((Nat.card E.transition.trace.tubes.Index : ℝ) * v) ≤
      riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen E.terminal.metric F)
    (hcurvature : ∀ b : ℝ, 0 < b →
      (∀ x, InFixedHamiltonIveyRegion E.terminal.metric b x) →
      ∀ x, InFixedHamiltonIveyRegion E.outputMetric b x)
    (hscalar : ∀ B : ℝ, B ≤ 0 →
      (∀ x, B ≤ metricScalarAt E.terminal.metric x) →
      ∀ x, B ≤ metricScalarAt E.outputMetric x) :
    ∃ F' : Set E'.incoming.terminalRegularOpen,
      HEq F' F ∧ IsCompact F' ∧
      riemannianVolumeMeasure ThreeModel Q'.Carrier E'.outputMetric univ +
        ENNReal.ofReal ((Nat.card E'.transition.trace.tubes.Index : ℝ) * v) ≤
        riemannianVolumeMeasure ThreeModel E'.incoming.terminalRegularOpen E'.terminal.metric F' ∧
      (∀ b : ℝ, 0 < b →
        (∀ x, InFixedHamiltonIveyRegion E'.terminal.metric b x) →
        ∀ x, InFixedHamiltonIveyRegion E'.outputMetric b x) ∧
      (∀ B : ℝ, B ≤ 0 →
        (∀ x, B ≤ metricScalarAt E'.terminal.metric x) →
        ∀ x, B ≤ metricScalarAt E'.outputMetric x) := by
  cases hP
  cases hQ
  cases ha
  cases hs
  have hEE : E' = E := eq_of_heq hE
  cases hEE
  exact ⟨F, HEq.rfl, hF, hdebit, hcurvature, hscalar⟩

namespace RetainedCoreHistory

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

theorem exists_extension_after_metricCutCapEvent_with_source (H : RetainedCoreHistory.{u})
    (A : InitialIdentification P g H.toHistory)
    (htime : H.time (Fin.last H.eventCount) = H.horizon)
    {Q : OrientedThreeStage.{u}} {s : ℝ}
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hOld : E.old = E.transition.trace.retainedCore)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    ∃ (K : RetainedCoreHistory.{u}) (B : InitialIdentification P g K.toHistory),
      A.IsPrefixOf B ∧ s < K.horizon ∧ K.eventCount = H.eventCount + 1 ∧
      K.time (Fin.last K.eventCount) = s ∧ K.stage (Fin.last K.eventCount) = Q ∧
      HEq (K.initialMetric (Fin.last K.eventCount)) E.outputMetric ∧
      ∃ i : Fin K.eventCount, i.val = H.eventCount ∧
        K.stage i.castSucc = H.stage (Fin.last H.eventCount) ∧
        K.time i.castSucc = H.time (Fin.last H.eventCount) ∧
        K.stage i.succ = Q ∧ K.time i.succ = s ∧
        HEq (K.coreEvent i) (E.toRetainedCoreEvent hOld) := by
  let F := E.toRetainedCoreEvent hOld
  let J := H.appendEvent E.incoming.lt F hinit
  have hJs : J.time (Fin.last J.eventCount) = s := H.appendEvent_time_last E.incoming.lt F hinit
  have hJtime : J.time (Fin.last J.eventCount) = J.horizon := hJs
  have hHJ : H.toHistory.IsPrefixOf J.toHistory :=
    H.appendEvent_isPrefixOf E.incoming.lt F hinit (htime ▸ E.incoming.lt)
      (H.appendEventCompatible_of_time_eq_horizon F htime)
  obtain ⟨b, hsb, S, hS⟩ := exists_closedSlab_of_metric
    (J.stage (Fin.last J.eventCount)) (J.initialMetric (Fin.last J.eventCount))
    (J.time (Fin.last J.eventCount))
  have hJb : J.horizon ≤ b := hJtime ▸ hsb.le
  let K := J.extendHorizon b hJb S hS
  have hJK : J.toHistory.IsPrefixOf K.toHistory :=
    J.extendHorizon_isPrefixOf_of_time_eq_horizon b hJb S hS hJtime
  have hstage : K.toHistory.stage 0 = H.toHistory.stage 0 :=
    H.appendEvent_stage_castSucc E.incoming.lt F hinit 0
  have hmetric : HEq (K.toHistory.initialMetric 0) (H.toHistory.initialMetric 0) :=
    H.appendEvent_initialMetric_castSucc_heq E.incoming.lt F hinit 0
  let B := A.of_stageZero hstage hmetric
  refine ⟨K, B, ⟨hHJ.trans hJK, (A.map_of_stageZero_heq hstage hmetric).symm⟩,
    hJs ▸ hsb, rfl, hJs, H.appendEvent_stage_last E.incoming.lt F hinit,
    H.appendEvent_initialMetric_last_heq E.incoming.lt F hinit, Fin.last H.eventCount, rfl,
    H.appendEvent_stage_castSucc E.incoming.lt F hinit (Fin.last H.eventCount),
    H.appendEvent_time_castSucc E.incoming.lt F hinit (Fin.last H.eventCount),
    H.appendEvent_stage_last E.incoming.lt F hinit,
    H.appendEvent_time_last E.incoming.lt F hinit, ?_⟩
  change HEq ((H.appendEvent E.incoming.lt F hinit).coreEvent (Fin.last H.eventCount)) F
  refine (heq_of_eq (H.appendEvent_coreEvent_last E.incoming.lt F hinit)).trans ?_
  change HEq (H.extendCoreEventLast F) F
  unfold extendCoreEventLast
  have ht {P₁ Q₁ P₂ Q₂ : OrientedThreeStage.{u}} {a₁ s₁ a₂ s₂ : ℝ}
      (hP : P₁ = P₂) (hQ : Q₁ = Q₂) (ha : a₁ = a₂) (hs : s₁ = s₂)
      (D : RetainedCoreEvent P₁ Q₁ a₁ s₁) :
      HEq (RetainedCoreEvent.transport hP hQ ha hs D) D := by
    cases hP
    cases hQ
    cases ha
    cases hs
    exact HEq.rfl
  exact ht _ _ _ _ F

theorem exists_extension_after_metricCutCapEvent (H : RetainedCoreHistory.{u})
    (A : InitialIdentification P g H.toHistory)
    (htime : H.time (Fin.last H.eventCount) = H.horizon)
    {Q : OrientedThreeStage.{u}} {s : ℝ}
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hOld : E.old = E.transition.trace.retainedCore)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    ∃ (K : RetainedCoreHistory.{u}) (B : InitialIdentification P g K.toHistory),
      A.IsPrefixOf B ∧ s < K.horizon ∧ K.eventCount = H.eventCount + 1 ∧
      K.time (Fin.last K.eventCount) = s ∧ K.stage (Fin.last K.eventCount) = Q ∧
      HEq (K.initialMetric (Fin.last K.eventCount)) E.outputMetric ∧
      ∃ i : Fin K.eventCount, i.val = H.eventCount ∧
        HEq (K.coreEvent i) (E.toRetainedCoreEvent hOld) := by
  obtain ⟨K,B,hprefix,horizon,hcount,htime',hstage,hmetric,i,hi,_,_,_,_,hevent⟩ :=
    H.exists_extension_after_metricCutCapEvent_with_source A htime E hOld hinit
  exact ⟨K,B,hprefix,horizon,hcount,htime',hstage,hmetric,i,hi,hevent⟩

theorem exists_extension_after_metricCutCapEvent_preserving_debit
    (H : RetainedCoreHistory.{u}) (A : InitialIdentification P g H.toHistory)
    (htime : H.time (Fin.last H.eventCount) = H.horizon)
    {Q : OrientedThreeStage.{u}} {s : ℝ}
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hOld : E.old = E.transition.trace.retainedCore)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (v : ℝ) (F : Set E.incoming.terminalRegularOpen) (hF : IsCompact F)
    (hdebit : riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric univ +
      ENNReal.ofReal ((Nat.card E.transition.trace.tubes.Index : ℝ) * v) ≤
      riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen E.terminal.metric F)
    (hcurvature : ∀ b : ℝ, 0 < b →
      (∀ x, InFixedHamiltonIveyRegion E.terminal.metric b x) →
      ∀ x, InFixedHamiltonIveyRegion E.outputMetric b x)
    (hscalar : ∀ B : ℝ, B ≤ 0 →
      (∀ x, B ≤ metricScalarAt E.terminal.metric x) →
      ∀ x, B ≤ metricScalarAt E.outputMetric x) :
    ∃ (K : RetainedCoreHistory.{u}) (B : InitialIdentification P g K.toHistory),
      A.IsPrefixOf B ∧ s < K.horizon ∧ K.eventCount = H.eventCount + 1 ∧
      K.time (Fin.last K.eventCount) = s ∧ K.stage (Fin.last K.eventCount) = Q ∧
      HEq (K.initialMetric (Fin.last K.eventCount)) E.outputMetric ∧
      ∃ i : Fin K.eventCount, i.val = H.eventCount ∧
        K.stage i.castSucc = H.stage (Fin.last H.eventCount) ∧
        K.time i.castSucc = H.time (Fin.last H.eventCount) ∧
        K.stage i.succ = Q ∧ K.time i.succ = s ∧
        HEq (K.coreEvent i) (E.toRetainedCoreEvent hOld) ∧
        ∃ F' : Set (K.coreEvent i).incoming.terminalRegularOpen,
          HEq F' F ∧ IsCompact F' ∧
          riemannianVolumeMeasure ThreeModel (K.stage i.succ).Carrier
            (K.coreEvent i).outputMetric univ +
              ENNReal.ofReal ((Nat.card (K.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
            riemannianVolumeMeasure ThreeModel (K.coreEvent i).incoming.terminalRegularOpen
              (K.coreEvent i).terminal.metric F' ∧
          (∀ b : ℝ, 0 < b →
            (∀ x, InFixedHamiltonIveyRegion (K.coreEvent i).terminal.metric b x) →
            ∀ x, InFixedHamiltonIveyRegion (K.coreEvent i).outputMetric b x) ∧
          (∀ B₀ : ℝ, B₀ ≤ 0 →
            (∀ x, B₀ ≤ metricScalarAt (K.coreEvent i).terminal.metric x) →
            ∀ x, B₀ ≤ metricScalarAt (K.coreEvent i).outputMetric x) := by
  obtain ⟨K,B,hprefix,hhorizon,hcount,hend,hout,hmetric,i,hi,hP,ha,hQ,hs,hE⟩ :=
    H.exists_extension_after_metricCutCapEvent_with_source A htime E hOld hinit
  have hlaws := compact_debit_preservation_of_heq hP.symm hQ.symm ha.symm hs.symm
    (E.toRetainedCoreEvent hOld) (K.coreEvent i) hE v F hF hdebit hcurvature hscalar
  exact ⟨K,B,hprefix,hhorizon,hcount,hend,hout,hmetric,i,hi,hP,ha,hQ,hs,hE,hlaws⟩


end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

noncomputable section

open Set
open DifferentialGeometry.Integral.Measure
open scoped ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

private theorem compact_volume_debit_transport
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    (E : RetainedCoreEvent P Q a s) (v : ℝ)
    (hdebit : ∃ F : Set E.incoming.terminalRegularOpen, IsCompact F ∧
      riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric univ +
        ENNReal.ofReal ((Nat.card E.transition.trace.tubes.Index : ℝ) * v) ≤
      riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen E.terminal.metric F) :
    ∃ F : Set (RetainedCoreEvent.transport hP hQ ha hs E).incoming.terminalRegularOpen,
      IsCompact F ∧
      riemannianVolumeMeasure ThreeModel Q'.Carrier
          (RetainedCoreEvent.transport hP hQ ha hs E).outputMetric univ +
        ENNReal.ofReal
          ((Nat.card (RetainedCoreEvent.transport hP hQ ha hs E).transition.trace.tubes.Index : ℝ) * v) ≤
      riemannianVolumeMeasure ThreeModel
        (RetainedCoreEvent.transport hP hQ ha hs E).incoming.terminalRegularOpen
        (RetainedCoreEvent.transport hP hQ ha hs E).terminal.metric F := by
  cases hP
  cases hQ
  cases ha
  cases hs
  exact hdebit

theorem RetainedCoreHistory.appendEvent_compact_volume_debit
    {Q : OrientedThreeStage.{u}} (H : RetainedCoreHistory.{u}) {s : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (v : ℝ)
    (hdebit : ∀ i : Fin H.eventCount,
      ∃ F : Set (H.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
        riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier
          (H.coreEvent i).outputMetric univ +
            ENNReal.ofReal ((Nat.card (H.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
        riemannianVolumeMeasure ThreeModel (H.coreEvent i).incoming.terminalRegularOpen
          (H.coreEvent i).terminal.metric F)
    (hE : ∃ F : Set E.incoming.terminalRegularOpen, IsCompact F ∧
      riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric univ +
        ENNReal.ofReal ((Nat.card E.transition.trace.tubes.Index : ℝ) * v) ≤
      riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen E.terminal.metric F) :
    ∀ i : Fin (H.appendEvent hs E hinit).eventCount,
      ∃ F : Set ((H.appendEvent hs E hinit).coreEvent i).incoming.terminalRegularOpen,
        IsCompact F ∧
        riemannianVolumeMeasure ThreeModel ((H.appendEvent hs E hinit).stage i.succ).Carrier
          ((H.appendEvent hs E hinit).coreEvent i).outputMetric univ +
            ENNReal.ofReal
              ((Nat.card ((H.appendEvent hs E hinit).coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
        riemannianVolumeMeasure ThreeModel
          ((H.appendEvent hs E hinit).coreEvent i).incoming.terminalRegularOpen
          ((H.appendEvent hs E hinit).coreEvent i).terminal.metric F := by
  change ∀ i : Fin (H.eventCount + 1), _
  intro i
  cases i using Fin.lastCases with
  | cast i =>
    rw [H.appendEvent_coreEvent_castSucc]
    exact compact_volume_debit_transport _ _ _ _ _ v (hdebit i)
  | last =>
    rw [H.appendEvent_coreEvent_last]
    exact compact_volume_debit_transport _ _ _ _ _ v hE

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

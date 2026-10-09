import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordSplicing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodContinuationLeaves

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- Canonical windows and event bounds follow the selected records through a future splice. -/
theorem RetainedCoreHistory.exists_isCanonicalCutoffRecordFamily_appendEvent_spliceAfter
    {Q : OrientedThreeStage.{u}} (H : RetainedCoreHistory.{u}) {s : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (hfuture : H.horizon < s)
    {p₀ p q : CutoffParameters} {δbound ρbound : ℝ}
    (old : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (hold : H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound old)
    (new : GeometricCutoffRecord (H.appendEvent hs E hinit).toHistory
      (Fin.last H.eventCount) q)
    (hstatic : q.fixed = p₀.fixed ∧ q.modelRadius = p₀.modelRadius ∧
      q.modelOrder = p₀.modelOrder ∧ q.modelAccuracy = p₀.modelAccuracy ∧
      q.recenterConstant = p₀.recenterConstant)
    (hnew : ∀ b, (new.static b).hasCanonicalWindow)
    (hδnew : q.delta s ≤ δbound) (hρnew : q.neckRadius s ≤ ρbound) :
    ∃ R : ∀ i : Fin (H.appendEvent hs E hinit).eventCount,
        GeometricCutoffRecord (H.appendEvent hs E hinit).toHistory i
          (p.spliceAfter q H.horizon),
      (H.appendEvent hs E hinit).IsCanonicalCutoffRecordFamily p₀ δbound ρbound R ∧
      (∀ i : Fin H.eventCount,
        HEq (R i.castSucc).nominalRadius (old i).nominalRadius ∧
        HEq (R i.castSucc).delta (old i).delta ∧
        HEq (R i.castSucc).order (old i).order ∧
        HEq (R i.castSucc).neck (old i).neck ∧
        HEq (R i.castSucc).static (old i).static) ∧
      HEq (R (Fin.last H.eventCount)).nominalRadius new.nominalRadius ∧
      HEq (R (Fin.last H.eventCount)).delta new.delta ∧
      HEq (R (Fin.last H.eventCount)).order new.order ∧
      HEq (R (Fin.last H.eventCount)).neck new.neck ∧
      HEq (R (Fin.last H.eventCount)).static new.static := by
  obtain ⟨hpf, hpD, hpm, hpε, hpc, holdwin, hδold, hρold⟩ := hold
  have hqp : q.fixed = p.fixed ∧ q.modelRadius = p.modelRadius ∧
      q.modelOrder = p.modelOrder ∧ q.modelAccuracy = p.modelAccuracy ∧
      q.recenterConstant = p.recenterConstant :=
    ⟨hstatic.1.trans hpf.symm, hstatic.2.1.trans hpD.symm,
      hstatic.2.2.1.trans hpm.symm, hstatic.2.2.2.1.trans hpε.symm,
      hstatic.2.2.2.2.trans hpc.symm⟩
  obtain ⟨R, hOld, hNewNominal, hNewDelta, hNewOrder, hNewNeck, hNewStatic⟩ :=
    H.exists_cutoff_records_at_appendEvent_spliceAfter hs E hinit hfuture old new hqp
  refine ⟨R, ?_, hOld, hNewNominal, hNewDelta, hNewOrder, hNewNeck, hNewStatic⟩
  refine ⟨hpf, hpD, hpm, hpε, hpc, ?_, ?_, ?_⟩
  · intro i
    cases i using Fin.lastCases with
    | last =>
      exact MetricCutCapEvent.PresentedStaticCap.hasCanonicalWindow_of_family_heq
        rfl rfl rfl rfl HEq.rfl hqp.1.symm hqp.2.1.symm hqp.2.2.1.symm
        hqp.2.2.2.1.symm new.static (R (Fin.last H.eventCount)).static hNewStatic hnew
    | cast i =>
      have hE : HEq ((H.appendEvent hs E hinit).toHistory.event i.castSucc)
          (H.toHistory.event i) := by
        change HEq ((H.extendCoreEventFamily E i.castSucc).toMetricCutCapEvent)
          (H.toHistory.event i)
        rw [H.extendCoreEventFamily_toMetricCutCapEvent]
        exact H.toHistory.appendEvent_event_castSucc_heq hs E.toMetricCutCapEvent hinit i
      exact MetricCutCapEvent.PresentedStaticCap.hasCanonicalWindow_of_family_heq
        (H.appendEvent_stage_castSucc hs E hinit i.castSucc)
        (H.appendEvent_stage_castSucc hs E hinit i.succ)
        (H.appendEvent_time_castSucc hs E hinit i.castSucc)
        (H.appendEvent_time_castSucc hs E hinit i.succ) hE
        rfl rfl rfl rfl (old i).static (R i.castSucc).static
        (hOld i).2.2.2.2 (holdwin i)
  · intro i
    cases i using Fin.lastCases with
    | last =>
      calc
        (p.spliceAfter q H.horizon).delta
            ((H.appendEvent hs E hinit).time (Fin.last H.eventCount).succ) =
            (p.spliceAfter q H.horizon).delta s :=
          congrArg _ (H.appendEvent_time_last hs E hinit)
        _ = q.delta s := (p.spliceAfter_eval_of_lt q hfuture).1
        _ ≤ δbound := hδnew
    | cast i =>
      have hti : H.time i.succ ≤ H.horizon :=
        (H.time_strictMono.monotone (Fin.le_last i.succ)).trans H.time_le_horizon
      calc
        (p.spliceAfter q H.horizon).delta
            ((H.appendEvent hs E hinit).time i.castSucc.succ) =
            (p.spliceAfter q H.horizon).delta (H.time i.succ) :=
          congrArg _ (H.appendEvent_time_castSucc hs E hinit i.succ)
        _ = p.delta (H.time i.succ) := (p.spliceAfter_eval_of_le q hti).1
        _ ≤ δbound := hδold i
  · intro i
    cases i using Fin.lastCases with
    | last =>
      calc
        (p.spliceAfter q H.horizon).neckRadius
            ((H.appendEvent hs E hinit).time (Fin.last H.eventCount).succ) =
            (p.spliceAfter q H.horizon).neckRadius s :=
          congrArg _ (H.appendEvent_time_last hs E hinit)
        _ = q.neckRadius s := (p.spliceAfter_eval_of_lt q hfuture).2.1
        _ ≤ ρbound := hρnew
    | cast i =>
      have hti : H.time i.succ ≤ H.horizon :=
        (H.time_strictMono.monotone (Fin.le_last i.succ)).trans H.time_le_horizon
      calc
        (p.spliceAfter q H.horizon).neckRadius
            ((H.appendEvent hs E hinit).time i.castSucc.succ) =
            (p.spliceAfter q H.horizon).neckRadius (H.time i.succ) :=
          congrArg _ (H.appendEvent_time_castSucc hs E hinit i.succ)
        _ = p.neckRadius (H.time i.succ) := (p.spliceAfter_eval_of_le q hti).2.1
        _ ≤ ρbound := hρold i

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

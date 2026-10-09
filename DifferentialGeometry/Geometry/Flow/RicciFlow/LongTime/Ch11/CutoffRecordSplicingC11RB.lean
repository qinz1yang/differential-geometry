import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffParameterGluing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordEventExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodContinuationLeaves

set_option autoImplicit false

/-!
# S-CH11-REPROVE-B (G1)：records 的 `appendEvent` + `spliceAfter`（S3 的 record 层核心）

按 reference 重证 astra `ST/CutoffRecordSplicing.lean`（W8 里编不过：私有结构 `CutoffFields`
的字段 `nominalRadius` 不可访问）与 `ST/CanonicalCutoffRecordSplicing.lean`（SKIP，依赖前者）。

* `nominalRadius_heq_of_neck_heq_C11RB`：**不碰私有结构**。`nominalRadius` 由 `scale_eq`
  （`(neck α).scale = (nominalRadius ⟨α⟩ ^ 2)⁻¹`）与 `nominal_pos` 完全决定，所以
  `neck` / `delta` / `order` 的 HEq 传递给 `nominalRadius`（只用公有 API）；
* `GeometricCutoffRecord.appendEvent_nominalRadius_heq_C11RB`：`appendEvent` 保 `nominalRadius`；
* `RetainedCoreHistory.exists_cutoff_records_at_appendEvent_spliceAfter_C11RB`：
  `appendEvent` 之后在整个旧区间保持旧参数（`spliceAfter`），新旧 record 的五个字段 HEq 传递；
* `RetainedCoreHistory.exists_isCanonicalCutoffRecordFamily_appendEvent_spliceAfter_C11RB`：
  S3 的 splicing 步：canonical window 与 `δ / ρ` 界随 `spliceAfter` 保持。
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- 两个事件 HEq 且 `neck / delta / order` HEq 时，`nominalRadius` HEq
（`scale_eq` 与 `nominal_pos` 决定 `nominalRadius`；只用公有字段）。 -/
theorem nominalRadius_heq_of_neck_heq_C11RB
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    {E : MetricCutCapEvent P Q a s} {E' : MetricCutCapEvent P' Q' a' s'}
    (hP : P' = P) (hQ : Q' = Q) (ha : a' = a) (hs : s' = s) (hE : HEq E' E)
    {δ : E.transition.trace.tubes.Index → ℝ} {δ' : E'.transition.trace.tubes.Index → ℝ}
    {k : E.transition.trace.tubes.Index → ℕ} {k' : E'.transition.trace.tubes.Index → ℕ}
    (hδ : HEq δ' δ) (hk : HEq k' k)
    {N : ∀ α, NormalizedNeck E.terminal.metric (δ α) (k α)}
    {N' : ∀ α, NormalizedNeck E'.terminal.metric (δ' α) (k' α)} (hN : HEq N' N)
    {f : Nonempty E.transition.trace.tubes.Index → ℝ}
    {f' : Nonempty E'.transition.trace.tubes.Index → ℝ}
    (hf : ∀ h, 0 < f h) (hf' : ∀ h, 0 < f' h)
    (hsc : ∀ α, (N α).scale = (f ⟨α⟩ ^ 2)⁻¹)
    (hsc' : ∀ α, (N' α).scale = (f' ⟨α⟩ ^ 2)⁻¹) :
    HEq f' f := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  cases eq_of_heq hδ
  cases eq_of_heq hk
  cases eq_of_heq hN
  refine heq_of_eq (funext fun h => ?_)
  obtain ⟨α⟩ := h
  have h1 : (f' ⟨α⟩ ^ 2)⁻¹ = (f ⟨α⟩ ^ 2)⁻¹ := (hsc' α).symm.trans (hsc α)
  have h2 : f' ⟨α⟩ ^ 2 = f ⟨α⟩ ^ 2 := inv_injective h1
  exact (pow_left_inj₀ (hf' ⟨α⟩).le (hf ⟨α⟩).le two_ne_zero).mp h2

/-- `appendEvent` 保 `nominalRadius`（HEq）。astra 用私有 `CutoffFields.transport`；这里由
`neck / delta / order` 的 HEq 与 `scale_eq` 推出。 -/
theorem GeometricCutoffRecord.appendEvent_nominalRadius_heq_C11RB
    {Q : OrientedThreeStage.{u}} {H : RetainedCoreHistory.{u}} {s : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H.toHistory i p) :
    HEq (GeometricCutoffRecord.appendEvent hs E hinit R).nominalRadius R.nominalRadius := by
  have hE : HEq ((H.appendEvent hs E hinit).toHistory.event i.castSucc)
      (H.toHistory.event i) := by
    change HEq ((H.extendCoreEventFamily E i.castSucc).toMetricCutCapEvent) (H.toHistory.event i)
    rw [H.extendCoreEventFamily_toMetricCutCapEvent]
    exact H.toHistory.appendEvent_event_castSucc_heq hs E.toMetricCutCapEvent hinit i
  exact nominalRadius_heq_of_neck_heq_C11RB
    (H.appendEvent_stage_castSucc hs E hinit i.castSucc)
    (H.appendEvent_stage_castSucc hs E hinit i.succ)
    (H.appendEvent_time_castSucc hs E hinit i.castSucc)
    (H.appendEvent_time_castSucc hs E hinit i.succ) hE
    (R.appendEvent_delta_heq hs E hinit) (R.appendEvent_order_heq hs E hinit)
    (R.appendEvent_neck_heq hs E hinit)
    R.nominal_pos (GeometricCutoffRecord.appendEvent hs E hinit R).nominal_pos
    R.scale_eq (GeometricCutoffRecord.appendEvent hs E hinit R).scale_eq

/-- Append the selected event and keep the parameters on the entire previous time interval
（`spliceAfter`）。旧 / 新 record 的 `nominalRadius / delta / order / neck / static` 都随 HEq 传递。 -/
theorem RetainedCoreHistory.exists_cutoff_records_at_appendEvent_spliceAfter_C11RB
    {Q : OrientedThreeStage.{u}} (H : RetainedCoreHistory.{u}) {s : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (hfuture : H.horizon < s)
    {p q : CutoffParameters}
    (old : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (new : GeometricCutoffRecord (H.appendEvent hs E hinit).toHistory
      (Fin.last H.eventCount) q)
    (hstatic : q.fixed = p.fixed ∧ q.modelRadius = p.modelRadius ∧
      q.modelOrder = p.modelOrder ∧ q.modelAccuracy = p.modelAccuracy ∧
      q.recenterConstant = p.recenterConstant) :
    ∃ R : ∀ i : Fin (H.appendEvent hs E hinit).eventCount,
        GeometricCutoffRecord (H.appendEvent hs E hinit).toHistory i
          (p.spliceAfter q H.horizon),
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
  let K := H.appendEvent hs E hinit
  have htime : K.toHistory.time (Fin.last H.eventCount).succ = s :=
    H.appendEvent_time_last hs E hinit
  have hnewtime : H.horizon < K.toHistory.time (Fin.last H.eventCount).succ := by
    rw [htime]
    exact hfuture
  have holdtime (i : Fin H.eventCount) : K.toHistory.time i.castSucc.succ ≤ H.horizon := by
    have ht : K.toHistory.time i.castSucc.succ = H.time i.succ :=
      H.appendEvent_time_castSucc hs E hinit i.succ
    rw [ht]
    exact (H.time_strictMono.monotone (Fin.le_last i.succ)).trans H.time_le_horizon
  let Rnew := new.spliceAfterParametersOfLT hstatic hnewtime
  let Rold (i : Fin H.eventCount) :=
    ((old i).appendEvent hs E hinit).spliceAfterParametersOfLE (q := q) (holdtime i)
  let R : ∀ i : Fin (H.eventCount + 1),
      GeometricCutoffRecord K.toHistory i (p.spliceAfter q H.horizon) :=
    Fin.lastCases Rnew Rold
  have hRold (i : Fin H.eventCount) : R i.castSucc = Rold i := Fin.lastCases_castSucc i
  have hRnew : R (Fin.last H.eventCount) = Rnew := Fin.lastCases_last
  refine ⟨R, ?_, ?_⟩
  · intro i
    rw [hRold]
    have hp := ((old i).appendEvent hs E hinit).spliceAfterParametersOfLE_preserves
      (q := q) (holdtime i)
    exact ⟨(heq_of_eq hp.1).trans ((old i).appendEvent_nominalRadius_heq_C11RB hs E hinit),
      (heq_of_eq hp.2.1).trans ((old i).appendEvent_delta_heq hs E hinit),
      (heq_of_eq hp.2.2.1).trans ((old i).appendEvent_order_heq hs E hinit),
      hp.2.2.2.1.trans ((old i).appendEvent_neck_heq hs E hinit),
      hp.2.2.2.2.trans ((old i).appendEvent_static_heq hs E hinit)⟩
  · rw [hRnew]
    have hp := new.spliceAfterParametersOfLT_preserves hstatic hnewtime
    exact ⟨heq_of_eq hp.1, heq_of_eq hp.2.1, heq_of_eq hp.2.2.1,
      hp.2.2.2.1, hp.2.2.2.2⟩

/-- Canonical windows and event bounds follow the selected records through a future splice
（S3 的 splicing 步）。 -/
theorem RetainedCoreHistory.exists_isCanonicalCutoffRecordFamily_appendEvent_spliceAfter_C11RB
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
    H.exists_cutoff_records_at_appendEvent_spliceAfter_C11RB hs E hinit hfuture old new hqp
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

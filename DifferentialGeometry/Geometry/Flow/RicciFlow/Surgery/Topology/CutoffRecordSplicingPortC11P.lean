import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffParameterGluing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordEventExtension

/-!
# O-CH11-FIX3 port of astra `CutoffRecordSplicing`（`PortC11P`）

来源：donor
`DifferentialGeometry/Geometry/Flow/RicciFlow/Surgery/Topology/CutoffRecordSplicing.lean`
（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。donor 文本在本树 elaboration 失败：私有结构
`CutoffFields`（宿主 `CutoffRecordEventExtension`，与 donor 逐字节相同）的字段 `nominalRadius`
用 dot notation `R.nominalRadius` 访问时报 "Field ... is private"（`open private` 不覆盖
private structure 的 field-notation），连带 `transport_nominalRadius_heq` unknown。

本 port 只有一处 elaboration 层面修补（no statement / definition / proof idea altered）：
* `transport_nominalRadius_heq` 的陈述里两处 `(…).nominalRadius` 改写为显式 projection
  application `CutoffFields.nominalRadius (…)`（同一个 term，只换 surface syntax）。

原路径 `CutoffRecordSplicing` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open private CutoffFields CutoffFields.transport from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordEventExtension

private theorem transport_nominalRadius_heq
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    {E : MetricCutCapEvent P Q a s} {E' : MetricCutCapEvent P' Q' a' s'}
    (hP : P' = P) (hQ : Q' = Q) (ha : a' = a) (hs : s' = s) (hE : HEq E' E)
    {F : {δ : ℝ} → {k : ℕ} → NormalizedNeck E.terminal.metric δ k → ℝ → Type u}
    {F' : {δ : ℝ} → {k : ℕ} → NormalizedNeck E'.terminal.metric δ k → ℝ → Type u}
    (hF : ∀ {δ r : ℝ} {k : ℕ}
      {N : NormalizedNeck E.terminal.metric δ k} {N' : NormalizedNeck E'.terminal.metric δ k},
      HEq N' N → F N r → F' N' r)
    {p : CutoffParameters} (R : CutoffFields E F p) :
    HEq (CutoffFields.nominalRadius
        (CutoffFields.transport (F := F) (F' := F') hP hQ ha hs hE hF R))
      (CutoffFields.nominalRadius R) := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  rfl

theorem GeometricCutoffRecord.appendEvent_nominalRadius_heq
    {Q : OrientedThreeStage.{u}} {H : RetainedCoreHistory.{u}} {s : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H.toHistory i p) :
    HEq (GeometricCutoffRecord.appendEvent hs E hinit R).nominalRadius R.nominalRadius := by
  exact transport_nominalRadius_heq _ _ _ _ _ _ _

/-- Append the selected event and keep the parameters on the entire previous time interval.
The old and new geometric records, including their finite orders and nominal radii, are
transported to the spliced parameter without replacing their geometric witnesses. -/
theorem RetainedCoreHistory.exists_cutoff_records_at_appendEvent_spliceAfter
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
    exact ⟨(heq_of_eq hp.1).trans ((old i).appendEvent_nominalRadius_heq hs E hinit),
      (heq_of_eq hp.2.1).trans ((old i).appendEvent_delta_heq hs E hinit),
      (heq_of_eq hp.2.2.1).trans ((old i).appendEvent_order_heq hs E hinit),
      hp.2.2.2.1.trans ((old i).appendEvent_neck_heq hs E hinit),
      hp.2.2.2.2.trans ((old i).appendEvent_static_heq hs E hinit)⟩
  · rw [hRnew]
    have hp := new.spliceAfterParametersOfLT_preserves hstatic hnewtime
    exact ⟨heq_of_eq hp.1, heq_of_eq hp.2.1, heq_of_eq hp.2.2.1,
      hp.2.2.2.1, hp.2.2.2.2⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

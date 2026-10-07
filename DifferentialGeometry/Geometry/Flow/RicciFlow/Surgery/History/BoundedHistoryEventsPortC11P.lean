import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.RawPrefixFineRecords
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryExtension

/-!
# S-CH11-FIX7 port of astra `BoundedHistoryEvents`（`PortC11P`）

来源：donor `BoundedHistoryEvents.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树有 3 个 error（`RawPrefixFineRecords` 落地后暴露）；本 port 只做 elaboration
层面修补（no statement / definition / proof idea altered）：
* `exists_unique_original_event_of_birth_le_prefix_horizon`：`exact congrArg Fin.val hi'`
  期望类型是 `i' = i` 的 `Fin.val` 版，先 `have hval := congrArg Fin.val hi'` 再 `exact hval`
  （让 `congrArg` 在不带期望类型的情形下 elaborate）。
* `exists_fixed_history_for_bounded_event_queries`：两处 `rw [F.tower.horizon_eq]` 找不到
  `(F.tower.history ?n).horizon`（目标写的是 `….toHistory.horizon`），先 `change` 成
  `(F.tower.history N).horizon ≤ (F.tower.history n).horizon` 与
  `(N : ℝ) ≤ (F.tower.history n).horizon`（defeq）再 `rw`。
-/

/-! Original events below a fixed observation horizon. The actual presentation
prefix excludes additional early events; the separate raw prefix retains the
literal old event, metric curves and arbitrary original fine records. -/
set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
namespace GC.GeneralFlow
universe u

/-- The closed horizon endpoint is included: every event born by the original
horizon already has an original index. A raw initial embedding alone would
not establish this assertion. -/
theorem event_index_lt_of_birth_le_prefix_horizon
    {H J : ObservedHistory.{u}} (hprefix : H.IsPrefixOf J)
    (j : Fin J.eventCount) (hj : J.time j.succ ≤ H.horizon) :
    j.val < H.eventCount := by
  let t : Icc (0 : ℝ) J.horizon :=
    ⟨H.horizon, H.horizon_nonneg, hprefix.horizon_le⟩
  have hstage : j.succ ≤ J.activeStage t := J.le_activeStage t j.succ hj
  have hcount : (J.activeStage t).val = H.eventCount := hprefix.presentation.count_eq
  have hindex : j.val + 1 ≤ (J.activeStage t).val := hstage
  omega

/-- The same later event has a unique original index. The literal raw-prefix
cast and the presentation-prefix count agree because both retain its value. -/
theorem exists_unique_original_event_of_birth_le_prefix_horizon
    {H J : RetainedCoreHistory.{u}} (I : RawInitialPrefix H J)
    (hprefix : H.toHistory.IsPrefixOf J.toHistory)
    (j : Fin J.eventCount) (hj : J.time j.succ ≤ H.horizon) :
    ∃! i : Fin H.eventCount, i.castLE I.count_le = j := by
  let i : Fin H.eventCount :=
    ⟨j.val, event_index_lt_of_birth_le_prefix_horizon hprefix j hj⟩
  refine ⟨i, Fin.ext rfl, ?_⟩
  intro i' hi'
  apply Fin.ext
  have hval := congrArg Fin.val hi'
  exact hval

private theorem metric_data_of_retained_event_heq
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (E : RetainedCoreEvent P Q a s) (E' : RetainedCoreEvent P' Q' a' s')
    (hP : P' = P) (hQ : Q' = Q) (ha : a' = a) (hs : s' = s) (hE : HEq E' E) :
    (∀ v : ℝ, HEq (E'.incoming.flow.base.metric v) (E.incoming.flow.base.metric v)) ∧
    HEq E'.terminal.metric E.terminal.metric ∧ HEq E'.outputMetric E.outputMetric := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  exact ⟨fun _ => HEq.rfl, HEq.rfl, HEq.rfl⟩

/-- The old metric curves and endpoint metrics are transported without any
cutoff-record input. This is literal event preservation, not flow uniqueness. -/
theorem raw_prefix_incoming_metric_data
    {H J : RetainedCoreHistory.{u}} (I : RawInitialPrefix H J)
    (i : Fin H.eventCount) :
    (∀ v : ℝ, HEq ((J.toHistory.event (i.castLE I.count_le)).incoming.flow.base.metric v)
      ((H.toHistory.event i).incoming.flow.base.metric v)) ∧
    HEq (J.toHistory.event (i.castLE I.count_le)).terminal.metric
      (H.toHistory.event i).terminal.metric ∧
    HEq (J.toHistory.event (i.castLE I.count_le)).outputMetric
      (H.toHistory.event i).outputMetric := by
  exact metric_data_of_retained_event_heq
    (H.coreEvent i) (J.coreEvent (i.castLE I.count_le))
    (I.stage_eq i.castSucc) (I.stage_eq i.succ)
    (I.time_eq i.castSucc) (I.time_eq i.succ) (I.event_heq i)

/-- The full old incoming curve, terminal limit and output metric survive
literally. The transported original record retains all five geometric fields;
it is not identified with an independently chosen later coarse record. -/
theorem raw_prefix_original_event_data
    {H J : RetainedCoreHistory.{u}} (I : RawInitialPrefix H J)
    (i : Fin H.eventCount) {p : CutoffParameters}
    (R : GeometricCutoffRecord H.toHistory i p) :
    J.time (i.castLE I.count_le).castSucc = H.time i.castSucc ∧
    J.time (i.castLE I.count_le).succ = H.time i.succ ∧
    J.stage (i.castLE I.count_le).castSucc = H.stage i.castSucc ∧
    J.stage (i.castLE I.count_le).succ = H.stage i.succ ∧
    (∀ v : ℝ, HEq ((J.toHistory.event (i.castLE I.count_le)).incoming.flow.base.metric v)
      ((H.toHistory.event i).incoming.flow.base.metric v)) ∧
    HEq (J.toHistory.event (i.castLE I.count_le)).terminal.metric
      (H.toHistory.event i).terminal.metric ∧
    HEq (J.toHistory.event (i.castLE I.count_le)).outputMetric
      (H.toHistory.event i).outputMetric ∧
    HEq (I.transportRecord R).nominalRadius R.nominalRadius ∧
    HEq (I.transportRecord R).delta R.delta ∧
    HEq (I.transportRecord R).order R.order ∧
    HEq (I.transportRecord R).neck R.neck ∧
    HEq (I.transportRecord R).static R.static := by
  obtain ⟨hincoming, hterminal, houtput⟩ := raw_prefix_incoming_metric_data I i
  exact ⟨I.time_eq i.castSucc, I.time_eq i.succ, I.stage_eq i.castSucc,
    I.stage_eq i.succ, hincoming, hterminal, houtput, I.transportRecord_preserves R⟩

/-- A fixed physical horizon chooses ONE original finite observation before all
queried later observations and events. Every birth at or below Tmax is the
literal cast of a unique event in that original history. -/
theorem exists_fixed_history_for_bounded_event_queries
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g)
    (step : ∀ n, RawInitialPrefix (F.tower.history n) (F.tower.history (n + 1)))
    (Tmax : ℝ) :
    ∃ N : ℕ, Tmax < (N : ℝ) ∧
      ∀ (n : ℕ) (hNn : N ≤ n),
        let I := rawPrefixOfLE F step N n hNn;
        ∀ (j : Fin (F.tower.history n).eventCount),
          (F.tower.history n).time j.succ ≤ Tmax →
          ∃! i : Fin (F.tower.history N).eventCount, i.castLE I.count_le = j := by
  obtain ⟨N, hTN⟩ := exists_nat_gt Tmax
  refine ⟨N, hTN, ?_⟩
  intro n hNn
  dsimp only
  intro j hj
  have hh : (F.tower.history N).toHistory.horizon ≤
      (F.tower.history n).toHistory.horizon := by
    change (F.tower.history N).horizon ≤ (F.tower.history n).horizon
    rw [F.tower.horizon_eq, F.tower.horizon_eq]
    exact_mod_cast hNn
  have hprefix : (F.tower.history N).toHistory.IsPrefixOf
      (F.tower.history n).toHistory := by
    refine ⟨hh, ?_⟩
    have ht : (⟨(F.tower.history N).toHistory.horizon,
        (F.tower.history N).toHistory.horizon_nonneg, hh⟩ :
        Icc (0 : ℝ) (F.tower.history n).toHistory.horizon) =
        ⟨(N : ℝ), Nat.cast_nonneg N, by
          change (N : ℝ) ≤ (F.tower.history n).horizon
          rw [F.tower.horizon_eq]
          exact_mod_cast hNn⟩ := Subtype.ext (F.tower.horizon_eq N)
    rw [ht]
    exact F.tower.toObservationTower.integer_restrict N n hNn
  apply exists_unique_original_event_of_birth_le_prefix_horizon
    (rawPrefixOfLE F step N n hNn) hprefix j
  rw [F.tower.horizon_eq]
  exact hj.trans hTN.le

end GC.GeneralFlow

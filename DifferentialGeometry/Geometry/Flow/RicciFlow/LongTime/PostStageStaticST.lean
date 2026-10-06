import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ExteriorDiskFlow

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Geometry.Curvature
open Set
open scoped Manifold ContDiff

/-!
# 无事件区间上的 `postStage` / `postMetric`（lane S-A14-STATIC，G1）

`GC.LongTime.postStage O t` 是 `O.observe (max t 0)` 的最后一个 stage。本文件证明：若
`Ioo a b`（`0 ≤ a`）里没有 event time（`∀ s ∈ O.eventTimes, s ∉ Ioo a b`），则

* `postStage O t = postStage O t'`（类型相等，`postStage_eq_of_no_event_ST`），因此有
  diffeo `postStageEquiv_ST`（其实是 `cast`，数据上是恒等）；
* 固定 history `O.history ⌈b⌉₊` 里 `postStage O t = stage j₀`、
  `HEq (postMetric O t) (stageMetric j₀ t)`（`postStage_eq_static_ST`、`postMetric_heq_static_ST`）；
* `postMetricAt_ST O t₀ t`：`postMetric O t` 沿 `postStageEquiv_ST` 拉回到 `postStage O t₀`，
  它在 `Ioo a b` 上等于该 stage 的 Ricci flow 解 `S.base.metric t`
  （`exists_stageFlow_of_no_event_ST`，带 `IsSolutionOn` 与 `MetricSmoothUpTo`）。

没有新的具名 Prop：事件条件直接写成 `∀ s ∈ O.eventTimes, s ∉ Ioo a b`。
`exists_noEvent_interval_ST` 说明每个 regular time `τ ∉ O.eventTimes` 有这样的区间。
-/

namespace GC.LongTime

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- `0 ≤ t` 时 `max t 0 = t`：`postStage` 直接读 `observe t`。 -/
theorem postStage_eq_observe_ST (O : ObservationTower P g) {t : ℝ} (ht : 0 ≤ t) :
    postStage O t = (O.observe t ht).stage (Fin.last (O.observe t ht).eventCount) := by
  have hobs : O.observe (max t 0) (le_max_right t 0) = O.observe t ht := by
    have hsub : (⟨max t 0, le_max_right t 0⟩ : {t : ℝ // 0 ≤ t}) = ⟨t, ht⟩ :=
      Subtype.ext (max_eq_left ht)
    exact congrArg (fun t : {t : ℝ // 0 ≤ t} => O.observe t.val t.property) hsub
  exact congrArg (fun H : ObservedHistory => H.stage (Fin.last H.eventCount)) hobs

/-- `t ≤ n` 时 `t` 作为 `(O.history n)` 的时间轴上的点。 -/
def timeIn_ST (O : ObservationTower P g) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (htn : t ≤ n) :
    Icc (0 : ℝ) (O.history n).horizon :=
  ⟨t, ht, by rw [O.horizon_eq]; exact htn⟩

/-- `postStage` 用固定 history `O.history n`（`t ≤ n`）表示：它是 `activeStage` 处的 stage。
（不需要无事件假设。） -/
theorem postStage_eq_history_ST (O : ObservationTower P g) (n : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (htn : t ≤ n) :
    postStage O t =
      (O.history n).stage ((O.history n).activeStage (timeIn_ST O n ht htn)) := by
  rw [postStage_eq_observe_ST O ht]
  have R := O.observe_eq_atIndex n t ht htn
  have hj : Fin.cast (congrArg (· + 1) R.count_eq) (Fin.last (O.observe t ht).eventCount) =
      Fin.last (O.atIndex n t ht htn).eventCount := Fin.ext R.count_eq
  rw [R.stage_eq (Fin.last (O.observe t ht).eventCount), hj]
  rfl

/-- `H.restrict t` 的最后一个 stage 的 metric 在 `t` 处就是 `H.stageMetric (activeStage t) t`
（`time (activeStage t) < t` 时）。 -/
theorem restrict_stageMetric_last_heq_ST (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
    (hlt : H.time (H.activeStage t) < t.1) :
    HEq ((H.restrict t).stageMetric (Fin.last (H.restrict t).eventCount) t.1)
      (H.stageMetric (H.activeStage t) t.1) := by
  have hf : (H.restrict t).time (Fin.last (H.restrict t).eventCount) <
      (H.restrict t).horizon := hlt
  simp only [ObservedHistory.stageMetric, Fin.lastCases_last, dite_eq_left hf]
  exact heq_of_eq (H.closedPrefixAt_metric t hlt t.1)

/-- `postMetric` 同样可以去掉 `max t 0`。 -/
theorem postMetric_heq_observe_ST (O : ObservationTower P g) {t : ℝ} (ht : 0 ≤ t) :
    HEq (postMetric O t)
      ((O.observe t ht).stageMetric (Fin.last (O.observe t ht).eventCount) t) := by
  have htime : max t 0 = t := max_eq_left ht
  have hobs : O.observe (max t 0) (le_max_right t 0) = O.observe t ht := by
    have hsub : (⟨max t 0, le_max_right t 0⟩ : {t : ℝ // 0 ≤ t}) = ⟨t, ht⟩ :=
      Subtype.ext htime
    exact congrArg (fun t : {t : ℝ // 0 ≤ t} => O.observe t.val t.property) hsub
  have hmetric : ∀ {H H' : ObservedHistory}, H = H' → ∀ t : ℝ,
      HEq (H.stageMetric (Fin.last H.eventCount) t)
        (H'.stageMetric (Fin.last H'.eventCount) t) := by
    intro H H' h t
    cases h
    rfl
  exact (heq_of_eq (congrArg
    (fun τ => (O.observe (max t 0) (le_max_right t 0)).stageMetric
      (Fin.last (O.observe (max t 0) (le_max_right t 0)).eventCount) τ) htime)).trans
    (hmetric hobs t)

/-- `postMetric O t` 用固定 history `O.history n` 的 `stageMetric` 表示（`HEq`）。 -/
theorem postMetric_heq_history_ST (O : ObservationTower P g) (n : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (htn : t ≤ n)
    (hlt : (O.history n).time ((O.history n).activeStage (timeIn_ST O n ht htn)) < t) :
    HEq (postMetric O t)
      ((O.history n).stageMetric ((O.history n).activeStage (timeIn_ST O n ht htn)) t) := by
  refine (postMetric_heq_observe_ST O ht).trans ?_
  have R := O.observe_eq_atIndex n t ht htn
  have hj : Fin.cast (congrArg (· + 1) R.count_eq) (Fin.last (O.observe t ht).eventCount) =
      Fin.last (O.atIndex n t ht htn).eventCount := Fin.ext R.count_eq
  have hdom : t ∈ (O.observe t ht).stageDomain (Fin.last (O.observe t ht).eventCount) := by
    simp only [ObservedHistory.stageDomain, Fin.lastCases_last]
    exact ⟨(O.observe t ht).time_le_horizon, le_rfl⟩
  refine (R.metric_heq _ t hdom).trans ?_
  rw [hj]
  exact restrict_stageMetric_last_heq_ST (O.history n) (timeIn_ST O n ht htn) hlt

/-- 无事件：`H.time j ≤ t'` 且 `t, t' ∈ Ioo a b` 蕴含 `H.time j ≤ t`。 -/
theorem time_le_of_no_event_ST (O : ObservationTower P g) (n : ℕ) {a b : ℝ} (ha : 0 ≤ a)
    (hno : ∀ s ∈ O.eventTimes, s ∉ Ioo a b) {t t' : ℝ} (ht : t ∈ Ioo a b)
    (ht' : t' ∈ Ioo a b) (j : Fin ((O.history n).eventCount + 1))
    (hj : (O.history n).time j ≤ t') : (O.history n).time j ≤ t := by
  by_contra hlt
  rw [not_le] at hlt
  cases j using Fin.cases with
  | zero =>
    rw [(O.history n).time_zero] at hlt
    exact absurd (ha.trans_lt ht.1) (not_lt.mpr hlt.le)
  | succ i =>
    have hmem : (O.history n).time i.succ ∈ O.eventTimes :=
      Set.mem_iUnion.2 ⟨n, i, rfl⟩
    exact hno _ hmem ⟨ht.1.trans hlt, hj.trans_lt ht'.2⟩

/-- 无事件区间上 `activeStage` 常值（`t ≤ t'` 版本）。 -/
theorem activeStage_eq_of_no_event_ST (O : ObservationTower P g) (n : ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (hno : ∀ s ∈ O.eventTimes, s ∉ Ioo a b) {t t' : ℝ}
    (ht : t ∈ Ioo a b) (ht' : t' ∈ Ioo a b) (htt : t ≤ t') (ht0 : 0 ≤ t) (ht'0 : 0 ≤ t')
    (htn : t ≤ n) (ht'n : t' ≤ n) :
    (O.history n).activeStage (timeIn_ST O n ht0 htn) =
      (O.history n).activeStage (timeIn_ST O n ht'0 ht'n) := by
  refine le_antisymm ((O.history n).activeStage_mono htt) ?_
  exact (O.history n).le_activeStage _ _
    (time_le_of_no_event_ST O n ha hno ht ht' _ ((O.history n).activeStage_time_le _))

/-- 无事件区间上 `time (activeStage t) < t`（`t` 是 regular time）。 -/
theorem time_activeStage_lt_ST (O : ObservationTower P g) (n : ℕ) {a b : ℝ} (ha : 0 ≤ a)
    (hno : ∀ s ∈ O.eventTimes, s ∉ Ioo a b) {t : ℝ} (ht : t ∈ Ioo a b) (ht0 : 0 ≤ t)
    (htn : t ≤ n) :
    (O.history n).time ((O.history n).activeStage (timeIn_ST O n ht0 htn)) < t := by
  refine lt_of_le_of_ne ((O.history n).activeStage_time_le _) ?_
  intro heq
  generalize hj : (O.history n).activeStage (timeIn_ST O n ht0 htn) = j at heq
  cases j using Fin.cases with
  | zero =>
    rw [(O.history n).time_zero] at heq
    exact absurd (ha.trans_lt ht.1) (by rw [← heq]; exact lt_irrefl _)
  | succ i =>
    have hmem : (O.history n).time i.succ ∈ O.eventTimes :=
      Set.mem_iUnion.2 ⟨n, i, rfl⟩
    exact hno _ hmem (by rw [heq]; exact ht)

/-- **G1 主定理**：无事件区间 `Ioo a b`（`0 ≤ a`）上 `postStage O t` 与 `t` 无关（类型相等）。 -/
theorem postStage_eq_of_no_event_ST (O : ObservationTower P g) {a b : ℝ} (ha : 0 ≤ a)
    (hno : ∀ s ∈ O.eventTimes, s ∉ Ioo a b) {t t' : ℝ} (ht : t ∈ Ioo a b)
    (ht' : t' ∈ Ioo a b) : postStage O t = postStage O t' := by
  have key : ∀ {t t' : ℝ}, t ∈ Ioo a b → t' ∈ Ioo a b → t ≤ t' →
      postStage O t = postStage O t' := by
    intro t t' ht ht' htt
    have ht0 : 0 ≤ t := ha.trans ht.1.le
    have ht'0 : 0 ≤ t' := ha.trans ht'.1.le
    have htn : t ≤ (⌈b⌉₊ : ℕ) := ht.2.le.trans (Nat.le_ceil b)
    have ht'n : t' ≤ (⌈b⌉₊ : ℕ) := ht'.2.le.trans (Nat.le_ceil b)
    rw [postStage_eq_history_ST O ⌈b⌉₊ ht0 htn, postStage_eq_history_ST O ⌈b⌉₊ ht'0 ht'n,
      activeStage_eq_of_no_event_ST O ⌈b⌉₊ ha hno ht ht' htt ht0 ht'0 htn ht'n]
  rcases le_total t t' with h | h
  · exact key ht ht' h
  · exact (key ht' ht h).symm

/-- `S = S'` 给出的 carrier 之间的 diffeo（就是 `cast`，数据上是恒等）。 -/
def stageDiffeo_ST {S S' : OrientedThreeStage.{u}} (h : S = S') :
    S.Carrier ≃ₘ⟮ThreeModel, ThreeModel⟯ S'.Carrier := by
  subst h
  exact Diffeomorph.refl ThreeModel S.Carrier ∞

theorem heq_stageDiffeo_ST_apply {S S' : OrientedThreeStage.{u}} (h : S = S')
    (x : S.Carrier) : HEq (stageDiffeo_ST h x) x := by
  subst h
  exact HEq.rfl

/-- G1：同一无事件区间内 `postStage O t` 与 `postStage O t'` 的 carrier 之间的 diffeo。 -/
def postStageEquiv_ST (O : ObservationTower P g) {a b : ℝ} (ha : 0 ≤ a)
    (hno : ∀ s ∈ O.eventTimes, s ∉ Ioo a b) {t t' : ℝ} (ht : t ∈ Ioo a b)
    (ht' : t' ∈ Ioo a b) :
    (postStage O t).Carrier ≃ₘ⟮ThreeModel, ThreeModel⟯ (postStage O t').Carrier :=
  stageDiffeo_ST (postStage_eq_of_no_event_ST O ha hno ht ht')

open Classical in
/-- `postMetric O t` 沿 `stageDiffeo_ST` 拉回到 `postStage O t₀` 上；若 `postStage O t₀ ≠
postStage O t`（不在同一无事件段）则取 junk 值 `postMetric O t₀`。 -/
def postMetricAt_ST (O : ObservationTower P g) (t₀ t : ℝ) : (postStage O t₀).Metric :=
  if h : postStage O t₀ = postStage O t then
    Diffeomorph.pullbackMetric (postMetric O t) (stageDiffeo_ST h)
  else postMetric O t₀

/-- `stageDiffeo_ST h` 拉回 `m` 后与 `m` 是 `HEq`（因为它数据上是恒等）。 -/
theorem heq_pullbackMetric_stageDiffeo_ST {S S' : OrientedThreeStage.{u}} (h : S = S')
    (m : S'.Metric) : HEq (Diffeomorph.pullbackMetric m (stageDiffeo_ST h)) m := by
  subst h
  exact heq_of_eq (Diffeomorph.pullbackMetric_refl m)

/-- `h : postStage O t₀ = postStage O t` 时，`postMetricAt_ST` 就是 `pullbackMetric`。 -/
theorem postMetricAt_ST_of_eq (O : ObservationTower P g) {t₀ t : ℝ}
    (h : postStage O t₀ = postStage O t) :
    postMetricAt_ST O t₀ t = Diffeomorph.pullbackMetric (postMetric O t) (stageDiffeo_ST h) := by
  simp only [postMetricAt_ST, dite_eq_left h]

/-- `t = t₀` 时 `postMetricAt_ST` 就是 `postMetric O t₀`（`pullbackMetric_refl`）。 -/
theorem postMetricAt_ST_self (O : ObservationTower P g) (t₀ : ℝ) :
    postMetricAt_ST O t₀ t₀ = postMetric O t₀ := by
  rw [postMetricAt_ST_of_eq O rfl]
  exact Diffeomorph.pullbackMetric_refl _

/-- `postMetricAt_ST O t₀ t` 与 `postMetric O t` 是 `HEq`（同一张量，只是 carrier 类型 cast）。 -/
theorem heq_postMetricAt_ST (O : ObservationTower P g) {t₀ t : ℝ}
    (h : postStage O t₀ = postStage O t) :
    HEq (postMetricAt_ST O t₀ t) (postMetric O t) := by
  rw [postMetricAt_ST_of_eq O h]
  exact heq_pullbackMetric_stageDiffeo_ST h _

/-- 固定 history `O.history ⌈b⌉₊` 中，时刻 `t₀` 所在的 stage 下标。 -/
def staticIdx_ST (O : ObservationTower P g) (b : ℝ) {t₀ : ℝ} (ht₀0 : 0 ≤ t₀) (ht₀b : t₀ ≤ b) :
    Fin ((O.history ⌈b⌉₊).eventCount + 1) :=
  (O.history ⌈b⌉₊).activeStage (timeIn_ST O ⌈b⌉₊ ht₀0 (ht₀b.trans (Nat.le_ceil b)))

/-- 无事件区间上所有 `t` 的 `activeStage` 等于 `staticIdx_ST`（任意次序）。 -/
theorem activeStage_eq_staticIdx_ST (O : ObservationTower P g) {a b : ℝ} (ha : 0 ≤ a)
    (hno : ∀ s ∈ O.eventTimes, s ∉ Ioo a b) {t₀ t : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (ht : t ∈ Ioo a b) :
    (O.history ⌈b⌉₊).activeStage
        (timeIn_ST O ⌈b⌉₊ (ha.trans ht.1.le) (ht.2.le.trans (Nat.le_ceil b))) =
      staticIdx_ST O b (ha.trans ht₀.1.le) ht₀.2.le := by
  rcases le_total t t₀ with h | h
  · exact activeStage_eq_of_no_event_ST O ⌈b⌉₊ ha hno ht ht₀ h _ _ _ _
  · exact (activeStage_eq_of_no_event_ST O ⌈b⌉₊ ha hno ht₀ ht h _ _ _ _).symm

/-- G1：`Ioo a b` 上 `postStage O t = stage j₀`（固定 history `⌈b⌉₊`，固定下标 `j₀`）。 -/
theorem postStage_eq_static_ST (O : ObservationTower P g) {a b : ℝ} (ha : 0 ≤ a)
    (hno : ∀ s ∈ O.eventTimes, s ∉ Ioo a b) {t₀ t : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (ht : t ∈ Ioo a b) :
    postStage O t =
      (O.history ⌈b⌉₊).stage (staticIdx_ST O b (ha.trans ht₀.1.le) ht₀.2.le) := by
  rw [postStage_eq_history_ST O ⌈b⌉₊ (ha.trans ht.1.le) (ht.2.le.trans (Nat.le_ceil b)),
    activeStage_eq_staticIdx_ST O ha hno ht₀ ht]

/-- G1：`Ioo a b` 上 `postMetric O t` 是 stage `j₀` 的 `stageMetric` 在 `t` 处的值（`HEq`）。 -/
theorem postMetric_heq_static_ST (O : ObservationTower P g) {a b : ℝ} (ha : 0 ≤ a)
    (hno : ∀ s ∈ O.eventTimes, s ∉ Ioo a b) {t₀ t : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (ht : t ∈ Ioo a b) :
    HEq (postMetric O t)
      ((O.history ⌈b⌉₊).stageMetric (staticIdx_ST O b (ha.trans ht₀.1.le) ht₀.2.le) t) := by
  have h := postMetric_heq_history_ST O ⌈b⌉₊ (ha.trans ht.1.le)
    (ht.2.le.trans (Nat.le_ceil b)) (time_activeStage_lt_ST O ⌈b⌉₊ ha hno ht _ _)
  rw [activeStage_eq_staticIdx_ST O ha hno ht₀ ht] at h
  exact h

/-- `Ioo a b` 内 `t` 严格晚于 stage `j₀` 的起始时刻（`t` 是 regular time）。 -/
theorem time_staticIdx_lt_ST (O : ObservationTower P g) {a b : ℝ} (ha : 0 ≤ a)
    (hno : ∀ s ∈ O.eventTimes, s ∉ Ioo a b) {t₀ t : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (ht : t ∈ Ioo a b) :
    (O.history ⌈b⌉₊).time (staticIdx_ST O b (ha.trans ht₀.1.le) ht₀.2.le) < t := by
  have h := time_activeStage_lt_ST O ⌈b⌉₊ ha hno ht (ha.trans ht.1.le)
    (ht.2.le.trans (Nat.le_ceil b))
  rw [activeStage_eq_staticIdx_ST O ha hno ht₀ ht] at h
  exact h

/-- stage `j₀ = i.castSucc` 时，`Ioo a b` 内 `t` 早于下一个 event 时刻。 -/
theorem lt_time_succ_staticIdx_ST (O : ObservationTower P g) {a b : ℝ} (ha : 0 ≤ a)
    (hno : ∀ s ∈ O.eventTimes, s ∉ Ioo a b) {t₀ t : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (ht : t ∈ Ioo a b) (i : Fin (O.history ⌈b⌉₊).eventCount)
    (hi : staticIdx_ST O b (ha.trans ht₀.1.le) ht₀.2.le = i.castSucc) :
    t < (O.history ⌈b⌉₊).time i.succ := by
  by_contra hle
  rw [not_lt] at hle
  have h := (O.history ⌈b⌉₊).le_activeStage
    (timeIn_ST O ⌈b⌉₊ (ha.trans ht.1.le) (ht.2.le.trans (Nat.le_ceil b))) i.succ hle
  rw [activeStage_eq_staticIdx_ST O ha hno ht₀ ht, hi] at h
  exact absurd h (not_le.mpr (Fin.castSucc_lt_succ (i := i)))

/-- `t < b` 时 `t` 在 `O.history ⌈b⌉₊` 的 horizon 之内。 -/
theorem lt_horizon_staticIdx_ST (O : ObservationTower P g) {b t : ℝ} (ht : t < b) :
    t < (O.history ⌈b⌉₊).horizon := by
  rw [O.horizon_eq]
  exact ht.trans_le (Nat.le_ceil b)

/-- 单个 stage `j` 上：只要 `J` 落在该 stage 的开时间段里，就有该 stage 的 Ricci flow 解
（`IsSolutionOn` + `MetricSmoothUpTo` + `J ⊆ D.regular` + metric 等于 `stageMetric j`）。 -/
theorem exists_stage_flow_ST (H : ObservedHistory.{u}) (j : Fin (H.eventCount + 1))
    (J : Set ℝ) (s₀ : ℝ) (hs₀ : s₀ ∈ J)
    (hJ : ∀ s ∈ J, H.time j < s ∧ (∀ i : Fin H.eventCount, j = i.castSucc → s < H.time i.succ) ∧
      (j = Fin.last H.eventCount → s < H.horizon)) :
    ∃ (D : RealTimeInterval) (S : SolutionOn (I := ThreeModel) (M := (H.stage j).Carrier) D),
      IsSolutionOn S ∧ (H.stage j).MetricSmoothUpTo S.base.metric D.carrier ∧ J ⊆ D.regular ∧
        ∀ s ∈ J, S.base.metric s = H.stageMetric j s := by
  cases j using Fin.lastCases with
  | last =>
    have h : H.time (Fin.last H.eventCount) < H.horizon :=
      (hJ s₀ hs₀).1.trans ((hJ s₀ hs₀).2.2 rfl)
    refine ⟨RealTimeInterval.closed _ _ h.le, (H.finalSlab h).flow, (H.finalSlab h).equation,
      (H.finalSlab h).smoothUpTo, ?_, ?_⟩
    · intro s hs
      exact ⟨(hJ s hs).1, (hJ s hs).2.2 rfl⟩
    · intro s _
      simp only [ObservedHistory.stageMetric, Fin.lastCases_last, dite_eq_left h]
  | cast i =>
    refine ⟨RealTimeInterval.closedOpen _ _ (H.time_strictMono (Fin.castSucc_lt_succ (i := i))),
      (H.event i).incoming.flow, (H.event i).incoming.equation, (H.event i).incoming.smoothUpTo,
      ?_, ?_⟩
    · intro s hs
      exact ⟨(hJ s hs).1, (hJ s hs).2.1 i rfl⟩
    · intro s _
      simp only [ObservedHistory.stageMetric, Fin.lastCases_castSucc]

/-- 沿 `Q = Q'` 搬运 flow 存在性（`HEq` 的 metric）。 -/
theorem exists_flow_transfer_ST {Q Q' : OrientedThreeStage.{u}} (e : Q = Q') (J : Set ℝ)
    (m : ℝ → Q.Metric) (m' : ℝ → Q'.Metric) (hm : ∀ s ∈ J, HEq (m s) (m' s)) :
    (∃ (D : RealTimeInterval) (S : SolutionOn (I := ThreeModel) (M := Q'.Carrier) D),
      IsSolutionOn S ∧ Q'.MetricSmoothUpTo S.base.metric D.carrier ∧ J ⊆ D.regular ∧
        ∀ s ∈ J, S.base.metric s = m' s) →
    (∃ (D : RealTimeInterval) (S : SolutionOn (I := ThreeModel) (M := Q.Carrier) D),
      IsSolutionOn S ∧ Q.MetricSmoothUpTo S.base.metric D.carrier ∧ J ⊆ D.regular ∧
        ∀ s ∈ J, S.base.metric s = m s) := by
  subst e
  rintro ⟨D, S, hS, hsm, hreg, hmeq⟩
  exact ⟨D, S, hS, hsm, hreg, fun s hs => (hmeq s hs).trans (eq_of_heq (hm s hs)).symm⟩

/-- **G1 主定理（flow 版）**：无事件区间 `Ioo a b` 上 `postStage O t₀` 的 Ricci flow 解 `S`：
`IsSolutionOn S`、`MetricSmoothUpTo`、`Ioo a b ⊆ D.regular`，且 `S.base.metric t =
postMetricAt_ST O t₀ t`（即 `postMetric O t` 经 `postStageEquiv_ST` 拉回）。 -/
theorem exists_stageFlow_of_no_event_ST (O : ObservationTower P g) {a b : ℝ} (ha : 0 ≤ a)
    (hno : ∀ s ∈ O.eventTimes, s ∉ Ioo a b) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) :
    ∃ (D : RealTimeInterval) (S : SolutionOn (I := ThreeModel) (M := (postStage O t₀).Carrier) D),
      IsSolutionOn S ∧ (postStage O t₀).MetricSmoothUpTo S.base.metric D.carrier ∧
        Ioo a b ⊆ D.regular ∧ ∀ s ∈ Ioo a b, S.base.metric s = postMetricAt_ST O t₀ s := by
  refine exists_flow_transfer_ST (postStage_eq_static_ST O ha hno ht₀ ht₀) (Ioo a b)
    (postMetricAt_ST O t₀) (fun s => (O.history ⌈b⌉₊).stageMetric
      (staticIdx_ST O b (ha.trans ht₀.1.le) ht₀.2.le) s) ?_ ?_
  · intro s hs
    exact (heq_postMetricAt_ST O (postStage_eq_of_no_event_ST O ha hno ht₀ hs)).trans
      (postMetric_heq_static_ST O ha hno ht₀ hs)
  · refine exists_stage_flow_ST (O.history ⌈b⌉₊) _ (Ioo a b) t₀ ht₀ ?_
    intro s hs
    refine ⟨time_staticIdx_lt_ST O ha hno ht₀ hs, ?_, ?_⟩
    · intro i hi
      exact lt_time_succ_staticIdx_ST O ha hno ht₀ hs i hi
    · intro _
      exact lt_horizon_staticIdx_ST O hs.2

/-- G1 consumer：`postMetricAt_ST O t t'` 的 `inner` 就是 `postMetric O t'` 沿
`postStageEquiv_ST` 的 pullback。 -/
theorem postMetricAt_ST_inner (O : ObservationTower P g) {a b : ℝ} (ha : 0 ≤ a)
    (hno : ∀ s ∈ O.eventTimes, s ∉ Ioo a b) {t t' : ℝ} (ht : t ∈ Ioo a b)
    (ht' : t' ∈ Ioo a b) (x : (postStage O t).Carrier) (v w : TangentSpace ThreeModel x) :
    (postMetricAt_ST O t t').inner x v w =
      (postMetric O t').inner (postStageEquiv_ST O ha hno ht ht' x)
        (mfderiv ThreeModel ThreeModel (postStageEquiv_ST O ha hno ht ht') x v)
        (mfderiv ThreeModel ThreeModel (postStageEquiv_ST O ha hno ht ht') x w) := by
  rw [postMetricAt_ST_of_eq O (postStage_eq_of_no_event_ST O ha hno ht ht')]
  exact Diffeomorph.pullbackMetric_inner _ _ x v w

/-- regular time `τ ∉ O.eventTimes` 周围有无事件区间 `Ioo a b ∋ τ`（`0 ≤ a`）。 -/
theorem exists_noEvent_interval_ST (O : ObservationTower P g) {τ : ℝ} (hτ : 0 < τ)
    (hreg : τ ∉ O.eventTimes) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < τ ∧ τ < b ∧ ∀ s ∈ O.eventTimes, s ∉ Ioo a b := by
  have hfin : (O.eventTimes ∩ Icc 0 (τ + 1)).Finite := O.eventTimes_finite_Icc 0 (τ + 1)
  have hτ' : τ ∈ (O.eventTimes ∩ Icc 0 (τ + 1))ᶜ := fun h => hreg h.1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hfin.isClosed.isOpen_compl τ hτ'
  refine ⟨τ - min ε τ, τ + min ε 1, ?_, ?_, ?_, ?_⟩
  · linarith [min_le_right ε τ]
  · linarith [lt_min hε hτ]
  · linarith [lt_min hε one_pos]
  · intro s hs hI
    have hd : dist s τ < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hI.1, hI.2, min_le_left ε τ, min_le_left ε 1]
    refine hball hd ⟨hs, ?_, ?_⟩
    · linarith [hI.1, min_le_right ε τ]
    · linarith [hI.2, min_le_right ε 1]

end GC.LongTime

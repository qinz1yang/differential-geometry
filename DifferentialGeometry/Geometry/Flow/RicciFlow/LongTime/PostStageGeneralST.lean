import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.PostStageStaticST
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.RawSurgery

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Set
open scoped Manifold ContDiff

/-!
# 任意 `t ≥ 0` 的 `postStage` / `postMetric` 对固定 history 的 `activeStage`（lane S-A14-STATIC，G5）

`postStage O t`、`postMetric O t` 经 `observe (max t 0) = (O.history ⌈t⌉₊).restrict t` 定义，
而 `PersistentModelPatch.speed` 等用的是任意 `n ≥ ⌈t⌉₊` 的 `(O.history n)` 的 active-stage
metric `stageMetric (activeStage t) t`。本文件给出一般 `t`（不要 regular、不要无事件假设）的
对齐：对 `t : Icc 0 (O.history n).horizon`（`horizon = n`，所以 `n ≥ t` 就是全部相容范围）

* `postStage_eq_activeStage_ST`：`postStage O t.1 = (O.history n).stageAt t`（类型相等）；
* `postMetric_heq_stageMetric_ST`：`HEq (postMetric O t.1) (stageMetric (activeStage t) t.1)`；
* `postMetric_inner_eq_stageMetric_ST`：沿上述 stage 等式 cast 后 `inner` 逐点相等；
* `*_tower_ST`：同样的陈述，直接写成 `F.tower.history n` 的 `toHistory`（`RawSurgery` 版）。

不需要 `time (activeStage t) < t`：`t` 恰是 event 时刻（或 `t = 0`）时用
`event_initial` / `final_initial`（`stageMetric_time_ST`）。没有 obstruction。
-/

namespace GC.LongTime

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- `stageMetric j` 在 `j` 的起始时刻 `time j` 取 `initialMetric j`（`event_initial` /
`final_initial`）。 -/
theorem stageMetric_time_ST (H : ObservedHistory.{u}) (j : Fin (H.eventCount + 1)) :
    H.stageMetric j (H.time j) = H.initialMetric j := by
  cases j using Fin.lastCases with
  | last =>
    by_cases h : H.time (Fin.last H.eventCount) < H.horizon
    · simp only [ObservedHistory.stageMetric, Fin.lastCases_last, dite_eq_left h]
      exact H.final_initial h
    · simp only [ObservedHistory.stageMetric, Fin.lastCases_last, h, dite_false]
  | cast i =>
    simp only [ObservedHistory.stageMetric, Fin.lastCases_castSucc]
    exact H.event_initial i

/-- `restrict_stageMetric_last_heq_ST` 去掉 `time (activeStage t) < t` 假设的版本。 -/
theorem restrict_stageMetric_last_heq_gen_ST (H : ObservedHistory.{u})
    (t : Icc (0 : ℝ) H.horizon) :
    HEq ((H.restrict t).stageMetric (Fin.last (H.restrict t).eventCount) t.1)
      (H.stageMetric (H.activeStage t) t.1) := by
  by_cases hlt : H.time (H.activeStage t) < t.1
  · exact restrict_stageMetric_last_heq_ST H t hlt
  · have heq : H.time (H.activeStage t) = t.1 :=
      le_antisymm (H.activeStage_time_le t) (not_lt.mp hlt)
    have hf : ¬ (H.restrict t).time (Fin.last (H.restrict t).eventCount) <
        (H.restrict t).horizon := hlt
    have key : H.stageMetric (H.activeStage t) t.1 = H.initialMetric (H.activeStage t) := by
      rw [← heq]
      exact stageMetric_time_ST H _
    rw [key]
    simp only [ObservedHistory.stageMetric, Fin.lastCases_last, hf, dite_false]
    exact HEq.rfl

/-- G5：`postMetric` 用固定 history `O.history n`（`t ≤ n`）的 `stageMetric` 表示（`HEq`），
任意 `0 ≤ t`。 -/
theorem postMetric_heq_history_gen_ST (O : ObservationTower P g) (n : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (htn : t ≤ n) :
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
  exact restrict_stageMetric_last_heq_gen_ST (O.history n) (timeIn_ST O n ht htn)

/-- **G5 主定理（stage）**：任意 `n` 与 `t ∈ Icc 0 (O.history n).horizon`：
`postStage O t = (O.history n).stageAt t`（类型相等）。 -/
theorem postStage_eq_activeStage_ST (O : ObservationTower P g) (n : ℕ)
    (t : Icc (0 : ℝ) (O.history n).horizon) :
    postStage O t.1 = (O.history n).stageAt t := by
  have htn : t.1 ≤ n := t.2.2.trans (O.horizon_eq n).le
  exact postStage_eq_history_ST O n t.2.1 htn

/-- **G5 主定理（metric）**：`postMetric O t` 与 `(O.history n).stageMetric (activeStage t) t`
是 `HEq`。 -/
theorem postMetric_heq_stageMetric_ST (O : ObservationTower P g) (n : ℕ)
    (t : Icc (0 : ℝ) (O.history n).horizon) :
    HEq (postMetric O t.1)
      ((O.history n).stageMetric ((O.history n).activeStage t) t.1) := by
  have htn : t.1 ≤ n := t.2.2.trans (O.horizon_eq n).le
  exact postMetric_heq_history_gen_ST O n t.2.1 htn

/-- `RawSurgery` / `F.tower.history n` 写法的 `postStage_eq_activeStage_ST`。 -/
theorem postStage_eq_stageAt_tower_ST (F : GC.Interface.RawSurgery P g) (n : ℕ)
    (t : Icc (0 : ℝ) (F.tower.history n).horizon) :
    postStage F.observation t.1 = (F.tower.history n).toHistory.stageAt t :=
  postStage_eq_activeStage_ST F.observation n t

/-- `RawSurgery` / `F.tower.history n` 写法的 `postMetric_heq_stageMetric_ST`。 -/
theorem postMetric_heq_stageMetric_tower_ST (F : GC.Interface.RawSurgery P g) (n : ℕ)
    (t : Icc (0 : ℝ) (F.tower.history n).horizon) :
    HEq (postMetric F.observation t.1)
      ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage t) t.1) :=
  postMetric_heq_stageMetric_ST F.observation n t

/-- 同一 stage 等式下 `HEq` 的 metric 的 `inner` 逐点相等（carrier 点沿 `cast` 对应）。 -/
theorem inner_eq_of_heq_ST {S S' : OrientedThreeStage.{u}} (h : S = S') {m : S.Metric}
    {m' : S'.Metric} (hm : HEq m m') (x : S.Carrier) (v w : TangentSpace ThreeModel x) :
    m.inner x v w = m'.inner (cast (congrArg OrientedThreeStage.Carrier h) x) v w := by
  subst h
  rw [eq_of_heq hm]
  rfl

/-- G5 consumer：`postMetric` 的 `inner` 等于 `stageMetric (activeStage t) t` 的 `inner`
（点沿 `postStage_eq_activeStage_ST` cast）。 -/
theorem postMetric_inner_eq_stageMetric_ST (O : ObservationTower P g) (n : ℕ)
    (t : Icc (0 : ℝ) (O.history n).horizon) (x : (postStage O t.1).Carrier)
    (v w : TangentSpace ThreeModel x) :
    (postMetric O t.1).inner x v w =
      ((O.history n).stageMetric ((O.history n).activeStage t) t.1).inner
        (cast (congrArg OrientedThreeStage.Carrier (postStage_eq_activeStage_ST O n t)) x) v w :=
  inner_eq_of_heq_ST (postStage_eq_activeStage_ST O n t) (postMetric_heq_stageMetric_ST O n t)
    x v w

end GC.LongTime

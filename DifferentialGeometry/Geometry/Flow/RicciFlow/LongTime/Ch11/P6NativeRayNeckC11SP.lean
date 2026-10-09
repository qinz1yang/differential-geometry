import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SliceSeeds_CX2

set_option autoImplicit false

/-!
# G1：slice ↔ tower traced-region 桥（O-CH11-NATIVE-RAYNECK，后缀 `_C11SP`）

G47 `native_chosen_neck_traced_of_chain_CXSP` 的 traced region 活在 `RegularSlice` 的
`s.history = (F.tower.history ⌈s.time⌉).restrict s.time` 上；hPlN′ 的 ray neck 子句要的是
tower 第 `idx'` 号 history 在 `t'` 处的 `isTracedRegion`。

* `SliceTowerTraceAt_C11SP F s k t`（**精确桥合同**）：`s.stage` = tower `k` 号在 `t` 的 stage，
  `s.metric` 与 tower metric HEq，且 slice 顶层 traced region（对所有 HEq 代表点）推出 tower 的
  traced region（同一 `ρ τ K`）。
* `sliceTowerTraceAt_ceil_C11SP`（PROVED）：`k = ⌈s.time⌉` 时桥成立（`slice_isTracedRegion_iff_CX2`
  的 restrict API + `activeStage_at_horizon`）。
* `k > ⌈s.time⌉` 的情形需要跨 `ObservedHistory.SamePresentation`
  （`ObservationTower.integer_restrict`）运输 `BackwardPointTrace`——**树内无此 API**
  （`L862TowerFamily_O28` docstring 已注），列为 API 缺口；本文件只登记合同形，不假装已证。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch11

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- **精确桥合同**（slice ↔ tower 第 `k` 号 history，时刻 `t = s.time`）。 -/
def SliceTowerTraceAt_C11SP (F : GC.Interface.RawSurgery P g)
    (s : RegularSlice F.observation) (k : ℕ)
    (t : Icc (0 : ℝ) (F.tower.history k).toHistory.horizon) : Prop :=
  s.stage = (F.tower.history k).toHistory.stageAt t ∧
    HEq s.metric ((F.tower.history k).toHistory.stageMetric
      ((F.tower.history k).toHistory.activeStage t) t) ∧
    ∀ (x : s.stage.Carrier) (y : ((F.tower.history k).toHistory.stageAt t).Carrier),
      HEq x y → ∀ ρ τ K : ℝ,
        (∀ xt : (s.history.stageAt ⟨s.time, s.positive.le, le_rfl⟩).Carrier, HEq xt x →
          s.history.isTracedRegion ⟨s.time, s.positive.le, le_rfl⟩ xt ρ τ K) →
        (F.tower.history k).toHistory.isTracedRegion t y ρ τ K

/-- slice 顶层的 active stage 是最后一个 stage。 -/
theorem slice_activeStage_top_C11SP {F : GC.Interface.RawSurgery P g}
    (s : RegularSlice F.observation) :
    s.history.activeStage ⟨s.time, s.positive.le, le_rfl⟩ = Fin.last s.history.eventCount :=
  s.history.activeStage_at_horizon

/-- slice 顶层 stage 与 `s.stage`。 -/
theorem slice_stageAt_top_C11SP {F : GC.Interface.RawSurgery P g}
    (s : RegularSlice F.observation) :
    s.history.stageAt ⟨s.time, s.positive.le, le_rfl⟩ = s.stage :=
  congrArg s.history.stage (slice_activeStage_top_C11SP s)

/-- slice 顶层 metric 与 `s.metric`。 -/
theorem slice_metric_top_heq_C11SP {F : GC.Interface.RawSurgery P g}
    (s : RegularSlice F.observation) :
    HEq (s.history.stageMetric (s.history.activeStage ⟨s.time, s.positive.le, le_rfl⟩) s.time)
      s.metric := by
  have h := slice_activeStage_top_C11SP s
  change HEq (s.history.stageMetric (s.history.activeStage ⟨s.time, s.positive.le, le_rfl⟩)
    s.time) (s.history.stageMetric (Fin.last s.history.eventCount) s.time)
  rw [h]

/-- **G1（PROVED）**：`k = ⌈s.time⌉` 时精确桥合同成立。 -/
theorem sliceTowerTraceAt_ceil_C11SP (F : GC.Interface.RawSurgery P g)
    (s : RegularSlice F.observation) (k : ℕ) (hk : k = Nat.ceil s.time)
    (t : Icc (0 : ℝ) (F.tower.history k).toHistory.horizon) (ht : (t : ℝ) = s.time) :
    SliceTowerTraceAt_C11SP F s k t := by
  subst hk
  let H : ObservedHistory.{u} := Ch12.sliceTowerHistory_CX2 s
  let cut := Ch12.sliceTowerTime_CX2 s
  let top : Icc (0 : ℝ) (H.restrict cut).horizon := ⟨s.time, s.positive.le, le_rfl⟩
  have htt : t = Ch12.restrictTime_CX2 H cut top := Subtype.ext ht
  subst htt
  have hZ1 : s.stage = (H.restrict cut).stageAt top := (slice_stageAt_top_C11SP s).symm
  have hZ2 : (H.restrict cut).stageAt top = H.stageAt (Ch12.restrictTime_CX2 H cut top) :=
    H.restrict_stageAt cut top
  refine ⟨hZ1.trans hZ2, ?_, ?_⟩
  · exact (slice_metric_top_heq_C11SP s).symm.trans (H.restrict_sliceMetric cut top)
  · intro x y hxy ρ τ K htr
    let xt : ((H.restrict cut).stageAt top).Carrier :=
      cast (congrArg OrientedThreeStage.Carrier hZ1) x
    have hxt : HEq xt x := cast_heq _ _
    have hs := htr xt hxt
    have hr := (Ch12.isTracedRegion_restrict_iff_CX2 H cut top xt ρ τ K).mp hs
    have hy : Ch12.restrictPoint_CX2 H cut top xt = y :=
      eq_of_heq ((Ch12.restrictPoint_heq_CX2 H cut top xt).trans (hxt.trans hxy))
    rw [hy] at hr
    exact hr

/-- consumer：合同在 `⌈s.time⌉` 号 tower history 上实际被 `sliceTowerTraceAt_ceil_C11SP` 支付，
并把 slice traced region 送到 tower。 -/
theorem tower_isTracedRegion_of_slice_ceil_C11SP (F : GC.Interface.RawSurgery P g)
    (s : RegularSlice F.observation)
    (t : Icc (0 : ℝ) (F.tower.history (Nat.ceil s.time)).toHistory.horizon)
    (ht : (t : ℝ) = s.time) (x : s.stage.Carrier)
    (y : ((F.tower.history (Nat.ceil s.time)).toHistory.stageAt t).Carrier) (hxy : HEq x y)
    {ρ τ K : ℝ}
    (htr : ∀ xt : (s.history.stageAt ⟨s.time, s.positive.le, le_rfl⟩).Carrier, HEq xt x →
      s.history.isTracedRegion ⟨s.time, s.positive.le, le_rfl⟩ xt ρ τ K) :
    (F.tower.history (Nat.ceil s.time)).toHistory.isTracedRegion t y ρ τ K :=
  (sliceTowerTraceAt_ceil_C11SP F s _ rfl t ht).2.2 x y hxy ρ τ K htr

end GC.LongTime.Ch11

end

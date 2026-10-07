import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialOwnThresholdDerivatives
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialChain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.RawSurgery.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.HistoryParabolicBallPrefixTransport

/-!
# S-CH11-FIX9 patched-at-path of astra `PreparedSpatialReserveTransport`

来源：donor `PreparedSpatialReserveTransport.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败（47 error）。除 (A) 外全是 elaboration 层面修补（no definition /
proof idea altered；不加 `set_option`）；下游 `PreparedSpatialUniformPinching` 等 import 本路径，
故 patched-at-path。

(A) **唯一的陈述级偏离**（private structure 的字段）：`ReserveShiftedTracePresentation.crossing_iff`
写作 `HEq p' p → HEq q' q → X ↔ Y`，Lean 优先级（`→` 25 > `↔` 20）把它解析成
`(HEq p' p → HEq q' q → X) ↔ Y`，这个命题对任意 `p q p' q'` 为假（`HEq` 不成立时左边空真而
`Y` 任意），donor 自己的构造（`crossing_iff i hp hq := hcross i _ _ _ _ hp hq`、
`hcross : ∀ … → HEq p' p → HEq q' q → (X ↔ Y)`）也按 `HEq → HEq → (X ↔ Y)` 用它 → 补括号
`HEq p' p → HEq q' q → (X ↔ Y)`。

(B) 其余修补（同族 `AffineHistoryParabolicBall` FIX6 G4 与 `PreparedSpatialOwnThresholdDerivatives`）：
* `shift_nonneg` 前 `include A in`（theorem 只纳入签名里提到的 variable，A/J/K 不进来，级联
  `shiftTime` / `stageAt_shift_eq` 等的 "no usable parameter"）；
* 3 处 `▸` 补类型 ascription（`traceEquiv`、`timeTraceEquiv` 的端点与 `transport_ball` 的 `he`）；
  `traceEquiv_point_heq` 的 `_ _` 显式给 `hf' hl'`；`timeTraceEquiv_controlled` 的
  `isRmControlled` 与 `timeTraceEquiv_point_heq` 显式 `(hat := hat)`；末尾 `simpa only [he]` →
  `clear_value v; subst he; exact hb`；
* `simpa only [stageIndex_succ] using X` / `(by simpa only [AffineEventPrefix.stageIndex_succ]
  using X)` → 直接 `X`（defeq）共 5 处；`pullTrace` 里多余的 `rw [← stageIndex_succ]` 去掉；
* `own_native_tail_clock_stage`：`R.history.time` 与 `R.history.toHistory.time` 不同 head → `change`；
  `let jR` 在 `refine` 后被展开 → `change … jR …`；`omega` 前 `simp only [Fin.val_last]`；
* `own_native_tail_trace_presentation`：同类 `Fin.val_last` / `.toHistory.time` 的 `change`；
  `add_le_add_right`（本树加项放左边）→ `add_le_add … le_rfl` / `add_lt_add_of_lt_of_le`；
  `rw [hindex]`（依赖类型的 motive 不良）→ `suffices hgen : ∀ e, e = … → …` + `subst`；
* `full_native_query_transport`：`let A … where …` → 结构体 `{ … }`；`simpa only [hT]` →
  `subst hT` 后直接项；
* `native_query_transport_to_observation`：`rw [hhistory] at h`（motive 不良）→ 一般引理 `gen`
  （对 `X` `subst`）；`rw [W.oldNative_horizon] at ht` → `ht.trans_eq W.oldNative_horizon`。
-/

set_option autoImplicit false
noncomputable section
open Set Filter DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal Topology
namespace GC.GeneralFlow
universe u

open private castPoint castPoint_heq normSq_eq_of_metric_heq ball_mem_iff_of_metric_heq
  trace_point_heq traceIndexEquiv traceIndexEquiv_point_heq controlled_of_regular
  crossing_iff_of_translated_event from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.AffineHistoryParabolicBall
open private event_samePresentation_of_prefix from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialStepDerivative
open private own_threshold_native_tail_stageMetric from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialOwnThresholdDerivatives
open private regularCrossing_iff_of_samePresentation_heq controlled_ball_iff_of_prefix from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.HistoryParabolicBallPrefixTransport

/-- Private exact presentation data used to push complete traces. It is produced
from the actual retained step below, never assumed by the public receiver. -/
private structure ReserveShiftedTracePresentation
    (K J : ObservedHistory.{u}) (c : ℝ) (offset : ℕ) where
  count_eq : J.eventCount = offset + K.eventCount
  time_eq : ∀ j : Fin (K.eventCount + 1),
    J.time ⟨offset + j.val, by have := j.isLt; omega⟩ = K.time j + c
  stage_eq : ∀ j : Fin (K.eventCount + 1),
    J.stage ⟨offset + j.val, by have := j.isLt; omega⟩ = K.stage j
  metric_heq : ∀ (j : Fin (K.eventCount + 1)) (s : ℝ), s ∈ K.stageDomain j →
    HEq (J.stageMetric ⟨offset + j.val, by have := j.isLt; omega⟩ (s + c))
      (K.stageMetric j s)
  crossing_iff : ∀ (i : Fin K.eventCount)
    {p : (K.stage i.castSucc).Carrier} {q : (K.stage i.succ).Carrier}
    {p' : (J.stage (⟨offset + i.val, by have := i.isLt; omega⟩ : Fin J.eventCount).castSucc).Carrier}
    {q' : (J.stage (⟨offset + i.val, by have := i.isLt; omega⟩ : Fin J.eventCount).succ).Carrier},
    HEq p' p → HEq q' q →
    ((J.event ⟨offset + i.val, by have := i.isLt; omega⟩).RegularCrossing p' q' ↔
      (K.event i).RegularCrossing p q)

namespace ReserveShiftedTracePresentation
variable {K J : ObservedHistory.{u}} {c : ℝ} {offset : ℕ}
  (A : ReserveShiftedTracePresentation K J c offset)

private def eventIndex (i : Fin K.eventCount) : Fin J.eventCount :=
  ⟨offset + i.val, by have := A.count_eq; have := i.isLt; omega⟩

/-- The actual stage of the joined history corresponding to a source stage. -/
private def stageIndex (j : Fin (K.eventCount + 1)) : Fin (J.eventCount + 1) :=
  ⟨offset + j.val, by have := A.count_eq; omega⟩

@[simp] private theorem stageIndex_val (j : Fin (K.eventCount + 1)) :
    (A.stageIndex j).val = offset + j.val := rfl

private theorem stageIndex_le_iff (j k : Fin (K.eventCount + 1)) :
    A.stageIndex j ≤ A.stageIndex k ↔ j ≤ k := by
  change offset + j.val ≤ offset + k.val ↔ j.val ≤ k.val
  omega

@[simp] private theorem stageIndex_castSucc (i : Fin K.eventCount) :
    A.stageIndex i.castSucc = (A.eventIndex i).castSucc := rfl

@[simp] private theorem stageIndex_succ (i : Fin K.eventCount) :
    A.stageIndex i.succ = (A.eventIndex i).succ := by
  apply Fin.ext
  change offset + (i.val + 1) = offset + i.val + 1
  omega

@[simp] private theorem stageIndex_last :
    A.stageIndex (Fin.last K.eventCount) = Fin.last J.eventCount := by
  apply Fin.ext
  exact A.count_eq.symm

private theorem stageIndex_time (j : Fin (K.eventCount + 1)) :
    J.time (A.stageIndex j) = K.time j + c := A.time_eq j

private theorem stageIndex_stage (j : Fin (K.eventCount + 1)) :
    J.stage (A.stageIndex j) = K.stage j := A.stage_eq j

include A in
private theorem shift_nonneg : 0 ≤ c := by
  have h := J.time_nonneg (A.stageIndex 0)
  rw [A.stageIndex_time, K.time_zero, zero_add] at h
  exact h

/-- Affine translation of a source observation time in the actual joined history. -/
private def shiftTime (hhor : J.horizon = K.horizon + c)
    (t : Icc (0 : ℝ) K.horizon) : Icc (0 : ℝ) J.horizon :=
  ⟨(t : ℝ) + c, add_nonneg t.property.1 A.shift_nonneg, by
    rw [hhor]
    exact add_le_add t.property.2 (le_refl c)⟩

@[simp] private theorem shiftTime_val (hhor : J.horizon = K.horizon + c)
    (t : Icc (0 : ℝ) K.horizon) : (A.shiftTime hhor t : ℝ) = (t : ℝ) + c := rfl

private theorem shiftTime_le_iff (hhor : J.horizon = K.horizon + c)
    (s t : Icc (0 : ℝ) K.horizon) : A.shiftTime hhor s ≤ A.shiftTime hhor t ↔ s ≤ t := by
  change (s : ℝ) + c ≤ (t : ℝ) + c ↔ (s : ℝ) ≤ (t : ℝ)
  constructor <;> intro h <;> linarith

private theorem activeStage_shift_eq (hhor : J.horizon = K.horizon + c)
    (t : Icc (0 : ℝ) K.horizon) :
    J.activeStage (A.shiftTime hhor t) = A.stageIndex (K.activeStage t) := by
  apply J.activeStage_eq_of_maximal
  · rw [A.stageIndex_time]
    exact add_le_add (K.activeStage_time_le t) (le_refl c)
  · intro j hj
    by_cases ho : j.val < offset
    · change j.val ≤ offset + (K.activeStage t).val
      omega
    · let k : Fin (K.eventCount + 1) :=
        ⟨j.val - offset, by have := j.isLt; have := A.count_eq; omega⟩
      have he : A.stageIndex k = j := by
        apply Fin.ext
        change offset + (j.val - offset) = j.val
        omega
      have ht : K.time k ≤ (t : ℝ) := by
        rw [← he, A.stageIndex_time] at hj
        change K.time k + c ≤ (t : ℝ) + c at hj
        linarith
      rw [← he]
      exact (A.stageIndex_le_iff _ _).mpr (K.le_activeStage t k ht)

private theorem stageAt_shift_eq (hhor : J.horizon = K.horizon + c)
    (t : Icc (0 : ℝ) K.horizon) :
    J.stageAt (A.shiftTime hhor t) = K.stageAt t := by
  change J.stage (J.activeStage (A.shiftTime hhor t)) =
    K.stage (K.activeStage t)
  rw [A.activeStage_shift_eq]
  exact A.stageIndex_stage _

private theorem sliceMetric_shift_heq (hhor : J.horizon = K.horizon + c)
    (t : Icc (0 : ℝ) K.horizon) :
    HEq (J.stageMetric (J.activeStage (A.shiftTime hhor t)) (A.shiftTime hhor t))
      (K.stageMetric (K.activeStage t) t) := by
  rw [A.activeStage_shift_eq]
  exact A.metric_heq (K.activeStage t) t (K.activeStage_mem t)

private def sourceStage (j : Fin (J.eventCount + 1)) :
    Fin (K.eventCount + 1) :=
  ⟨j.val - offset, by have := j.isLt; have := A.count_eq; omega⟩

private theorem stageIndex_sourceStage (j : Fin (J.eventCount + 1)) (hj : offset ≤ j.val) :
    A.stageIndex (A.sourceStage j) = j := by
  apply Fin.ext
  change offset + (j.val - offset) = j.val
  omega

private theorem sourceStage_stageIndex (j : Fin (K.eventCount + 1)) :
    A.sourceStage (A.stageIndex j) = j := by
  apply Fin.ext
  change offset + j.val - offset = j.val
  omega

private def pushTracePoint {first last : Fin (K.eventCount + 1)} {hle : first ≤ last}
    {p : (K.stage last).Carrier} (B : BackwardPointTrace K first last hle p)
    (j : Fin (J.eventCount + 1)) (hf : A.stageIndex first ≤ j) (hl : j ≤ A.stageIndex last) :
    (J.stage j).Carrier := by
  have ho : offset ≤ j.val := by change offset + first.val ≤ j.val at hf; omega
  have hfirst : first ≤ A.sourceStage j := by
    change first.val ≤ j.val - offset
    change offset + first.val ≤ j.val at hf
    omega
  have hlast : A.sourceStage j ≤ last := by
    change j.val - offset ≤ last.val
    change j.val ≤ offset + last.val at hl
    omega
  exact castPoint
    ((congrArg J.stage (A.stageIndex_sourceStage j ho)).symm.trans
      (A.stageIndex_stage (A.sourceStage j))).symm
    (B.point (A.sourceStage j) hfirst hlast)

private theorem pushTracePoint_heq {first last : Fin (K.eventCount + 1)} {hle : first ≤ last}
    {p : (K.stage last).Carrier} (B : BackwardPointTrace K first last hle p)
    (j : Fin (K.eventCount + 1)) (hf : first ≤ j) (hl : j ≤ last)
    (hf' : A.stageIndex first ≤ A.stageIndex j) (hl' : A.stageIndex j ≤ A.stageIndex last) :
    HEq (A.pushTracePoint B (A.stageIndex j) hf' hl') (B.point j hf hl) := by
  unfold pushTracePoint
  exact (castPoint_heq _ _).trans
    (trace_point_heq B (A.sourceStage_stageIndex j) _ _ hf hl)

private def pushTrace {first last : Fin (K.eventCount + 1)} (hle : first ≤ last)
    {p : (K.stage last).Carrier} (B : BackwardPointTrace K first last hle p) :
    BackwardPointTrace J (A.stageIndex first) (A.stageIndex last)
      ((A.stageIndex_le_iff first last).mpr hle) (castPoint (A.stageIndex_stage last).symm p) where
  point := A.pushTracePoint B
  endpoint_eq := by
    apply eq_of_heq
    exact (A.pushTracePoint_heq B last hle le_rfl _ _).trans
      ((heq_of_eq B.endpoint_eq).trans (castPoint_heq _ _).symm)
  crossing i hf hl := by
    have ho : offset ≤ i.val := by change offset + first.val ≤ i.val at hf; omega
    obtain ⟨k, rfl⟩ : ∃ k : Fin K.eventCount, A.eventIndex k = i := by
      refine ⟨⟨i.val - offset, by have := i.isLt; have := A.count_eq; omega⟩, ?_⟩
      apply Fin.ext
      change offset + (i.val - offset) = i.val
      omega
    have hkf : first ≤ k.castSucc := by
      change offset + first.val ≤ offset + k.val at hf
      change first.val ≤ k.val
      omega
    have hkl : k.succ ≤ last := by
      change offset + k.val + 1 ≤ offset + last.val at hl
      change k.val + 1 ≤ last.val
      omega
    apply (A.crossing_iff k ?_ ?_).mpr (B.crossing k hkf hkl)
    · exact A.pushTracePoint_heq B k.castSucc hkf (k.castSucc_lt_succ.le.trans hkl) _ _
    · exact A.pushTracePoint_heq B k.succ (hkf.trans k.castSucc_lt_succ.le) hkl _ _

private def pullTrace {first last : Fin (K.eventCount + 1)} (hle : first ≤ last)
    {p : (K.stage last).Carrier}
    (B : BackwardPointTrace J (A.stageIndex first) (A.stageIndex last)
      ((A.stageIndex_le_iff first last).mpr hle) (castPoint (A.stageIndex_stage last).symm p)) :
    BackwardPointTrace K first last hle p where
  point j hf hl := castPoint (A.stageIndex_stage j)
    (B.point (A.stageIndex j) ((A.stageIndex_le_iff _ _).mpr hf) ((A.stageIndex_le_iff _ _).mpr hl))
  endpoint_eq := by
    apply eq_of_heq
    exact (castPoint_heq _ _).trans
      ((heq_of_eq B.endpoint_eq).trans (castPoint_heq _ _))
  crossing i hf hl := by
    have hf' : A.stageIndex first ≤ (A.eventIndex i).castSucc :=
      (A.stageIndex_le_iff _ _).mpr hf
    have hl' : (A.eventIndex i).succ ≤ A.stageIndex last := by
      rw [← A.stageIndex_succ]
      exact (A.stageIndex_le_iff _ _).mpr hl
    apply (A.crossing_iff i ?_ ?_).mp (B.crossing (A.eventIndex i) hf' hl')
    · exact (castPoint_heq _ _).symm
    · exact (castPoint_heq _ _).symm

/-- Backward traces in the source and in its translated tail have exactly the
same points and retained crossings. No trace can acquire a stage before the join. -/
private def traceEquiv (first last : Fin (K.eventCount + 1)) (hle : first ≤ last)
    (p : (K.stage last).Carrier) :
    BackwardPointTrace K first last hle p ≃
      BackwardPointTrace J (A.stageIndex first) (A.stageIndex last)
        ((A.stageIndex_le_iff first last).mpr hle)
      ((A.stageIndex_stage last).symm ▸ p : (J.stage (A.stageIndex last)).Carrier) where
  toFun := A.pushTrace hle
  invFun := A.pullTrace hle
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

private theorem traceEquiv_point_heq {first last : Fin (K.eventCount + 1)} {hle : first ≤ last}
    {p : (K.stage last).Carrier} (B : BackwardPointTrace K first last hle p)
    (j : Fin (K.eventCount + 1)) (hf : first ≤ j) (hl : j ≤ last) :
    HEq ((A.traceEquiv first last hle p B).point (A.stageIndex j)
      ((A.stageIndex_le_iff _ _).mpr hf) ((A.stageIndex_le_iff _ _).mpr hl))
      (B.point j hf hl) :=
  A.pushTracePoint_heq B j hf hl ((A.stageIndex_le_iff first j).mpr hf)
    ((A.stageIndex_le_iff j last).mpr hl)

private theorem traceEquiv_symm_point_heq {first last : Fin (K.eventCount + 1)} {hle : first ≤ last}
    {p : (K.stage last).Carrier}
    (B : BackwardPointTrace J (A.stageIndex first) (A.stageIndex last)
      ((A.stageIndex_le_iff first last).mpr hle) ((A.stageIndex_stage last).symm ▸ p))
    (j : Fin (K.eventCount + 1)) (hf : first ≤ j) (hl : j ≤ last) :
    HEq (((A.traceEquiv first last hle p).symm B).point j hf hl)
      (B.point (A.stageIndex j) ((A.stageIndex_le_iff _ _).mpr hf)
        ((A.stageIndex_le_iff _ _).mpr hl)) := castPoint_heq _ _

private def timeTraceEquiv (hhor : J.horizon = K.horizon + c)
    (a t : Icc (0 : ℝ) K.horizon) (hat : a ≤ t) (p : (K.stageAt t).Carrier) :
    BackwardPointTrace K (K.activeStage a) (K.activeStage t)
      (K.activeStage_mono hat) p ≃
    BackwardPointTrace J (J.activeStage (A.shiftTime hhor a))
      (J.activeStage (A.shiftTime hhor t))
      (J.activeStage_mono ((A.shiftTime_le_iff hhor a t).mpr hat))
      ((A.stageAt_shift_eq hhor t).symm ▸ p : (J.stageAt (A.shiftTime hhor t)).Carrier) :=
  (A.traceEquiv _ _ (K.activeStage_mono hat) p).trans
    (traceIndexEquiv (A.activeStage_shift_eq hhor a) (A.activeStage_shift_eq hhor t) _ _ _ _
      ((castPoint_heq (A.stageAt_shift_eq hhor t).symm p).trans
        (castPoint_heq (A.stageIndex_stage (K.activeStage t)).symm p).symm))

private theorem timeTraceEquiv_point_heq (hhor : J.horizon = K.horizon + c)
    {a t : Icc (0 : ℝ) K.horizon} {hat : a ≤ t} {p : (K.stageAt t).Carrier}
    (B : BackwardPointTrace K (K.activeStage a) (K.activeStage t)
      (K.activeStage_mono hat) p)
    (s : Icc (0 : ℝ) K.horizon) (has : a ≤ s) (hst : s ≤ t) :
    HEq ((A.timeTraceEquiv hhor a t hat p B).point
      (J.activeStage (A.shiftTime hhor s))
      (J.activeStage_mono ((A.shiftTime_le_iff hhor a s).mpr has))
      (J.activeStage_mono ((A.shiftTime_le_iff hhor s t).mpr hst)))
      (B.point (K.activeStage s)
        (K.activeStage_mono has) (K.activeStage_mono hst)) := by
  unfold timeTraceEquiv
  exact (traceIndexEquiv_point_heq _ _ _ _ _ _ _ _ (A.activeStage_shift_eq hhor s) _ _ _ _).trans
    (A.traceEquiv_point_heq B _ _ _)

private theorem timeTraceEquiv_controlled (hhor : J.horizon = K.horizon + c)
    {a t : Icc (0 : ℝ) K.horizon} {hat : a ≤ t} {p : (K.stageAt t).Carrier}
    (B : BackwardPointTrace K (K.activeStage a) (K.activeStage t)
      (K.activeStage_mono hat) p) (r : ℝ) (hB : B.isRmControlled (hat := hat) r) :
    (A.timeTraceEquiv hhor a t hat p B).isRmControlled
      (hat := (A.shiftTime_le_iff hhor a t).mpr hat) r := by
  apply controlled_of_regular _ r
  intro s has hst
  let v : Icc (0 : ℝ) K.horizon := ⟨(s : ℝ) - c, by
    have ha0 := a.property.1
    change (a : ℝ) + c ≤ (s : ℝ) at has
    linarith, by
    have htK := t.property.2
    change (s : ℝ) ≤ (t : ℝ) + c at hst
    linarith⟩
  have he : A.shiftTime hhor v = s := by apply Subtype.ext; dsimp [shiftTime, v]; ring
  have hav : a ≤ v := by
    change (a : ℝ) ≤ (s : ℝ) - c
    change (a : ℝ) + c ≤ (s : ℝ) at has
    linarith
  have hvt : v ≤ t := by
    change (s : ℝ) - c ≤ (t : ℝ)
    change (s : ℝ) ≤ (t : ℝ) + c at hst
    linarith
  have hn := normSq_eq_of_metric_heq (A.stageAt_shift_eq hhor v)
    (A.sliceMetric_shift_heq hhor v) (A.timeTraceEquiv_point_heq (hat := hat) hhor B v hav hvt)
  have hb := hB.1 v hav hvt
  rw [← hn] at hb
  clear_value v
  subst he
  exact hb

private theorem transport_ball (hhor : J.horizon = K.horizon + c)
    (t : Icc (0 : ℝ) K.horizon) (p : (K.stageAt t).Carrier) (r : ℝ)
    (hball : K.isParabolicallyRmControlledBall t p r) :
    J.isParabolicallyRmControlledBall (A.shiftTime hhor t)
      ((A.stageAt_shift_eq hhor t).symm ▸ p) r := by
  obtain ⟨hr, a, hat, ha, htraces⟩ := hball
  have hat' := (A.shiftTime_le_iff hhor a t).mpr hat
  refine ⟨hr, A.shiftTime hhor a, hat', ?_, ?_⟩
  · change (a : ℝ) + c = ((t : ℝ) + c) - r ^ 2
    linarith
  · intro y hy
    let x : (K.stageAt t).Carrier := castPoint (A.stageAt_shift_eq hhor t) y
    have hx : x ∈ riemannianBallOf (K.stageMetric (K.activeStage t) t) p r :=
      (ball_mem_iff_of_metric_heq (A.stageAt_shift_eq hhor t)
        (A.sliceMetric_shift_heq hhor t) (castPoint_heq _ y).symm
        (castPoint_heq _ p) r).mp hy
    obtain ⟨B, hB⟩ := htraces x hx
    have he : ((A.stageAt_shift_eq hhor t).symm ▸ x :
        (J.stageAt (A.shiftTime hhor t)).Carrier) = y :=
      eq_of_heq ((castPoint_heq _ x).trans (castPoint_heq _ y))
    exact he ▸ ⟨A.timeTraceEquiv hhor a t hat x B,
      A.timeTraceEquiv_controlled hhor B r hB⟩

end ReserveShiftedTracePresentation

private theorem regularCrossing_iff_of_retained_event_heq
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    {E : RetainedCoreEvent P Q a s} {F : RetainedCoreEvent P' Q' a' s'}
    (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s') (hE : HEq E F)
    {p : P.Carrier} {q : Q.Carrier} {p' : P'.Carrier} {q' : Q'.Carrier}
    (hp : HEq p p') (hq : HEq q q') :
    E.toMetricCutCapEvent.RegularCrossing p q ↔ F.toMetricCutCapEvent.RegularCrossing p' q' := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  cases eq_of_heq hp
  cases eq_of_heq hq
  rfl

private theorem own_native_tail_clock_stage
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {E B Bnext activation eta d εcut Dcut : ℝ} {mcut : ℕ}
    {L : PreparedSpatialState pBase C P g E B}
    {R : PreparedSpatialState pBase C P g B Bnext}
    (W : PreparedSpatialStepRetention L R d eta εcut Dcut mcut)
    (hLR : PreparedSpatialSuccessor L R activation eta d)
    (hshift : R.shift = L.history.time (Fin.last L.history.eventCount))
    (hoffset : R.offset = L.history.eventCount)
    (hcount : R.history.eventCount = L.offset + W.oldNative.eventCount)
    (j : Fin (W.oldNative.eventCount + 1)) :
    let jR : Fin (R.history.eventCount + 1) :=
      ⟨L.offset + j.val, by have := j.isLt; omega⟩
    R.history.time jR = W.oldNative.time j + L.shift ∧
      R.history.stage jR = W.oldNative.stage j := by
  let jR : Fin (R.history.eventCount + 1) :=
    ⟨L.offset + j.val, by have := j.isLt; omega⟩
  by_cases hold : j.val < L.native.eventCount
  · let i : Fin L.native.eventCount := ⟨j.val, hold⟩
    let iOld := L.affine.eventIndex i
    let iFull := iOld.castLE hLR.count_le
    let iK := i.castLE W.oldNativeRawPrefix.count_le
    have hj : j = iK.castSucc := Fin.ext rfl
    have hjR : jR = iFull.castSucc := Fin.ext rfl
    have hPresent := event_samePresentation_of_prefix hLR.initial_prefix.1 hLR.count_le iOld
    have hAffStage := L.affine.stageIndex_stage i.castSucc
    rw [AffineEventPrefix.stageIndex_castSucc] at hAffStage
    have hRawStage := W.oldNativeRawPrefix.stage_eq i.castSucc
    change W.oldNative.stage iK.castSucc = L.native.stage i.castSucc at hRawStage
    have hStage : R.history.stage jR = W.oldNative.stage j := by
      rw [hjR, hj]
      exact hPresent.incomingStage_eq.trans (hAffStage.trans hRawStage.symm)
    refine ⟨?_, hStage⟩
    have hAff := L.affine.stageIndex_time i.castSucc
    rw [AffineEventPrefix.stageIndex_castSucc] at hAff
    have hRaw := W.oldNativeRawPrefix.time_eq i.castSucc
    change W.oldNative.time iK.castSucc = L.native.time i.castSucc at hRaw
    change R.history.time jR = W.oldNative.time j + L.shift
    rw [hjR]
    change R.history.toHistory.time iFull.castSucc = W.oldNative.time j + L.shift
    rw [hj, hPresent.leftTime_eq]
    change L.history.time iOld.castSucc = W.oldNative.time iK.castSucc + L.shift
    rw [hAff, ← hRaw]
  · let k : Fin (R.native.eventCount + 1) :=
      ⟨j.val - L.native.eventCount, by
        have := W.oldNativeAffine.count_eq
        have := j.isLt
        omega⟩
    have hk : W.oldNativeAffine.stageIndex k = j := by
      apply Fin.ext
      change L.native.eventCount + (j.val - L.native.eventCount) = j.val
      omega
    have hkR : R.affine.stageIndex k = jR := by
      apply Fin.ext
      change R.offset + (j.val - L.native.eventCount) = L.offset + j.val
      rw [hoffset]
      have := L.affine.count_eq
      simp only [Fin.val_last] at this
      omega
    have hba : R.shift = L.native.time (Fin.last L.native.eventCount) + L.shift := by
      rw [hshift]
      have h := L.affine.stageIndex_time (Fin.last L.native.eventCount)
      rw [L.affine.stageIndex_last] at h
      exact h
    refine ⟨?_, ?_⟩
    · change R.history.time jR = W.oldNative.time j + L.shift
      rw [← hkR, ← hk, R.affine.stageIndex_time, W.oldNativeAffine.stageIndex_time, hba]
      ring
    · change R.history.stage jR = W.oldNative.stage j
      rw [← hkR, ← hk]
      exact (R.affine.stageIndex_stage k).trans (W.oldNativeAffine.stageIndex_stage k).symm

private theorem own_native_tail_trace_presentation
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {E B Bnext activation eta d εcut Dcut : ℝ} {mcut : ℕ}
    {L : PreparedSpatialState pBase C P g E B}
    {R : PreparedSpatialState pBase C P g B Bnext}
    (W : PreparedSpatialStepRetention L R d eta εcut Dcut mcut)
    (hLR : PreparedSpatialSuccessor L R activation eta d)
    (hshift : R.shift = L.history.time (Fin.last L.history.eventCount))
    (hoffset : R.offset = L.history.eventCount)
    : let K := W.oldNative
      ∃ hcount : R.history.eventCount = L.offset + K.eventCount,
        let liftStage : Fin (K.eventCount + 1) → Fin (R.history.eventCount + 1) :=
          fun j => ⟨L.offset + j.val, by have hj := j.isLt; omega⟩
        let liftEvent : Fin K.eventCount → Fin R.history.eventCount :=
          fun i => ⟨L.offset + i.val, by have hi := i.isLt; omega⟩
        (∀ j : Fin (K.eventCount + 1),
          R.history.time (liftStage j) = K.time j + L.shift ∧
          R.history.stage (liftStage j) = K.stage j ∧
          ∀ s : ℝ, s ∈ K.toHistory.stageDomain j →
            HEq (R.history.toHistory.stageMetric (liftStage j) (s + L.shift))
              (K.toHistory.stageMetric j s)) ∧
        ∀ (i : Fin K.eventCount)
          (p : (K.stage i.castSucc).Carrier) (q : (K.stage i.succ).Carrier)
          (p' : (R.history.stage (liftEvent i).castSucc).Carrier)
          (q' : (R.history.stage (liftEvent i).succ).Carrier),
          HEq p' p → HEq q' q →
          ((R.history.toHistory.event (liftEvent i)).RegularCrossing p' q' ↔
            (K.toHistory.event i).RegularCrossing p q) := by
  have hcount : R.history.eventCount = L.offset + W.oldNative.eventCount := by
    have hR := R.affine.count_eq
    have hL := L.affine.count_eq
    have hK := W.oldNativeAffine.count_eq
    rw [hoffset] at hR
    simp only [Fin.val_last] at hR hL hK
    omega
  let liftStage : Fin (W.oldNative.eventCount + 1) → Fin (R.history.eventCount + 1) :=
    fun j => ⟨L.offset + j.val, by have := j.isLt; omega⟩
  let liftEvent : Fin W.oldNative.eventCount → Fin R.history.eventCount :=
    fun i => ⟨L.offset + i.val, by have := i.isLt; omega⟩
  have hStageTime (j : Fin (W.oldNative.eventCount + 1)) :
      R.history.time (liftStage j) = W.oldNative.time j + L.shift ∧
      R.history.stage (liftStage j) = W.oldNative.stage j :=
    own_native_tail_clock_stage W hLR hshift hoffset hcount j
  have hba : R.shift = L.native.time (Fin.last L.native.eventCount) + L.shift := by
    rw [hshift]
    have h := L.affine.stageIndex_time (Fin.last L.native.eventCount)
    rw [L.affine.stageIndex_last] at h
    exact h
  refine ⟨hcount, ?_, ?_⟩
  · intro j
    refine ⟨(hStageTime j).1, (hStageTime j).2, ?_⟩
    intro s hs
    cases j using Fin.lastCases with
    | last =>
      have hj : liftStage (Fin.last W.oldNative.eventCount) = Fin.last R.history.eventCount :=
        Fin.ext hcount.symm
      have hR := R.finalMetric_heq (s - L.native.time (Fin.last L.native.eventCount))
      have hK := W.oldNative_finalMetric (s - L.native.time (Fin.last L.native.eventCount))
      have hclock : s - L.native.time (Fin.last L.native.eventCount) + R.shift =
          s + L.shift := by rw [hba]; ring
      rw [hclock] at hR
      rw [sub_add_cancel] at hK
      change HEq (R.history.toHistory.stageMetric (liftStage (Fin.last W.oldNative.eventCount))
        (s + L.shift)) (W.oldNative.toHistory.stageMetric (Fin.last W.oldNative.eventCount) s)
      rw [hj]
      exact hR.trans hK.symm
    | cast i =>
      have hj : liftStage i.castSucc = (liftEvent i).castSucc := rfl
      have hsucc : liftStage i.succ = (liftEvent i).succ := Fin.ext rfl
      have hdom : s + L.shift ∈ Ico (R.history.time (liftStage i.castSucc))
          (R.history.toHistory.stageEndTime (liftStage i.castSucc)) := by
        simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc, Set.mem_Ico] at hs
        rw [hj, R.history.toHistory.stageEndTime_castSucc, ← hsucc]
        rw [← hj, (hStageTime i.castSucc).1]
        change s + L.shift ∈ Ico (W.oldNative.time i.castSucc + L.shift)
          (R.history.time (liftStage i.succ))
        rw [(hStageTime i.succ).1]
        exact ⟨add_le_add hs.1 le_rfl, add_lt_add_of_lt_of_le hs.2 le_rfl⟩
      obtain ⟨k, _, htime, _, hmetric⟩ := own_threshold_native_tail_stageMetric
        W hLR hshift hoffset (liftStage i.castSucc) (by change L.offset ≤ L.offset + i.val; omega)
      have hk : k = i.castSucc := W.oldNative.time_strictMono.injective (by
        have ht := (hStageTime i.castSucc).1
        linarith)
      subst k
      simpa only [add_sub_cancel_right] using hmetric (s + L.shift) hdom
  · intro i
    by_cases hold : i.val < L.native.eventCount
    · obtain ⟨k, rfl⟩ : ∃ k : Fin L.native.eventCount,
          k.castLE W.oldNativeRawPrefix.count_le = i :=
        ⟨⟨i.val, hold⟩, Fin.ext rfl⟩
      let iOld := L.affine.eventIndex k
      let iFull := iOld.castLE hLR.count_le
      have hindex : liftEvent (k.castLE W.oldNativeRawPrefix.count_le) = iFull := Fin.ext rfl
      suffices hgen : ∀ e : Fin R.history.eventCount, e = iFull →
          ∀ (p : (W.oldNative.stage (k.castLE W.oldNativeRawPrefix.count_le).castSucc).Carrier)
            (q : (W.oldNative.stage (k.castLE W.oldNativeRawPrefix.count_le).succ).Carrier)
            (p' : (R.history.stage e.castSucc).Carrier)
            (q' : (R.history.stage e.succ).Carrier), HEq p' p → HEq q' q →
            ((R.history.toHistory.event e).RegularCrossing p' q' ↔
              (W.oldNative.toHistory.event
                (k.castLE W.oldNativeRawPrefix.count_le)).RegularCrossing p q) by
        exact hgen _ hindex
      intro e he p q p' q' hp hq
      subst he
      have hP := W.oldNativeRawPrefix.stage_eq k.castSucc
      have hQ := W.oldNativeRawPrefix.stage_eq k.succ
      let pN := castPoint hP p
      let qN := castPoint hQ q
      have hpN : HEq pN p := castPoint_heq hP p
      have hqN : HEq qN q := castPoint_heq hQ q
      have hAP := L.affine.stageIndex_stage k.castSucc
      have hAQ := L.affine.stageIndex_stage k.succ
      rw [AffineEventPrefix.stageIndex_castSucc] at hAP
      rw [AffineEventPrefix.stageIndex_succ] at hAQ
      let pL := castPoint hAP.symm pN
      let qL := castPoint hAQ.symm qN
      have hpL : HEq pL pN := castPoint_heq hAP.symm pN
      have hqL : HEq qL qN := castPoint_heq hAQ.symm qN
      have hPresent := event_samePresentation_of_prefix hLR.initial_prefix.1 hLR.count_le iOld
      have hFirst := regularCrossing_iff_of_samePresentation_heq hPresent
        (hp.trans (hpL.trans hpN).symm) (hq.trans (hqL.trans hqN).symm)
      have hSecond := crossing_iff_of_translated_event (L.native.coreEvent k) L.shift
        hAP hAQ (L.affine.stageIndex_time k.castSucc)
        (L.affine.stageIndex_time k.succ)
        (L.affine.event_heq k) hpL hqL
      have hThird := regularCrossing_iff_of_retained_event_heq hP hQ
        (W.oldNativeRawPrefix.time_eq k.castSucc) (W.oldNativeRawPrefix.time_eq k.succ)
        (W.oldNativeRawPrefix.event_heq k) hpN.symm hqN.symm
      exact hFirst.trans (hSecond.trans hThird.symm)
    · obtain ⟨k, rfl⟩ : ∃ k : Fin R.native.eventCount, W.oldNativeAffine.eventIndex k = i := by
        refine ⟨⟨i.val - L.native.eventCount, by
          have := W.oldNativeAffine.count_eq
          have := i.isLt
          omega⟩, ?_⟩
        apply Fin.ext
        change L.native.eventCount + (i.val - L.native.eventCount) = i.val
        omega
      have hindex : liftEvent (W.oldNativeAffine.eventIndex k) = R.affine.eventIndex k := by
        apply Fin.ext
        change L.offset + (L.native.eventCount + k.val) = R.offset + k.val
        rw [hoffset]
        have := L.affine.count_eq
        simp only [Fin.val_last] at this
        omega
      suffices hgen : ∀ e : Fin R.history.eventCount, e = R.affine.eventIndex k →
          ∀ (p : (W.oldNative.stage (W.oldNativeAffine.eventIndex k).castSucc).Carrier)
            (q : (W.oldNative.stage (W.oldNativeAffine.eventIndex k).succ).Carrier)
            (p' : (R.history.stage e.castSucc).Carrier)
            (q' : (R.history.stage e.succ).Carrier), HEq p' p → HEq q' q →
            ((R.history.toHistory.event e).RegularCrossing p' q' ↔
              (W.oldNative.toHistory.event (W.oldNativeAffine.eventIndex k)).RegularCrossing p q) by
        exact hgen _ hindex
      intro e he p q p' q' hp hq
      subst he
      have hP := W.oldNativeAffine.stageIndex_stage k.castSucc
      have hQ := W.oldNativeAffine.stageIndex_stage k.succ
      rw [AffineEventPrefix.stageIndex_castSucc] at hP
      rw [AffineEventPrefix.stageIndex_succ] at hQ
      let pN := castPoint hP p
      let qN := castPoint hQ q
      have hpN : HEq pN p := castPoint_heq hP p
      have hqN : HEq qN q := castPoint_heq hQ q
      have hOld := crossing_iff_of_translated_event (R.native.coreEvent k)
        (L.native.time (Fin.last L.native.eventCount)) hP hQ
        (W.oldNativeAffine.stageIndex_time k.castSucc)
        (W.oldNativeAffine.stageIndex_time k.succ)
        (W.oldNativeAffine.event_heq k) hpN.symm hqN.symm
      have hNew := crossing_iff_of_translated_event (R.native.coreEvent k) R.shift
        (R.affine.stageIndex_stage k.castSucc)
        (R.affine.stageIndex_stage k.succ)
        (R.affine.stageIndex_time k.castSucc)
        (R.affine.stageIndex_time k.succ)
        (R.affine.event_heq k) (hp.trans hpN.symm) (hq.trans hqN.symm)
      exact hNew.trans hOld.symm

/-- Translate the actual retained native tail, including every backward trace and terminal bound. -/
theorem PreparedSpatialStepRetention.full_native_query_transport
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {E B Bnext activation eta d εcut Dcut : ℝ} {mcut : ℕ}
    {L : PreparedSpatialState pBase C P g E B}
    {R : PreparedSpatialState pBase C P g B Bnext}
    (W : PreparedSpatialStepRetention L R d eta εcut Dcut mcut)
    (hLR : PreparedSpatialSuccessor L R activation eta d)
    (hshift : R.shift = L.history.time (Fin.last L.history.eventCount))
    (hoffset : R.offset = L.history.eventCount)
    (τ : Icc (0 : ℝ) W.oldNative.horizon)
    (T : Icc (0 : ℝ) R.history.horizon) (hclock : (T : ℝ) = (τ : ℝ) + L.shift) :
    R.history.toHistory.stageAt T = W.oldNative.toHistory.stageAt τ ∧
    HEq (R.history.toHistory.stageMetric (R.history.toHistory.activeStage T) T)
      (W.oldNative.toHistory.stageMetric (W.oldNative.toHistory.activeStage τ) τ) ∧
    ∀ (x : (R.history.toHistory.stageAt T).Carrier)
      (y : (W.oldNative.toHistory.stageAt τ).Carrier), HEq x y →
      ∀ r : ℝ, W.oldNative.toHistory.isParabolicallyRmControlledBall τ y r →
        R.history.toHistory.isParabolicallyRmControlledBall T x r := by
  obtain ⟨hcount, hdata, hcross⟩ := own_native_tail_trace_presentation W hLR hshift hoffset
  let A : ReserveShiftedTracePresentation W.oldNative.toHistory R.history.toHistory
      L.shift L.offset :=
    { count_eq := hcount
      time_eq := fun j => (hdata j).1
      stage_eq := fun j => (hdata j).2.1
      metric_heq := fun j s hs => (hdata j).2.2 s hs
      crossing_iff := fun i _ _ _ _ hp hq => hcross i _ _ _ _ hp hq }
  have hhor : R.history.horizon = W.oldNative.horizon + L.shift := by
    rw [R.horizon_eq, W.oldNative_horizon]
    ring
  have hT : A.shiftTime hhor τ = T := Subtype.ext hclock.symm
  subst hT
  have hstage : R.history.toHistory.stageAt (A.shiftTime hhor τ) =
      W.oldNative.toHistory.stageAt τ := A.stageAt_shift_eq hhor τ
  have hmetric : HEq
      (R.history.toHistory.stageMetric
        (R.history.toHistory.activeStage (A.shiftTime hhor τ)) (A.shiftTime hhor τ))
      (W.oldNative.toHistory.stageMetric (W.oldNative.toHistory.activeStage τ) τ) :=
    A.sliceMetric_shift_heq hhor τ
  refine ⟨hstage, hmetric, ?_⟩
  intro x y hxy r hball
  have hb : R.history.toHistory.isParabolicallyRmControlledBall (A.shiftTime hhor τ)
      (castPoint hstage.symm y) r := A.transport_ball hhor τ y r hball
  have he : castPoint hstage.symm y = x :=
    eq_of_heq ((castPoint_heq hstage.symm y).trans hxy.symm)
  rwa [he] at hb

/-- The existing marked family supplies every later full prefix. -/
private theorem reserve_state_prefix
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g) (m n : ℕ) (hmn : m ≤ n) :
    (S.state m).history.toHistory.IsPrefixOf (S.state n).history.toHistory := by
  induction n, hmn using Nat.le_induction with
  | base => exact ObservedHistory.IsPrefixOf.refl _
  | succ n _ ih => exact ih.trans (S.successor n).initial_prefix.1

/-- Transport the native query into an arbitrary observation of the same constructed family. -/
theorem PreparedSpatialChain.native_query_transport_to_observation
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g)
    (F : GC.Interface.RawSurgery P g) (hTower : F.tower = S.tower)
    (j : ℕ) {εcut Dcut : ℝ} {mcut : ℕ}
    (W : PreparedSpatialStepRetention (S.state j) (S.state (j + 1))
      (S.accuracy j) (1 / ((j : ℝ) + 2)) εcut Dcut mcut)
    (hshift : (S.state (j + 1)).shift =
      (S.state j).history.time (Fin.last (S.state j).history.eventCount))
    (hoffset : (S.state (j + 1)).offset = (S.state j).history.eventCount)
    (U : ℝ) (hU : 0 ≤ U)
    (T : Icc (0 : ℝ) (F.observation.observe U hU).horizon)
    (τ : Icc (0 : ℝ) W.oldNative.horizon)
    (hclock : (T : ℝ) = (τ : ℝ) + (S.state j).shift)
    : let H := F.observation.observe U hU
      H.stageAt T = W.oldNative.toHistory.stageAt τ ∧
      HEq (H.stageMetric (H.activeStage T) T)
        (W.oldNative.toHistory.stageMetric (W.oldNative.toHistory.activeStage τ) τ) ∧
      ∀ (x : (H.stageAt T).Carrier)
        (y : (W.oldNative.toHistory.stageAt τ).Carrier), HEq x y →
        ∀ r : ℝ, W.oldNative.toHistory.isParabolicallyRmControlledBall τ y r →
          H.isParabolicallyRmControlledBall T x r := by
  let K := W.oldNative
  let R := S.state (j + 1)
  let H := F.observation.observe U hU
  let N := max j (Nat.ceil U)
  let D := (S.state (N + 1)).history.toHistory
  have hjN : j ≤ N := le_max_left _ _
  have hUN : U ≤ (N : ℝ) := (Nat.le_ceil U).trans (by
    exact_mod_cast (le_max_right j (Nat.ceil U)))
  have hpR : R.history.toHistory.IsPrefixOf D :=
    reserve_state_prefix S (j + 1) (N + 1) (Nat.succ_le_succ hjN)
  have hUD : U ≤ D.horizon := hUN.trans (by
    change (N : ℝ) ≤ (S.state (N + 1)).history.horizon
    rw [(S.state (N + 1)).horizon_eq]
    exact (nat_lt_three_pow N).le)
  let a : Icc (0 : ℝ) D.horizon := S.observationTime N
  let u : Icc (0 : ℝ) (D.restrict a).horizon := ⟨U, hU, hUN⟩
  have hhistory : F.observation.history N = D.restrict a := by
    change (F.tower.history N).toHistory = _
    rw [hTower]
    rfl
  have hIndex : H.SamePresentation ((D.restrict a).restrict u) := by
    have h := F.observation.observe_eq_atIndex N U hU hUN
    change H.SamePresentation ((F.observation.history N).restrict _) at h
    have gen : ∀ (X : ObservedHistory.{u}) (_ : F.observation.history N = X)
        (z : Icc (0 : ℝ) (F.observation.history N).horizon) (z' : Icc (0 : ℝ) X.horizon),
        H.SamePresentation ((F.observation.history N).restrict z) → (z : ℝ) = z' →
        H.SamePresentation (X.restrict z') := by
      intro X hX z z' hh hz
      subst hX
      have hzz : z = z' := Subtype.ext hz
      subst hzz
      exact hh
    exact gen _ hhistory _ u h rfl
  have hpH : H.IsPrefixOf D := by
    refine ⟨hUD, ?_⟩
    exact (hIndex.trans (D.restrict_restrict a u)).symm
  let tR : Icc (0 : ℝ) R.history.horizon := ⟨T, T.property.1, by
    have ht := τ.property.2
    replace ht := ht.trans_eq W.oldNative_horizon
    change (T : ℝ) ≤ (S.state (j + 1)).history.horizon
    rw [(S.state (j + 1)).horizon_eq]
    change (T : ℝ) ≤ (3 : ℝ) ^ j
    linarith [hclock]⟩
  have hW := W.full_native_query_transport (S.successor j) hshift hoffset τ tR hclock
  have hRD := hpR.stageAt_eq tR
  have hHD := hpH.stageAt_eq T
  have hstage : H.stageAt T = K.toHistory.stageAt τ :=
    hHD.trans (hRD.symm.trans hW.1)
  have hmetric : HEq (H.stageMetric (H.activeStage T) T)
      (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) :=
    (hpH.sliceMetric_heq T).trans ((hpR.sliceMetric_heq tR).symm.trans hW.2.1)
  refine ⟨hstage, hmetric, ?_⟩
  intro x y hxy r hball
  let xR := castPoint hW.1.symm y
  have hxR : HEq xR y := castPoint_heq hW.1.symm y
  have hballR := hW.2.2 xR y hxR r hball
  let xD := castPoint hRD xR
  have hxD : HEq xD xR := castPoint_heq hRD xR
  have hballD := (controlled_ball_iff_of_prefix hpR tR xR xD hxD r).mpr hballR
  exact (controlled_ball_iff_of_prefix hpH T x xD
    (hxD.trans (hxR.trans hxy.symm)) r).mp hballD

end GC.GeneralFlow

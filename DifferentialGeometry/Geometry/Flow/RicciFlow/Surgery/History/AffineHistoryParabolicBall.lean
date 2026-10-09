import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.CutoffRecordConcatenation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingRoom

/-!
S-CH11-FIX6 patched-at-path（astra `History/AffineHistoryParabolicBall` 的 elaboration 修补；
下游 `PreparedSpatialReserveTransport` 有 `open private … from` 本路径）。陈述 / 定义 / 证明思路
逐字不变；本树 Lean 与 donor 的差异只有以下几类（43 error → 0）：
(a) `shift_nonneg : 0 ≤ c` 前加 `include A in`（theorem 只纳入签名里提到的 variable，A/J/K 不进来，
    级联出 `shiftTime` / `stageAt_shift_eq` 等的 "no usable parameter" 报错）；
    其体内 `J.toHistory.time_nonneg …` 先 ascribe 到 `J.time` 形；
(b) `omega` 前显式给 `J.eventCount` 与 `J.toHistory.eventCount` 两个 `count_eq` 事实
    （`↑(Fin.last _)` 与 abbrev `toHistory` 被 omega 当作不同原子）；
(c) `rw [A.stageIndex_time]` 前 `change` 到 `J.time` 形（`J.toHistory.time` 与 `J.time` 不同 head）；
(d) `simpa only [A.stageIndex_succ] using X` → 直接 `X`（defeq）；`simpa … add_sub_cancel_right`
    → `have h := …; rw … at h; exact h`；`rw [← A.stageIndex_succ]` 去掉（motive 不良）；
(e) `h ▸ p` 作为 `BackwardPointTrace` 端点处补类型 ascription（`J.stage …` / `J.toHistory.stageAt …`
    的 `Carrier`），否则 `▸` 找不到 expected type；
(f) 依赖 proof 实参的隐式参数显式给：`B.isRmControlled (hat := hat)`、
    `(A.shiftTime_le_iff hhor a t).mpr hat`、`stageIndex_le_iff first j / j last` 等；
(g) `timeTraceEquiv_controlled_iff` 末尾 `simpa only [he] using hb`（whnf 超时）→
    `clear_value v; subst he; exact hb`；`isParabolicallyRmControlledBall_shift_iff` 里
    `simpa only [C, Equiv.apply_symm_apply] using hB` →
    `have h2 : … = B := Equiv.apply_symm_apply _ B; rw [h2]; exact hB`。
-/

set_option autoImplicit false
noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal

namespace GC.GeneralFlow

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private def castPoint {P Q : OrientedThreeStage.{u}} (h : P = Q)
    (p : P.Carrier) : Q.Carrier := h ▸ p

private theorem castPoint_heq {P Q : OrientedThreeStage.{u}} (h : P = Q)
    (p : P.Carrier) : HEq (castPoint h p) p := by
  cases h
  exact HEq.rfl

private theorem normSq_eq_of_metric_heq {P Q : OrientedThreeStage.{u}}
    (h : P = Q) {g : P.Metric} {g' : Q.Metric} (hg : HEq g g')
    {x : P.Carrier} {y : Q.Carrier} (hx : HEq x y) :
    normSq0S g x 4 (metricRm04At g x) =
      normSq0S g' y 4 (metricRm04At g' y) := by
  cases h
  cases eq_of_heq hg
  cases eq_of_heq hx
  rfl

private theorem ball_mem_iff_of_metric_heq {P Q : OrientedThreeStage.{u}}
    (h : P = Q) {g : P.Metric} {g' : Q.Metric} (hg : HEq g g')
    {x p : P.Carrier} {y q : Q.Carrier} (hx : HEq x y) (hp : HEq p q) (r : ℝ) :
    x ∈ riemannianBallOf g p r ↔ y ∈ riemannianBallOf g' q r := by
  cases h
  cases eq_of_heq hg
  cases eq_of_heq hx
  cases eq_of_heq hp
  rfl

private theorem ball_volume_eq_of_metric_heq {P Q : OrientedThreeStage.{u}}
    (h : P = Q) {g : P.Metric} {g' : Q.Metric} (hg : HEq g g')
    {p : P.Carrier} {q : Q.Carrier} (hp : HEq p q) (r : ℝ) :
    riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g p r) =
      riemannianVolumeMeasure ThreeModel Q.Carrier g' (riemannianBallOf g' q r) := by
  cases h
  cases eq_of_heq hg
  cases eq_of_heq hp
  rfl

private theorem crossing_iff_of_translated_event
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (E : RetainedCoreEvent P Q a s) (c : ℝ)
    {E' : RetainedCoreEvent P' Q' a' s'}
    (hP : P' = P) (hQ : Q' = Q) (ha : a' = a + c) (hs : s' = s + c)
    (hE : HEq E' (translate_retained_event E c))
    {x' : P'.Carrier} {y' : Q'.Carrier} {x : P.Carrier} {y : Q.Carrier}
    (hx : HEq x' x) (hy : HEq y' y) :
    E'.toMetricCutCapEvent.RegularCrossing x' y' ↔
      E.toMetricCutCapEvent.RegularCrossing x y := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  cases eq_of_heq hx
  cases eq_of_heq hy
  rfl

private theorem trace_point_heq {H : ObservedHistory.{u}}
    {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
    {p : (H.stage last).Carrier} (B : BackwardPointTrace H first last hle p)
    {j k : Fin (H.eventCount + 1)} (hjk : j = k)
    (hf : first ≤ j) (hl : j ≤ last) (hf' : first ≤ k) (hl' : k ≤ last) :
    HEq (B.point j hf hl) (B.point k hf' hl') := by
  cases hjk
  exact HEq.rfl

namespace AffineEventPrefix

variable {K J : RetainedCoreHistory.{u}} {c : ℝ} {offset : ℕ}
    (A : AffineEventPrefix K J c offset (Fin.last K.eventCount))

/-- The actual stage of the joined history corresponding to a source stage. -/
def stageIndex (j : Fin (K.eventCount + 1)) : Fin (J.eventCount + 1) :=
  ⟨offset + j.val, by
    have h1 : J.eventCount = offset + K.eventCount := A.count_eq
    have h2 : J.toHistory.eventCount = offset + K.eventCount := A.count_eq
    omega⟩

@[simp] theorem stageIndex_val (j : Fin (K.eventCount + 1)) :
    (A.stageIndex j).val = offset + j.val := rfl

theorem stageIndex_le_iff (j k : Fin (K.eventCount + 1)) :
    A.stageIndex j ≤ A.stageIndex k ↔ j ≤ k := by
  change offset + j.val ≤ offset + k.val ↔ j.val ≤ k.val
  omega

@[simp] theorem stageIndex_castSucc (i : Fin K.eventCount) :
    A.stageIndex i.castSucc = (A.eventIndex i).castSucc := rfl

@[simp] theorem stageIndex_succ (i : Fin K.eventCount) :
    A.stageIndex i.succ = (A.eventIndex i).succ := by
  apply Fin.ext
  change offset + (i.val + 1) = offset + i.val + 1
  omega

@[simp] theorem stageIndex_last :
    A.stageIndex (Fin.last K.eventCount) = Fin.last J.eventCount := by
  apply Fin.ext
  exact A.count_eq.symm

theorem stageIndex_time (j : Fin (K.eventCount + 1)) :
    J.time (A.stageIndex j) = K.time j + c := A.time_eq j

theorem stageIndex_stage (j : Fin (K.eventCount + 1)) :
    J.stage (A.stageIndex j) = K.stage j := A.stage_eq j

include A in
theorem shift_nonneg : 0 ≤ c := by
  have h : 0 ≤ J.time (A.stageIndex 0) := J.toHistory.time_nonneg (A.stageIndex 0)
  rw [A.stageIndex_time, K.time_zero, zero_add] at h
  exact h

/-- Affine translation of a source observation time in the actual joined history. -/
def shiftTime (hhor : J.horizon = K.horizon + c)
    (t : Icc (0 : ℝ) K.horizon) : Icc (0 : ℝ) J.horizon :=
  ⟨(t : ℝ) + c, add_nonneg t.property.1 A.shift_nonneg, by
    rw [hhor]
    exact add_le_add t.property.2 (le_refl c)⟩

@[simp] theorem shiftTime_val (hhor : J.horizon = K.horizon + c)
    (t : Icc (0 : ℝ) K.horizon) : (A.shiftTime hhor t : ℝ) = (t : ℝ) + c := rfl

theorem shiftTime_le_iff (hhor : J.horizon = K.horizon + c)
    (s t : Icc (0 : ℝ) K.horizon) : A.shiftTime hhor s ≤ A.shiftTime hhor t ↔ s ≤ t := by
  change (s : ℝ) + c ≤ (t : ℝ) + c ↔ (s : ℝ) ≤ (t : ℝ)
  constructor <;> intro h <;> linarith

theorem activeStage_shift_eq (hhor : J.horizon = K.horizon + c)
    (t : Icc (0 : ℝ) K.horizon) :
    J.toHistory.activeStage (A.shiftTime hhor t) = A.stageIndex (K.toHistory.activeStage t) := by
  apply J.toHistory.activeStage_eq_of_maximal
  · change J.time (A.stageIndex (K.toHistory.activeStage t)) ≤ (t : ℝ) + c
    rw [A.stageIndex_time]
    exact add_le_add (K.toHistory.activeStage_time_le t) (le_refl c)
  · intro j hj
    by_cases ho : j.val < offset
    · change j.val ≤ offset + (K.toHistory.activeStage t).val
      omega
    · let k : Fin (K.eventCount + 1) :=
        ⟨j.val - offset, by
          have := j.isLt
          have h1 : J.eventCount = offset + K.eventCount := A.count_eq
          have h2 : J.toHistory.eventCount = offset + K.eventCount := A.count_eq
          omega⟩
      have he : A.stageIndex k = j := by
        apply Fin.ext
        change offset + (j.val - offset) = j.val
        omega
      have ht : K.time k ≤ (t : ℝ) := by
        rw [← he] at hj
        change J.time (A.stageIndex k) ≤ (t : ℝ) + c at hj
        rw [A.stageIndex_time] at hj
        change K.time k + c ≤ (t : ℝ) + c at hj
        linarith
      rw [← he]
      exact (A.stageIndex_le_iff _ _).mpr (K.toHistory.le_activeStage t k ht)

theorem stageAt_shift_eq (hhor : J.horizon = K.horizon + c)
    (t : Icc (0 : ℝ) K.horizon) :
    J.toHistory.stageAt (A.shiftTime hhor t) = K.toHistory.stageAt t := by
  change J.stage (J.toHistory.activeStage (A.shiftTime hhor t)) =
    K.stage (K.toHistory.activeStage t)
  rw [A.activeStage_shift_eq]
  exact A.stageIndex_stage _

theorem stageMetric_shift_heq
    (hfinal : ∀ t : ℝ,
      HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (t + c))
        (K.toHistory.stageMetric (Fin.last K.eventCount) t))
    (j : Fin (K.eventCount + 1)) (t : ℝ) :
    HEq (J.toHistory.stageMetric (A.stageIndex j) (t + c))
      (K.toHistory.stageMetric j t) := by
  cases j using Fin.lastCases with
  | last =>
      rw [A.stageIndex_last]
      exact hfinal t
  | cast i =>
      rw [A.stageIndex_castSucc, ObservedHistory.stageMetric_castSucc_apply,
        ObservedHistory.stageMetric_castSucc_apply]
      have h := A.incoming_metric_heq i (t + c)
      rw [add_sub_cancel_right] at h
      exact h

theorem sliceMetric_shift_heq (hhor : J.horizon = K.horizon + c)
    (hfinal : ∀ t : ℝ,
      HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (t + c))
        (K.toHistory.stageMetric (Fin.last K.eventCount) t))
    (t : Icc (0 : ℝ) K.horizon) :
    HEq (J.toHistory.stageMetric (J.toHistory.activeStage (A.shiftTime hhor t))
      (A.shiftTime hhor t)) (K.toHistory.stageMetric (K.toHistory.activeStage t) t) := by
  rw [A.activeStage_shift_eq]
  exact A.stageMetric_shift_heq hfinal _ _

private def sourceStage (j : Fin (J.eventCount + 1)) :
    Fin (K.eventCount + 1) :=
  ⟨j.val - offset, by
    have := j.isLt
    have h1 : J.eventCount = offset + K.eventCount := A.count_eq
    have h2 : J.toHistory.eventCount = offset + K.eventCount := A.count_eq
    omega⟩

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
    {p : (K.stage last).Carrier} (B : BackwardPointTrace K.toHistory first last hle p)
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
    {p : (K.stage last).Carrier} (B : BackwardPointTrace K.toHistory first last hle p)
    (j : Fin (K.eventCount + 1)) (hf : first ≤ j) (hl : j ≤ last)
    (hf' : A.stageIndex first ≤ A.stageIndex j) (hl' : A.stageIndex j ≤ A.stageIndex last) :
    HEq (A.pushTracePoint B (A.stageIndex j) hf' hl') (B.point j hf hl) := by
  unfold pushTracePoint
  exact (castPoint_heq _ _).trans
    (trace_point_heq B (A.sourceStage_stageIndex j) _ _ hf hl)

private def pushTrace {first last : Fin (K.eventCount + 1)} (hle : first ≤ last)
    {p : (K.stage last).Carrier} (B : BackwardPointTrace K.toHistory first last hle p) :
    BackwardPointTrace J.toHistory (A.stageIndex first) (A.stageIndex last)
      ((A.stageIndex_le_iff first last).mpr hle) (castPoint (A.stageIndex_stage last).symm p) where
  point := A.pushTracePoint B
  endpoint_eq := by
    apply eq_of_heq
    exact (A.pushTracePoint_heq B last hle le_rfl _ _).trans
      ((heq_of_eq B.endpoint_eq).trans (castPoint_heq _ _).symm)
  crossing i hf hl := by
    have ho : offset ≤ i.val := by change offset + first.val ≤ i.val at hf; omega
    obtain ⟨k, rfl⟩ : ∃ k : Fin K.eventCount, A.eventIndex k = i := by
      refine ⟨⟨i.val - offset, by
        have := i.isLt
        have h1 : J.eventCount = offset + K.eventCount := A.count_eq
        have h2 : J.toHistory.eventCount = offset + K.eventCount := A.count_eq
        omega⟩, ?_⟩
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
    apply (crossing_iff_of_translated_event (K.coreEvent k) c
      (A.stageIndex_stage k.castSucc) (A.stageIndex_stage k.succ)
      (A.stageIndex_time k.castSucc) (A.stageIndex_time k.succ)
      (A.event_heq k) ?_ ?_).mpr (B.crossing k hkf hkl)
    · exact A.pushTracePoint_heq B k.castSucc hkf (k.castSucc_lt_succ.le.trans hkl) _ _
    · exact A.pushTracePoint_heq B k.succ (hkf.trans k.castSucc_lt_succ.le) hkl _ _

private def pullTrace {first last : Fin (K.eventCount + 1)} (hle : first ≤ last)
    {p : (K.stage last).Carrier}
    (B : BackwardPointTrace J.toHistory (A.stageIndex first) (A.stageIndex last)
      ((A.stageIndex_le_iff first last).mpr hle) (castPoint (A.stageIndex_stage last).symm p)) :
    BackwardPointTrace K.toHistory first last hle p where
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
    apply (crossing_iff_of_translated_event (K.coreEvent i) c
      (A.stageIndex_stage i.castSucc) (A.stageIndex_stage i.succ)
      (A.stageIndex_time i.castSucc) (A.stageIndex_time i.succ)
      (A.event_heq i) ?_ ?_).mp (B.crossing (A.eventIndex i) hf' hl')
    · exact (castPoint_heq _ _).symm
    · exact (castPoint_heq _ _).symm

/-- Backward traces in the source and in its translated tail have exactly the
same points and retained crossings. No trace can acquire a stage before the join. -/
def traceEquiv (first last : Fin (K.eventCount + 1)) (hle : first ≤ last)
    (p : (K.stage last).Carrier) :
    BackwardPointTrace K.toHistory first last hle p ≃
      BackwardPointTrace J.toHistory (A.stageIndex first) (A.stageIndex last)
        ((A.stageIndex_le_iff first last).mpr hle)
        ((A.stageIndex_stage last).symm ▸ p : (J.stage (A.stageIndex last)).Carrier) where
  toFun := A.pushTrace hle
  invFun := A.pullTrace hle
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

theorem traceEquiv_point_heq {first last : Fin (K.eventCount + 1)} {hle : first ≤ last}
    {p : (K.stage last).Carrier} (B : BackwardPointTrace K.toHistory first last hle p)
    (j : Fin (K.eventCount + 1)) (hf : first ≤ j) (hl : j ≤ last) :
    HEq ((A.traceEquiv first last hle p B).point (A.stageIndex j)
      ((A.stageIndex_le_iff first j).mpr hf) ((A.stageIndex_le_iff j last).mpr hl))
      (B.point j hf hl) :=
  A.pushTracePoint_heq B j hf hl ((A.stageIndex_le_iff first j).mpr hf)
    ((A.stageIndex_le_iff j last).mpr hl)

theorem traceEquiv_symm_point_heq {first last : Fin (K.eventCount + 1)} {hle : first ≤ last}
    {p : (K.stage last).Carrier}
    (B : BackwardPointTrace J.toHistory (A.stageIndex first) (A.stageIndex last)
      ((A.stageIndex_le_iff first last).mpr hle)
      ((A.stageIndex_stage last).symm ▸ p : (J.stage (A.stageIndex last)).Carrier))
    (j : Fin (K.eventCount + 1)) (hf : first ≤ j) (hl : j ≤ last) :
    HEq (((A.traceEquiv first last hle p).symm B).point j hf hl)
      (B.point (A.stageIndex j) ((A.stageIndex_le_iff _ _).mpr hf)
        ((A.stageIndex_le_iff _ _).mpr hl)) := castPoint_heq _ _

end AffineEventPrefix

private def traceIndexEquiv {H : ObservedHistory.{u}}
    {first last first' last' : Fin (H.eventCount + 1)}
    (hf : first' = first) (hl : last' = last) (hle : first ≤ last) (hle' : first' ≤ last')
    (p : (H.stage last).Carrier) (p' : (H.stage last').Carrier) (hp : HEq p' p) :
    BackwardPointTrace H first last hle p ≃ BackwardPointTrace H first' last' hle' p' := by
  cases hf
  cases hl
  cases eq_of_heq hp
  exact Equiv.refl _

private theorem traceIndexEquiv_point_heq {H : ObservedHistory.{u}}
    {first last first' last' : Fin (H.eventCount + 1)}
    (hf : first' = first) (hl : last' = last) (hle : first ≤ last) (hle' : first' ≤ last')
    (p : (H.stage last).Carrier) (p' : (H.stage last').Carrier) (hp : HEq p' p)
    (B : BackwardPointTrace H first last hle p)
    {j j' : Fin (H.eventCount + 1)} (hj : j' = j)
    (hfj : first ≤ j) (hjl : j ≤ last) (hfj' : first' ≤ j') (hjl' : j' ≤ last') :
    HEq ((traceIndexEquiv hf hl hle hle' p p' hp B).point j' hfj' hjl')
      (B.point j hfj hjl) := by
  cases hf
  cases hl
  cases eq_of_heq hp
  cases hj
  exact HEq.rfl

private theorem controlled_of_regular {H : ObservedHistory.{u}}
    {a t : Icc (0 : ℝ) H.horizon} {hat : a ≤ t} {p : (H.stageAt t).Carrier}
    (B : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    (r : ℝ)
    (hregular : ∀ (s : Icc (0 : ℝ) H.horizon) (has : a ≤ s) (hst : s ≤ t),
      r ^ 4 * normSq0S (H.stageMetric (H.activeStage s) s)
        (B.point (H.activeStage s) (H.activeStage_mono has) (H.activeStage_mono hst)) 4
        (metricRm04At (H.stageMetric (H.activeStage s) s)
          (B.point (H.activeStage s) (H.activeStage_mono has) (H.activeStage_mono hst))) ≤ 1) :
    B.isRmControlled (hat := hat) r := by
  refine ⟨hregular, ?_⟩
  intro i hf hl
  have hIoc := (H.crossed_event_iff_mem_Ioc a t i).mp ⟨hf, hl⟩
  let v : Icc (0 : ℝ) H.horizon :=
    ⟨H.time i.succ, H.time_nonneg _, H.time_le_horizon_at _⟩
  have hav : H.activeStage v = i.succ := H.activeStage_at_time i.succ
  have hav' : a ≤ v := hIoc.1.le
  have hvt : v ≤ t := hIoc.2
  have hb := hregular v hav' hvt
  have heq : normSq0S (H.stageMetric (H.activeStage v) v)
      (B.point (H.activeStage v) (H.activeStage_mono hav') (H.activeStage_mono hvt)) 4
      (metricRm04At (H.stageMetric (H.activeStage v) v)
        (B.point (H.activeStage v) (H.activeStage_mono hav') (H.activeStage_mono hvt))) =
      normSq0S (H.stageMetric i.succ v)
        (B.point i.succ (hf.trans i.castSucc_lt_succ.le) hl) 4
        (metricRm04At (H.stageMetric i.succ v)
          (B.point i.succ (hf.trans i.castSucc_lt_succ.le) hl)) :=
    normSq_eq_of_metric_heq (congrArg H.stage hav)
      (heq_apply_of_eq (fun j => H.stageMetric j (v : ℝ)) hav)
      (trace_point_heq B hav _ _ _ _)
  rw [heq] at hb
  have hx := MetricCutCapEvent.RegularCrossing.rmNormSq_eq (H.event i)
    (p := ⟨B.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl),
      (B.crossing i hf hl).mem_terminalRegularRegion (H.event i)⟩) (B.crossing i hf hl)
  change r ^ 4 * normSq0S (H.event i).terminal.metric _ 4 (metricRm04At _ _) ≤ 1
  rw [hx, H.event_output i, ← H.stageMetric_initial]
  exact hb

namespace AffineEventPrefix

variable {K J : RetainedCoreHistory.{u}} {c : ℝ} {offset : ℕ}
    (A : AffineEventPrefix K J c offset (Fin.last K.eventCount))

private def timeTraceEquiv (hhor : J.horizon = K.horizon + c)
    (a t : Icc (0 : ℝ) K.horizon) (hat : a ≤ t) (p : (K.toHistory.stageAt t).Carrier) :
    BackwardPointTrace K.toHistory (K.toHistory.activeStage a) (K.toHistory.activeStage t)
      (K.toHistory.activeStage_mono hat) p ≃
    BackwardPointTrace J.toHistory (J.toHistory.activeStage (A.shiftTime hhor a))
      (J.toHistory.activeStage (A.shiftTime hhor t))
      (J.toHistory.activeStage_mono ((A.shiftTime_le_iff hhor a t).mpr hat))
      ((A.stageAt_shift_eq hhor t).symm ▸ p : (J.toHistory.stageAt (A.shiftTime hhor t)).Carrier) :=
  (A.traceEquiv _ _ (K.toHistory.activeStage_mono hat) p).trans
    (traceIndexEquiv (A.activeStage_shift_eq hhor a) (A.activeStage_shift_eq hhor t) _ _ _ _
      ((castPoint_heq (A.stageAt_shift_eq hhor t).symm p).trans
        (castPoint_heq (A.stageIndex_stage (K.toHistory.activeStage t)).symm p).symm))

private theorem timeTraceEquiv_point_heq (hhor : J.horizon = K.horizon + c)
    {a t : Icc (0 : ℝ) K.horizon} {hat : a ≤ t} {p : (K.toHistory.stageAt t).Carrier}
    (B : BackwardPointTrace K.toHistory (K.toHistory.activeStage a) (K.toHistory.activeStage t)
      (K.toHistory.activeStage_mono hat) p)
    (s : Icc (0 : ℝ) K.horizon) (has : a ≤ s) (hst : s ≤ t) :
    HEq ((A.timeTraceEquiv hhor a t hat p B).point
      (J.toHistory.activeStage (A.shiftTime hhor s))
      (J.toHistory.activeStage_mono ((A.shiftTime_le_iff hhor a s).mpr has))
      (J.toHistory.activeStage_mono ((A.shiftTime_le_iff hhor s t).mpr hst)))
      (B.point (K.toHistory.activeStage s)
        (K.toHistory.activeStage_mono has) (K.toHistory.activeStage_mono hst)) := by
  unfold timeTraceEquiv
  exact (traceIndexEquiv_point_heq _ _ _ _ _ _ _ _ (A.activeStage_shift_eq hhor s) _ _ _ _).trans
    (A.traceEquiv_point_heq B _ _ _)

private theorem timeTraceEquiv_controlled_iff (hhor : J.horizon = K.horizon + c)
    (hfinal : ∀ t : ℝ,
      HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (t + c))
        (K.toHistory.stageMetric (Fin.last K.eventCount) t))
    {a t : Icc (0 : ℝ) K.horizon} {hat : a ≤ t} {p : (K.toHistory.stageAt t).Carrier}
    (B : BackwardPointTrace K.toHistory (K.toHistory.activeStage a) (K.toHistory.activeStage t)
      (K.toHistory.activeStage_mono hat) p) (r : ℝ) :
    (A.timeTraceEquiv hhor a t hat p B).isRmControlled
        (hat := (A.shiftTime_le_iff hhor a t).mpr hat) r ↔
      B.isRmControlled (hat := hat) r := by
  constructor
  · intro hB
    apply controlled_of_regular B r
    intro s has hst
    have hsA := (A.shiftTime_le_iff hhor a s).mpr has
    have hsT := (A.shiftTime_le_iff hhor s t).mpr hst
    have hb := hB.1 (A.shiftTime hhor s) hsA hsT
    rw [normSq_eq_of_metric_heq (A.stageAt_shift_eq hhor s)
      (A.sliceMetric_shift_heq hhor hfinal s) (A.timeTraceEquiv_point_heq hhor B s has hst)] at hb
    exact hb
  · intro hB
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
      (A.sliceMetric_shift_heq hhor hfinal v)
      (A.timeTraceEquiv_point_heq (hat := hat) hhor B v hav hvt)
    have hb := hB.1 v hav hvt
    rw [← hn] at hb
    clear_value v
    subst he
    exact hb

/-- A parabolic ball contained in the translated tail is controlled exactly when
its original ball is controlled. The radius condition excludes backward times
before the join; the actual points, metrics and crossings are unchanged. -/
theorem isParabolicallyRmControlledBall_shift_iff (hhor : J.horizon = K.horizon + c)
    (hfinal : ∀ t : ℝ,
      HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (t + c))
        (K.toHistory.stageMetric (Fin.last K.eventCount) t))
    (t : Icc (0 : ℝ) K.horizon) (p : (K.toHistory.stageAt t).Carrier) (r : ℝ)
    (hrtime : r ^ 2 ≤ (t : ℝ)) :
    J.toHistory.isParabolicallyRmControlledBall (A.shiftTime hhor t)
      ((A.stageAt_shift_eq hhor t).symm ▸ p) r ↔
    K.toHistory.isParabolicallyRmControlledBall t p r := by
  constructor
  · rintro ⟨hr, b, hbt, hb, htraces⟩
    let a : Icc (0 : ℝ) K.horizon := ⟨(t : ℝ) - r ^ 2, sub_nonneg.mpr hrtime,
      (sub_le_self _ (sq_nonneg r)).trans t.property.2⟩
    have hat : a ≤ t := sub_le_self _ (sq_nonneg r)
    have hba : b = A.shiftTime hhor a := by
      apply Subtype.ext
      change (b : ℝ) = ((t : ℝ) - r ^ 2) + c
      change (b : ℝ) = ((t : ℝ) + c) - r ^ 2 at hb
      linarith
    subst b
    refine ⟨hr, a, hat, rfl, ?_⟩
    intro x hx
    let y : (J.toHistory.stageAt (A.shiftTime hhor t)).Carrier :=
      castPoint (A.stageAt_shift_eq hhor t).symm x
    have hy : y ∈ riemannianBallOf
        (J.toHistory.stageMetric (J.toHistory.activeStage (A.shiftTime hhor t))
          (A.shiftTime hhor t))
        ((A.stageAt_shift_eq hhor t).symm ▸ p :
          (J.toHistory.stageAt (A.shiftTime hhor t)).Carrier) r :=
      (ball_mem_iff_of_metric_heq (A.stageAt_shift_eq hhor t)
        (A.sliceMetric_shift_heq hhor hfinal t) (castPoint_heq _ x) (castPoint_heq _ p) r).mpr hx
    obtain ⟨B, hB⟩ := htraces y hy
    let C := (A.timeTraceEquiv hhor a t hat x).symm B
    refine ⟨C, (A.timeTraceEquiv_controlled_iff (hat := hat) hhor hfinal C r).mp ?_⟩
    have h2 : A.timeTraceEquiv hhor a t hat x C = B := Equiv.apply_symm_apply _ B
    rw [h2]
    exact hB
  · rintro ⟨hr, a, hat, ha, htraces⟩
    have hat' := (A.shiftTime_le_iff hhor a t).mpr hat
    refine ⟨hr, A.shiftTime hhor a, hat', ?_, ?_⟩
    · change (a : ℝ) + c = ((t : ℝ) + c) - r ^ 2
      linarith
    · intro y hy
      let x : (K.toHistory.stageAt t).Carrier := castPoint (A.stageAt_shift_eq hhor t) y
      have hx : x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage t) t) p r :=
        (ball_mem_iff_of_metric_heq (A.stageAt_shift_eq hhor t)
          (A.sliceMetric_shift_heq hhor hfinal t) (castPoint_heq _ y).symm
          (castPoint_heq _ p) r).mp hy
      obtain ⟨B, hB⟩ := htraces x hx
      have he : ((A.stageAt_shift_eq hhor t).symm ▸ x :
          (J.toHistory.stageAt (A.shiftTime hhor t)).Carrier) = y :=
        eq_of_heq ((castPoint_heq _ x).trans (castPoint_heq _ y))
      have hC := (A.timeTraceEquiv_controlled_iff (hat := hat) hhor hfinal B r).mpr hB
      exact he ▸ ⟨A.timeTraceEquiv hhor a t hat x B, hC⟩

/-- The transported ball has exactly the original volume, with its center cast
through the proved equality of the actual stages. -/
theorem ball_volume_shift_eq (hhor : J.horizon = K.horizon + c)
    (hfinal : ∀ t : ℝ,
      HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (t + c))
        (K.toHistory.stageMetric (Fin.last K.eventCount) t))
    (t : Icc (0 : ℝ) K.horizon) (p : (K.toHistory.stageAt t).Carrier) (r : ℝ) :
    riemannianVolumeMeasure ThreeModel (J.toHistory.stageAt (A.shiftTime hhor t)).Carrier
      (J.toHistory.stageMetric (J.toHistory.activeStage (A.shiftTime hhor t)) (A.shiftTime hhor t))
      (riemannianBallOf
        (J.toHistory.stageMetric (J.toHistory.activeStage (A.shiftTime hhor t))
          (A.shiftTime hhor t))
        ((A.stageAt_shift_eq hhor t).symm ▸ p) r) =
    riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt t).Carrier
      (K.toHistory.stageMetric (K.toHistory.activeStage t) t)
      (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage t) t) p r) :=
  ball_volume_eq_of_metric_heq (A.stageAt_shift_eq hhor t)
    (A.sliceMetric_shift_heq hhor hfinal t) (castPoint_heq _ p) r

end AffineEventPrefix
end GC.GeneralFlow

import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryNoncollapsePrefix.Basic

/-!
S-CH11-FIX6 patched-at-path（astra `History/HistoryParabolicBallPrefixTransport` 的 elaboration 修补；
下游 `PreparedSpatialBirthVolumeOrReserve` / `PreparedSpatialReserveTransport` /
`PreparedSpatialPhysicalVolumeOrReserve` 有 `open private … from` 本路径）。陈述 / 证明思路逐字不变：
(a) `controlled_ball_of_samePresentation` 里 `let B : BackwardPointTrace … where …`
    → 结构实例 `:= { point := fun … , endpoint_eq := …, crossing := fun … }`（design-C11-S6 §3.1(a)）；
(b) 同一证明里 `hxK` 的 `rw [← hmetric (L.activeStage t) …]` 前加 `change`（K/L 的 `activeStage`
    只 defeq，motive 不良；§3.1(b)）；
(c) 6 处 `rw [congrArg Fin.val (H.restrict_activeStage a s/t)]; exact hf/hl`（`Fin.castLE` 的 val 与目标
    非 syntactic 一致）→ `exact (congrArg Fin.val …).trans_le (Fin.le_def.mp hf)` /
    `exact (Fin.le_def.mp hl).trans_eq (congrArg Fin.val …).symm`。
-/

set_option autoImplicit false
noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.GeneralFlow

universe u

open private cast_point cast_point_heq ball_mem_iff_of_metric_heq
  curvature_sq_eq_of_metric_heq trace_point_heq_of_index_eq
  lift_restricted_time restricted_controlled_ball from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryNoncollapsePrefix.Basic
open private regularCrossing_iff_of_samePresentation
  terminal_curvature_normSq_eq_of_samePresentation from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryNoncollapsingPresentation.Basic

private theorem regularCrossing_iff_of_samePresentation_heq
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    {E : MetricCutCapEvent P Q a s} {F : MetricCutCapEvent P' Q' a' s'}
    (R : E.SamePresentation F)
    {p : P.Carrier} {q : Q.Carrier} {p' : P'.Carrier} {q' : Q'.Carrier}
    (hp : HEq p p') (hq : HEq q q') :
    E.RegularCrossing p q ↔ F.RegularCrossing p' q' := by
  cases R.incomingStage_eq
  cases R.outgoingStage_eq
  cases R.leftTime_eq
  cases R.eventTime_eq
  have hpp : p = p' := eq_of_heq hp
  subst p'
  have hqq : q = q' := eq_of_heq hq
  subst q'
  exact regularCrossing_iff_of_samePresentation R p q

private theorem controlled_ball_of_samePresentation
    {H K : ObservedHistory.{u}} (R : H.SamePresentation K)
    (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier)
    (q : (K.stageAt ⟨t.1, t.2.1, by rw [← R.horizon_eq]; exact t.2.2⟩).Carrier)
    (hpq : HEq q p) (r : ℝ)
    (hball : K.isParabolicallyRmControlledBall
      ⟨t.1, t.2.1, by rw [← R.horizon_eq]; exact t.2.2⟩ q r) :
    H.isParabolicallyRmControlledBall t p r := by
  rcases H with ⟨T, hT, n, times, htimes, hzero, hlast, stages, initialH,
    eventsH, hinitialH, houtputH, finalH, hfinalH⟩
  rcases K with ⟨T', hT', n', times', htimes', hzero', hlast', stages', initialK,
    eventsK, hinitialK, houtputK, finalK, hfinalK⟩
  have hhorizon : T = T' := R.horizon_eq
  subst T'
  have hcount : n = n' := R.count_eq
  subst n'
  have htime : times = times' := funext fun j => R.time_eq j
  subst times'
  have hstage : stages = stages' := funext fun j => R.stage_eq j
  subst stages'
  have hqp : q = p := eq_of_heq hpq
  subst q
  let L : ObservedHistory.{u} :=
    ⟨T, hT, n, times, htimes, hzero, hlast, stages, initialH,
      eventsH, hinitialH, houtputH, finalH, hfinalH⟩
  let K : ObservedHistory.{u} :=
    ⟨T, hT', n, times, htimes', hzero', hlast', stages, initialK,
      eventsK, hinitialK, houtputK, finalK, hfinalK⟩
  change L.SamePresentation K at R
  change K.isParabolicallyRmControlledBall t p r at hball
  change L.isParabolicallyRmControlledBall t p r
  have hmetric (j : Fin (n + 1)) (v : ℝ) (hv : v ∈ L.stageDomain j) :
      L.stageMetric j v = K.stageMetric j v :=
    eq_of_heq (R.metric_heq j v hv)
  obtain ⟨hrpos, a, hat, ha, htraces⟩ := hball
  refine ⟨hrpos, a, hat, ha, ?_⟩
  intro x hx
  have hxK : x ∈ riemannianBallOf (K.stageMetric (K.activeStage t) t) p r := by
    change x ∈ riemannianBallOf (K.stageMetric (L.activeStage t) t) p r
    rw [← hmetric (L.activeStage t) t (L.activeStage_mem t)]
    exact hx
  obtain ⟨A, hA⟩ := htraces x hxK
  let B : BackwardPointTrace L (L.activeStage a) (L.activeStage t)
      (L.activeStage_mono hat) x :=
    { point := fun j hf hl => A.point j hf hl
      endpoint_eq := A.endpoint_eq
      crossing := fun i hf hl =>
        (regularCrossing_iff_of_samePresentation (R.event_eq i) _ _).mpr (A.crossing i hf hl) }
  refine ⟨B, ?_, ?_⟩
  · intro v hav hvt
    change r ^ 4 * normSq0S (L.stageMetric (L.activeStage v) v)
      (A.point (L.activeStage v) (L.activeStage_mono hav) (L.activeStage_mono hvt)) 4
      (metricRm04At (L.stageMetric (L.activeStage v) v)
        (A.point (L.activeStage v) (L.activeStage_mono hav) (L.activeStage_mono hvt))) ≤ 1
    rw [hmetric (L.activeStage v) v (L.activeStage_mem v)]
    exact hA.1 v hav hvt
  · intro i hf hl
    let yL : (L.event i).incoming.terminalRegularOpen :=
      ⟨B.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl),
        (B.crossing i hf hl).mem_terminalRegularRegion (L.event i)⟩
    let yK : (K.event i).incoming.terminalRegularOpen :=
      ⟨A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl),
        (A.crossing i hf hl).mem_terminalRegularRegion (K.event i)⟩
    have hnorm : normSq0S (L.event i).terminal.metric yL 4
        (metricRm04At (L.event i).terminal.metric yL) =
        normSq0S (K.event i).terminal.metric yK 4
          (metricRm04At (K.event i).terminal.metric yK) :=
      terminal_curvature_normSq_eq_of_samePresentation (R.event_eq i)
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) yL.property yK.property
    change r ^ 4 * normSq0S (L.event i).terminal.metric yL 4
      (metricRm04At (L.event i).terminal.metric yL) ≤ 1
    rw [hnorm]
    exact hA.2 i hf hl

private theorem controlled_ball_iff_of_samePresentation
    {H K : ObservedHistory.{u}} (R : H.SamePresentation K)
    (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier)
    (q : (K.stageAt ⟨t.1, t.2.1, by rw [← R.horizon_eq]; exact t.2.2⟩).Carrier)
    (hpq : HEq q p) (r : ℝ) :
    K.isParabolicallyRmControlledBall
      ⟨t.1, t.2.1, by rw [← R.horizon_eq]; exact t.2.2⟩ q r ↔
      H.isParabolicallyRmControlledBall t p r := by
  constructor
  · exact controlled_ball_of_samePresentation R t p q hpq r
  · exact controlled_ball_of_samePresentation R.symm
      ⟨t.1, t.2.1, by rw [← R.horizon_eq]; exact t.2.2⟩ q p hpq.symm r

private def restricted_stage_index (H : ObservedHistory.{u})
    (a : Icc (0 : ℝ) H.horizon) (t : Icc (0 : ℝ) (H.restrict a).horizon)
    (j : Fin (H.eventCount + 1)) (hj : j ≤ H.activeStage (lift_restricted_time H a t)) :
    Fin ((H.restrict a).eventCount + 1) :=
  ⟨j.val, Nat.lt_succ_of_le
    (hj.trans (H.activeStage_mono (show lift_restricted_time H a t ≤ a from t.2.2)))⟩

private theorem restricted_stage_index_first (H : ObservedHistory.{u})
    (a : Icc (0 : ℝ) H.horizon)
    (s t : Icc (0 : ℝ) (H.restrict a).horizon)
    (j : Fin (H.eventCount + 1))
    (hf : H.activeStage (lift_restricted_time H a s) ≤ j)
    (hl : j ≤ H.activeStage (lift_restricted_time H a t)) :
    (H.restrict a).activeStage s ≤ restricted_stage_index H a t j hl := by
  change ((H.restrict a).activeStage s).val ≤ j.val
  exact (congrArg Fin.val (H.restrict_activeStage a s)).trans_le
    (Fin.le_def.mp hf)

private theorem restricted_stage_index_last (H : ObservedHistory.{u})
    (a : Icc (0 : ℝ) H.horizon) (t : Icc (0 : ℝ) (H.restrict a).horizon)
    (j : Fin (H.eventCount + 1))
    (hl : j ≤ H.activeStage (lift_restricted_time H a t)) :
    restricted_stage_index H a t j hl ≤ (H.restrict a).activeStage t := by
  change j.val ≤ ((H.restrict a).activeStage t).val
  exact (Fin.le_def.mp hl).trans_eq
    (congrArg Fin.val (H.restrict_activeStage a t)).symm

private def extend_restricted_trace (H : ObservedHistory.{u})
    (a : Icc (0 : ℝ) H.horizon)
    (s t : Icc (0 : ℝ) (H.restrict a).horizon) (hst : s ≤ t)
    {x : ((H.restrict a).stageAt t).Carrier}
    {x' : (H.stageAt (lift_restricted_time H a t)).Carrier} (hx : HEq x x')
    (A : BackwardPointTrace (H.restrict a) ((H.restrict a).activeStage s)
      ((H.restrict a).activeStage t) ((H.restrict a).activeStage_mono hst) x) :
    BackwardPointTrace H (H.activeStage (lift_restricted_time H a s))
      (H.activeStage (lift_restricted_time H a t)) (H.activeStage_mono (by exact hst)) x' := by
  refine {
    point := fun j hf hl => A.point (restricted_stage_index H a t j hl)
      (restricted_stage_index_first H a s t j hf hl)
      (restricted_stage_index_last H a t j hl)
    endpoint_eq := ?_
    crossing := ?_ }
  · have hi : restricted_stage_index H a t
        (H.activeStage (lift_restricted_time H a t)) le_rfl =
        (H.restrict a).activeStage t :=
      Fin.ext (congrArg Fin.val (H.restrict_activeStage a t)).symm
    exact eq_of_heq ((trace_point_heq_of_index_eq A hi _ _
      ((H.restrict a).activeStage_mono hst) le_rfl).trans
      ((heq_of_eq A.endpoint_eq).trans hx))
  · intro i hf hl
    have ht : H.activeStage (lift_restricted_time H a t) ≤ H.activeStage a :=
      H.activeStage_mono (show lift_restricted_time H a t ≤ a from t.2.2)
    let i' : Fin (H.restrict a).eventCount :=
      ⟨i.val, lt_of_lt_of_le i.castSucc_lt_succ (hl.trans ht)⟩
    have hf' : (H.restrict a).activeStage s ≤ i'.castSucc := by
      change ((H.restrict a).activeStage s).val ≤ i.val
      exact (congrArg Fin.val (H.restrict_activeStage a s)).trans_le
        (Fin.le_def.mp hf)
    have hl' : i'.succ ≤ (H.restrict a).activeStage t := by
      change i.val + 1 ≤ ((H.restrict a).activeStage t).val
      exact (Fin.le_def.mp hl).trans_eq
        (congrArg Fin.val (H.restrict_activeStage a t)).symm
    exact A.crossing i' hf' hl'

private theorem extend_restricted_trace_controlled (H : ObservedHistory.{u})
    (a : Icc (0 : ℝ) H.horizon)
    (s t : Icc (0 : ℝ) (H.restrict a).horizon) (hst : s ≤ t)
    {x : ((H.restrict a).stageAt t).Carrier}
    {x' : (H.stageAt (lift_restricted_time H a t)).Carrier} (hx : HEq x x')
    (A : BackwardPointTrace (H.restrict a) ((H.restrict a).activeStage s)
      ((H.restrict a).activeStage t) ((H.restrict a).activeStage_mono hst) x)
    {r : ℝ} (hA : A.isRmControlled (a := s) (t := t) (hat := hst) r) :
    (extend_restricted_trace H a s t hst hx A).isRmControlled
      (a := lift_restricted_time H a s) (t := lift_restricted_time H a t)
      (hat := by exact hst) r := by
  let B := extend_restricted_trace H a s t hst hx A
  constructor
  · intro v hsv hvt
    let vR : Icc (0 : ℝ) (H.restrict a).horizon :=
      ⟨v.1, v.2.1, hvt.trans t.2.2⟩
    have hp : HEq
        (B.point (H.activeStage v) (H.activeStage_mono hsv) (H.activeStage_mono hvt))
        (A.point ((H.restrict a).activeStage vR)
          ((H.restrict a).activeStage_mono (by exact hsv))
          ((H.restrict a).activeStage_mono (by exact hvt))) := by
      exact trace_point_heq_of_index_eq A
        (Fin.ext (congrArg Fin.val (H.restrict_activeStage a vR)).symm) _ _ _ _
    have hm := curvature_sq_eq_of_metric_heq (H.restrict_stageAt a vR)
      ((H.restrict a).stageMetric ((H.restrict a).activeStage vR) v)
      (H.stageMetric (H.activeStage v) v) (H.restrict_sliceMetric a vR) hp.symm
    change r ^ 4 * normSq0S (H.stageMetric (H.activeStage v) v)
      (B.point (H.activeStage v) (H.activeStage_mono hsv) (H.activeStage_mono hvt)) 4
      (metricRm04At (H.stageMetric (H.activeStage v) v)
        (B.point (H.activeStage v) (H.activeStage_mono hsv) (H.activeStage_mono hvt))) ≤ 1
    rw [← hm]
    exact hA.1 vR hsv hvt
  · intro i hf hl
    have ht : H.activeStage (lift_restricted_time H a t) ≤ H.activeStage a :=
      H.activeStage_mono (show lift_restricted_time H a t ≤ a from t.2.2)
    let i' : Fin (H.restrict a).eventCount :=
      ⟨i.val, lt_of_lt_of_le i.castSucc_lt_succ (hl.trans ht)⟩
    have hf' : (H.restrict a).activeStage s ≤ i'.castSucc := by
      change ((H.restrict a).activeStage s).val ≤ i.val
      exact (congrArg Fin.val (H.restrict_activeStage a s)).trans_le
        (Fin.le_def.mp hf)
    have hl' : i'.succ ≤ (H.restrict a).activeStage t := by
      change i.val + 1 ≤ ((H.restrict a).activeStage t).val
      exact (Fin.le_def.mp hl).trans_eq
        (congrArg Fin.val (H.restrict_activeStage a t)).symm
    exact hA.2 i' hf' hl'

private theorem extended_restricted_controlled_ball (H : ObservedHistory.{u})
    (a : Icc (0 : ℝ) H.horizon) (t : Icc (0 : ℝ) (H.restrict a).horizon)
    (p : ((H.restrict a).stageAt t).Carrier)
    (p' : (H.stageAt (lift_restricted_time H a t)).Carrier) (hp : HEq p p')
    {r : ℝ} (hball : (H.restrict a).isParabolicallyRmControlledBall t p r) :
    H.isParabolicallyRmControlledBall (lift_restricted_time H a t) p' r := by
  obtain ⟨hr, s, hst, hleft, htraces⟩ := hball
  refine ⟨hr, lift_restricted_time H a s, hst, hleft, ?_⟩
  intro x' hx'
  let x := cast_point (H.restrict_stageAt a t).symm x'
  have hxx' : HEq x x' := cast_point_heq (H.restrict_stageAt a t).symm x'
  have hx : x ∈ riemannianBallOf
      ((H.restrict a).stageMetric ((H.restrict a).activeStage t) t) p r :=
    (ball_mem_iff_of_metric_heq (H.restrict_stageAt a t)
      ((H.restrict a).stageMetric ((H.restrict a).activeStage t) t)
      (H.stageMetric (H.activeStage (lift_restricted_time H a t)) t)
      (H.restrict_sliceMetric a t) hp hxx' r).mpr hx'
  obtain ⟨A, hA⟩ := htraces x hx
  exact ⟨extend_restricted_trace H a s t hst hxx' A,
    extend_restricted_trace_controlled H a s t hst hxx' A hA⟩

private theorem controlled_ball_iff_of_prefix
    {H J : ObservedHistory.{u}} (hp : H.IsPrefixOf J)
    (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier)
    (q : (J.stageAt ⟨t.1, t.2.1, t.2.2.trans hp.horizon_le⟩).Carrier)
    (hpq : HEq q p) (r : ℝ) :
    J.isParabolicallyRmControlledBall ⟨t.1, t.2.1, t.2.2.trans hp.horizon_le⟩ q r ↔
      H.isParabolicallyRmControlledBall t p r := by
  let a : Icc (0 : ℝ) J.horizon := ⟨H.horizon, H.horizon_nonneg, hp.horizon_le⟩
  let tR : Icc (0 : ℝ) (J.restrict a).horizon := ⟨t.1, t.2⟩
  let pR := cast_point (hp.presentation.symm.stageAt_eq t) p
  have hpR : HEq pR p := cast_point_heq (hp.presentation.symm.stageAt_eq t) p
  have hRq : HEq pR q := hpR.trans hpq.symm
  have hpres := controlled_ball_iff_of_samePresentation hp.presentation.symm t p pR hpR r
  constructor
  · intro hball
    exact hpres.mp (restricted_controlled_ball J a tR pR q hRq hball)
  · intro hball
    exact extended_restricted_controlled_ball J a tR pR q hRq (hpres.mpr hball)

end GC.GeneralFlow

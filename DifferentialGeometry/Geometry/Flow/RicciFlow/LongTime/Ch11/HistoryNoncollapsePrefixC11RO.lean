import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryPresentation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySlices
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SurvivorChartMetric

set_option autoImplicit false

/-!
# O-CH11-REPROVE-O (G1)：noncollapse 在 same presentation / prefix 下的传递（S6 零件）

S6 `NoncollapseSupply_C11S` 的 astra producer（narrow tuple 的 `hnc` 条款）在 tower 的不同层
`n ≤ m` 之间搬运 `NoncollapsedBefore`：history `n` 是 history `m` 的 prefix，`m` 上已有的
noncollapse 要回到 `n`，`n` 上的 noncollapse 要推到 extension `m` 的早期时刻。astra 的两份文件
`ST/HistoryNoncollapsingPresentation/Basic.lean`、`ST/HistoryNoncollapsePrefix/Basic.lean`
不在 W8 树里（reference-only），这里按其证明思路用树内 API **重证**（新名字，后缀 `_C11RO`）：

* `RetainedCoreHistory.noncollapsedBefore_iff_of_samePresentation_C11RO`：两个 history 有
  `ObservedHistory.SamePresentation` ⇒ `NoncollapsedBefore κ ρ t₀` 等价。W8 的
  `SamePresentation` 在 `time_eq / stage_eq / event_eq / metric_heq` 里带 `Fin.cast`，
  `subst` 之后 `Fin.cast rfl j` 与 `j` definitional（structure eta），所以按 reference 直接 `subst`。
* `RetainedCoreHistory.noncollapsedBefore_of_isPrefixOf_C11RO`：`H.toHistory.IsPrefixOf J.toHistory`、
  `t₀ ≤ H.horizon`、`H.NoncollapsedBefore κ ρ t₀` ⇒ `J.NoncollapsedBefore κ ρ t₀`。证明：在
  `J.restrict ⟨H.horizon, _⟩` 上用上一条，再把 `J` 上的 parabolically controlled ball 限制到
  `J.restrict`（backward trace 沿 `Fin.castLE` 回读，active-stage 与 crossed-terminal 两类曲率
  控制都保留），体积沿 `restrict_sliceMetric` 的 HEq 原样搬回。
astra 只用 prefix ⇒ extension 这一个方向（`SH/PreparedSpatialSurgery.lean:176`、
`SH/CommonScaffoldSurgery.lean:109`、`SN/AffineJoinNoncollapse.lean:71`）。

只用树内类型；没有新结构、没有额外前提。
-/

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-! ## HEq 搬运的小引理 -/

private def castPoint_C11RO {P Q : OrientedThreeStage.{u}} (h : P = Q) (p : P.Carrier) :
    Q.Carrier := h ▸ p

private theorem castPoint_heq_C11RO {P Q : OrientedThreeStage.{u}} (h : P = Q)
    (p : P.Carrier) : HEq (castPoint_C11RO h p) p := by
  cases h
  exact HEq.rfl

private theorem ball_mem_iff_of_metric_heq_C11RO
    {P Q : OrientedThreeStage.{u}} (hP : P = Q) (g : P.Metric) (h : Q.Metric)
    (hg : HEq g h) {p x : P.Carrier} {p' x' : Q.Carrier}
    (hp : HEq p p') (hx : HEq x x') {r : ℝ} :
    x ∈ riemannianBallOf g p r ↔ x' ∈ riemannianBallOf h p' r := by
  cases hP
  cases eq_of_heq hg
  cases eq_of_heq hp
  cases eq_of_heq hx
  rfl

private theorem ball_volume_eq_of_metric_heq_C11RO
    {P Q : OrientedThreeStage.{u}} (hP : P = Q) (g : P.Metric) (h : Q.Metric)
    (hg : HEq g h) {p : P.Carrier} {p' : Q.Carrier} (hp : HEq p p') (r : ℝ) :
    riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g p r) =
      riemannianVolumeMeasure ThreeModel Q.Carrier h (riemannianBallOf h p' r) := by
  cases hP
  cases eq_of_heq hg
  cases eq_of_heq hp
  rfl

private theorem curvature_sq_eq_of_metric_heq_C11RO
    {P Q : OrientedThreeStage.{u}} (hP : P = Q) (g : P.Metric) (h : Q.Metric)
    (hg : HEq g h) {x : P.Carrier} {x' : Q.Carrier} (hx : HEq x x') :
    normSq0S g x 4 (metricRm04At g x) =
      normSq0S h x' 4 (metricRm04At h x') := by
  cases hP
  cases eq_of_heq hg
  cases eq_of_heq hx
  rfl

/-! ## same presentation ⇒ 同一 noncollapse -/

private theorem regularCrossing_iff_of_samePresentation_C11RO
    {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    {E F : MetricCutCapEvent P Q a s} (R : E.SamePresentation F)
    {p : P.Carrier} {q : Q.Carrier} : E.RegularCrossing p q ↔ F.RegularCrossing p q := by
  cases E
  cases F
  cases R.discarded_eq
  cases R.capped_eq
  cases eq_of_heq R.transition_heq
  cases eq_of_heq R.old_heq
  cases eq_of_heq R.oldCharts_heq
  cases eq_of_heq R.oldOutput_heq
  rfl

private theorem curvature_normSq_eq_of_open_eq_C11RO
    {P : OrientedThreeStage.{u}} {U V : TopologicalSpace.Opens P.Carrier}
    (hUV : U = V) (gU : SmoothRiemannianMetric ThreeModel U)
    (gV : SmoothRiemannianMetric ThreeModel V) (hg : HEq gU gV)
    (p : P.Carrier) (hpU : p ∈ U) (hpV : p ∈ V) :
    normSq0S gU ⟨p, hpU⟩ 4 (metricRm04At gU ⟨p, hpU⟩) =
      normSq0S gV ⟨p, hpV⟩ 4 (metricRm04At gV ⟨p, hpV⟩) := by
  cases hUV
  cases eq_of_heq hg
  rfl

private theorem terminal_curvature_normSq_eq_of_samePresentation_C11RO
    {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    {E F : MetricCutCapEvent P Q a s} (R : E.SamePresentation F)
    (p : P.Carrier) (hpE : p ∈ E.incoming.terminalRegularOpen)
    (hpF : p ∈ F.incoming.terminalRegularOpen) :
    normSq0S E.terminal.metric ⟨p, hpE⟩ 4
        (metricRm04At E.terminal.metric ⟨p, hpE⟩) =
      normSq0S F.terminal.metric ⟨p, hpF⟩ 4
        (metricRm04At F.terminal.metric ⟨p, hpF⟩) :=
  curvature_normSq_eq_of_open_eq_C11RO (eq_of_heq R.terminalRegion_heq)
    E.terminal.metric F.terminal.metric R.terminalMetric_heq p hpE hpF

private theorem noncollapsedBefore_of_samePresentation_C11RO
    {H K : RetainedCoreHistory.{u}} (R : H.toHistory.SamePresentation K.toHistory)
    {κ ρ t₀ : ℝ} (hnc : H.NoncollapsedBefore κ ρ t₀) :
    K.NoncollapsedBefore κ ρ t₀ := by
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
  let LH : RetainedCoreHistory.{u} :=
    ⟨T, hT, n, times, htimes, hzero, hlast, stages, initialH,
      eventsH, hinitialH, houtputH, finalH, hfinalH⟩
  let KH : RetainedCoreHistory.{u} :=
    ⟨T, hT', n, times, htimes', hzero', hlast', stages, initialK,
      eventsK, hinitialK, houtputK, finalK, hfinalK⟩
  let L := LH.toHistory
  let K := KH.toHistory
  change L.SamePresentation K at R
  change LH.NoncollapsedBefore κ ρ t₀ at hnc
  change KH.NoncollapsedBefore κ ρ t₀
  have hmetric (j : Fin (n + 1)) (v : ℝ) (hv : v ∈ L.stageDomain j) :
      L.stageMetric j v = K.stageMetric j v :=
    eq_of_heq (R.metric_heq j v hv)
  intro t p r ht hr hball
  have hballL : L.isParabolicallyRmControlledBall t p r := by
    obtain ⟨hrpos, a, hat, ha, htraces⟩ := hball
    refine ⟨hrpos, a, hat, ha, ?_⟩
    intro x hx
    have hxK : x ∈ riemannianBallOf (K.stageMetric (K.activeStage t) t) p r := by
      have hm := hmetric (L.activeStage t) t (L.activeStage_mem t)
      change x ∈ riemannianBallOf (K.stageMetric (L.activeStage t) t) p r
      rw [← hm]
      exact hx
    obtain ⟨A, hA⟩ := htraces x hxK
    let B : BackwardPointTrace L (L.activeStage a) (L.activeStage t)
        (L.activeStage_mono hat) x :=
      { point := fun j hf hl => A.point j hf hl
        endpoint_eq := A.endpoint_eq
        crossing := fun i hf hl =>
          (regularCrossing_iff_of_samePresentation_C11RO (R.event_eq i)).mpr
            (A.crossing i hf hl) }
    refine ⟨B, ?_, ?_⟩
    · intro s has hst
      change r ^ 4 * normSq0S (L.stageMetric (L.activeStage s) s)
        (A.point (L.activeStage s) (L.activeStage_mono has) (L.activeStage_mono hst)) 4
        (metricRm04At (L.stageMetric (L.activeStage s) s)
          (A.point (L.activeStage s) (L.activeStage_mono has) (L.activeStage_mono hst))) ≤ 1
      rw [hmetric (L.activeStage s) s (L.activeStage_mem s)]
      exact hA.1 s has hst
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
        terminal_curvature_normSq_eq_of_samePresentation_C11RO (R.event_eq i)
          (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) yL.property yK.property
      change r ^ 4 * normSq0S (L.event i).terminal.metric yL 4
        (metricRm04At (L.event i).terminal.metric yL) ≤ 1
      rw [hnorm]
      exact hA.2 i hf hl
  have hvolume := hnc t p r ht hr hballL
  rw [hmetric (L.activeStage t) t (L.activeStage_mem t)] at hvolume
  exact hvolume

/-! ## restrict：controlled ball 从 `H` 限制到 `H.restrict a` -/

private theorem trace_point_heq_of_index_eq_C11RO
    {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
    {p : (H.stage last).Carrier} (A : BackwardPointTrace H first last hle p)
    {j k : Fin (H.eventCount + 1)} (hjk : j = k)
    (hjf : first ≤ j) (hjl : j ≤ last) (hkf : first ≤ k) (hkl : k ≤ last) :
    HEq (A.point j hjf hjl) (A.point k hkf hkl) := by
  cases hjk
  exact HEq.rfl

private def liftRestrictedTime_C11RO (H : ObservedHistory.{u})
    (a : Icc (0 : ℝ) H.horizon) (t : Icc (0 : ℝ) (H.restrict a).horizon) :
    Icc (0 : ℝ) H.horizon := ⟨t.1, t.2.1, t.2.2.trans a.2.2⟩

private def restrictTrace_C11RO (H : ObservedHistory.{u}) (a : Icc (0 : ℝ) H.horizon)
    (s t : Icc (0 : ℝ) (H.restrict a).horizon) (hst : s ≤ t)
    {x : ((H.restrict a).stageAt t).Carrier}
    {x' : (H.stageAt (liftRestrictedTime_C11RO H a t)).Carrier} (hx : HEq x x')
    (A : BackwardPointTrace H (H.activeStage (liftRestrictedTime_C11RO H a s))
      (H.activeStage (liftRestrictedTime_C11RO H a t))
      (H.activeStage_mono (by exact hst)) x') :
    BackwardPointTrace (H.restrict a) ((H.restrict a).activeStage s)
      ((H.restrict a).activeStage t) ((H.restrict a).activeStage_mono hst) x := by
  let cast : Fin ((H.restrict a).eventCount + 1) → Fin (H.eventCount + 1) :=
    Fin.castLE (Nat.add_le_add_right (Nat.le_of_lt_succ (H.activeStage a).isLt) 1)
  have hs : cast ((H.restrict a).activeStage s) =
      H.activeStage (liftRestrictedTime_C11RO H a s) := H.restrict_activeStage a s
  have ht : cast ((H.restrict a).activeStage t) =
      H.activeStage (liftRestrictedTime_C11RO H a t) := H.restrict_activeStage a t
  have hfirst (j : Fin ((H.restrict a).eventCount + 1))
      (hj : (H.restrict a).activeStage s ≤ j) :
      H.activeStage (liftRestrictedTime_C11RO H a s) ≤ cast j := by
    rw [← hs]
    exact hj
  have hlast (j : Fin ((H.restrict a).eventCount + 1))
      (hj : j ≤ (H.restrict a).activeStage t) :
      cast j ≤ H.activeStage (liftRestrictedTime_C11RO H a t) := by
    rw [← ht]
    exact hj
  refine {
    point := fun j hf hl => A.point (cast j) (hfirst j hf) (hlast j hl)
    endpoint_eq := ?_
    crossing := ?_ }
  · exact eq_of_heq ((trace_point_heq_of_index_eq_C11RO A ht
      (hfirst _ ((H.restrict a).activeStage_mono hst)) (hlast _ le_rfl)
      (H.activeStage_mono (by exact hst)) le_rfl).trans
      ((heq_of_eq A.endpoint_eq).trans hx.symm))
  · intro i hf hl
    exact A.crossing (Fin.castLE (Nat.le_of_lt_succ (H.activeStage a).isLt) i)
      (hfirst i.castSucc hf) (hlast i.succ hl)

private theorem restrictTrace_controlled_C11RO (H : ObservedHistory.{u})
    (a : Icc (0 : ℝ) H.horizon) (s t : Icc (0 : ℝ) (H.restrict a).horizon) (hst : s ≤ t)
    {x : ((H.restrict a).stageAt t).Carrier}
    {x' : (H.stageAt (liftRestrictedTime_C11RO H a t)).Carrier} (hx : HEq x x')
    (A : BackwardPointTrace H (H.activeStage (liftRestrictedTime_C11RO H a s))
      (H.activeStage (liftRestrictedTime_C11RO H a t))
      (H.activeStage_mono (by exact hst)) x')
    {r : ℝ}
    (hA : A.isRmControlled (a := liftRestrictedTime_C11RO H a s)
      (t := liftRestrictedTime_C11RO H a t) (hat := by exact hst) r) :
    (restrictTrace_C11RO H a s t hst hx A).isRmControlled (a := s) (t := t) (hat := hst) r := by
  let B := restrictTrace_C11RO H a s t hst hx A
  let cast : Fin ((H.restrict a).eventCount + 1) → Fin (H.eventCount + 1) :=
    Fin.castLE (Nat.add_le_add_right (Nat.le_of_lt_succ (H.activeStage a).isLt) 1)
  constructor
  · intro v hsv hvt
    have hp : HEq
        (B.point ((H.restrict a).activeStage v)
          ((H.restrict a).activeStage_mono hsv) ((H.restrict a).activeStage_mono hvt))
        (A.point (H.activeStage (liftRestrictedTime_C11RO H a v))
          (H.activeStage_mono (by exact hsv)) (H.activeStage_mono (by exact hvt))) :=
      trace_point_heq_of_index_eq_C11RO A (H.restrict_activeStage a v)
        (by rw [H.restrict_activeStage a v]; exact H.activeStage_mono (by exact hsv))
        (by rw [H.restrict_activeStage a v]; exact H.activeStage_mono (by exact hvt))
        (H.activeStage_mono (by exact hsv)) (H.activeStage_mono (by exact hvt))
    have hm := curvature_sq_eq_of_metric_heq_C11RO (H.restrict_stageAt a v)
      ((H.restrict a).stageMetric ((H.restrict a).activeStage v) v)
      (H.stageMetric (H.activeStage (liftRestrictedTime_C11RO H a v)) v)
      (H.restrict_sliceMetric a v) hp
    change r ^ 4 * normSq0S ((H.restrict a).stageMetric ((H.restrict a).activeStage v) v)
      (B.point ((H.restrict a).activeStage v)
        ((H.restrict a).activeStage_mono hsv) ((H.restrict a).activeStage_mono hvt)) 4
      (metricRm04At ((H.restrict a).stageMetric ((H.restrict a).activeStage v) v)
        (B.point ((H.restrict a).activeStage v)
          ((H.restrict a).activeStage_mono hsv) ((H.restrict a).activeStage_mono hvt))) ≤ 1
    rw [hm]
    exact hA.1 (liftRestrictedTime_C11RO H a v) hsv hvt
  · intro i hf hl
    have hs : cast ((H.restrict a).activeStage s) =
        H.activeStage (liftRestrictedTime_C11RO H a s) := H.restrict_activeStage a s
    have ht : cast ((H.restrict a).activeStage t) =
        H.activeStage (liftRestrictedTime_C11RO H a t) := H.restrict_activeStage a t
    have hf' : H.activeStage (liftRestrictedTime_C11RO H a s) ≤ cast i.castSucc := by
      rw [← hs]
      exact hf
    have hl' : cast i.succ ≤ H.activeStage (liftRestrictedTime_C11RO H a t) := by
      rw [← ht]
      exact hl
    exact hA.2 (Fin.castLE (Nat.le_of_lt_succ (H.activeStage a).isLt) i) hf' hl'

private theorem restrictedControlledBall_C11RO (H : ObservedHistory.{u})
    (a : Icc (0 : ℝ) H.horizon) (t : Icc (0 : ℝ) (H.restrict a).horizon)
    (p : ((H.restrict a).stageAt t).Carrier)
    (p' : (H.stageAt (liftRestrictedTime_C11RO H a t)).Carrier) (hp : HEq p p')
    {r : ℝ}
    (hball : H.isParabolicallyRmControlledBall (liftRestrictedTime_C11RO H a t) p' r) :
    (H.restrict a).isParabolicallyRmControlledBall t p r := by
  obtain ⟨hr, s, hst, hleft, htraces⟩ := hball
  let s' : Icc (0 : ℝ) (H.restrict a).horizon :=
    ⟨s.1, s.2.1, hst.trans t.2.2⟩
  have hs't : s' ≤ t := hst
  refine ⟨hr, s', hs't, hleft, ?_⟩
  intro x hx
  let x' := castPoint_C11RO (H.restrict_stageAt a t) x
  have hxx' : HEq x x' := (castPoint_heq_C11RO (H.restrict_stageAt a t) x).symm
  have hx' : x' ∈ riemannianBallOf
      (H.stageMetric (H.activeStage (liftRestrictedTime_C11RO H a t)) t) p' r :=
    (ball_mem_iff_of_metric_heq_C11RO (H.restrict_stageAt a t)
      ((H.restrict a).stageMetric ((H.restrict a).activeStage t) t)
      (H.stageMetric (H.activeStage (liftRestrictedTime_C11RO H a t)) t)
      (H.restrict_sliceMetric a t) hp hxx' (r := r)).mp hx
  obtain ⟨A, hA⟩ := htraces x' hx'
  exact ⟨restrictTrace_C11RO H a s' t hs't hxx' A,
    restrictTrace_controlled_C11RO H a s' t hs't hxx' A hA⟩

namespace RetainedCoreHistory

/-- same presentation 的两个 retained-core history 有同样的 `NoncollapsedBefore`。 -/
theorem noncollapsedBefore_iff_of_samePresentation_C11RO
    {H K : RetainedCoreHistory.{u}} (R : H.toHistory.SamePresentation K.toHistory)
    {κ ρ t₀ : ℝ} : H.NoncollapsedBefore κ ρ t₀ ↔ K.NoncollapsedBefore κ ρ t₀ :=
  ⟨noncollapsedBefore_of_samePresentation_C11RO R,
    noncollapsedBefore_of_samePresentation_C11RO R.symm⟩

/-- **prefix ⇒ extension**：`H` 是 `J` 的 prefix 且 `t₀ ≤ H.horizon` 时，`H` 上的
`NoncollapsedBefore κ ρ t₀` 推出 `J` 上的同一条（早期 ball 的曲率控制在 `J.restrict` 上保留）。 -/
theorem noncollapsedBefore_of_isPrefixOf_C11RO
    {H J : RetainedCoreHistory.{u}} (hp : H.toHistory.IsPrefixOf J.toHistory)
    {κ ρ t₀ : ℝ} (ht : t₀ ≤ H.horizon) (hnc : H.NoncollapsedBefore κ ρ t₀) :
    J.NoncollapsedBefore κ ρ t₀ := by
  let a : Icc (0 : ℝ) J.horizon := ⟨H.horizon, H.horizon_nonneg, hp.horizon_le⟩
  let R := J.restrict a
  have hncR : R.NoncollapsedBefore κ ρ t₀ :=
    (noncollapsedBefore_iff_of_samePresentation_C11RO (H := R) (K := H)
      hp.presentation).mpr hnc
  intro t p r htt hr hball
  let tR : Icc (0 : ℝ) R.horizon := ⟨t.1, t.2.1, htt.trans ht⟩
  have hstage : (R.toHistory.stageAt tR) = J.toHistory.stageAt t :=
    J.toHistory.restrict_stageAt a tR
  let pR := castPoint_C11RO hstage.symm p
  have hpR : HEq pR p := castPoint_heq_C11RO hstage.symm p
  have hballR : R.toHistory.isParabolicallyRmControlledBall tR pR r :=
    restrictedControlledBall_C11RO J.toHistory a tR pR p hpR hball
  have hv := hncR tR pR r htt hr hballR
  exact hv.trans_eq (ball_volume_eq_of_metric_heq_C11RO hstage
    (R.toHistory.stageMetric (R.toHistory.activeStage tR) tR)
    (J.toHistory.stageMetric (J.toHistory.activeStage t) t)
    (J.toHistory.restrict_sliceMetric a tR) hpR r)

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

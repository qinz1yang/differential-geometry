import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeRayNeckC11SP

set_option autoImplicit false

/-!
# G3：跨 tower 号的 slice ↔ tower 桥（O-CH11-NATIVE-RAYNECK，后缀 `_C11SP`）

补树内缺的 API：沿 `ObservedHistory.SamePresentation` 运输 `isTracedRegion`。
* `regularCrossing_of_samePresentation_C11SP`：`MetricCutCapEvent.SamePresentation` 保持
  RegularCrossing（只依赖 `old` / `oldCharts` / `oldOutput`；`oldSmooth` 是 Prop）。
* `terminal_normSq_of_samePresentation_C11SP`：terminal metric 的 `Rm` 范数在同一点不变。
* `isTracedRegion_of_samePresentation_C11SP`：history 级运输（结构拆开后 time / stage / initialMetric
  逐个 subst，事件只用 SamePresentation，stageMetric 只用 `metric_heq` 在 `stageDomain` 上）。
* `sliceTowerTraceAt_C11SP`（**PROVED**）：G1 合同 `SliceTowerTraceAt_C11SP` 对任意 tower 号成立
  （`⌈t⌉` 号 G1 → `ObservationTower.integer_restrict` → restrict API）。G1 的 repair target 由此关闭。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle

namespace GC.LongTime.Ch11

universe u

/-- `MetricCutCapEvent.SamePresentation` 保持 RegularCrossing（只依赖 `old` / charts / `oldOutput`）。 -/
theorem regularCrossing_of_samePresentation_C11SP
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    {E : MetricCutCapEvent P Q a s} {F : MetricCutCapEvent P' Q' a' s'}
    (R : E.SamePresentation F) {p : P.Carrier} {q : Q.Carrier} {p' : P'.Carrier}
    {q' : Q'.Carrier} (hp : HEq p p') (hq : HEq q q') (h : E.RegularCrossing p q) :
    F.RegularCrossing p' q' := by
  obtain ⟨hP, hQ, ha, hs, hdis, hcap, htr, -, -, -, -, hold, hch, -, hout⟩ := R
  subst hP hQ ha hs
  cases hp
  cases hq
  cases E
  cases F
  dsimp only at hdis hcap htr hold hch hout
  subst hdis hcap
  cases htr
  cases hold
  cases hch
  cases hout
  exact h

/-- terminal metric 的 `Rm` 范数在 SamePresentation 下不变（同一物理点）。 -/
theorem terminal_normSq_of_samePresentation_C11SP
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    {E : MetricCutCapEvent P Q a s} {F : MetricCutCapEvent P' Q' a' s'}
    (R : E.SamePresentation F) (x : E.incoming.terminalRegularOpen)
    (x' : F.incoming.terminalRegularOpen) (hx : HEq x.1 x'.1) :
    normSq0S E.terminal.metric x 4 (metricRm04At E.terminal.metric x) =
      normSq0S F.terminal.metric x' 4 (metricRm04At F.terminal.metric x') := by
  obtain ⟨hP, hQ, ha, hs, -, -, -, -, hreg, hmet, -, -, -, -, -⟩ := R
  subst hP hQ ha hs
  obtain ⟨x, hxU⟩ := x
  obtain ⟨x', hxU'⟩ := x'
  cases hx
  revert hxU hxU'
  generalize E.terminal.metric = gE at hmet ⊢
  generalize F.terminal.metric = gF at hmet ⊢
  revert gE gF
  generalize E.incoming.terminalRegularOpen = UE at hreg ⊢
  generalize F.incoming.terminalRegularOpen = UF at hreg ⊢
  cases hreg
  intro gE gF hmet _ _
  cases hmet
  rfl

/-- **跨 `ObservedHistory.SamePresentation` 运输 traced region**（树内缺的 API）。 -/
theorem isTracedRegion_of_samePresentation_C11SP {H K : ObservedHistory.{u}}
    (R : H.SamePresentation K) (t : Icc (0 : ℝ) H.horizon) (t' : Icc (0 : ℝ) K.horizon)
    (htt : (t : ℝ) = t') (p : (H.stageAt t).Carrier) (p' : (K.stageAt t').Carrier)
    (hp : HEq p p') {ρ τ C : ℝ} (h : H.isTracedRegion t p ρ τ C) :
    K.isTracedRegion t' p' ρ τ C := by
  obtain ⟨hor, hnn, n, time, tsm, tz, tlh, stage, im, ev, ei, eo, fs, fi⟩ := H
  obtain ⟨hor', hnn', n', time', tsm', tz', tlh', stage', im', ev', ei', eo', fs', fi'⟩ := K
  obtain ⟨hh, hc, ht, hst, hi, he, hm⟩ := R
  dsimp only at hh hc
  subst hh hc
  have htime : time = time' := funext fun j => ht j
  subst htime
  have hstage : stage = stage' := funext fun j => hst j
  subst hstage
  have him : im = im' := funext fun j => eq_of_heq (hi j)
  subst him
  have htt' : t = t' := Subtype.ext htt
  subst htt'
  have hpp : p = p' := eq_of_heq hp
  subst hpp
  obtain ⟨hρ, hτ, a, hat, ha, htr⟩ := h
  refine ⟨hρ, hτ, a, hat, ha, fun x hx => ?_⟩
  have hx' := (Ch12.metricBall_heq_CX2 rfl (hm _ t.1 (ObservedHistory.activeStage_mem _ t))
    HEq.rfl HEq.rfl ρ).mpr hx
  obtain ⟨A, hA⟩ := htr x hx'
  refine ⟨BackwardPointTrace.mk A.point A.endpoint_eq (fun i hf hl =>
      regularCrossing_of_samePresentation_C11SP (he i) HEq.rfl HEq.rfl (A.crossing i hf hl)),
    fun s has hst => ?_, fun i hf hl => ?_⟩
  · exact (le_of_eq (Ch12.rmNormSq_heq_CX2 rfl (hm _ s.1 (ObservedHistory.activeStage_mem _ s))
      HEq.rfl).symm).trans (hA.1 s has hst)
  · exact (le_of_eq (terminal_normSq_of_samePresentation_C11SP (he i)
      ⟨A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl),
        (A.crossing i hf hl).mem_terminalRegularRegion _⟩ _ HEq.rfl).symm).trans
      (hA.2 i hf hl)

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- **G3（PROVED）**：G1 精确桥合同对**任意** tower 号 `k`（`t ≤ k` 自动给 `⌈s.time⌉ ≤ k`）成立：
`⌈t⌉` 号（G1）→ `integer_restrict` 的 SamePresentation 运输 → restrict API。 -/
theorem sliceTowerTraceAt_C11SP (F : GC.Interface.RawSurgery P g)
    (s : RegularSlice F.observation) (k : ℕ)
    (t : Icc (0 : ℝ) (F.tower.history k).toHistory.horizon) (ht : (t : ℝ) = s.time) :
    SliceTowerTraceAt_C11SP F s k t := by
  let c : ℕ := Nat.ceil s.time
  let Hk : ObservedHistory.{u} := (F.tower.history k).toHistory
  let Hc : ObservedHistory.{u} := (F.tower.history c).toHistory
  have hkH : Hk.horizon = (k : ℝ) := F.observation.horizon_eq k
  have hcH : Hc.horizon = (c : ℝ) := F.observation.horizon_eq c
  have hck : c ≤ k := by
    apply Nat.ceil_le.mpr
    rw [← ht]
    exact t.2.2.trans hkH.le
  let u : Icc (0 : ℝ) Hk.horizon := ⟨(c : ℝ), Nat.cast_nonneg c, by rw [hkH]; exact_mod_cast hck⟩
  have R1 : (Hk.restrict u).SamePresentation Hc := F.observation.integer_restrict c k hck
  let tc : Icc (0 : ℝ) Hc.horizon := ⟨s.time, s.positive.le, by rw [hcH]; exact Nat.le_ceil _⟩
  let tu : Icc (0 : ℝ) (Hk.restrict u).horizon := ⟨s.time, s.positive.le, Nat.le_ceil _⟩
  have htu : t = ⟨tu.1, tu.2.1, tu.2.2.trans u.2.2⟩ := Subtype.ext ht
  subst htu
  obtain ⟨hZc, hMc, hTc⟩ := sliceTowerTraceAt_ceil_C11SP F s c rfl tc rfl
  have hZ2 : Hc.stageAt tc = (Hk.restrict u).stageAt tu := R1.symm.stageAt_eq tc
  have hZ3 : (Hk.restrict u).stageAt tu = Hk.stageAt ⟨tu.1, tu.2.1, tu.2.2.trans u.2.2⟩ :=
    Hk.restrict_stageAt u tu
  refine ⟨hZc.trans (hZ2.trans hZ3), ?_, ?_⟩
  · exact hMc.trans ((R1.symm.sliceMetric_heq tc).trans (Hk.restrict_sliceMetric u tu))
  · intro x y hxy ρ τ K htr
    let yc : (Hc.stageAt tc).Carrier := cast (congrArg OrientedThreeStage.Carrier hZc) x
    have hyc : HEq yc x := cast_heq _ _
    have hc_tr := hTc x yc hyc.symm ρ τ K htr
    let yu : ((Hk.restrict u).stageAt tu).Carrier :=
      cast (congrArg OrientedThreeStage.Carrier hZ2) yc
    have hyu : HEq yu yc := cast_heq _ _
    have hu_tr := isTracedRegion_of_samePresentation_C11SP R1.symm tc tu rfl yc yu hyu.symm hc_tr
    have hk_tr := (Ch12.isTracedRegion_restrict_iff_CX2 Hk u tu yu ρ τ K).mp hu_tr
    have hy : Ch12.restrictPoint_CX2 Hk u tu yu = y :=
      eq_of_heq ((Ch12.restrictPoint_heq_CX2 Hk u tu yu).trans (hyu.trans (hyc.trans hxy)))
    rw [hy] at hk_tr
    exact hk_tr

/-- consumer：G2 的 `hbr` 退为"`t` 是 RegularSlice 时刻"（桥对任意 tower 号由本 G3 支付）。 -/
theorem sliceTowerTraceAt_seq_C11SP (F : GC.Interface.RawSurgery P g) (idx : ℕ → ℕ)
    (t : ∀ i, Icc (0 : ℝ) (F.tower.history (idx i)).toHistory.horizon)
    (sl : ℕ → RegularSlice F.observation) (hsl : ∀ i, (sl i).time = (t i : ℝ)) :
    ∀ i, SliceTowerTraceAt_C11SP F (sl i) (idx i) (t i) :=
  fun i => sliceTowerTraceAt_C11SP F (sl i) (idx i) (t i) (hsl i).symm

end GC.LongTime.Ch11

end

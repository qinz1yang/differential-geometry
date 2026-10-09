import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceHistoryBridgeP6M
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.EndpointAssemblyC11G
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.SliceRecords_P6N

/-!
# P6 prefix transport G1/G2：K0 / pinching / records 沿 `K.eventPrefix j T`（`_C11G2`）

K-route 的 `E := K.eventPrefix j T = (K.prefixAt j.castSucc).extendHorizon T …` 与 `K` 在
`[0, T] ⊆ (time j.castSucc, time j.succ)` 上有**相同**的 stage / metric / event（`Fin.castLE` 指标；
树内 `eventPrefix_activeStage_val` / `eventPrefix_stageMetric`）。本文件把 P6GEO
`exists_hgeom_of_K0_pinching_C11G` 在 `Hs := E.toHistory` 上要的三类 K 层输入搬到 E：

* **trace 限制**（G1 的底层）`exists_eventPrefixTrace_C11G2`：K 的 trace（stage 指标 `f' = eIdx f`、
  `l' = eIdx l`）⇒ E 的 trace（`point` 逐点相等）；K 层 `K.activeStage a'` 与 E 层
  `eIdx (E.activeStage a)` 只是命题等（`Fin.ext eventPrefix_activeStage_val`），经 `subst` 对齐。
* **G1 K0** `hasSmallParabolicCurvature_eventPrefix_C11G2`：K 的 `hasSmallParabolicCurvature`（中心 `p'`、
  时刻 `τ'`）⇒ E 的同形（`HEq` 中心、同一实时刻 `τ ≤ T`）。球成员用树内 `mem_ball_of_eventPrefix_P6M`，
  trace 用上面的限制，`isRmControlled` 逐 stage / 逐 event 搬运（stage 指标 `subst`）。
* **G1 pinching** `inFixedHI_eventPrefix_C11G2`：Pre841 native 形 `InFixedHamiltonIveyRegion`
  （`K.activeStage τ'` 包装）⇒ E 的同形（`τ ≤ T`；`inFixedHI_stage_C11G` + `eventPrefix_stageMetric`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

variable (K : RetainedCoreHistory.{u})

/-- E 的 stage 指标 ↦ K 的 stage 指标（`Fin.castLE`；与 `eventPrefix_stageMetric` 同一写法）。 -/
abbrev eIdx_C11G2 (j : Fin K.eventCount) {T : ℝ} (hjT : K.time j.castSucc < T)
    (hTj : T < K.time j.succ)
    (m : Fin ((K.eventPrefix j T hjT hTj).toHistory.eventCount + 1)) : Fin (K.eventCount + 1) :=
  Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt)) m

theorem eIdx_mono_C11G2 (j : Fin K.eventCount) {T : ℝ} (hjT : K.time j.castSucc < T)
    (hTj : T < K.time j.succ)
    {f m : Fin ((K.eventPrefix j T hjT hTj).toHistory.eventCount + 1)} (h : f ≤ m) :
    K.eIdx_C11G2 j hjT hTj f ≤ K.eIdx_C11G2 j hjT hTj m :=
  Fin.le_def.mpr (Fin.le_def.mp h)

/-- **trace 限制（`_C11G2`）**：K 的 trace（stage 指标 `f' = eIdx f`、`l' = eIdx l`，端点 `HEq`）
⇒ E 的 trace，`point` 逐点相等（`subst` 对齐 K 层 `K.activeStage a'` 与 E 层 `eIdx (E.activeStage a)`
的命题等）。 -/
theorem exists_eventPrefixTrace_C11G2 (j : Fin K.eventCount) {T : ℝ}
    (hjT : K.time j.castSucc < T) (hTj : T < K.time j.succ)
    {f l : Fin ((K.eventPrefix j T hjT hTj).toHistory.eventCount + 1)}
    {f' l' : Fin (K.eventCount + 1)} (hf : f' = K.eIdx_C11G2 j hjT hTj f)
    (hl : l' = K.eIdx_C11G2 j hjT hTj l) {hle : f ≤ l} {hle' : f' ≤ l'}
    {x : ((K.eventPrefix j T hjT hTj).toHistory.stage l).Carrier}
    {x' : (K.toHistory.stage l').Carrier} (hx : HEq x x')
    (A' : BackwardPointTrace K.toHistory f' l' hle' x') :
    ∃ A : BackwardPointTrace (K.eventPrefix j T hjT hTj).toHistory f l hle x,
      ∀ (m : Fin ((K.eventPrefix j T hjT hTj).toHistory.eventCount + 1)) (h1 : f ≤ m) (h2 : m ≤ l)
        (h1' : f' ≤ K.eIdx_C11G2 j hjT hTj m) (h2' : K.eIdx_C11G2 j hjT hTj m ≤ l'),
        A.point m h1 h2 = A'.point (K.eIdx_C11G2 j hjT hTj m) h1' h2' := by
  subst hf hl
  obtain rfl := eq_of_heq hx
  refine ⟨{
      point := fun m h1 h2 => A'.point (K.eIdx_C11G2 j hjT hTj m)
        (K.eIdx_mono_C11G2 j hjT hTj h1) (K.eIdx_mono_C11G2 j hjT hTj h2)
      endpoint_eq := A'.endpoint_eq
      crossing := fun i hf hl => A'.crossing (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i)
        (K.eIdx_mono_C11G2 j hjT hTj hf) (K.eIdx_mono_C11G2 j hjT hTj hl) }, ?_⟩
  intro m h1 h2 h1' h2'
  rfl

/-- stage 指标推广（`m' = m`）：`r⁴ |Rm|² ≤ 1` 在两种指标写法间搬运。 -/
private theorem rm_bound_congr_C11G2 {H : ObservedHistory.{u}}
    {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {x : (H.stage last).Carrier}
    (B : BackwardPointTrace H first last hle x) {m m' : Fin (H.eventCount + 1)} (hm : m' = m)
    (h1 : first ≤ m) (h2 : m ≤ last) (h1' : first ≤ m') (h2' : m' ≤ last) (v r : ℝ)
    (h : r ^ 4 * normSq0S (H.stageMetric m' v) (B.point m' h1' h2') 4
      (metricRm04At (H.stageMetric m' v) (B.point m' h1' h2')) ≤ 1) :
    r ^ 4 * normSq0S (H.stageMetric m v) (B.point m h1 h2) 4
      (metricRm04At (H.stageMetric m v) (B.point m h1 h2)) ≤ 1 := by
  subst hm
  exact h

/-- **G1：K0 沿 eventPrefix（`_C11G2`）**：K 的 `hasSmallParabolicCurvature`（中心 `p'`、时刻 `τ'`、
半径 `r`）⇒ E 的同形（`HEq` 中心、同一实时刻 `τ ≤ T`）。球成员用 `mem_ball_of_eventPrefix_P6M`，
trace 用 `exists_eventPrefixTrace_C11G2`，`isRmControlled` 逐 stage / 逐 event 搬运。 -/
theorem hasSmallParabolicCurvature_eventPrefix_C11G2 (j : Fin K.eventCount) {T : ℝ}
    (hjT : K.time j.castSucc < T) (hTj : T < K.time j.succ)
    (τ : Icc (0 : ℝ) (K.eventPrefix j T hjT hTj).toHistory.horizon)
    (τ' : Icc (0 : ℝ) K.toHistory.horizon) (hττ : (τ : ℝ) = τ')
    (p : ((K.eventPrefix j T hjT hTj).toHistory.stageAt τ).Carrier)
    (p' : (K.toHistory.stageAt τ').Carrier) (hp : HEq p p') {r : ℝ}
    (h : GC.LongTime.hasSmallParabolicCurvature K.toHistory τ' p' r) :
    GC.LongTime.hasSmallParabolicCurvature (K.eventPrefix j T hjT hTj).toHistory τ p r := by
  obtain ⟨hr, a', hat', hclock', htr⟩ := h
  have hτT : (τ : ℝ) ≤ T := τ.2.2
  have ha'T : (a' : ℝ) ≤ T :=
    (show (a' : ℝ) ≤ τ' from hat').trans (by rw [← hττ]; exact hτT)
  let a : Icc (0 : ℝ) (K.eventPrefix j T hjT hTj).toHistory.horizon := ⟨a', a'.2.1, ha'T⟩
  have hat : a ≤ τ := show (a' : ℝ) ≤ τ by rw [hττ]; exact hat'
  refine ⟨hr, a, hat, ?_, ?_⟩
  · change (a' : ℝ) = (τ : ℝ) - r ^ 2
    rw [hττ]
    exact hclock'
  intro x hx
  have hAτ := K.eventPrefix_activeStage_val j hjT hTj τ τ' hττ
  have hAa := K.eventPrefix_activeStage_val j hjT hTj a a' rfl
  have hl : K.toHistory.activeStage τ' = K.eIdx_C11G2 j hjT hTj
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ) := Fin.ext hAτ.symm
  have hf : K.toHistory.activeStage a' = K.eIdx_C11G2 j hjT hTj
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage a) := Fin.ext hAa.symm
  let x' : (K.toHistory.stageAt τ').Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hl.symm) x
  have hxx : HEq x x' := (cast_heq _ _).symm
  have hx' := K.mem_ball_of_eventPrefix_P6M j hjT hTj τ τ' hττ p x p' x' hp hxx r hx
  obtain ⟨A', hA'⟩ := htr x' hx'
  obtain ⟨A, hApt⟩ := K.exists_eventPrefixTrace_C11G2 j hjT hTj hf hl
    (hle := (K.eventPrefix j T hjT hTj).toHistory.activeStage_mono hat)
    (hle' := K.toHistory.activeStage_mono hat') hxx A'
  refine ⟨A, ?_, ?_⟩
  · intro s has hst
    have hsT : (s : ℝ) ≤ T := s.2.2
    have hTH : T ≤ K.horizon := hTj.le.trans (K.toHistory.time_le_horizon_at j.succ)
    let s' : Icc (0 : ℝ) K.toHistory.horizon := ⟨s, s.2.1, hsT.trans hTH⟩
    have hAs := K.eventPrefix_activeStage_val j hjT hTj s s' rfl
    have hs : K.toHistory.activeStage s' = K.eIdx_C11G2 j hjT hTj
        ((K.eventPrefix j T hjT hTj).toHistory.activeStage s) := Fin.ext hAs.symm
    have h1' : a' ≤ s' := show (a' : ℝ) ≤ s from has
    have h2' : s' ≤ τ' := show (s : ℝ) ≤ τ' by rw [← hττ]; exact hst
    have hb := hA'.1 s' h1' h2'
    have hM1 : K.toHistory.activeStage a' ≤ K.eIdx_C11G2 j hjT hTj
        ((K.eventPrefix j T hjT hTj).toHistory.activeStage s) :=
      hf.le.trans (K.eIdx_mono_C11G2 j hjT hTj
        ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono has))
    have hM2 : K.eIdx_C11G2 j hjT hTj ((K.eventPrefix j T hjT hTj).toHistory.activeStage s) ≤
        K.toHistory.activeStage τ' :=
      (K.eIdx_mono_C11G2 j hjT hTj
        ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono hst)).trans hl.symm.le
    have hb' := rm_bound_congr_C11G2 A' hs hM1 hM2
      (K.toHistory.activeStage_mono h1') (K.toHistory.activeStage_mono h2') s (Real.sqrt 3 * r) hb
    rw [hApt _ ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono has)
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono hst) hM1 hM2,
      K.eventPrefix_stageMetric j hjT hTj]
    exact hb'
  · intro i hfi hli
    let i' : Fin K.eventCount := Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i
    have hfK : K.toHistory.activeStage a' ≤ i'.castSucc :=
      hf.le.trans (K.eIdx_mono_C11G2 j hjT hTj hfi)
    have hlK : i'.succ ≤ K.toHistory.activeStage τ' :=
      (K.eIdx_mono_C11G2 j hjT hTj hli).trans hl.symm.le
    have hb := hA'.2 i' hfK hlK
    have hpt : A.point i.castSucc hfi (i.castSucc_lt_succ.le.trans hli) =
        A'.point i'.castSucc hfK (i'.castSucc_lt_succ.le.trans hlK) :=
      hApt _ hfi (i.castSucc_lt_succ.le.trans hli) hfK (i'.castSucc_lt_succ.le.trans hlK)
    intro x
    have hx : x = ⟨A'.point i'.castSucc hfK (i'.castSucc_lt_succ.le.trans hlK),
        (A'.crossing i' hfK hlK).mem_terminalRegularRegion (K.toHistory.event i')⟩ :=
      Subtype.ext hpt
    rw [hx]
    exact hb

/-- **G1：pinching 沿 eventPrefix（`_C11G2`）**：K 层 Pre841 native 形
`InFixedHamiltonIveyRegion (K.stageMetric (K.activeStage τ') τ') (a₀ + τ') x`（对所有 `τ'`）⇒ E 的同形
（对所有 `τ ≤ T`；`E.horizon = T`）。 -/
theorem inFixedHI_eventPrefix_C11G2 (j : Fin K.eventCount) {T : ℝ}
    (hjT : K.time j.castSucc < T) (hTj : T < K.time j.succ) {a₀ : ℝ}
    (hpin : ∀ (τ' : Icc (0 : ℝ) K.toHistory.horizon) (x : (K.toHistory.stageAt τ').Carrier),
      InFixedHamiltonIveyRegion (K.toHistory.stageMetric (K.toHistory.activeStage τ') τ')
        (a₀ + τ') x)
    (τ : Icc (0 : ℝ) (K.eventPrefix j T hjT hTj).toHistory.horizon)
    (x : ((K.eventPrefix j T hjT hTj).toHistory.stageAt τ).Carrier) :
    InFixedHamiltonIveyRegion ((K.eventPrefix j T hjT hTj).toHistory.stageMetric
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ) τ) (a₀ + τ) x := by
  have hTH : T ≤ K.horizon := hTj.le.trans (K.toHistory.time_le_horizon_at j.succ)
  let τ' : Icc (0 : ℝ) K.toHistory.horizon := ⟨τ, τ.2.1, τ.2.2.trans hTH⟩
  have hidx : K.eIdx_C11G2 j hjT hTj ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ) =
      K.toHistory.activeStage τ' := Fin.ext (K.eventPrefix_activeStage_val j hjT hTj τ τ' rfl)
  have h := K.toHistory.inFixedHI_stage_C11G hpin τ'
    (K.eIdx_C11G2 j hjT hTj ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ)) hidx.symm x
  rw [K.eventPrefix_stageMetric j hjT hTj]
  exact h

/-! ## G2：records 沿 eventPrefix -/

/-- **G2：record adapter（`_C11G2`）**：K 的 `GeometricCutoffRecord`（事件 `castLE e`）⇒
`K.eventPrefix j T` 的 record（事件 `e`）。`eventPrefix = (prefixAt j.castSucc).extendHorizon T …`：
先 `geometricCutoffRecordOfPrefix`（树内，`prefixLateRecords_P6N` 同款）再
`GeometricCutoffRecord.extendHorizon`（树内，`CutoffRecordHorizonExtension`）。 -/
def eventPrefixRecord_C11G2 (j : Fin K.eventCount) {T : ℝ} (hjT : K.time j.castSucc < T)
    (hTj : T < K.time j.succ) {p : CutoffParameters}
    (e : Fin (K.eventPrefix j T hjT hTj).toHistory.eventCount)
    (R : GeometricCutoffRecord K.toHistory (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) e) p) :
    GeometricCutoffRecord (K.eventPrefix j T hjT hTj).toHistory e p :=
  GeometricCutoffRecord.extendHorizon (H := K.prefixAt j.castSucc) T hjT.le
    ((K.toHistory.event j).incoming.closedPrefix T hjT hTj) (K.event_initial j)
    (K.geometricCutoffRecordOfPrefix j.castSucc R)

/-- **G2：late records 沿 eventPrefix（`_C11G2`）**：K 的 late records（阈值 `T₀`）⇒ E 的
late records。 -/
def eventPrefixRecords_C11G2 (j : Fin K.eventCount) {T : ℝ} (hjT : K.time j.castSucc < T)
    (hTj : T < K.time j.succ) {p : CutoffParameters} {T₀ : ℝ}
    (records : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ → GeometricCutoffRecord K.toHistory i p) :
    ∀ e : Fin (K.eventPrefix j T hjT hTj).toHistory.eventCount,
      T₀ ≤ (K.eventPrefix j T hjT hTj).toHistory.time e.succ →
      GeometricCutoffRecord (K.eventPrefix j T hjT hTj).toHistory e p :=
  fun e he => K.eventPrefixRecord_C11G2 j hjT hTj e
    (records (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) e) he)

/-- `static` 字段逐点相等（`window` / `neck.scale` / `hasCanonicalWindow` 全部原样）。 -/
theorem eventPrefixRecords_static_C11G2 (j : Fin K.eventCount) {T : ℝ}
    (hjT : K.time j.castSucc < T) (hTj : T < K.time j.succ) {p : CutoffParameters} {T₀ : ℝ}
    (records : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ → GeometricCutoffRecord K.toHistory i p)
    (e : Fin (K.eventPrefix j T hjT hTj).toHistory.eventCount)
    (he : T₀ ≤ (K.eventPrefix j T hjT hTj).toHistory.time e.succ) :
    (K.eventPrefixRecords_C11G2 j hjT hTj records e he).static =
      (records (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) e) he).static :=
  rfl

/-- 与 P6CON `prefixLateRecords_P6N`（`K.prefixAt j.castSucc` 上）的 `static` 一致——P6N 的
`not_capWindowPoint_prefix_of_late_P6N` 等对 E 的 records 同样适用。 -/
theorem eventPrefixRecords_static_eq_prefixLate_C11G2 (j : Fin K.eventCount) {T : ℝ}
    (hjT : K.time j.castSucc < T) (hTj : T < K.time j.succ) {p : CutoffParameters} {T₀ : ℝ}
    (records : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ → GeometricCutoffRecord K.toHistory i p)
    (e : Fin (K.eventPrefix j T hjT hTj).toHistory.eventCount)
    (he : T₀ ≤ (K.eventPrefix j T hjT hTj).toHistory.time e.succ) :
    (K.eventPrefixRecords_C11G2 j hjT hTj records e he).static =
      (K.prefixLateRecords_P6N j.castSucc records e he).static :=
  rfl

/-- `hcan`（canonical window）沿 eventPrefix 原样。 -/
theorem eventPrefixRecords_hcan_C11G2 (j : Fin K.eventCount) {T : ℝ}
    (hjT : K.time j.castSucc < T) (hTj : T < K.time j.succ) {p : CutoffParameters} {T₀ : ℝ}
    (records : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ → GeometricCutoffRecord K.toHistory i p)
    (hcan : ∀ i hi b, ((records i hi).static b).hasCanonicalWindow) :
    ∀ (e : Fin (K.eventPrefix j T hjT hTj).toHistory.eventCount)
      (he : T₀ ≤ (K.eventPrefix j T hjT hTj).toHistory.time e.succ) b,
      (((K.eventPrefixRecords_C11G2 j hjT hTj records) e he).static b).hasCanonicalWindow :=
  fun e he b => hcan (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) e) he b

/-- scale 分离沿 eventPrefix：K 层只要求 E 的事件（`i = castLE e`，即 `i < j`）。 -/
theorem eventPrefixRecords_scale_C11G2 (j : Fin K.eventCount) {T : ℝ}
    (hjT : K.time j.castSucc < T) (hTj : T < K.time j.succ) {p : CutoffParameters} {T₀ B : ℝ}
    (records : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ → GeometricCutoffRecord K.toHistory i p)
    (hsep : ∀ (i : Fin K.eventCount) (_hij : i.val < j.val) (hi : T₀ ≤ K.time i.succ) b,
      B < ((records i hi).static b).neck.scale) :
    ∀ (e : Fin (K.eventPrefix j T hjT hTj).toHistory.eventCount)
      (he : T₀ ≤ (K.eventPrefix j T hjT hTj).toHistory.time e.succ) b,
      B < (((K.eventPrefixRecords_C11G2 j hjT hTj records) e he).static b).neck.scale :=
  fun e he b => hsep (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) e) e.isLt he b

end RetainedCoreHistory

/-! ## consumer：喂 P6GEO `exists_hgeom_of_K0_pinching_C11G` 的 `hsmall` / `hpin` / `records` / `hcan`

`Hs n := ((K n).eventPrefix (j n) (t n) _ _).toHistory`；K 层输入（K0、Pre841 native pinching、
late records）⇒ 序列层 hgeom 在 `Hs` 上的同名前提（类型逐字对上）。 -/

/-- G1 consumer：K 层 K0 + pinching ⇒ `exists_hgeom_of_K0_pinching_C11G` 的 `hsmall` 与 `hpin`
（`Hs n = ((K n).eventPrefix (j n) (t n) _ _).toHistory`）。 -/
example (K : ℕ → RetainedCoreHistory.{u}) (j : ∀ n, Fin (K n).eventCount) (t : ℕ → ℝ)
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    (Hs : ℕ → ObservedHistory.{u})
    (hHs : Hs = fun n => ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory)
    (tE : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (pE : ∀ n, ((Hs n).stageAt (tE n)).Carrier)
    (tK : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (pK : ∀ n, ((K n).toHistory.stageAt (tK n)).Carrier) (r : ℕ → ℝ)
    (htK : ∀ n, (tE n : ℝ) = tK n) (hpK : ∀ n, HEq (pE n) (pK n))
    (hsmallK : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (tK n) (pK n) (r n))
    {a₀ : ℝ}
    (hpinK : ∀ n (τ' : Icc (0 : ℝ) (K n).toHistory.horizon)
      (x : ((K n).toHistory.stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ') τ')
        (a₀ + τ') x) :
    (∀ n, GC.LongTime.hasSmallParabolicCurvature (Hs n) (tE n) (pE n) (r n)) ∧
    (∀ n (τ : Icc (0 : ℝ) (Hs n).horizon) (x : ((Hs n).stageAt τ).Carrier),
      InFixedHamiltonIveyRegion ((Hs n).stageMetric ((Hs n).activeStage τ) τ) (a₀ + τ) x) := by
  subst hHs
  exact ⟨fun n => (K n).hasSmallParabolicCurvature_eventPrefix_C11G2 (j n) (hjt n) (htj n)
      (tE n) (tK n) (htK n) (pE n) (pK n) (hpK n) (hsmallK n),
    fun n => (K n).inFixedHI_eventPrefix_C11G2 (j n) (hjt n) (htj n) (hpinK n)⟩

/-- G2 consumer：K 层 late records + canonical window ⇒ `Hs` 上的 `records` / `hcan`
（`exists_hgeom_of_K0_pinching_C11G` 的 `records`、`hcan` 逐字类型）。 -/
example (K : ℕ → RetainedCoreHistory.{u}) (j : ∀ n, Fin (K n).eventCount) (t : ℕ → ℝ)
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ)
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (q n))
    (hcanK : ∀ n i (hi : T₀ n ≤ (K n).time i.succ) b,
      ((recordsK n i hi).static b).hasCanonicalWindow) :
    ∃ records : ∀ n (e : Fin ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory.eventCount),
        T₀ n ≤ ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory.time e.succ →
        GeometricCutoffRecord ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory e (q n),
      ∀ n e (he : T₀ n ≤ ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory.time e.succ) b,
        ((records n e he).static b).hasCanonicalWindow :=
  ⟨fun n => (K n).eventPrefixRecords_C11G2 (j n) (hjt n) (htj n) (recordsK n),
    fun n => (K n).eventPrefixRecords_hcan_C11G2 (j n) (hjt n) (htj n) (recordsK n) (hcanK n)⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

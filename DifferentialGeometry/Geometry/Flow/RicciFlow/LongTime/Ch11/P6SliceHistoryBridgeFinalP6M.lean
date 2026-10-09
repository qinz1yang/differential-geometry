import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryPrefixTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryExtendAt
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedSlabEndpoints
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitness
import DifferentialGeometry.Geometry.Collapse.CurvatureScale
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionMaximalDepth

/-!
# 桥（final-slab 情形，O-CH11-P6ANCH G3f）：final 截断 history ↔ `K`（`_final_P6M`）

event-slab 版（`P6SliceHistoryBridgeP6M`）的 final-slab 对应：坏点 `σ n` 落在 final slab
（`K.time (Fin.last _) < T < K.horizon`）时，SLT / P6D2 G3 的 history 换成
`E := (K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _) G
(K.final_initial hfin) hT hTs`，`G := (K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl`（= 树内
`terminalNoncollapsedBefore_finalSlab` 的 `J` / `G`；`extendAt` 即 `extendHorizon … (G.closedPrefix …)`
的包装）。与 event 情形不同，这里 `E` 与 `K` 的 `eventCount` / `time` / `stage` / `event` **定义等**
（`prefixAt (Fin.last _)` 不截断任何 event），只有视界与 last stage 的度量不同：
* `activeStage_final_P6M`：`E.activeStage τ = K.activeStage τ'`（同实时刻，`Fin (K.eventCount + 1)` 中）；
* `stageMetric_final_P6M`：`E.stageMetric m v = K.stageMetric m v`（last stage 两边都化到
  `K.finalSlab` 的度量，`stageMetric_last_of_lt`；其余化到 event incoming flow）；
* trace 直接 `⟨tr.point, tr.endpoint_eq, tr.crossing⟩` 重组（不需 `backwardPointTraceOfPrefix`）。
其余引理与 event 版逐一对应：E → K traced region / 受控球 / SLT `hnc`（`tested_noncollapse_final_P6M`）；
K → E 单 / 双 trace pullback、球成员、`hwit` / `hkappa` / `hbcad` / 体积单 history 形、序列形四个、
`depthExtendable_final_P6M`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace RetainedCoreHistory

variable (K : RetainedCoreHistory.{u})

/-- **`_final_P6M`（`activeStage` 值识别）**：final 截断 history `E` 与 `K` 在同一实时刻的 active stage
指标值相同（两边 `time` 定义等；`le_activeStage` / `activeStage_time_le` 两向夹逼）。 -/
theorem activeStage_val_final_P6M (hfin : K.time (Fin.last K.eventCount) < K.horizon) {T : ℝ}
    (hT : K.time (Fin.last K.eventCount) < T) (hTs : T < K.horizon) :
    let E := ((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
      ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
      hTs).toHistory
    ∀ (τ : Icc (0 : ℝ) E.horizon) (τ' : Icc (0 : ℝ) K.toHistory.horizon), (τ : ℝ) = τ' →
      (E.activeStage τ).val = (K.toHistory.activeStage τ').val := by
  intro E τ τ' hττ
  have h1 : (E.activeStage τ : Fin (K.toHistory.eventCount + 1)) ≤ K.toHistory.activeStage τ' :=
    K.toHistory.le_activeStage τ' _ (by
      rw [← hττ]
      exact E.activeStage_time_le τ)
  have h2 : (K.toHistory.activeStage τ' : Fin (E.eventCount + 1)) ≤ E.activeStage τ :=
    E.le_activeStage τ _ (by
      rw [hττ]
      exact K.toHistory.activeStage_time_le τ')
  exact le_antisymm (Fin.le_def.mp h1) (Fin.le_def.mp h2)

/-- **`_final_P6M`（`activeStage` 识别，`Fin` 等式形）**：`E.activeStage τ = K.activeStage τ'`
（等式在 `Fin (K.toHistory.eventCount + 1)` 中；两边类型定义等）。 -/
theorem activeStage_final_P6M (hfin : K.time (Fin.last K.eventCount) < K.horizon) {T : ℝ}
    (hT : K.time (Fin.last K.eventCount) < T) (hTs : T < K.horizon) :
    let E := ((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
      ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
      hTs).toHistory
    ∀ (τ : Icc (0 : ℝ) E.horizon) (τ' : Icc (0 : ℝ) K.toHistory.horizon), (τ : ℝ) = τ' →
      @Eq (Fin (K.toHistory.eventCount + 1)) (E.activeStage τ) (K.toHistory.activeStage τ') :=
  fun τ τ' hττ => Fin.ext (K.activeStage_val_final_P6M hfin hT hTs τ τ' hττ)

/-- **`_final_P6M`（`stageMetric` 识别）**：`E.stageMetric m v = K.stageMetric m v`。last stage：
`E` 侧是 `closedPrefix` 的度量、`K` 侧是 `finalSlab` 的度量（`stageMetric_last_of_lt`），二者定义等；
其余 stage：两边都是 event incoming flow（`stageMetric_castSucc_apply`）。 -/
theorem stageMetric_final_P6M (hfin : K.time (Fin.last K.eventCount) < K.horizon) {T : ℝ}
    (hT : K.time (Fin.last K.eventCount) < T) (hTs : T < K.horizon) :
    let E := ((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
      ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
      hTs).toHistory
    ∀ (m : Fin (K.toHistory.eventCount + 1)) (v : ℝ),
      E.stageMetric m v = K.toHistory.stageMetric m v := by
  intro E m v
  cases m using Fin.lastCases with
  | last =>
    refine (ObservedHistory.stageMetric_last_of_lt (H := E) (h := hT) v).trans ?_
    refine Eq.trans ?_
      (ObservedHistory.stageMetric_last_of_lt (H := K.toHistory) (h := hfin) v).symm
    rfl
  | cast i =>
    refine (ObservedHistory.stageMetric_castSucc_apply (H := E) i v).trans ?_
    refine Eq.trans ?_ (ObservedHistory.stageMetric_castSucc_apply (H := K.toHistory) i v).symm
    rfl

/-- stage 指标推广：`m' = m` 时 `‖Rm‖² ≤ C²` 在两种指标写法间搬运。 -/
private theorem rm_sq_bound_of_stage_eq_final_P6M {H : ObservedHistory.{u}}
    {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {x : (H.stage last).Carrier}
    (B : BackwardPointTrace H first last hle x) {m m' : Fin (H.eventCount + 1)} (hm : m' = m)
    (h1 : first ≤ m) (h2 : m ≤ last) (h1' : first ≤ m') (h2' : m' ≤ last) (v C : ℝ)
    (h : normSq0S (H.stageMetric m' v) (B.point m' h1' h2') 4
      (metricRm04At (H.stageMetric m' v) (B.point m' h1' h2')) ≤ C ^ 2) :
    normSq0S (H.stageMetric m v) (B.point m h1 h2) 4
      (metricRm04At (H.stageMetric m v) (B.point m h1 h2)) ≤ C ^ 2 := by
  subst hm
  exact h

/-- K 层 traced region（stage 指标 `last` 推广形，`subst` 后即定义）。 -/
private theorem isTracedRegion_of_stage_index_final_P6M (H : ObservedHistory.{u})
    (τ : Icc (0 : ℝ) H.horizon) (last : Fin (H.eventCount + 1)) (hlast : H.activeStage τ = last)
    (p : (H.stage last).Carrier) (p' : (H.stageAt τ).Carrier) (hp : HEq p p')
    {ρ δ C : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ)
    (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ τ) (ha : (a : ℝ) = (τ : ℝ) - δ)
    (first : Fin (H.eventCount + 1)) (hfirst : first ≤ H.activeStage a) (hf : first ≤ last)
    (htrace : ∀ x ∈ riemannianBallOf (H.stageMetric last τ) p ρ,
      ∃ B : BackwardPointTrace H first last hf x,
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ τ),
          normSq0S (H.stageMetric (H.activeStage v) v)
            (B.point (H.activeStage v) (hfirst.trans (H.activeStage_mono hav))
              ((H.activeStage_mono hvt).trans hlast.le)) 4
            (metricRm04At (H.stageMetric (H.activeStage v) v)
              (B.point (H.activeStage v) (hfirst.trans (H.activeStage_mono hav))
                ((H.activeStage_mono hvt).trans hlast.le))) ≤ C ^ 2) ∧
        ∀ (i : Fin H.eventCount) (hi : H.activeStage a ≤ i.castSucc) (hil : i.succ ≤ last),
          let y : (H.event i).incoming.terminalRegularOpen :=
            ⟨B.point i.castSucc (hfirst.trans hi) (i.castSucc_lt_succ.le.trans hil),
              (B.crossing i (hfirst.trans hi) hil).mem_terminalRegularRegion (H.event i)⟩;
          normSq0S (H.event i).terminal.metric y 4
            (metricRm04At (H.event i).terminal.metric y) ≤ C ^ 2) :
    H.isTracedRegion τ p' ρ δ C := by
  subst hlast
  obtain rfl := eq_of_heq hp
  refine ⟨hρ, hδ, a, hat, ha, fun x hx => ?_⟩
  obtain ⟨B, hobs, hseam⟩ := htrace x hx
  exact ⟨B.restrictFirst hfirst (H.activeStage_mono hat), hobs, fun i hi hil => hseam i hi hil⟩

/-- **`_final_P6M`（桥 E → K）**：final 截断 history `E` 的 traced region（时刻 `τ`、中心 `p`）⇒ `K` 的
traced region（同一实时刻 `τ'`、`HEq` 中心 `p'`），半径 / 深度 / 曲率界不变。trace 直接重组
（`E` 与 `K` 的 stage / event 定义等），度量经 `stageMetric_final_P6M`。 -/
theorem isTracedRegion_final_P6M (hfin : K.time (Fin.last K.eventCount) < K.horizon) {T : ℝ}
    (hT : K.time (Fin.last K.eventCount) < T) (hTs : T < K.horizon) {ρ δ C : ℝ} :
    let E := ((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
      ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
      hTs).toHistory
    ∀ (τ : Icc (0 : ℝ) E.horizon) (τ' : Icc (0 : ℝ) K.toHistory.horizon), (τ : ℝ) = τ' →
    ∀ (p : (E.stageAt τ).Carrier) (p' : (K.toHistory.stageAt τ').Carrier), HEq p p' →
      E.isTracedRegion τ p ρ δ C → K.toHistory.isTracedRegion τ' p' ρ δ C := by
  intro E τ τ' hττ p p' hp h
  obtain ⟨hρ, hδ, a, hat, ha, htr⟩ := h
  let a' : Icc (0 : ℝ) K.toHistory.horizon := ⟨a, a.2.1, a.2.2.trans hTs.le⟩
  have hAτ : @Eq (Fin (K.toHistory.eventCount + 1)) (E.activeStage τ)
      (K.toHistory.activeStage τ') := K.activeStage_final_P6M hfin hT hTs τ τ' hττ
  have hAa : @Eq (Fin (K.toHistory.eventCount + 1)) (E.activeStage a)
      (K.toHistory.activeStage a') := K.activeStage_final_P6M hfin hT hTs a a' rfl
  have hka := E.activeStage_mono hat
  have hat' : a' ≤ τ' := show (a : ℝ) ≤ τ' from hττ ▸ hat
  have ha' : (a' : ℝ) = (τ' : ℝ) - δ := by
    change (a : ℝ) = (τ' : ℝ) - δ
    rw [← hττ]
    exact ha
  refine isTracedRegion_of_stage_index_final_P6M K.toHistory τ' (E.activeStage τ) hAτ.symm p p'
    hp hρ hδ a' hat' ha' (E.activeStage a) hAa.le hka ?_
  intro x hx
  have hm : E.stageMetric (E.activeStage τ) τ =
      K.toHistory.stageMetric (E.activeStage τ) τ := K.stageMetric_final_P6M hfin hT hTs _ _
  have hx' : x ∈ riemannianBallOf (E.stageMetric (E.activeStage τ) τ) p ρ := by
    rw [hm, hττ]
    exact hx
  obtain ⟨A, hA1, hA2⟩ := htr x hx'
  refine ⟨⟨A.point, A.endpoint_eq, A.crossing⟩, ?_, ?_⟩
  · intro v hav hvt
    have hvT : (v : ℝ) ≤ T := (show (v : ℝ) ≤ τ' from hvt).trans (hττ ▸ τ.2.2)
    let vK : Icc (0 : ℝ) E.horizon := ⟨v, v.2.1, hvT⟩
    have hAv : @Eq (Fin (K.toHistory.eventCount + 1)) (E.activeStage vK)
        (K.toHistory.activeStage v) := K.activeStage_final_P6M hfin hT hTs vK v rfl
    have hav' : a ≤ vK := show (a : ℝ) ≤ v from hav
    have hvt' : vK ≤ τ := show (v : ℝ) ≤ τ from hττ ▸ hvt
    have hb := hA1 vK hav' hvt'
    have hmv : E.stageMetric (E.activeStage vK) vK =
        K.toHistory.stageMetric (E.activeStage vK) vK := K.stageMetric_final_P6M hfin hT hTs _ _
    rw [hmv] at hb
    exact rm_sq_bound_of_stage_eq_final_P6M _ (m' := E.activeStage vK)
      (m := K.toHistory.activeStage v) hAv _ _ (E.activeStage_mono hav')
      (E.activeStage_mono hvt') v C hb
  · intro i hi hil
    exact hA2 i (hAa.le.trans hi) hil

/-- **`_final_P6M`（桥 E → K）**：E 的受控抛物球 ⇒ K 的受控抛物球（同一实时刻、`HEq` 中心、同半径）。 -/
theorem isParabolicallyRmControlledBall_final_P6M
    (hfin : K.time (Fin.last K.eventCount) < K.horizon) {T : ℝ}
    (hT : K.time (Fin.last K.eventCount) < T) (hTs : T < K.horizon) {r : ℝ} :
    let E := ((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
      ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
      hTs).toHistory
    ∀ (τ : Icc (0 : ℝ) E.horizon) (τ' : Icc (0 : ℝ) K.toHistory.horizon), (τ : ℝ) = τ' →
    ∀ (p : (E.stageAt τ).Carrier) (p' : (K.toHistory.stageAt τ').Carrier), HEq p p' →
      E.isParabolicallyRmControlledBall τ p r →
        K.toHistory.isParabolicallyRmControlledBall τ' p' r := by
  intro E τ τ' hττ p p' hp h
  exact (K.toHistory.isParabolicallyRmControlledBall_iff_isTracedRegion τ' p' r).2
    (K.isTracedRegion_final_P6M hfin hT hTs τ τ' hττ p p' hp
      ((E.isParabolicallyRmControlledBall_iff_isTracedRegion τ p r).1 h))

/-- 体积按 stage 指标搬运（`m = m'`、度量 `g = stageMetric m v`、中心 `HEq`）。 -/
private theorem volume_ball_congr_final_P6M (H : ObservedHistory.{u})
    {m m' : Fin (H.eventCount + 1)}
    (hm : m = m') (v : ℝ) (g : (H.stage m).Metric) (hg : g = H.stageMetric m v)
    (p : (H.stage m).Carrier) (p' : (H.stage m').Carrier) (hp : HEq p p') (b : ℝ) :
    riemannianVolumeMeasure ThreeModel (H.stage m).Carrier g (riemannianBallOf g p b) =
      riemannianVolumeMeasure ThreeModel (H.stage m').Carrier (H.stageMetric m' v)
        (riemannianBallOf (H.stageMetric m' v) p' b) := by
  subst hg
  subst hm
  obtain rfl := eq_of_heq hp
  rfl

/-- **`_final_P6M`（L-RS `hnc`，final slab）**：K 层区域 / 窗口形 tested κ（`a ≤ τ ≤ t`、`τ` 在 final slab
内部、中心 `∈ U`）⇒ SLT 的 `hnc` 形（`H := K.prefixAt (Fin.last _)`、`G := (K.finalSlab hfin)`
的 incoming 形；每个 `T ∈ (time last, t]`、`a ≤ T` 的 `extendHorizon`）。 -/
theorem tested_noncollapse_final_P6M (hfin : K.time (Fin.last K.eventCount) < K.horizon)
    {κ ρ a t : ℝ} (U : Set (K.stage (Fin.last K.eventCount)).Carrier)
    (hK : ∀ (τ : Icc (0 : ℝ) K.toHistory.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
      K.time (Fin.last K.eventCount) < τ → (τ : ℝ) < K.horizon →
      ∀ z ∈ U, ∀ zz : (K.toHistory.stageAt τ).Carrier, HEq zz z →
      ∀ b : ℝ, 0 < b → b ≤ ρ → K.toHistory.isParabolicallyRmControlledBall τ zz b →
        ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
          riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt τ).Carrier
            (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
            (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) zz b))
    (hend : (K.prefixAt (Fin.last K.eventCount)).time
        (Fin.last (K.prefixAt (Fin.last K.eventCount)).eventCount) =
      (K.prefixAt (Fin.last K.eventCount)).horizon) :
    ∀ (T : ℝ) (hT : (K.prefixAt (Fin.last K.eventCount)).time
        (Fin.last (K.prefixAt (Fin.last K.eventCount)).eventCount) < T)
      (hTs : T < K.horizon), T ≤ t → a ≤ T →
        let B := (K.prefixAt (Fin.last K.eventCount)).extendHorizon T (hend ▸ hT.le)
          (((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).closedPrefix T hT hTs)
          (K.final_initial hfin)
        let tm : Icc (0 : ℝ) B.horizon :=
          ⟨T, (K.prefixAt (Fin.last K.eventCount)).horizon_nonneg.trans (hend ▸ hT.le), le_rfl⟩
        ∀ z ∈ U, ∀ (yy : (B.toHistory.stageAt tm).Carrier), HEq yy z →
        ∀ (b : ℝ), 0 < b → b ≤ ρ →
          B.toHistory.isParabolicallyRmControlledBall tm yy b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
                (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                  yy b) := by
  intro T hT hTs hTt haT B tm z hz yy hyy b hb hbρ hball
  let τ' : Icc (0 : ℝ) K.toHistory.horizon := ⟨T, tm.2.1, hTs.le⟩
  have hidx : @Eq (Fin (K.toHistory.eventCount + 1)) (B.toHistory.activeStage tm)
      (K.toHistory.activeStage τ') := K.activeStage_final_P6M hfin hT hTs tm τ' rfl
  let zz : (K.toHistory.stageAt τ').Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hidx) yy
  have hzz : HEq zz yy := cast_heq _ _
  have hball' := K.isParabolicallyRmControlledBall_final_P6M hfin hT hTs tm τ' rfl yy zz
    hzz.symm hball
  have h := hK τ' haT hTt hT hTs z hz zz (hzz.trans hyy) b hb hbρ hball'
  have hmet : B.toHistory.stageMetric (B.toHistory.activeStage tm) T =
      K.toHistory.stageMetric (B.toHistory.activeStage tm) T :=
    K.stageMetric_final_P6M hfin hT hTs _ _
  refine h.trans (le_of_eq ?_)
  exact (volume_ball_congr_final_P6M K.toHistory hidx T
    (B.toHistory.stageMetric (B.toHistory.activeStage tm) T) hmet yy zz hzz.symm b).symm

/-! ### 桥 K → E：trace-local 前提的 pullback（final slab；P6D2 G3 的 `Hs`-层输入） -/

/-- trace 指标推广：首末 stage 指标与端点 `HEq` 一致时，K 层"对所有 trace"的结论搬到给定 trace。 -/
private theorem trace_index_final_P6M (H : ObservedHistory.{u})
    (P : ∀ m : Fin (H.eventCount + 1), (H.stage m).Carrier → Prop)
    {f l f' l' : Fin (H.eventCount + 1)} (hf : f = f') (hl : l = l') {hle : f ≤ l}
    {hle' : f' ≤ l'} {x : (H.stage l).Carrier} {x' : (H.stage l').Carrier} (hx : HEq x x')
    (A : BackwardPointTrace H f l hle x)
    (hK : ∀ A' : BackwardPointTrace H f' l' hle' x', P f' (A'.point f' le_rfl hle')) :
    P f (A.point f le_rfl hle) := by
  subst hf
  subst hl
  obtain rfl := eq_of_heq hx
  exact hK A

/-- 两条 trace 版（同首末指标）。 -/
private theorem trace_index₂_final_P6M (H : ObservedHistory.{u})
    (P : ∀ m : Fin (H.eventCount + 1), (H.stage m).Carrier → (H.stage m).Carrier → Prop)
    {f l f' l' : Fin (H.eventCount + 1)} (hf : f = f') (hl : l = l') {hle : f ≤ l}
    {hle' : f' ≤ l'} {x₁ x₂ : (H.stage l).Carrier} {x₁' x₂' : (H.stage l').Carrier}
    (hx₁ : HEq x₁ x₁') (hx₂ : HEq x₂ x₂')
    (A₁ : BackwardPointTrace H f l hle x₁) (A₂ : BackwardPointTrace H f l hle x₂)
    (hK : ∀ (A₁' : BackwardPointTrace H f' l' hle' x₁') (A₂' : BackwardPointTrace H f' l' hle' x₂'),
      P f' (A₁'.point f' le_rfl hle') (A₂'.point f' le_rfl hle')) :
    P f (A₁.point f le_rfl hle) (A₂.point f le_rfl hle) := by
  subst hf
  subst hl
  obtain rfl := eq_of_heq hx₁
  obtain rfl := eq_of_heq hx₂
  exact hK A₁ A₂

/-- **`_final_P6M`（桥 K → E，单 trace 通用形）**：E 的 trace（`v ≤ τ`）重组成 K 的 trace（同实时刻
`v' τ'`），K 层"对所有 trace 成立"的点态性质 `P` 回落到 E 的 trace 点（stage 指标 `E.activeStage v`
直接视作 `Fin (K.eventCount + 1)`，载体定义等）。 -/
theorem forall_trace_final_P6M (hfin : K.time (Fin.last K.eventCount) < K.horizon) {T : ℝ}
    (hT : K.time (Fin.last K.eventCount) < T) (hTs : T < K.horizon) :
    let E := ((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
      ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
      hTs).toHistory
    ∀ (τ v : Icc (0 : ℝ) E.horizon) (hvτ : v ≤ τ) (τ' v' : Icc (0 : ℝ) K.toHistory.horizon),
      (τ : ℝ) = τ' → (v : ℝ) = v' →
    ∀ (x : (E.stageAt τ).Carrier) (x' : (K.toHistory.stageAt τ').Carrier), HEq x x' →
    ∀ (P : ∀ m : Fin (K.eventCount + 1), (K.stage m).Carrier → Prop),
      (∀ (hvτ' : v' ≤ τ') (tr' : BackwardPointTrace K.toHistory (K.toHistory.activeStage v')
          (K.toHistory.activeStage τ') (K.toHistory.activeStage_mono hvτ') x'),
        P (K.toHistory.activeStage v')
          (tr'.point (K.toHistory.activeStage v') le_rfl (K.toHistory.activeStage_mono hvτ'))) →
    ∀ (tr : BackwardPointTrace E (E.activeStage v) (E.activeStage τ) (E.activeStage_mono hvτ) x),
      P (E.activeStage v) (tr.point (E.activeStage v) le_rfl (E.activeStage_mono hvτ)) := by
  intro E τ v hvτ τ' v' hττ hvv x x' hx P hK tr
  have hvτ' : v' ≤ τ' := show (v' : ℝ) ≤ τ' from hvv ▸ hττ ▸ hvτ
  exact trace_index_final_P6M K.toHistory P (K.activeStage_final_P6M hfin hT hTs v v' hvv)
    (K.activeStage_final_P6M hfin hT hTs τ τ' hττ) hx
    (show BackwardPointTrace K.toHistory (E.activeStage v) (E.activeStage τ)
      (E.activeStage_mono hvτ) x from ⟨tr.point, tr.endpoint_eq, tr.crossing⟩) (hK hvτ')

/-- **`_final_P6M`（桥 K → E，双 trace 通用形）**：`hbcad` 用。 -/
theorem forall_trace₂_final_P6M (hfin : K.time (Fin.last K.eventCount) < K.horizon) {T : ℝ}
    (hT : K.time (Fin.last K.eventCount) < T) (hTs : T < K.horizon) :
    let E := ((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
      ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
      hTs).toHistory
    ∀ (τ v : Icc (0 : ℝ) E.horizon) (hvτ : v ≤ τ) (τ' v' : Icc (0 : ℝ) K.toHistory.horizon),
      (τ : ℝ) = τ' → (v : ℝ) = v' →
    ∀ (x₁ x₂ : (E.stageAt τ).Carrier) (x₁' x₂' : (K.toHistory.stageAt τ').Carrier),
      HEq x₁ x₁' → HEq x₂ x₂' →
    ∀ (P : ∀ m : Fin (K.eventCount + 1), (K.stage m).Carrier → (K.stage m).Carrier → Prop),
      (∀ (hvτ' : v' ≤ τ')
        (tr₁' : BackwardPointTrace K.toHistory (K.toHistory.activeStage v')
          (K.toHistory.activeStage τ') (K.toHistory.activeStage_mono hvτ') x₁')
        (tr₂' : BackwardPointTrace K.toHistory (K.toHistory.activeStage v')
          (K.toHistory.activeStage τ') (K.toHistory.activeStage_mono hvτ') x₂'),
        P (K.toHistory.activeStage v')
          (tr₁'.point (K.toHistory.activeStage v') le_rfl (K.toHistory.activeStage_mono hvτ'))
          (tr₂'.point (K.toHistory.activeStage v') le_rfl (K.toHistory.activeStage_mono hvτ'))) →
    ∀ (tr₁ : BackwardPointTrace E (E.activeStage v) (E.activeStage τ) (E.activeStage_mono hvτ)
        x₁)
      (tr₂ : BackwardPointTrace E (E.activeStage v) (E.activeStage τ) (E.activeStage_mono hvτ)
        x₂),
      P (E.activeStage v) (tr₁.point (E.activeStage v) le_rfl (E.activeStage_mono hvτ))
        (tr₂.point (E.activeStage v) le_rfl (E.activeStage_mono hvτ)) := by
  intro E τ v hvτ τ' v' hττ hvv x₁ x₂ x₁' x₂' hx₁ hx₂ P hK tr₁ tr₂
  have hvτ' : v' ≤ τ' := show (v' : ℝ) ≤ τ' from hvv ▸ hττ ▸ hvτ
  exact trace_index₂_final_P6M K.toHistory P (K.activeStage_final_P6M hfin hT hTs v v' hvv)
    (K.activeStage_final_P6M hfin hT hTs τ τ' hττ) hx₁ hx₂
    (show BackwardPointTrace K.toHistory (E.activeStage v) (E.activeStage τ)
      (E.activeStage_mono hvτ) x₁ from ⟨tr₁.point, tr₁.endpoint_eq, tr₁.crossing⟩)
    (show BackwardPointTrace K.toHistory (E.activeStage v) (E.activeStage τ)
      (E.activeStage_mono hvτ) x₂ from ⟨tr₂.point, tr₂.endpoint_eq, tr₂.crossing⟩)
    (hK hvτ')

/-- 球成员按 stage 指标搬运（`m = m'`、度量 `g = stageMetric m v`、`HEq` 中心与点）。 -/
private theorem mem_ball_congr_final_P6M (H : ObservedHistory.{u})
    {m m' : Fin (H.eventCount + 1)}
    (hm : m = m') (v : ℝ) (g : (H.stage m).Metric) (hg : g = H.stageMetric m v)
    (p x : (H.stage m).Carrier) (p' x' : (H.stage m').Carrier) (hp : HEq p p') (hx : HEq x x')
    (b : ℝ) (h : x ∈ riemannianBallOf g p b) : x' ∈ riemannianBallOf (H.stageMetric m' v) p' b := by
  subst hg
  subst hm
  obtain rfl := eq_of_heq hp
  obtain rfl := eq_of_heq hx
  exact h

/-- **`_final_P6M`（桥 K → E，基点球）**：E 在时刻 `τ` 的球成员 ⇒ K 在同一实时刻的球成员（`HEq` 搬运）。 -/
theorem mem_ball_final_P6M (hfin : K.time (Fin.last K.eventCount) < K.horizon) {T : ℝ}
    (hT : K.time (Fin.last K.eventCount) < T) (hTs : T < K.horizon) :
    let E := ((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
      ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
      hTs).toHistory
    ∀ (τ : Icc (0 : ℝ) E.horizon) (τ' : Icc (0 : ℝ) K.toHistory.horizon), (τ : ℝ) = τ' →
    ∀ (p x : (E.stageAt τ).Carrier) (p' x' : (K.toHistory.stageAt τ').Carrier), HEq p p' →
      HEq x x' → ∀ b : ℝ, x ∈ riemannianBallOf (E.stageMetric (E.activeStage τ) τ) p b →
        x' ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ') τ') p' b := by
  intro E τ τ' hττ p x p' x' hp hx b h
  have hAτ : @Eq (Fin (K.toHistory.eventCount + 1)) (E.activeStage τ)
      (K.toHistory.activeStage τ') := K.activeStage_final_P6M hfin hT hTs τ τ' hττ
  have hmet : E.stageMetric (E.activeStage τ) τ' =
      K.toHistory.stageMetric (E.activeStage τ) τ' := K.stageMetric_final_P6M hfin hT hTs _ _
  rw [hττ] at h
  exact mem_ball_congr_final_P6M K.toHistory hAτ τ' _ hmet p x p' x' hp hx b h

/-- **`_final_P6M`（K → E，`hwit` 单 history 形）**：K 层窗口 witness（中心 `p'`、半径 `ρ`、深度 `θ`）
⇒ final 截断 history `E` 层同形。 -/
theorem hwit_final_P6M (hfin : K.time (Fin.last K.eventCount) < K.horizon) {T : ℝ}
    (hT : K.time (Fin.last K.eventCount) < T) (hTs : T < K.horizon)
    (E : ObservedHistory.{u}) (hE : E = ((K.prefixAt (Fin.last K.eventCount)).extendAt
      (K.prefixAt_time_last _) ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl)
      (K.final_initial hfin) hT hTs).toHistory)
    (τ : Icc (0 : ℝ) E.horizon) (τ' : Icc (0 : ℝ) K.toHistory.horizon) (hττ : (τ : ℝ) = τ')
    (p : (E.stageAt τ).Carrier) (p' : (K.toHistory.stageAt τ').Carrier) (hp : HEq p p')
    {ε C1s C2s qs ρ θ : ℝ}
    (hK : ∀ x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ') τ') p' ρ,
      ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hvt : v ≤ τ'), (τ' : ℝ) - θ ≤ v →
      (v : ℝ) < τ' → K.toHistory.time (K.toHistory.activeStage v) < v →
      ∀ tr : BackwardPointTrace K.toHistory (K.toHistory.activeStage v)
        (K.toHistory.activeStage τ') (K.toHistory.activeStage_mono hvt) x,
        qs < metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
          (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvt)) →
        ∃ Wt : SpatialCanonicalWitness (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            ε C1s C2s
            (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvt)),
          Wt.capTubeHasNeckChart ε) :
    ∀ x ∈ riemannianBallOf (E.stageMetric (E.activeStage τ) τ) p ρ,
      ∀ (v : Icc (0 : ℝ) E.horizon) (hvt : v ≤ τ), (τ : ℝ) - θ ≤ v →
      (v : ℝ) < τ → E.time (E.activeStage v) < v →
      ∀ tr : BackwardPointTrace E (E.activeStage v) (E.activeStage τ)
        (E.activeStage_mono hvt) x,
        qs < metricScalarAt (E.stageMetric (E.activeStage v) v)
          (tr.point (E.activeStage v) le_rfl (E.activeStage_mono hvt)) →
        ∃ Wt : SpatialCanonicalWitness (E.stageMetric (E.activeStage v) v) ε C1s C2s
            (tr.point (E.activeStage v) le_rfl (E.activeStage_mono hvt)),
          Wt.capTubeHasNeckChart ε := by
  subst hE
  intro x hx v hvt hθ hvτ hage tr hq
  let v' : Icc (0 : ℝ) K.toHistory.horizon := ⟨v, v.2.1, v.2.2.trans hTs.le⟩
  have hidx := K.activeStage_final_P6M hfin hT hTs τ τ' hττ
  let x' : (K.toHistory.stageAt τ').Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hidx) x
  have hxx : HEq x x' := (cast_heq _ _).symm
  have hx' := K.mem_ball_final_P6M hfin hT hTs τ τ' hττ p x p' x' hp hxx ρ hx
  have h := K.forall_trace_final_P6M hfin hT hTs τ v hvt τ' v' hττ rfl x x' hxx
    (fun m pt => K.time m < v → qs < metricScalarAt (K.toHistory.stageMetric m v) pt →
      ∃ Wt : SpatialCanonicalWitness (K.toHistory.stageMetric m v) ε C1s C2s pt,
        Wt.capTubeHasNeckChart ε)
    (fun hvτ' tr' hage' hq' => hK x' hx' v' hvτ' (by rw [← hττ]; exact hθ)
      (by rw [← hττ]; exact hvτ) hage' tr' hq') tr
  have hmet := K.stageMetric_final_P6M hfin hT hTs
    (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
      ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
      hTs).toHistory.activeStage v) v
  rw [hmet] at hq ⊢
  exact h hage hq

/-- **`_final_P6M`（K → E，`hkappa` 单 history 形）**：K 层 trace-local κ（受控球 ⇒ 体积）⇒ E 层同形；
E 的受控球经 `isParabolicallyRmControlledBall_final_P6M` 回到 K。 -/
theorem hkappa_final_P6M (hfin : K.time (Fin.last K.eventCount) < K.horizon) {T : ℝ}
    (hT : K.time (Fin.last K.eventCount) < T) (hTs : T < K.horizon)
    (E : ObservedHistory.{u}) (hE : E = ((K.prefixAt (Fin.last K.eventCount)).extendAt
      (K.prefixAt_time_last _) ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl)
      (K.final_initial hfin) hT hTs).toHistory)
    (τ : Icc (0 : ℝ) E.horizon) (τ' : Icc (0 : ℝ) K.toHistory.horizon) (hττ : (τ : ℝ) = τ')
    (p : (E.stageAt τ).Carrier) (p' : (K.toHistory.stageAt τ').Carrier) (hp : HEq p p')
    {κ ρnc ρ θ : ℝ}
    (hK : ∀ x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ') τ') p' ρ,
      ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hvt : v ≤ τ'), (τ' : ℝ) - θ ≤ v →
      ∀ tr : BackwardPointTrace K.toHistory (K.toHistory.activeStage v)
        (K.toHistory.activeStage τ') (K.toHistory.activeStage_mono hvt) x,
      ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc →
        K.toHistory.isParabolicallyRmControlledBall v
          (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvt)) r'' →
        ENNReal.ofReal (κ * r'' ^ 3) ≤
          Geometry.Collapse.ballVolume (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvt)) r'') :
    ∀ x ∈ riemannianBallOf (E.stageMetric (E.activeStage τ) τ) p ρ,
      ∀ (v : Icc (0 : ℝ) E.horizon) (hvt : v ≤ τ), (τ : ℝ) - θ ≤ v →
      ∀ tr : BackwardPointTrace E (E.activeStage v) (E.activeStage τ)
        (E.activeStage_mono hvt) x,
      ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc →
        E.isParabolicallyRmControlledBall v
          (tr.point (E.activeStage v) le_rfl (E.activeStage_mono hvt)) r'' →
        ENNReal.ofReal (κ * r'' ^ 3) ≤
          Geometry.Collapse.ballVolume (E.stageMetric (E.activeStage v) v)
            (tr.point (E.activeStage v) le_rfl (E.activeStage_mono hvt)) r'' := by
  subst hE
  intro x hx v hvt hθ tr r'' hr hrρ hball
  let v' : Icc (0 : ℝ) K.toHistory.horizon := ⟨v, v.2.1, v.2.2.trans hTs.le⟩
  have hidx := K.activeStage_final_P6M hfin hT hTs τ τ' hττ
  let x' : (K.toHistory.stageAt τ').Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hidx) x
  have hxx : HEq x x' := (cast_heq _ _).symm
  have hx' := K.mem_ball_final_P6M hfin hT hTs τ τ' hττ p x p' x' hp hxx ρ hx
  have h := K.forall_trace_final_P6M hfin hT hTs τ v hvt τ' v' hττ rfl x x' hxx
    (fun m pt => (∀ pt' : (K.toHistory.stageAt v').Carrier, HEq pt' pt →
        K.toHistory.isParabolicallyRmControlledBall v' pt' r'') →
      ENNReal.ofReal (κ * r'' ^ 3) ≤
        Geometry.Collapse.ballVolume (K.toHistory.stageMetric m v) pt r'')
    (fun hvτ' tr' hc => hK x' hx' v' hvτ' (by rw [← hττ]; exact hθ) tr' r'' hr hrρ
      (hc _ HEq.rfl)) tr
  have hc : ∀ pt' : (K.toHistory.stageAt v').Carrier,
      HEq pt' (tr.point (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
        ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
        hTs).toHistory.activeStage v) le_rfl
        (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
        ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
        hTs).toHistory.activeStage_mono hvt)) →
      K.toHistory.isParabolicallyRmControlledBall v' pt' r'' := fun pt' hpt =>
    K.isParabolicallyRmControlledBall_final_P6M hfin hT hTs v v' rfl _ pt' hpt.symm hball
  have hmet := K.stageMetric_final_P6M hfin hT hTs
    (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
      ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
      hTs).toHistory.activeStage v) v
  rw [hmet]
  exact h hc

/-- **`_final_P6M`（K → E，`hbcad` 单 history 形）**：K 层双 trace BCAD（固定 `v`、阈值 `A'`、距离
`Dd'`、界 `C'`）⇒ E 层同形。 -/
theorem hbcad_final_P6M (hfin : K.time (Fin.last K.eventCount) < K.horizon) {T : ℝ}
    (hT : K.time (Fin.last K.eventCount) < T) (hTs : T < K.horizon)
    (E : ObservedHistory.{u}) (hE : E = ((K.prefixAt (Fin.last K.eventCount)).extendAt
      (K.prefixAt_time_last _) ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl)
      (K.final_initial hfin) hT hTs).toHistory)
    (τ : Icc (0 : ℝ) E.horizon) (τ' : Icc (0 : ℝ) K.toHistory.horizon) (hττ : (τ : ℝ) = τ')
    (p : (E.stageAt τ).Carrier) (p' : (K.toHistory.stageAt τ').Carrier) (hp : HEq p p')
    {ρ δ A' Dd' C' : ℝ}
    (hK : ∀ x₁ ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ') τ') p' ρ,
      ∀ x₂ ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ') τ') p' ρ,
      ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hvt : v ≤ τ'), (v : ℝ) = τ' + δ →
      ∀ (tr₁ : BackwardPointTrace K.toHistory (K.toHistory.activeStage v)
          (K.toHistory.activeStage τ') (K.toHistory.activeStage_mono hvt) x₁)
        (tr₂ : BackwardPointTrace K.toHistory (K.toHistory.activeStage v)
          (K.toHistory.activeStage τ') (K.toHistory.activeStage_mono hvt) x₂),
        metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (tr₁.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvt)) ≤
          A' →
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (tr₁.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvt))
            (tr₂.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvt)) <
          ENNReal.ofReal Dd' →
        metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (tr₂.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvt)) ≤
          C') :
    ∀ x₁ ∈ riemannianBallOf (E.stageMetric (E.activeStage τ) τ) p ρ,
      ∀ x₂ ∈ riemannianBallOf (E.stageMetric (E.activeStage τ) τ) p ρ,
      ∀ (v : Icc (0 : ℝ) E.horizon) (hvt : v ≤ τ), (v : ℝ) = τ + δ →
      ∀ (tr₁ : BackwardPointTrace E (E.activeStage v) (E.activeStage τ)
          (E.activeStage_mono hvt) x₁)
        (tr₂ : BackwardPointTrace E (E.activeStage v) (E.activeStage τ)
          (E.activeStage_mono hvt) x₂),
        metricScalarAt (E.stageMetric (E.activeStage v) v)
            (tr₁.point (E.activeStage v) le_rfl (E.activeStage_mono hvt)) ≤ A' →
        riemannianEDistOf (E.stageMetric (E.activeStage v) v)
            (tr₁.point (E.activeStage v) le_rfl (E.activeStage_mono hvt))
            (tr₂.point (E.activeStage v) le_rfl (E.activeStage_mono hvt)) <
          ENNReal.ofReal Dd' →
        metricScalarAt (E.stageMetric (E.activeStage v) v)
            (tr₂.point (E.activeStage v) le_rfl (E.activeStage_mono hvt)) ≤ C' := by
  subst hE
  intro x₁ hx₁ x₂ hx₂ v hvt hv tr₁ tr₂ hA hD
  let v' : Icc (0 : ℝ) K.toHistory.horizon := ⟨v, v.2.1, v.2.2.trans hTs.le⟩
  have hidx := K.activeStage_final_P6M hfin hT hTs τ τ' hττ
  let x₁' : (K.toHistory.stageAt τ').Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hidx) x₁
  let x₂' : (K.toHistory.stageAt τ').Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hidx) x₂
  have hxx₁ : HEq x₁ x₁' := (cast_heq _ _).symm
  have hxx₂ : HEq x₂ x₂' := (cast_heq _ _).symm
  have hx₁' := K.mem_ball_final_P6M hfin hT hTs τ τ' hττ p x₁ p' x₁' hp hxx₁ ρ hx₁
  have hx₂' := K.mem_ball_final_P6M hfin hT hTs τ τ' hττ p x₂ p' x₂' hp hxx₂ ρ hx₂
  have h := K.forall_trace₂_final_P6M hfin hT hTs τ v hvt τ' v' hττ rfl x₁ x₂ x₁' x₂'
    hxx₁ hxx₂
    (fun m p₁ p₂ => metricScalarAt (K.toHistory.stageMetric m v) p₁ ≤ A' →
      riemannianEDistOf (K.toHistory.stageMetric m v) p₁ p₂ < ENNReal.ofReal Dd' →
      metricScalarAt (K.toHistory.stageMetric m v) p₂ ≤ C')
    (fun hvτ' tr₁' tr₂' => hK x₁' hx₁' x₂' hx₂' v' hvτ' (by rw [← hττ]; exact hv) tr₁' tr₂')
    tr₁ tr₂
  have hmet := K.stageMetric_final_P6M hfin hT hTs
    (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
      ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
      hTs).toHistory.activeStage v) v
  rw [hmet] at hA hD ⊢
  exact h hA hD

/-- **`_final_P6M`（K → E，`hseed` 单 history 形）**：基点球体积（同一实时刻、`HEq` 中心）。 -/
theorem volume_ball_final_P6M (hfin : K.time (Fin.last K.eventCount) < K.horizon) {T : ℝ}
    (hT : K.time (Fin.last K.eventCount) < T) (hTs : T < K.horizon)
    (E : ObservedHistory.{u}) (hE : E = ((K.prefixAt (Fin.last K.eventCount)).extendAt
      (K.prefixAt_time_last _) ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl)
      (K.final_initial hfin) hT hTs).toHistory)
    (τ : Icc (0 : ℝ) E.horizon) (τ' : Icc (0 : ℝ) K.toHistory.horizon) (hττ : (τ : ℝ) = τ')
    (p : (E.stageAt τ).Carrier) (p' : (K.toHistory.stageAt τ').Carrier) (hp : HEq p p')
    (b : ℝ) :
    riemannianVolumeMeasure ThreeModel (E.stageAt τ).Carrier
        (E.stageMetric (E.activeStage τ) τ)
        (riemannianBallOf (E.stageMetric (E.activeStage τ) τ) p b) =
      riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt τ').Carrier
        (K.toHistory.stageMetric (K.toHistory.activeStage τ') τ')
        (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ') τ') p' b) := by
  subst hE
  have hidx := K.activeStage_final_P6M hfin hT hTs τ τ' hττ
  have hmet := K.stageMetric_final_P6M hfin hT hTs
    (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
      ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
      hTs).toHistory.activeStage τ) τ
  rw [hττ] at hmet
  rw [hττ]
  exact volume_ball_congr_final_P6M K.toHistory hidx τ' _ hmet p p' hp b

/-- traced region E → K（`E` 抽象 + 等式形，供序列层逐 n 调用）。 -/
theorem isTracedRegion'_final_P6M (hfin : K.time (Fin.last K.eventCount) < K.horizon) {T : ℝ}
    (hT : K.time (Fin.last K.eventCount) < T) (hTs : T < K.horizon)
    (E : ObservedHistory.{u}) (hE : E = ((K.prefixAt (Fin.last K.eventCount)).extendAt
      (K.prefixAt_time_last _) ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl)
      (K.final_initial hfin) hT hTs).toHistory)
    (τ : Icc (0 : ℝ) E.horizon) (τ' : Icc (0 : ℝ) K.toHistory.horizon) (hττ : (τ : ℝ) = τ')
    (p : (E.stageAt τ).Carrier) (p' : (K.toHistory.stageAt τ').Carrier) (hp : HEq p p')
    {ρ δ C : ℝ} (h : E.isTracedRegion τ p ρ δ C) : K.toHistory.isTracedRegion τ' p' ρ δ C := by
  subst hE
  exact K.isTracedRegion_final_P6M hfin hT hTs τ τ' hττ p p' hp h

end RetainedCoreHistory

/-! ### 序列层（final slab）：P6D2 G3 的 `Hs`-层输入 ⇐ K 层；`DepthExtendable` 回 K -/

namespace ObservedHistory

variable {K : ℕ → RetainedCoreHistory.{u}} {t : ℕ → ℝ}
  {htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n} {htK : ∀ n, t n < (K n).horizon}
  {σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon} {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier}
  {Hs : ℕ → ObservedHistory.{u}} {ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon}
  {ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier} {R : ℕ → ℝ}

/-- **`_final_P6M`（序列 `hwit`）**：K 层（`σ n`、`y n`）⇒ `Hs n` = final 截断 history 层
（P6D2 G3 的 `hwit` 逐字形）。 -/
theorem hwit_seq_final_P6M
    (hHs : ∀ n, Hs n = (((K n).prefixAt (Fin.last (K n).eventCount)).extendAt
      ((K n).prefixAt_time_last _) (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming
        le_rfl ((htl n).trans (htK n)) le_rfl) ((K n).final_initial ((htl n).trans (htK n)))
      (htl n) (htK n)).toHistory)
    (hσ : ∀ n, (ts n : ℝ) = σ n) (hys : ∀ n, HEq (ys n) (y n)) {ε C1s C2s : ℝ} {qs : ℕ → ℝ}
    (hK : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
            (σ n)) (y n) (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (K n).toHistory.time ((K n).toHistory.activeStage v) < v →
        ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
          ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvt) x,
          qs n < metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            (tr.point ((K n).toHistory.activeStage v) le_rfl
              ((K n).toHistory.activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness
              ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) ε C1s C2s
              (tr.point ((K n).toHistory.activeStage v) le_rfl
                ((K n).toHistory.activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        (v : ℝ) < ts n → (Hs n).time ((Hs n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Hs n).stageMetric ((Hs n).activeStage v) v) ε C1s C2s
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε := by
  intro D T hD hT
  filter_upwards [hK D T hD hT] with n hn
  exact (K n).hwit_final_P6M ((htl n).trans (htK n)) (htl n) (htK n) (Hs n) (hHs n) (ts n) (σ n)
    (hσ n) (ys n) (y n) (hys n) hn

/-- **`_final_P6M`（序列 `hkappa`）**：K 层 trace-local κ ⇒ `Hs` 层（逐字形）。 -/
theorem hkappa_seq_final_P6M
    (hHs : ∀ n, Hs n = (((K n).prefixAt (Fin.last (K n).eventCount)).extendAt
      ((K n).prefixAt_time_last _) (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming
        le_rfl ((htl n).trans (htK n)) le_rfl) ((K n).final_initial ((htl n).trans (htK n)))
      (htl n) (htK n)).toHistory)
    (hσ : ∀ n, (ts n : ℝ) = σ n) (hys : ∀ n, HEq (ys n) (y n)) {κ : ℝ} {ρnc : ℕ → ℝ}
    (hK : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
            (σ n)) (y n) (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
          ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (K n).toHistory.isParabolicallyRmControlledBall v
            (tr.point ((K n).toHistory.activeStage v) le_rfl
              ((K n).toHistory.activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume
              ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              (tr.point ((K n).toHistory.activeStage v) le_rfl
                ((K n).toHistory.activeStage_mono hvt)) r'') :
    ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Hs n).isParabolicallyRmControlledBall v
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) r'' := by
  intro D T hD hT
  filter_upwards [hK D T hD hT] with n hn
  exact (K n).hkappa_final_P6M ((htl n).trans (htK n)) (htl n) (htK n) (Hs n) (hHs n) (ts n)
    (σ n) (hσ n) (ys n) (y n) (hys n) hn

/-- **`_final_P6M`（序列 `hbcad`）**：K 层双 trace BCAD ⇒ `Hs` 层（逐字形）。 -/
theorem hbcad_seq_final_P6M
    (hHs : ∀ n, Hs n = (((K n).prefixAt (Fin.last (K n).eventCount)).extendAt
      ((K n).prefixAt_time_last _) (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming
        le_rfl ((htl n).trans (htK n)) le_rfl) ((K n).final_initial ((htl n).trans (htK n)))
      (htl n) (htK n)).toHistory)
    (hσ : ∀ n, (ts n : ℝ) = σ n) (hys : ∀ n, HEq (ys n) (y n))
    (hK : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw →
        ∀ᶠ n in atTop,
        ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
            (σ n)) (y n) (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
            (σ n)) (y n) (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hvt : v ≤ σ n),
          (v : ℝ) = σ n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
            ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
            ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvt) x₂),
          metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              (tr₁.point ((K n).toHistory.activeStage v) le_rfl
                ((K n).toHistory.activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              (tr₁.point ((K n).toHistory.activeStage v) le_rfl
                ((K n).toHistory.activeStage_mono hvt))
              (tr₂.point ((K n).toHistory.activeStage v) le_rfl
                ((K n).toHistory.activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              (tr₂.point ((K n).toHistory.activeStage v) le_rfl
                ((K n).toHistory.activeStage_mono hvt)) ≤ C * R n) :
    ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw →
        ∀ᶠ n in atTop,
        ∀ x₁ ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (v : ℝ) = ts n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
            ((Hs n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
            ((Hs n).activeStage_mono hvt) x₂),
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr₁.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr₁.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt))
              (tr₂.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr₂.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ≤
            C * R n := by
  intro A Dd hA hDd
  obtain ⟨C, hC⟩ := hK A Dd hA hDd
  refine ⟨C, fun σ' hσ' Dw hDw => ?_⟩
  filter_upwards [hC σ' hσ' Dw hDw] with n hn
  exact (K n).hbcad_final_P6M ((htl n).trans (htK n)) (htl n) (htK n) (Hs n) (hHs n) (ts n)
    (σ n) (hσ n) (ys n) (y n) (hys n) hn

/-- **`_final_P6M`（序列 `hseed`）**：K 层基点种子体积 ⇒ `Hs` 层（逐字形）。 -/
theorem hseed_seq_final_P6M
    (hHs : ∀ n, Hs n = (((K n).prefixAt (Fin.last (K n).eventCount)).extendAt
      ((K n).prefixAt_time_last _) (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming
        le_rfl ((htl n).trans (htK n)) le_rfl) ((K n).final_initial ((htl n).trans (htK n)))
      (htl n) (htK n)).toHistory)
    (hσ : ∀ n, (ts n : ℝ) = σ n) (hys : ∀ n, HEq (ys n) (y n)) {r₀ w : ℝ}
    (hK : ∀ᶠ n in atTop,
      ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
        riemannianVolumeMeasure ThreeModel ((K n).toHistory.stageAt (σ n)).Carrier
          ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
          (riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
            (σ n)) (y n) (r₀ / Real.sqrt (R n)))) :
    ∀ᶠ n in atTop,
      ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
        riemannianVolumeMeasure ThreeModel ((Hs n).stageAt (ts n)).Carrier
          ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
          (riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (r₀ / Real.sqrt (R n))) := by
  filter_upwards [hK] with n hn
  rw [(K n).volume_ball_final_P6M ((htl n).trans (htK n)) (htl n) (htK n) (Hs n) (hHs n) (ts n)
    (σ n) (hσ n) (ys n) (y n) (hys n)]
  exact hn

/-- **`_final_P6M`（`htraced` 回 K）**：`Hs` 层 `DepthExtendable`（P6D2 G3 输出）⇒ K 层
`DepthExtendable`（同子列、同深度）。 -/
theorem depthExtendable_final_P6M
    (hHs : ∀ n, Hs n = (((K n).prefixAt (Fin.last (K n).eventCount)).extendAt
      ((K n).prefixAt_time_last _) (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming
        le_rfl ((htl n).trans (htK n)) le_rfl) ((K n).final_initial ((htl n).trans (htK n)))
      (htl n) (htK n)).toHistory)
    (hσ : ∀ n, (ts n : ℝ) = σ n) (hys : ∀ n, HEq (ys n) (y n)) {ψ : ℕ → ℕ} {T : ℝ}
    (h : DepthExtendable Hs ts ys R ψ T) :
    DepthExtendable (fun n => (K n).toHistory) σ y R ψ T := by
  intro A hA
  obtain ⟨C, hC, hev⟩ := h A hA
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev] with i hi
  exact (K (ψ i)).isTracedRegion'_final_P6M ((htl (ψ i)).trans (htK (ψ i))) (htl (ψ i))
    (htK (ψ i)) (Hs (ψ i)) (hHs (ψ i)) (ts (ψ i)) (σ (ψ i)) (hσ (ψ i)) (ys (ψ i)) (y (ψ i))
    (hys (ψ i)) hi

end ObservedHistory

/-- consumer（L-RS `hnc` 推回树内形，final slab）：K 层全局 `NoncollapsedBefore κ ρ t` ⇒ SLT 的 `hnc`
（`U = univ`、`a = time last`）——即树内 `terminalNoncollapsedBefore_finalSlab` 的 tested-ball 版。 -/
example (K : RetainedCoreHistory.{u}) (hfin : K.time (Fin.last K.eventCount) < K.horizon)
    {κ ρ t : ℝ} (hH : K.NoncollapsedBefore κ ρ t)
    (hend : (K.prefixAt (Fin.last K.eventCount)).time
        (Fin.last (K.prefixAt (Fin.last K.eventCount)).eventCount) =
      (K.prefixAt (Fin.last K.eventCount)).horizon) :
    ∀ (T : ℝ) (hT : (K.prefixAt (Fin.last K.eventCount)).time
        (Fin.last (K.prefixAt (Fin.last K.eventCount)).eventCount) < T)
      (hTs : T < K.horizon), T ≤ t → K.time (Fin.last K.eventCount) ≤ T →
        let B := (K.prefixAt (Fin.last K.eventCount)).extendHorizon T (hend ▸ hT.le)
          (((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).closedPrefix T hT hTs)
          (K.final_initial hfin)
        let tm : Icc (0 : ℝ) B.horizon :=
          ⟨T, (K.prefixAt (Fin.last K.eventCount)).horizon_nonneg.trans (hend ▸ hT.le), le_rfl⟩
        ∀ z ∈ (univ : Set (K.stage (Fin.last K.eventCount)).Carrier),
        ∀ (yy : (B.toHistory.stageAt tm).Carrier), HEq yy z → ∀ (b : ℝ), 0 < b → b ≤ ρ →
          B.toHistory.isParabolicallyRmControlledBall tm yy b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
                (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                  yy b) :=
  K.tested_noncollapse_final_P6M hfin univ
    (fun τ _ hτt _ _ _ _ zz _ b _ hbρ hball => hH τ zz b hτt hbρ hball) hend

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

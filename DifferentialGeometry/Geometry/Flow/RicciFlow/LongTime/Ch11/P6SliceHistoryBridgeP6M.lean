import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryPrefixTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryExtendAt
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitness
import DifferentialGeometry.Geometry.Collapse.CurvatureScale
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionMaximalDepth

/-!
# 桥（L-RS 收尾 + G3）：`K.eventPrefix j T` ↔ `K` 的 traced region / 受控球 / tested κ（`_P6M`）

selection 在 `K : RetainedCoreHistory` 的 `toHistory` 上；SLT / P6D2 G3 在
`E := K.eventPrefix j T = (K.prefixAt j.castSucc).extendAt rfl (K.event j).incoming …`（定义等，
`T ∈ (time j.castSucc, time j.succ)`）上。树内 `RetainedCoreHistoryPrefixTransport` 已有 `activeStage`
（`eventPrefix_activeStage_val`）与 `stageMetric`（`eventPrefix_stageMetric`）识别，以及**全局**
`NoncollapsedBefore` 的 transport `noncollapsedBefore_eventPrefix`。本文件把其中的受控球识别证法
（E 的 trace ↦ `backwardPointTraceOfPrefix`，stage 指标 `subst` 推广）**局部化**：
* `isTracedRegion_of_eventPrefix_P6M`：E 的 traced region ⇒ K 的 traced region（同一实时刻、同一中心，
  `HEq`）；`isParabolicallyRmControlledBall_of_eventPrefix_P6M`：受控球同理（经树内
  `isParabolicallyRmControlledBall_iff_isTracedRegion`）。
* **L-RS `hnc`**（P6CON HANDOVER 第 2 项"唯一非机械项"）`tested_noncollapse_eventPrefix_P6M`：K 层
  **区域 / 窗口形** tested κ（`a ≤ τ ≤ t`、中心 `∈ U`）⇒ SLT（`_P6L` / 窗口版）的 `hnc` 形
  （`H := K.prefixAt j.castSucc`、`G := (K.event j).incoming`，每个 `T ≤ t` 的 `extendHorizon`）。
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

/-- stage 指标推广：`m' = m` 时 `‖Rm‖² ≤ C²` 在两种指标写法间搬运。 -/
private theorem rm_sq_bound_of_stage_eq_P6M {H : ObservedHistory.{u}}
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
private theorem isTracedRegion_of_stage_index_P6M (H : ObservedHistory.{u})
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

/-- **`_P6M`（桥 E → K）**：`K.eventPrefix j T` 的 traced region（时刻 `τ`、中心 `p`）⇒ `K` 的 traced
region（同一实时刻 `τ'`、`HEq` 中心 `p'`），半径 / 深度 / 曲率界不变。证法 = 树内
`noncollapsedBefore_eventPrefix` 的受控球识别（trace 经 `backwardPointTraceOfPrefix` 上推）。 -/
theorem isTracedRegion_of_eventPrefix_P6M (j : Fin K.eventCount) {T : ℝ}
    (hjT : K.time j.castSucc < T) (hTj : T < K.time j.succ)
    (τ : Icc (0 : ℝ) (K.eventPrefix j T hjT hTj).toHistory.horizon)
    (τ' : Icc (0 : ℝ) K.toHistory.horizon) (hττ : (τ : ℝ) = τ')
    (p : ((K.eventPrefix j T hjT hTj).toHistory.stageAt τ).Carrier)
    (p' : (K.toHistory.stageAt τ').Carrier) (hp : HEq p p') {ρ δ C : ℝ}
    (h : (K.eventPrefix j T hjT hTj).toHistory.isTracedRegion τ p ρ δ C) :
    K.toHistory.isTracedRegion τ' p' ρ δ C := by
  have hTH : T ≤ K.horizon := hTj.le.trans (K.toHistory.time_le_horizon_at j.succ)
  obtain ⟨hρ, hδ, a, hat, ha, htr⟩ := h
  let a' : Icc (0 : ℝ) K.toHistory.horizon := ⟨a, a.2.1, a.2.2.trans hTH⟩
  have hAτ := K.eventPrefix_activeStage_val j hjT hTj τ τ' hττ
  have hAa := K.eventPrefix_activeStage_val j hjT hTj a a' rfl
  have hka := (K.eventPrefix j T hjT hTj).toHistory.activeStage_mono hat
  have hat' : a' ≤ τ' := show (a : ℝ) ≤ τ' from hττ ▸ hat
  have ha' : (a' : ℝ) = (τ' : ℝ) - δ := by
    change (a : ℝ) = (τ' : ℝ) - δ
    rw [← hττ]
    exact ha
  refine isTracedRegion_of_stage_index_P6M K.toHistory τ'
    (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt))
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ)) (Fin.ext hAτ.symm) p p' hp hρ hδ a'
    hat' ha' (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt))
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage a))
    (Fin.le_def.mpr (le_of_eq hAa)) (Fin.le_def.mpr (Fin.le_def.mp hka)) ?_
  intro x hx
  have hx' : x ∈ riemannianBallOf ((K.eventPrefix j T hjT hTj).toHistory.stageMetric
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ) τ) p ρ := by
    rw [K.eventPrefix_stageMetric j hjT hTj, hττ]
    exact hx
  obtain ⟨A, hA1, hA2⟩ := htr x hx'
  refine ⟨K.backwardPointTraceOfPrefix j.castSucc ⟨A.point, A.endpoint_eq, A.crossing⟩, ?_, ?_⟩
  · intro v hav hvt
    have hvT : (v : ℝ) ≤ T := (show (v : ℝ) ≤ τ' from hvt).trans (hττ ▸ τ.2.2)
    let vK : Icc (0 : ℝ) (K.eventPrefix j T hjT hTj).toHistory.horizon := ⟨v, v.2.1, hvT⟩
    have hAv := K.eventPrefix_activeStage_val j hjT hTj vK v rfl
    have hav' : a ≤ vK := show (a : ℝ) ≤ v from hav
    have hvt' : vK ≤ τ := show (v : ℝ) ≤ τ from hττ ▸ hvt
    have h := hA1 vK hav' hvt'
    rw [K.eventPrefix_stageMetric j hjT hTj] at h
    refine rm_sq_bound_of_stage_eq_P6M _ (m' := Fin.castLE
      (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt))
        ((K.eventPrefix j T hjT hTj).toHistory.activeStage vK))
      (m := K.toHistory.activeStage v) (Fin.ext hAv) _ _
      (Fin.le_def.mpr (Fin.le_def.mp
        ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono hav')))
      (Fin.le_def.mpr (Fin.le_def.mp
        ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono hvt'))) v C ?_
    exact h
  · intro i hi hil
    have hil' : i.val + 1 ≤ ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ).val :=
      Fin.le_def.mp hil
    have hkj : ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ).val < j.val + 1 :=
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ).isLt
    have hi' : ((K.eventPrefix j T hjT hTj).toHistory.activeStage a).val ≤ i.val := by
      rw [hAa]
      exact Fin.le_def.mp hi
    exact hA2 ⟨i.val, by
        change i.val < j.val
        omega⟩ (Fin.le_def.mpr hi') (Fin.le_def.mpr hil')

/-- **`_P6M`（桥 E → K）**：E 的受控抛物球 ⇒ K 的受控抛物球（同一实时刻、`HEq` 中心、同半径）。 -/
theorem isParabolicallyRmControlledBall_of_eventPrefix_P6M (j : Fin K.eventCount) {T : ℝ}
    (hjT : K.time j.castSucc < T) (hTj : T < K.time j.succ)
    (τ : Icc (0 : ℝ) (K.eventPrefix j T hjT hTj).toHistory.horizon)
    (τ' : Icc (0 : ℝ) K.toHistory.horizon) (hττ : (τ : ℝ) = τ')
    (p : ((K.eventPrefix j T hjT hTj).toHistory.stageAt τ).Carrier)
    (p' : (K.toHistory.stageAt τ').Carrier) (hp : HEq p p') {r : ℝ}
    (h : (K.eventPrefix j T hjT hTj).toHistory.isParabolicallyRmControlledBall τ p r) :
    K.toHistory.isParabolicallyRmControlledBall τ' p' r :=
  (K.toHistory.isParabolicallyRmControlledBall_iff_isTracedRegion τ' p' r).2
    (K.isTracedRegion_of_eventPrefix_P6M j hjT hTj τ τ' hττ p p' hp
      (((K.eventPrefix j T hjT hTj).toHistory.isParabolicallyRmControlledBall_iff_isTracedRegion
        τ p r).1 h))

/-- 体积按 stage 指标搬运（`m = m'`、度量 `g = stageMetric m v`、中心 `HEq`）。 -/
private theorem volume_ball_congr_P6M (H : ObservedHistory.{u}) {m m' : Fin (H.eventCount + 1)}
    (hm : m = m') (v : ℝ) (g : (H.stage m).Metric) (hg : g = H.stageMetric m v)
    (p : (H.stage m).Carrier) (p' : (H.stage m').Carrier) (hp : HEq p p') (b : ℝ) :
    riemannianVolumeMeasure ThreeModel (H.stage m).Carrier g (riemannianBallOf g p b) =
      riemannianVolumeMeasure ThreeModel (H.stage m').Carrier (H.stageMetric m' v)
        (riemannianBallOf (H.stageMetric m' v) p' b) := by
  subst hg
  subst hm
  obtain rfl := eq_of_heq hp
  rfl

/-- **`_P6M`（L-RS `hnc`）**：K 层区域 / 窗口形 tested κ（`a ≤ τ ≤ t`、`τ` 在 event slab `j` 内部、中心
`∈ U`）⇒ SLT 的 `hnc` 形（`H := K.prefixAt j.castSucc`、`G := (K.event j).incoming`；每个
`T ∈ (time j.castSucc, t]`、`a ≤ T` 的 `extendHorizon`）。`a` 任取（`a = time j.castSucc` 即 `_P6L` 原形，
`a = t − Bw/R` 即窗口形）。 -/
theorem tested_noncollapse_eventPrefix_P6M (j : Fin K.eventCount) {κ ρ a t : ℝ}
    (U : Set (K.stage j.castSucc).Carrier)
    (hK : ∀ (τ : Icc (0 : ℝ) K.toHistory.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
      K.time j.castSucc < τ → (τ : ℝ) < K.time j.succ →
      ∀ z ∈ U, ∀ zz : (K.toHistory.stageAt τ).Carrier, HEq zz z →
      ∀ b : ℝ, 0 < b → b ≤ ρ → K.toHistory.isParabolicallyRmControlledBall τ zz b →
        ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
          riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt τ).Carrier
            (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
            (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) zz b))
    (hend : (K.prefixAt j.castSucc).time (Fin.last (K.prefixAt j.castSucc).eventCount) =
      (K.prefixAt j.castSucc).horizon) :
    ∀ (T : ℝ) (hT : (K.prefixAt j.castSucc).time (Fin.last (K.prefixAt j.castSucc).eventCount) < T)
      (hTs : T < K.time j.succ), T ≤ t → a ≤ T →
        let B := (K.prefixAt j.castSucc).extendHorizon T (hend ▸ hT.le)
          ((K.toHistory.event j).incoming.closedPrefix T hT hTs) (K.event_initial j)
        let tm : Icc (0 : ℝ) B.horizon :=
          ⟨T, (K.prefixAt j.castSucc).horizon_nonneg.trans (hend ▸ hT.le), le_rfl⟩
        ∀ z ∈ U, ∀ (yy : (B.toHistory.stageAt tm).Carrier), HEq yy z →
        ∀ (b : ℝ), 0 < b → b ≤ ρ →
          B.toHistory.isParabolicallyRmControlledBall tm yy b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
                (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                  yy b) := by
  intro T hT hTs hTt haT B tm z hz yy hyy b hb hbρ hball
  have hTH : T ≤ K.horizon := hTs.le.trans (K.toHistory.time_le_horizon_at j.succ)
  let τ' : Icc (0 : ℝ) K.toHistory.horizon := ⟨T, tm.2.1, hTH⟩
  have hAτ := K.eventPrefix_activeStage_val j hT hTs tm τ' rfl
  have hidx : Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt))
      (B.toHistory.activeStage tm) = K.toHistory.activeStage τ' := Fin.ext hAτ
  let zz : (K.toHistory.stageAt τ').Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hidx) yy
  have hzz : HEq zz yy := cast_heq _ _
  have hball' := K.isParabolicallyRmControlledBall_of_eventPrefix_P6M j hT hTs tm τ' rfl yy zz
    hzz.symm hball
  have h := hK τ' haT hTt hT hTs z hz zz (hzz.trans hyy) b hb hbρ hball'
  have hmet := K.eventPrefix_stageMetric j hT hTs (B.toHistory.activeStage tm) T
  refine h.trans (le_of_eq ?_)
  exact (volume_ball_congr_P6M K.toHistory hidx T
    ((K.eventPrefix j T hT hTs).toHistory.stageMetric (B.toHistory.activeStage tm) T) hmet yy zz
    hzz.symm b).symm

/-- consumer（L-RS `hnc` 推回树内形）：K 层全局 `NoncollapsedBefore κ ρ t` ⇒ SLT 的 `hnc`
（`U = univ`、`a = time j.castSucc`）——即树内 `terminalNoncollapsedBefore_prefixAt` 的 tested-ball 版。 -/
example (j : Fin K.eventCount) {κ ρ t : ℝ} (hH : K.NoncollapsedBefore κ ρ t)
    (hend : (K.prefixAt j.castSucc).time (Fin.last (K.prefixAt j.castSucc).eventCount) =
      (K.prefixAt j.castSucc).horizon) :
    ∀ (T : ℝ) (hT : (K.prefixAt j.castSucc).time (Fin.last (K.prefixAt j.castSucc).eventCount) < T)
      (hTs : T < K.time j.succ), T ≤ t → K.time j.castSucc ≤ T →
        let B := (K.prefixAt j.castSucc).extendHorizon T (hend ▸ hT.le)
          ((K.toHistory.event j).incoming.closedPrefix T hT hTs) (K.event_initial j)
        let tm : Icc (0 : ℝ) B.horizon :=
          ⟨T, (K.prefixAt j.castSucc).horizon_nonneg.trans (hend ▸ hT.le), le_rfl⟩
        ∀ z ∈ (univ : Set (K.stage j.castSucc).Carrier), ∀ (yy : (B.toHistory.stageAt tm).Carrier),
        HEq yy z → ∀ (b : ℝ), 0 < b → b ≤ ρ →
          B.toHistory.isParabolicallyRmControlledBall tm yy b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
                (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                  yy b) :=
  K.tested_noncollapse_eventPrefix_P6M j univ
    (fun τ _ hτt _ _ _ _ zz _ b _ hbρ hball => hH τ zz b hτt hbρ hball) hend


/-! ### 桥 K → E：trace-local 前提的 pullback（P6D2 G3 / P6ClosureP6D2 的 `Hs`-层输入） -/

/-- trace 指标推广：首末 stage 指标与端点 `HEq` 一致时，K 层"对所有 trace"的结论搬到给定 trace。 -/
private theorem trace_index_P6M (H : ObservedHistory.{u})
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
private theorem trace_index₂_P6M (H : ObservedHistory.{u})
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

/-- **`_P6M`（桥 K → E，单 trace 通用形）**：E 的 trace（`v ≤ τ`）经 `backwardPointTraceOfPrefix` 上推成
K 的 trace（同实时刻 `v' τ'`），K 层"对所有 trace 成立"的点态性质 `P` 回落到 E 的 trace 点
（stage 指标写作 `Fin.castLE (E.activeStage v)`，载体定义等）。 -/
theorem forall_trace_eventPrefix_P6M (j : Fin K.eventCount) {T : ℝ}
    (hjT : K.time j.castSucc < T) (hTj : T < K.time j.succ)
    (τ v : Icc (0 : ℝ) (K.eventPrefix j T hjT hTj).toHistory.horizon) (hvτ : v ≤ τ)
    (τ' v' : Icc (0 : ℝ) K.toHistory.horizon) (hττ : (τ : ℝ) = τ') (hvv : (v : ℝ) = v')
    (x : ((K.eventPrefix j T hjT hTj).toHistory.stageAt τ).Carrier)
    (x' : (K.toHistory.stageAt τ').Carrier) (hx : HEq x x')
    (P : ∀ m : Fin (K.eventCount + 1), (K.stage m).Carrier → Prop)
    (hK : ∀ (hvτ' : v' ≤ τ') (tr' : BackwardPointTrace K.toHistory (K.toHistory.activeStage v')
        (K.toHistory.activeStage τ') (K.toHistory.activeStage_mono hvτ') x'),
      P (K.toHistory.activeStage v')
        (tr'.point (K.toHistory.activeStage v') le_rfl (K.toHistory.activeStage_mono hvτ')))
    (tr : BackwardPointTrace (K.eventPrefix j T hjT hTj).toHistory
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage v)
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ)
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono hvτ) x) :
    P (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt))
        ((K.eventPrefix j T hjT hTj).toHistory.activeStage v))
      (tr.point ((K.eventPrefix j T hjT hTj).toHistory.activeStage v) le_rfl
        ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono hvτ)) := by
  have hvτ' : v' ≤ τ' := show (v' : ℝ) ≤ τ' from hvv ▸ hττ ▸ hvτ
  have hAv := K.eventPrefix_activeStage_val j hjT hTj v v' hvv
  have hAτ := K.eventPrefix_activeStage_val j hjT hTj τ τ' hττ
  exact trace_index_P6M K.toHistory P (Fin.ext hAv) (Fin.ext hAτ) hx
    (K.backwardPointTraceOfPrefix j.castSucc ⟨tr.point, tr.endpoint_eq, tr.crossing⟩) (hK hvτ')

/-- **`_P6M`（桥 K → E，双 trace 通用形）**：`hbcad` 用。 -/
theorem forall_trace₂_eventPrefix_P6M (j : Fin K.eventCount) {T : ℝ}
    (hjT : K.time j.castSucc < T) (hTj : T < K.time j.succ)
    (τ v : Icc (0 : ℝ) (K.eventPrefix j T hjT hTj).toHistory.horizon) (hvτ : v ≤ τ)
    (τ' v' : Icc (0 : ℝ) K.toHistory.horizon) (hττ : (τ : ℝ) = τ') (hvv : (v : ℝ) = v')
    (x₁ x₂ : ((K.eventPrefix j T hjT hTj).toHistory.stageAt τ).Carrier)
    (x₁' x₂' : (K.toHistory.stageAt τ').Carrier) (hx₁ : HEq x₁ x₁') (hx₂ : HEq x₂ x₂')
    (P : ∀ m : Fin (K.eventCount + 1), (K.stage m).Carrier → (K.stage m).Carrier → Prop)
    (hK : ∀ (hvτ' : v' ≤ τ')
      (tr₁' : BackwardPointTrace K.toHistory (K.toHistory.activeStage v')
        (K.toHistory.activeStage τ') (K.toHistory.activeStage_mono hvτ') x₁')
      (tr₂' : BackwardPointTrace K.toHistory (K.toHistory.activeStage v')
        (K.toHistory.activeStage τ') (K.toHistory.activeStage_mono hvτ') x₂'),
      P (K.toHistory.activeStage v')
        (tr₁'.point (K.toHistory.activeStage v') le_rfl (K.toHistory.activeStage_mono hvτ'))
        (tr₂'.point (K.toHistory.activeStage v') le_rfl (K.toHistory.activeStage_mono hvτ')))
    (tr₁ : BackwardPointTrace (K.eventPrefix j T hjT hTj).toHistory
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage v)
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ)
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono hvτ) x₁)
    (tr₂ : BackwardPointTrace (K.eventPrefix j T hjT hTj).toHistory
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage v)
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ)
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono hvτ) x₂) :
    P (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt))
        ((K.eventPrefix j T hjT hTj).toHistory.activeStage v))
      (tr₁.point ((K.eventPrefix j T hjT hTj).toHistory.activeStage v) le_rfl
        ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono hvτ))
      (tr₂.point ((K.eventPrefix j T hjT hTj).toHistory.activeStage v) le_rfl
        ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono hvτ)) := by
  have hvτ' : v' ≤ τ' := show (v' : ℝ) ≤ τ' from hvv ▸ hττ ▸ hvτ
  have hAv := K.eventPrefix_activeStage_val j hjT hTj v v' hvv
  have hAτ := K.eventPrefix_activeStage_val j hjT hTj τ τ' hττ
  exact trace_index₂_P6M K.toHistory P (Fin.ext hAv) (Fin.ext hAτ) hx₁ hx₂
    (K.backwardPointTraceOfPrefix j.castSucc ⟨tr₁.point, tr₁.endpoint_eq, tr₁.crossing⟩)
    (K.backwardPointTraceOfPrefix j.castSucc ⟨tr₂.point, tr₂.endpoint_eq, tr₂.crossing⟩)
    (hK hvτ')

/-- 球成员按 stage 指标搬运（`m = m'`、度量 `g = stageMetric m v`、`HEq` 中心与点）。 -/
private theorem mem_ball_congr_P6M (H : ObservedHistory.{u}) {m m' : Fin (H.eventCount + 1)}
    (hm : m = m') (v : ℝ) (g : (H.stage m).Metric) (hg : g = H.stageMetric m v)
    (p x : (H.stage m).Carrier) (p' x' : (H.stage m').Carrier) (hp : HEq p p') (hx : HEq x x')
    (b : ℝ) (h : x ∈ riemannianBallOf g p b) : x' ∈ riemannianBallOf (H.stageMetric m' v) p' b := by
  subst hg
  subst hm
  obtain rfl := eq_of_heq hp
  obtain rfl := eq_of_heq hx
  exact h

/-- **`_P6M`（桥 K → E，基点球）**：E 在时刻 `τ` 的球成员 ⇒ K 在同一实时刻的球成员（`HEq` 搬运）。 -/
theorem mem_ball_of_eventPrefix_P6M (j : Fin K.eventCount) {T : ℝ}
    (hjT : K.time j.castSucc < T) (hTj : T < K.time j.succ)
    (τ : Icc (0 : ℝ) (K.eventPrefix j T hjT hTj).toHistory.horizon)
    (τ' : Icc (0 : ℝ) K.toHistory.horizon) (hττ : (τ : ℝ) = τ')
    (p x : ((K.eventPrefix j T hjT hTj).toHistory.stageAt τ).Carrier)
    (p' x' : (K.toHistory.stageAt τ').Carrier) (hp : HEq p p') (hx : HEq x x') (b : ℝ)
    (h : x ∈ riemannianBallOf ((K.eventPrefix j T hjT hTj).toHistory.stageMetric
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ) τ) p b) :
    x' ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ') τ') p' b := by
  have hAτ := K.eventPrefix_activeStage_val j hjT hTj τ τ' hττ
  have hmet := K.eventPrefix_stageMetric j hjT hTj
    ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ) τ
  rw [hττ] at hmet
  rw [hττ] at h
  exact mem_ball_congr_P6M K.toHistory (Fin.ext hAτ) τ' _ hmet p x p' x' hp hx b h

/-- **`_P6M`（K → E，`hwit` 单 history 形）**：K 层窗口 witness（中心 `p'`、半径 `ρ`、深度 `θ`）⇒ E 层同形。 -/
theorem hwit_of_eventPrefix_P6M (j : Fin K.eventCount) {T : ℝ}
    (hjT : K.time j.castSucc < T) (hTj : T < K.time j.succ)
    (E : ObservedHistory.{u}) (hE : E = (K.eventPrefix j T hjT hTj).toHistory)
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
  have hTH : T ≤ K.horizon := hTj.le.trans (K.toHistory.time_le_horizon_at j.succ)
  let v' : Icc (0 : ℝ) K.toHistory.horizon := ⟨v, v.2.1, v.2.2.trans hTH⟩
  have hidx : Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt))
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ) = K.toHistory.activeStage τ' :=
    Fin.ext (K.eventPrefix_activeStage_val j hjT hTj τ τ' hττ)
  let x' : (K.toHistory.stageAt τ').Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hidx) x
  have hxx : HEq x x' := (cast_heq _ _).symm
  have hx' := K.mem_ball_of_eventPrefix_P6M j hjT hTj τ τ' hττ p x p' x' hp hxx ρ hx
  have h := K.forall_trace_eventPrefix_P6M j hjT hTj τ v hvt τ' v' hττ rfl x x' hxx
    (fun m pt => K.time m < v → qs < metricScalarAt (K.toHistory.stageMetric m v) pt →
      ∃ Wt : SpatialCanonicalWitness (K.toHistory.stageMetric m v) ε C1s C2s pt,
        Wt.capTubeHasNeckChart ε)
    (fun hvτ' tr' hage' hq' => hK x' hx' v' hvτ' (by rw [← hττ]; exact hθ)
      (by rw [← hττ]; exact hvτ) hage' tr' hq') tr
  have hmet := K.eventPrefix_stageMetric j hjT hTj
    ((K.eventPrefix j T hjT hTj).toHistory.activeStage v) v
  rw [hmet] at hq ⊢
  exact h hage hq

/-- **`_P6M`（K → E，`hkappa` 单 history 形）**：K 层 trace-local κ（受控球 ⇒ 体积）⇒ E 层同形；
E 的受控球经 `isParabolicallyRmControlledBall_of_eventPrefix_P6M` 回到 K。 -/
theorem hkappa_of_eventPrefix_P6M (j : Fin K.eventCount) {T : ℝ}
    (hjT : K.time j.castSucc < T) (hTj : T < K.time j.succ)
    (E : ObservedHistory.{u}) (hE : E = (K.eventPrefix j T hjT hTj).toHistory)
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
  have hTH : T ≤ K.horizon := hTj.le.trans (K.toHistory.time_le_horizon_at j.succ)
  let v' : Icc (0 : ℝ) K.toHistory.horizon := ⟨v, v.2.1, v.2.2.trans hTH⟩
  have hidx : Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt))
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ) = K.toHistory.activeStage τ' :=
    Fin.ext (K.eventPrefix_activeStage_val j hjT hTj τ τ' hττ)
  let x' : (K.toHistory.stageAt τ').Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hidx) x
  have hxx : HEq x x' := (cast_heq _ _).symm
  have hx' := K.mem_ball_of_eventPrefix_P6M j hjT hTj τ τ' hττ p x p' x' hp hxx ρ hx
  have h := K.forall_trace_eventPrefix_P6M j hjT hTj τ v hvt τ' v' hττ rfl x x' hxx
    (fun m pt => (∀ pt' : (K.toHistory.stageAt v').Carrier, HEq pt' pt →
        K.toHistory.isParabolicallyRmControlledBall v' pt' r'') →
      ENNReal.ofReal (κ * r'' ^ 3) ≤
        Geometry.Collapse.ballVolume (K.toHistory.stageMetric m v) pt r'')
    (fun hvτ' tr' hc => hK x' hx' v' hvτ' (by rw [← hττ]; exact hθ) tr' r'' hr hrρ
      (hc _ HEq.rfl)) tr
  have hc : ∀ pt' : (K.toHistory.stageAt v').Carrier,
      HEq pt' (tr.point ((K.eventPrefix j T hjT hTj).toHistory.activeStage v) le_rfl
        ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono hvt)) →
      K.toHistory.isParabolicallyRmControlledBall v' pt' r'' := fun pt' hpt =>
    K.isParabolicallyRmControlledBall_of_eventPrefix_P6M j hjT hTj v v' rfl _ pt' hpt.symm hball
  have hmet := K.eventPrefix_stageMetric j hjT hTj
    ((K.eventPrefix j T hjT hTj).toHistory.activeStage v) v
  rw [hmet]
  exact h hc

/-- **`_P6M`（K → E，`hbcad` 单 history 形）**：K 层双 trace BCAD（固定 `v`、阈值 `A'`、距离 `Dd'`、
界 `C'`）⇒ E 层同形。 -/
theorem hbcad_of_eventPrefix_P6M (j : Fin K.eventCount) {T : ℝ}
    (hjT : K.time j.castSucc < T) (hTj : T < K.time j.succ)
    (E : ObservedHistory.{u}) (hE : E = (K.eventPrefix j T hjT hTj).toHistory)
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
  have hTH : T ≤ K.horizon := hTj.le.trans (K.toHistory.time_le_horizon_at j.succ)
  let v' : Icc (0 : ℝ) K.toHistory.horizon := ⟨v, v.2.1, v.2.2.trans hTH⟩
  have hidx : Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt))
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ) = K.toHistory.activeStage τ' :=
    Fin.ext (K.eventPrefix_activeStage_val j hjT hTj τ τ' hττ)
  let x₁' : (K.toHistory.stageAt τ').Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hidx) x₁
  let x₂' : (K.toHistory.stageAt τ').Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hidx) x₂
  have hxx₁ : HEq x₁ x₁' := (cast_heq _ _).symm
  have hxx₂ : HEq x₂ x₂' := (cast_heq _ _).symm
  have hx₁' := K.mem_ball_of_eventPrefix_P6M j hjT hTj τ τ' hττ p x₁ p' x₁' hp hxx₁ ρ hx₁
  have hx₂' := K.mem_ball_of_eventPrefix_P6M j hjT hTj τ τ' hττ p x₂ p' x₂' hp hxx₂ ρ hx₂
  have h := K.forall_trace₂_eventPrefix_P6M j hjT hTj τ v hvt τ' v' hττ rfl x₁ x₂ x₁' x₂'
    hxx₁ hxx₂
    (fun m p₁ p₂ => metricScalarAt (K.toHistory.stageMetric m v) p₁ ≤ A' →
      riemannianEDistOf (K.toHistory.stageMetric m v) p₁ p₂ < ENNReal.ofReal Dd' →
      metricScalarAt (K.toHistory.stageMetric m v) p₂ ≤ C')
    (fun hvτ' tr₁' tr₂' => hK x₁' hx₁' x₂' hx₂' v' hvτ' (by rw [← hττ]; exact hv) tr₁' tr₂')
    tr₁ tr₂
  have hmet := K.eventPrefix_stageMetric j hjT hTj
    ((K.eventPrefix j T hjT hTj).toHistory.activeStage v) v
  rw [hmet] at hA hD ⊢
  exact h hA hD

/-- **`_P6M`（K → E，`hseed` 单 history 形）**：基点球体积（同一实时刻、`HEq` 中心）。 -/
theorem volume_ball_of_eventPrefix_P6M (j : Fin K.eventCount) {T : ℝ}
    (hjT : K.time j.castSucc < T) (hTj : T < K.time j.succ)
    (E : ObservedHistory.{u}) (hE : E = (K.eventPrefix j T hjT hTj).toHistory)
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
  have hidx : Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt))
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ) = K.toHistory.activeStage τ' :=
    Fin.ext (K.eventPrefix_activeStage_val j hjT hTj τ τ' hττ)
  have hmet := K.eventPrefix_stageMetric j hjT hTj
    ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ) τ
  rw [hττ] at hmet
  rw [hττ]
  exact volume_ball_congr_P6M K.toHistory hidx τ' _ hmet p p' hp b

/-- traced region E → K（`E` 抽象 + 等式形，供序列层逐 n 调用）。 -/
theorem isTracedRegion_of_eventPrefix'_P6M (j : Fin K.eventCount) {T : ℝ}
    (hjT : K.time j.castSucc < T) (hTj : T < K.time j.succ)
    (E : ObservedHistory.{u}) (hE : E = (K.eventPrefix j T hjT hTj).toHistory)
    (τ : Icc (0 : ℝ) E.horizon) (τ' : Icc (0 : ℝ) K.toHistory.horizon) (hττ : (τ : ℝ) = τ')
    (p : (E.stageAt τ).Carrier) (p' : (K.toHistory.stageAt τ').Carrier) (hp : HEq p p')
    {ρ δ C : ℝ} (h : E.isTracedRegion τ p ρ δ C) : K.toHistory.isTracedRegion τ' p' ρ δ C := by
  subst hE
  exact K.isTracedRegion_of_eventPrefix_P6M j hjT hTj τ τ' hττ p p' hp h

end RetainedCoreHistory

/-! ### 序列层：P6ClosureP6D2 / P6D2 G3 的 `Hs`-层输入 ⇐ K 层；`DepthExtendable` 回 K -/

namespace ObservedHistory

variable {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
  {hjt : ∀ n, (K n).time (j n).castSucc < t n} {htj : ∀ n, t n < (K n).time (j n).succ}
  {σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon} {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier}
  {Hs : ℕ → ObservedHistory.{u}} {ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon}
  {ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier} {R : ℕ → ℝ}

/-- **`_P6M`（序列 `hwit`）**：K 层（`σ n`、`y n`）⇒ `Hs n = (K n).eventPrefix (j n) (t n)` 层
（P6ClosureP6D2 / P6D2 G3 的 `hwit` 逐字形）。 -/
theorem hwit_seq_of_eventPrefix_P6M
    (hHs : ∀ n, Hs n = ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory)
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
  exact (K n).hwit_of_eventPrefix_P6M (j n) (hjt n) (htj n) (Hs n) (hHs n) (ts n) (σ n) (hσ n)
    (ys n) (y n) (hys n) hn

/-- **`_P6M`（序列 `hkappa`）**：K 层 trace-local κ ⇒ `Hs` 层（逐字形）。 -/
theorem hkappa_seq_of_eventPrefix_P6M
    (hHs : ∀ n, Hs n = ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory)
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
  exact (K n).hkappa_of_eventPrefix_P6M (j n) (hjt n) (htj n) (Hs n) (hHs n) (ts n) (σ n) (hσ n)
    (ys n) (y n) (hys n) hn

/-- **`_P6M`（序列 `hbcad`）**：K 层双 trace BCAD ⇒ `Hs` 层（逐字形）。 -/
theorem hbcad_seq_of_eventPrefix_P6M
    (hHs : ∀ n, Hs n = ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory)
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
  exact (K n).hbcad_of_eventPrefix_P6M (j n) (hjt n) (htj n) (Hs n) (hHs n) (ts n) (σ n) (hσ n)
    (ys n) (y n) (hys n) hn

/-- **`_P6M`（序列 `hseed`）**：K 层基点种子体积 ⇒ `Hs` 层（逐字形）。 -/
theorem hseed_seq_of_eventPrefix_P6M
    (hHs : ∀ n, Hs n = ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory)
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
  rw [(K n).volume_ball_of_eventPrefix_P6M (j n) (hjt n) (htj n) (Hs n) (hHs n) (ts n) (σ n)
    (hσ n) (ys n) (y n) (hys n)]
  exact hn

/-- **`_P6M`（`htraced` 回 K）**：`Hs` 层 `DepthExtendable`（P6D2 G3 输出）⇒ K 层 `DepthExtendable`
（同子列、同深度）。 -/
theorem depthExtendable_of_eventPrefix_P6M
    (hHs : ∀ n, Hs n = ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory)
    (hσ : ∀ n, (ts n : ℝ) = σ n) (hys : ∀ n, HEq (ys n) (y n)) {ψ : ℕ → ℕ} {T : ℝ}
    (h : DepthExtendable Hs ts ys R ψ T) :
    DepthExtendable (fun n => (K n).toHistory) σ y R ψ T := by
  intro A hA
  obtain ⟨C, hC, hev⟩ := h A hA
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev] with i hi
  exact (K (ψ i)).isTracedRegion_of_eventPrefix'_P6M (j (ψ i)) (hjt (ψ i)) (htj (ψ i)) (Hs (ψ i))
    (hHs (ψ i)) (ts (ψ i)) (σ (ψ i)) (hσ (ψ i)) (ys (ψ i)) (y (ψ i)) (hys (ψ i)) hi

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

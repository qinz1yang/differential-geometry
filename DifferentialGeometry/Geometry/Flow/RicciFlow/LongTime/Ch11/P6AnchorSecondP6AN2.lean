import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AnchorP6AN
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KSWShortWindowC11KS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KRouteCondP6CD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6FinalCondP6FCKRoute

/-!
# ANCHOR 第二轮：子列包装、top-anchor adapter、R-AN-3（O-CH11-ANCHOR2，后缀 `_P6AN2`）

依据：外审 R-C11-12 Q3（`docs/geometrization/chapter8/out/review-R-C11-12-shallow-ksw.md`）与处置 D-7 / D-8 /
D-9(4)。
* **G1（PROVED）两项包装**：`exists_const_eventually_of_subseq_mono_P6AN2`（对角反证：`¬ P_{n_k}(k+1)` 的
  严格增 `n_k` + 子列 driver + `P_n(C)` 对 `C` 单调 ⇒ `∃ C, ∀ᶠ n, P_n(C)`；坏指标上 `P` 平凡）；
  `hscalW_body_mono_P6AN2`（单调性）；`hscalW_eventually_of_subseqDriver_P6AN2`（结论 = `hscalW` 逐字，只需
  regular-top 子列上的 driver 输出）与 final 孪生 `hscalW_final_eventually_of_subseqDriver_P6AN2`
  （`hscalW_final_P6M6` 仍是显式 Prop，这里证它）。supplies 的重索引（含 `n` 依赖的 schedule `hqcan / hpar /
  hscale / hθcap` 的重索引稳定性）见 G3 的 `hdepth_toHistory_eventSlab_P6AN2`。
* **G2 top-anchor adapter**：合同 `TopAnchorInputs_P6AN2 β`（独立 top-local supplies + 非-cap 排除或 cap 比较，
  extendAt 构形上）与 `hanchor0_of_shortSLT_top_P6AN2`（PROVISIONAL，binder = `ShortSLT_C11KS β` +
  `TopAnchorInputs_P6AN2 β`；**不是** `σ′ = 0` 字面实例）；event / final slab 版单列
  （`hanchor0_event_of_shortSLT_top_P6AN2` / `hanchor0_final_of_shortSLT_top_P6AN2`）；
  stage-birth top 排除 `hscalW_body_of_not_regularTop_P6AN2` /
  `hscalW_final_body_of_not_finalTop_P6AN2`（PROVED）；非-cap 排除 ⇐ selection `hnot`：
  `notCWP_of_hnot_P6AN2`（PROVED）；合同的已付部分
  `topAnchorInputs_of_local_P6AN2` + `selectionSchedule_P6AN2`（PROVED；剩余 = 显式 `hlocal`，即 top 时刻的
  `q, ρ, U` 局部 supplies）。
* **G3 R-AN-3（PROVED，搬运路线）**：P6CD 的 `Kh = (K n).toHistory` 与 driver 的 extendAt history
  `Hs n = (K n).eventPrefix …` 之间：K 层 supplies 经树内桥（`*_seq_of_eventPrefix_P6M/P6CD`）下推到 `Hs`，
  driver 在 `Hs` 上跑（`exists_subseq_htraced_extendAt_late_cond_P6CD`），`DepthExtendable` 经
  `depthExtendable_of_eventPrefix_P6M` 回到 `toHistory`（只用 `≤ σ` 的时刻）；遗传子列形
  `hdepth_toHistory_eventSlab_P6AN2` 把**全部** supplies 重索引到任意子列（schedule 的重索引稳定性）。
  final slab 孪生 `*_finalSlab_P6AN2`（FINCOND 条件 kernel + `depthExtendable_final_P6M`）。组合：
  `hscalW_eventSlab_of_supplies_P6AN2` / `hscalW_final_finalSlab_of_supplies_P6AN2`
  （G-flow `hanchor0` 作 binder）
  与 `hscalW_eventSlab_of_shortSLT_top_P6AN2` / `hscalW_final_finalSlab_of_shortSLT_top_P6AN2`
  （`hanchor0` 换 ShortSLT_β + TopAnchorInputs）。
非循环：`hanchor0` 只来自 ShortSLT_β + TopAnchorInputs（或作 binder），**不**经 `hdistW ← hscalW`
（`hanchor0_of_closure_data_window_q_P6M` / `hgrad_of_selection_sameSlab_Cg_P6CD` 不出现）；前提中无 HU、hgapJ、
hclosG、CanonicalLateCore、hspine。`hbcadC` 仍是 driver binder（owner SHALLOW / KSW）。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

/-- **top-anchor adapter 合同 `TopAnchorInputs_P6AN2 β`（合同 Prop，lead 简报登记；R-C11-12 D-8）**：
序列化的 extendAt 构形 `(H n, G n, t n, y n)`（`H n` 的最后一个 stage 接 incoming slab `G n`，top 时刻
`t n` 在 `G n` 内部；event 版 `H n = prefixAt j.castSucc`、final 版 `H n = prefixAt last`）上，供
`ShortSLT_C11KS β` 使用的**独立 top-local supplies + 非-cap 排除或 cap 比较**的精确形：
* 固定常数 `ε ≤ coneAccuracy`、`κ > 0`、`C1 C2`、`Ctime Cgrad`、admissible `phi`、`Cq`（在 `A` 之前）；
* 对任意 `A > 0` 与 ShortSLT 可能给出的任意 `Λ ≥ 1`、`transitionEnd < Dcap ≤ Rrad`、`ζ₀ > 0`、`Rad`，
  存在 cap 比较常数 `Qcap`，使 eventually 在 `n` 上有 ShortSLT 前提的**全部实例**：`q, ρ`、尺度
  （`Λ ≤ R`、`Λ ≤ R t`、`Λ ≤ ρ √R`）、记录 / cap 参数（`p, T₀ ≤ t − β/R, records`）、局部区域 `U ⊇ B(y, Rad/√R)`
  上的 witness / 导数 / 梯度 / pinching / κ（窗口 `[t − β/R, t]`），以及
* **非-cap 排除或 cap 比较**：若 `y n` 恰是年龄 `β`、位置 `< Dcap + 1` 的 cap window point（CWP），则
  top 球 `B(y, A/√R)` 上 `R ≤ Qcap R(y)`（cap 比较）；不是 CWP 时由 ShortSLT 付。selection 族上 CWP 被
  `hnot` 排除（`notCWP_of_hnot_P6AN2`），cap 比较蕴含式空转。
**不是**冻结负偏移合同（ShallowBcadC `σ′ < 0` / ShallowSliceRC `σ₂ < 0`）的字面 `σ′ = 0` 实例：top 数据
在 `t n` 时刻本身、在 extendAt 历史的 incoming slab 里给出。owner：top supplies = SHALLOW/PICKBALL 的 top 版
（与浅窗 slice 数据同类，但时刻是 top）；cap 比较 = cap 链（`capWindow_branch_late_P6L3` 型）。 -/
def TopAnchorInputs_P6AN2 (β : ℝ) (H : ℕ → RetainedCoreHistory.{u})
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon) (s : ℕ → ℝ)
    (G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n))
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (t : ℕ → ℝ) (y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier) : Prop :=
  ∃ ε : ℝ, ε ≤ coneAccuracy ∧ ∃ κ C1 C2 : ℝ, 0 < κ ∧ ∃ (Ctime Cgrad : ℝ≥0) (phi : ℝ → ℝ),
  Perelman.AdmissiblePinchingFunction phi ∧ ∃ Cq : ℝ,
  ∀ A : ℝ, 0 < A → ∀ Λ Dcap Rrad ζ₀ Rad : ℝ, 1 ≤ Λ → StandardCap.transitionEnd < Dcap →
  Dcap ≤ Rrad → 0 < ζ₀ → ∃ Qcap : ℝ, ∀ᶠ n in atTop,
  ∃ q ρ : ℝ, 0 < q ∧ q ≤ Cq * (G n).flow.scalar (t n) (y n) ∧
    Λ ≤ (G n).flow.scalar (t n) (y n) ∧ Λ ≤ (G n).flow.scalar (t n) (y n) * t n ∧
    ∃ (p : CutoffParameters) (T₀ : ℝ), T₀ ≤ t n - β / (G n).flow.scalar (t n) (y n) ∧
    ∃ records : (∀ i : Fin (H n).eventCount, T₀ ≤ (H n).time i.succ →
        GeometricCutoffRecord (H n).toHistory i p),
      (∀ i hT b, ((records i hT).static b).hasCanonicalWindow) ∧
      Rrad ≤ p.modelRadius ∧ 2 ≤ p.modelOrder ∧ p.modelAccuracy ≤ ζ₀ ∧
      ∃ U : Set ((H n).stage (Fin.last (H n).eventCount)).Carrier,
        (∀ w ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
            (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
          w ∈ U) ∧
        (∀ x ∈ U, q < (G n).flow.scalar (t n) x →
          ∃ W : SpatialCanonicalWitness ((G n).flow.base.metric (t n)) ε C1 C2 x,
            W.capTubeHasNeckChart ε) ∧
        (∀ j : Fin (H n).eventCount,
          ∀ (first : Fin ((H n).eventCount + 1)) (hf : first ≤ j.castSucc),
          ∀ z ∈ U, ∀ B : BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
            (Fin.le_last first) z,
          ∀ v ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
          t n - β / (G n).flow.scalar (t n) (y n) ≤ v →
          q < ((H n).toHistory.event j).incoming.flow.scalar v
            (B.point j.castSucc hf (Fin.le_last _)) →
          |derivWithin (fun w => ((H n).toHistory.event j).incoming.flow.scalar w
            (B.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
            Ctime * ((H n).toHistory.event j).incoming.flow.scalar v
              (B.point j.castSucc hf (Fin.le_last _)) ^ 2) ∧
        (∀ x ∈ U, ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
          t n - β / (G n).flow.scalar (t n) (y n) ≤ v →
          q < (G n).flow.scalar v x →
          |derivWithin (fun w => (G n).flow.scalar w x) (Iic v) v| ≤
            Ctime * (G n).flow.scalar v x ^ 2) ∧
        (∀ x ∈ U, ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
          t n - β / (G n).flow.scalar (t n) (y n) ≤ v →
          q < (G n).flow.scalar v x →
          ∀ w : TangentSpace ThreeModel x,
            |scalarDifferential (G n).flow v x w| ≤
              Cgrad * (G n).flow.scalar v x * Real.sqrt ((G n).flow.scalar v x) *
                Real.sqrt (((G n).flow.base.metric v).inner x w w)) ∧
        (∀ j : Fin (H n).eventCount,
          Perelman.PhiAlmostNonnegative ((H n).toHistory.event j).incoming.flow
            (Ico ((H n).time j.castSucc) ((H n).time j.succ) ∩
              Ici (t n - β / (G n).flow.scalar (t n) (y n))) phi) ∧
        Perelman.PhiAlmostNonnegative (G n).flow
          (Ico ((H n).time (Fin.last (H n).eventCount)) (s n) ∩
            Ici (t n - β / (G n).flow.scalar (t n) (y n))) phi ∧
        (∀ (T : ℝ) (hT : (H n).time (Fin.last (H n).eventCount) < T) (hTs : T < s n), T ≤ t n →
          t n - β / (G n).flow.scalar (t n) (y n) ≤ T →
          let B := (H n).extendHorizon T ((hend n) ▸ hT.le) ((G n).closedPrefix T hT hTs) (hGi n)
          let tm : Icc (0 : ℝ) B.horizon :=
            ⟨T, (H n).horizon_nonneg.trans ((hend n) ▸ hT.le), le_rfl⟩
          ∀ z ∈ U, ∀ (yy : (B.toHistory.stageAt tm).Carrier), HEq yy z →
          ∀ (b : ℝ), 0 < b → b ≤ ρ →
            B.toHistory.isParabolicallyRmControlledBall tm yy b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
                  (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                  (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                    yy b)) ∧
        Λ ≤ ρ * Real.sqrt ((G n).flow.scalar (t n) (y n)) ∧
      ((∃ (j : Fin (H n).eventCount) (hT : T₀ ≤ (H n).time j.succ)
          (hl : j.succ ≤ Fin.last (H n).eventCount)
          (B : BackwardPointTrace (H n).toHistory j.succ (Fin.last (H n).eventCount) hl (y n))
          (b : ((H n).toHistory.event j).RetainedBoundaryIndex)
          (x : standardCapWindow p.modelRadius),
          B.point j.succ le_rfl hl = ((records j hT).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
            t n - (H n).time j.succ ≤ β * (((records j hT).static b).neck.scale)⁻¹) →
        ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
            (A / Real.sqrt ((G n).flow.scalar (t n) (y n))),
          (G n).flow.scalar (t n) z ≤ Qcap * (G n).flow.scalar (t n) (y n))

/-- **`hanchor0_of_shortSLT_top_P6AN2`（top-anchor adapter，PROVISIONAL：binder =
`ShortSLT_C11KS β` + `TopAnchorInputs_P6AN2 β …`）**：结论 = driver 包装
`exists_subseq_htraced_extendAt_late_cond_P6CD` / `hanchor0_of_extendAt_P6D2` 的 G-flow 形 `hanchor0`
**逐字**（top 切片 `t n` 上任意半径 `A` 的 BCBD，`Q ≥ 2`）。证明：对每个 `A`，ShortSLT 给 `Q Λ Dcap Rrad ζ₀ Rad`；
TopAnchorInputs 在这些常数上给 eventually 的全部实例与 `Qcap`；逐 n 分 CWP / 非 CWP：非 CWP 用 ShortSLT 结论，
CWP 用 cap 比较；`Q_final = max (max Q Qcap) 2`。**不**经 `hdistW ← hscalW`、不用锥刚性新定理（锥端排除在
ShortSLT 的 producer 里）、不用 HU / hgapJ / hclosG / CanonicalLateCore / hspine。 -/
theorem hanchor0_of_shortSLT_top_P6AN2 {β : ℝ} (hX : ShortSLT_C11KS.{u} β)
    {s t : ℕ → ℝ} {H : ℕ → RetainedCoreHistory.{u}}
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon)
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n) (hts : ∀ n, t n < s n)
    (hin : TopAnchorInputs_P6AN2 β H hend s G hGi t y) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
          (A / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        (G n).flow.scalar (t n) z ≤ Q * (G n).flow.scalar (t n) (y n) := by
  obtain ⟨ε, hε, κ, C1, C2, hκ, Ctime, Cgrad, phi, hphi, Cq, hin⟩ := hin
  intro A hA
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, -, hΛ, hD1, hD2, hζ, hX'⟩ :=
    hX hε κ C1 C2 hκ Ctime Cgrad hphi A hA Cq
  obtain ⟨Qcap, hcap⟩ := hin A hA Λ Dcap Rrad ζ₀ Rad hΛ hD1 hD2 hζ
  refine ⟨max (max Q Qcap) 2, le_max_right _ _, ?_⟩
  filter_upwards [hcap] with n hn
  obtain ⟨q, ρ, hq, hqC, hΛR, hΛRt, p, T₀, hT₀, records, hcan, hRrad, hord, hacc, U, hU, hwit,
    hderE, hderT, hgrad, hpinE, hpinT, hkap, hΛρ, hcmp⟩ := hn
  have hR0 : 0 ≤ (G n).flow.scalar (t n) (y n) := by linarith
  intro z hz
  have hb1 := fun hc => (hcmp hc z hz).trans
    (mul_le_mul_of_nonneg_right ((le_max_right Q Qcap).trans (le_max_left _ 2)) hR0)
  have hb2 := fun hc => (hX' (H n) (hend n) (G n) (hGi n) (hat n) (hts n) (y n) q ρ hq hqC hΛR
    hΛRt T₀ hT₀ records hcan hRrad hord hacc U hU hwit hderE hderT hgrad hpinE hpinT hkap hΛρ hc z
    hz).trans (mul_le_mul_of_nonneg_right ((le_max_left Q Qcap).trans (le_max_left _ 2)) hR0)
  exact (Classical.em _).elim hb1 hb2

/-- **非-cap 排除 ⇐ selection 的 `hnot`（`_P6AN2`，PROVED）**：selection 坏点不是 cap window point
（位置 `< Dsel + 1`、年龄 `θsel`）⇒ 对任意 `Dcap ≤ Dsel`、`β ≤ θsel` 也不是（同 records / `T₀`）。
P6CD / P6HF 的 `hnot` 带 `D n ≥ n + 1 → ∞`、`θcap n ≥ 1 − 1/(n+2) ≥ 1/2`，故对 ShortSLT 的任意 `Dcap` 与
`β ≤ 1/2` eventually 成立；`TopAnchorInputs` 的 cap 比较蕴含式在 selection 族上空转。 -/
theorem notCWP_of_hnot_P6AN2 {H : RetainedCoreHistory.{u}} {p : CutoffParameters}
    {T₀ t Dsel θsel Dcap β : ℝ}
    {records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ → GeometricCutoffRecord H.toHistory i p}
    {y : (H.stage (Fin.last H.eventCount)).Carrier}
    (hscale : ∀ i hi b, 0 < ((records i hi).static b).neck.scale)
    (hD : Dcap ≤ Dsel) (hβ : β ≤ θsel)
    (hnot : ¬ ∃ (j : Fin H.eventCount) (hT : T₀ ≤ H.time j.succ)
      (hl : j.succ ≤ Fin.last H.eventCount)
      (B : BackwardPointTrace H.toHistory j.succ (Fin.last H.eventCount) hl y)
      (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      B.point j.succ le_rfl hl = ((records j hT).static b).window x ∧ ‖x.val‖ < Dsel + 1 ∧
        t - H.time j.succ ≤ θsel * (((records j hT).static b).neck.scale)⁻¹) :
    ¬ ∃ (j : Fin H.eventCount) (hT : T₀ ≤ H.time j.succ)
      (hl : j.succ ≤ Fin.last H.eventCount)
      (B : BackwardPointTrace H.toHistory j.succ (Fin.last H.eventCount) hl y)
      (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      B.point j.succ le_rfl hl = ((records j hT).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
        t - H.time j.succ ≤ β * (((records j hT).static b).neck.scale)⁻¹ := by
  rintro ⟨j, hT, hl, B, b, x, h1, h2, h3⟩
  exact hnot ⟨j, hT, hl, B, b, x, h1, by linarith,
    h3.trans (mul_le_mul_of_nonneg_right hβ (inv_nonneg.mpr (hscale j hT b).le))⟩

/-- **final slab 版（单列，`_P6AN2`，PROVISIONAL：binder = `ShortSLT_C11KS β` + `TopAnchorInputs_P6AN2 β`
于 final 构形）**：`H n = prefixAt last`、`G n = finalSlab.restrictIncoming`（P6HF / FINCOND 的 final 构形，
`s n = horizon`）、`time last < t n < horizon`（final-slab regular top；stage-birth top 由 hscalW_final 的
guard 先排掉，见 `hscalW_final_body_of_not_finalTop_P6AN2`）。结论 = P6HF `hanchor0`
（`G := finalSlab …` 后）逐字。 -/
theorem hanchor0_final_of_shortSLT_top_P6AN2 {β : ℝ} (hX : ShortSLT_C11KS.{u} β)
    {K : ℕ → RetainedCoreHistory.{u}} {t : ℕ → ℝ}
    (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) (htK : ∀ n, t n < (K n).horizon)
    {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier}
    (hin : TopAnchorInputs_P6AN2 β (fun n => (K n).prefixAt (Fin.last (K n).eventCount))
      (fun n => (K n).prefixAt_time_last _) (fun n => (K n).horizon)
      (fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
        ((htl n).trans (htK n)) le_rfl)
      (fun n => (K n).final_initial ((htl n).trans (htK n))) t yG) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
          ((htl n).trans (htK n)) le_rfl).flow.base.metric (t n)) (yG n)
          (A / Real.sqrt ((((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
            ((htl n).trans (htK n)) le_rfl).flow.scalar (t n) (yG n))),
        (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
            ((htl n).trans (htK n)) le_rfl).flow.scalar (t n) z ≤
          Q * (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
            ((htl n).trans (htK n)) le_rfl).flow.scalar (t n) (yG n) :=
  hanchor0_of_shortSLT_top_P6AN2 hX
    (H := fun n => (K n).prefixAt (Fin.last (K n).eventCount))
    (G := fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl)
    (s := fun n => (K n).horizon) (y := yG) (fun n => (K n).prefixAt_time_last _)
    (fun n => (K n).final_initial ((htl n).trans (htK n))) htl htK hin

/-- **event slab 版（`_P6AN2`，PROVISIONAL：同上 binder 于 event 构形）**：`H n = prefixAt (j n).castSucc`、
`G n = (event j n).incoming`、`s n = time (j n).succ`、`time (j n).castSucc < t n < time (j n).succ`
（event-interior regular top）。结论 = P6CD `hanchor0` 逐字。 -/
theorem hanchor0_event_of_shortSLT_top_P6AN2 {β : ℝ} (hX : ShortSLT_C11KS.{u} β)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hin : TopAnchorInputs_P6AN2 β (fun n => (K n).prefixAt (j n).castSucc)
      (fun n => (K n).prefixAt_time_last _) (fun n => (K n).time (j n).succ)
      (fun n => ((K n).toHistory.event (j n)).incoming) (fun n => (K n).event_initial (j n)) t
      yG) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
          (yG n)
          (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
        ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
          Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) :=
  hanchor0_of_shortSLT_top_P6AN2 hX (H := fun n => (K n).prefixAt (j n).castSucc)
    (G := fun n => ((K n).toHistory.event (j n)).incoming) (s := fun n => (K n).time (j n).succ)
    (y := yG) (fun n => (K n).prefixAt_time_last _) (fun n => (K n).event_initial (j n)) hjt htj
    hin

/-- **TopAnchorInputs 的已付部分（`_P6AN2`，PROVED ⇐ 显式 residual `hlocal`）**：selection 型数据付掉
`TopAnchorInputs_P6AN2` 的尺度 / 记录 / cap 参数 / 非-cap 排除部分：
`Λ ≤ R`（`hRlim`）、`Λ ≤ R t`（`hRt`）、`T₀ ≤ t − β/R`（`hT₀`）、`Rrad ≤ modelRadius`（`Dsel → ∞`、
`Dsel ≤ modelRadius`）、`2 ≤ modelOrder`、`modelAccuracy ≤ ζ₀`（`hacc`）、canonical window（`hcan`）、
非-cap 排除（`hnot` + `Dcap ≤ Dsel`、`β ≤ θsel`，`notCWP_of_hnot_P6AN2`；cap 比较蕴含式空转，`Qcap = 0`）。
**剩余 = `hlocal`**（top-local supplies 的精确 repair target）：常数 `ε κ C1 C2 Ctime Cgrad phi Cq`，对任意
`Λ ≥ 1`、`Rad`，eventually 有 `0 < q ≤ Cq R`、`ρ` 与 `U ⊇ B(y, Rad/√R)` 上 witness / 导数 / 梯度 /
pinching / κ
（top 窗口 `[t − β/R, t]`）及 `Λ ≤ ρ √R`。owner：SHALLOW / PICKBALL 的 top 版（picked-ball 数据在 top 时刻）。 -/
theorem topAnchorInputs_of_local_P6AN2 {β : ℝ} {s t : ℕ → ℝ} {H : ℕ → RetainedCoreHistory.{u}}
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon)
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    {p : ℕ → CutoffParameters} {T₀ Dsel θsel : ℕ → ℝ}
    (records : ∀ n (i : Fin (H n).eventCount), T₀ n ≤ (H n).time i.succ →
      GeometricCutoffRecord (H n).toHistory i (p n))
    (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow)
    (hscale : ∀ n i hi b, 0 < ((records n i hi).static b).neck.scale)
    (hRlim : Tendsto (fun n => (G n).flow.scalar (t n) (y n)) atTop atTop)
    (hRt : Tendsto (fun n => (G n).flow.scalar (t n) (y n) * t n) atTop atTop)
    (hT₀ : ∀ᶠ n in atTop, T₀ n ≤ t n - β / (G n).flow.scalar (t n) (y n))
    (hDsel : Tendsto Dsel atTop atTop) (hDrad : ∀ n, Dsel n ≤ (p n).modelRadius)
    (hord : ∀ n, 2 ≤ (p n).modelOrder)
    (hacc : ∀ ζ : ℝ, 0 < ζ → ∀ᶠ n in atTop, (p n).modelAccuracy ≤ ζ)
    (hθ : ∀ᶠ n in atTop, β ≤ θsel n)
    (hnot : ∀ n, ¬ ∃ (j : Fin (H n).eventCount) (hT : T₀ n ≤ (H n).time j.succ)
      (hl : j.succ ≤ Fin.last (H n).eventCount)
      (B : BackwardPointTrace (H n).toHistory j.succ (Fin.last (H n).eventCount) hl (y n))
      (b : ((H n).toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      B.point j.succ le_rfl hl = ((records n j hT).static b).window x ∧ ‖x.val‖ < Dsel n + 1 ∧
        t n - (H n).time j.succ ≤ θsel n * (((records n j hT).static b).neck.scale)⁻¹)
    (hlocal : ∃ ε : ℝ, ε ≤ coneAccuracy ∧ ∃ κ C1 C2 : ℝ, 0 < κ ∧
      ∃ (Ctime Cgrad : ℝ≥0) (phi : ℝ → ℝ), Perelman.AdmissiblePinchingFunction phi ∧ ∃ Cq : ℝ,
      ∀ Λ Rad : ℝ, 1 ≤ Λ → ∀ᶠ n in atTop,
      ∃ q ρ : ℝ, 0 < q ∧ q ≤ Cq * (G n).flow.scalar (t n) (y n) ∧
      ∃ U : Set ((H n).stage (Fin.last (H n).eventCount)).Carrier,
        (∀ w ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
            (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
          w ∈ U) ∧
        (∀ x ∈ U, q < (G n).flow.scalar (t n) x →
          ∃ W : SpatialCanonicalWitness ((G n).flow.base.metric (t n)) ε C1 C2 x,
            W.capTubeHasNeckChart ε) ∧
        (∀ j : Fin (H n).eventCount,
          ∀ (first : Fin ((H n).eventCount + 1)) (hf : first ≤ j.castSucc),
          ∀ z ∈ U, ∀ B : BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
            (Fin.le_last first) z,
          ∀ v ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
          t n - β / (G n).flow.scalar (t n) (y n) ≤ v →
          q < ((H n).toHistory.event j).incoming.flow.scalar v
            (B.point j.castSucc hf (Fin.le_last _)) →
          |derivWithin (fun w => ((H n).toHistory.event j).incoming.flow.scalar w
            (B.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
            Ctime * ((H n).toHistory.event j).incoming.flow.scalar v
              (B.point j.castSucc hf (Fin.le_last _)) ^ 2) ∧
        (∀ x ∈ U, ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
          t n - β / (G n).flow.scalar (t n) (y n) ≤ v →
          q < (G n).flow.scalar v x →
          |derivWithin (fun w => (G n).flow.scalar w x) (Iic v) v| ≤
            Ctime * (G n).flow.scalar v x ^ 2) ∧
        (∀ x ∈ U, ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
          t n - β / (G n).flow.scalar (t n) (y n) ≤ v →
          q < (G n).flow.scalar v x →
          ∀ w : TangentSpace ThreeModel x,
            |scalarDifferential (G n).flow v x w| ≤
              Cgrad * (G n).flow.scalar v x * Real.sqrt ((G n).flow.scalar v x) *
                Real.sqrt (((G n).flow.base.metric v).inner x w w)) ∧
        (∀ j : Fin (H n).eventCount,
          Perelman.PhiAlmostNonnegative ((H n).toHistory.event j).incoming.flow
            (Ico ((H n).time j.castSucc) ((H n).time j.succ) ∩
              Ici (t n - β / (G n).flow.scalar (t n) (y n))) phi) ∧
        Perelman.PhiAlmostNonnegative (G n).flow
          (Ico ((H n).time (Fin.last (H n).eventCount)) (s n) ∩
            Ici (t n - β / (G n).flow.scalar (t n) (y n))) phi ∧
        (∀ (T : ℝ) (hT : (H n).time (Fin.last (H n).eventCount) < T) (hTs : T < s n), T ≤ t n →
          t n - β / (G n).flow.scalar (t n) (y n) ≤ T →
          let B := (H n).extendHorizon T ((hend n) ▸ hT.le) ((G n).closedPrefix T hT hTs) (hGi n)
          let tm : Icc (0 : ℝ) B.horizon :=
            ⟨T, (H n).horizon_nonneg.trans ((hend n) ▸ hT.le), le_rfl⟩
          ∀ z ∈ U, ∀ (yy : (B.toHistory.stageAt tm).Carrier), HEq yy z →
          ∀ (b : ℝ), 0 < b → b ≤ ρ →
            B.toHistory.isParabolicallyRmControlledBall tm yy b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
                  (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                  (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                    yy b)) ∧
        Λ ≤ ρ * Real.sqrt ((G n).flow.scalar (t n) (y n))) :
    TopAnchorInputs_P6AN2 β H hend s G hGi t y := by
  obtain ⟨ε, hε, κ, C1, C2, hκ, Ctime, Cgrad, phi, hphi, Cq, hloc⟩ := hlocal
  refine ⟨ε, hε, κ, C1, C2, hκ, Ctime, Cgrad, phi, hphi, Cq,
    fun _ _ Λ Dcap Rrad ζ₀ Rad hΛ _ hD2 hζ => ⟨0, ?_⟩⟩
  filter_upwards [hloc Λ Rad hΛ, hRlim.eventually_ge_atTop Λ, hRt.eventually_ge_atTop Λ, hT₀,
    hDsel.eventually_ge_atTop Rrad, hacc ζ₀ hζ, hθ] with n hl hR1 hR2 hT hD hac hθn
  obtain ⟨q, ρ, hq, hqC, U, hU, hwit, hderE, hderT, hgrad, hpinE, hpinT, hkap, hΛρ⟩ := hl
  exact ⟨q, ρ, hq, hqC, hR1, hR2, p n, T₀ n, hT, records n, hcan n, hD.trans (hDrad n), hord n,
    hac, U, hU, hwit, hderE, hderT, hgrad, hpinE, hpinT, hkap, hΛρ,
    fun hc => absurd hc (notCWP_of_hnot_P6AN2 (hscale n) (hD2.trans hD) hθn (hnot n))⟩

/-- **selection schedule ⇒ 通用 schedule 前提（`_P6AN2`，PROVED）**：P6CD / P6HF 的 `hpar`（精度
`≤ 1/(n+1)`、`n + 1 ≤ D n ≤ modelRadius`、阶 `≥ n + 2`）、`hθcap`（`θcap n ≥ 1 − 1/(n+2)`）、`hqcan / hqR /
hscale` ⇒ `topAnchorInputs_of_local_P6AN2` 的 `hDsel / hDrad / hord / hacc / hθ`（`β ≤ 1/2`）与 `R → ∞`、
scale 正。 -/
theorem selectionSchedule_P6AN2 {β : ℝ} (hβ : β ≤ 1 / 2) {p : ℕ → CutoffParameters}
    {D θcap qcan R : ℕ → ℝ} {δb : ℕ → ℝ}
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) (hqR : ∀ n, qcan n < R n)
    (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) :
    Tendsto R atTop atTop ∧ Tendsto D atTop atTop ∧ (∀ n, D n ≤ (p n).modelRadius) ∧
      (∀ n, 2 ≤ (p n).modelOrder) ∧ (∀ ζ : ℝ, 0 < ζ → ∀ᶠ n in atTop, (p n).modelAccuracy ≤ ζ) ∧
      (∀ᶠ n in atTop, β ≤ θcap n) ∧ (∀ n, 0 < qcan n) := by
  refine ⟨tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop,
    tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop, fun n => (hpar n).2.2.1,
    fun n => le_trans (Nat.le_add_left 2 n) (hpar n).2.2.2.1, fun ζ hζ => ?_,
    Eventually.of_forall fun n => ?_, fun n => ?_⟩
  · linarith [hqcan n, hqR n]
  · linarith [(hpar n).2.1]
  · filter_upwards [(tendsto_order.1 tendsto_one_div_add_atTop_nhds_zero_nat).2 ζ hζ] with n hn
    exact (hpar n).1.trans hn.le
  · have h2 : 1 / ((n : ℝ) + 2) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    linarith [hθcap n]
  · linarith [hqcan n, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

namespace ObservedHistory

/-- **子列 → 原序列 eventually 的对角反证（单调形，`_P6AN2`，PROVED）**：外审 R-C11-12 Q3(b) 的包装。
`P n C` 对 `C` 单调（`1 ≤ C ≤ C'`），且在"坏指标"（`¬ G n`）上平凡成立；若每个**全由好指标组成**的
子列 `φ` 都有再子列 `ψ` 与常数 `C₀ ≥ 1` 使 `∀ᶠ i, P (φ (ψ i)) C₀`，则 `∃ C ≥ 1, ∀ᶠ n, P n C`。
证明：反设，取严格增 `φ` 使 `¬ P (φ k) (k + 1)`（`Filter.extraction_forall_of_frequently`）；由 `hvac`
每个 `φ k` 都是好指标；对 `φ` 跑子列 driver 得 `ψ, C₀`；取 `ψ i ≥ C₀` 处由单调性得 `P (φ (ψ i)) (ψ i + 1)`，
矛盾。 -/
theorem exists_const_eventually_of_subseq_mono_P6AN2 {P : ℕ → ℝ → Prop} {G : ℕ → Prop}
    (hvac : ∀ n, ¬ G n → ∀ C : ℝ, P n C)
    (hmono : ∀ n (C C' : ℝ), 1 ≤ C → C ≤ C' → P n C → P n C')
    (h : ∀ φ : ℕ → ℕ, StrictMono φ → (∀ k, G (φ k)) → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ᶠ i in atTop, P (φ (ψ i)) C₀) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop, P n C := by
  by_contra hcon
  have hfreq : ∀ k : ℕ, ∃ᶠ n in atTop, ¬ P n ((k : ℝ) + 1) := by
    intro k
    refine Filter.not_eventually.mp fun hev => hcon ⟨(k : ℝ) + 1, ?_, hev⟩
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  obtain ⟨φ, hφ, hbad⟩ := Filter.extraction_forall_of_frequently hfreq
  have hG : ∀ k, G (φ k) := fun k => by
    by_contra hk
    exact hbad k (hvac _ hk _)
  obtain ⟨ψ, hψ, C₀, hC₀, hev⟩ := h φ hφ hG
  obtain ⟨N, hN⟩ := exists_nat_ge C₀
  obtain ⟨i, hi, hiN⟩ := (hev.and (eventually_ge_atTop N)).exists
  have hψi : (N : ℝ) ≤ (ψ i : ℝ) := by exact_mod_cast hiN.trans (hψ.id_le i)
  exact hbad (ψ i) (hmono _ _ _ hC₀ (by linarith) hi)

/-- **`hscalW` 逐 n 体对 `C` 单调（`_P6AN2`，PROVED）**：`1 ≤ C ≤ C'`、`R > 0` ⇒ 测试球
`B_s(x, 1/√(C'R)) ⊆ B_s(x, 1/√(CR))`、上界 `CR ≤ C'R`。`o` = seed trace 在 `σ` 时刻的点（ExitGuard 原样透传）。 -/
theorem hscalW_body_mono_P6AN2 (H : ObservedHistory.{u}) (σ : Icc (0 : ℝ) H.horizon)
    (y o : (H.stageAt σ).Carrier) {R D T Lg C C' : ℝ} (hR : 0 < R) (hC : 1 ≤ C) (hCC : C ≤ C')
    (h : ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage σ) σ) y (D / Real.sqrt R),
      ∀ s : ℝ, (σ : ℝ) - T / R < s → s < σ → H.time (H.activeStage σ) < s →
        riemannianEDistOf (H.stageMetric (H.activeStage σ) s) o x ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ) o y +
            ENNReal.ofReal (Lg / Real.sqrt R) →
        ∀ z : (H.stageAt σ).Carrier,
          riemannianEDistOf (H.stageMetric (H.activeStage σ) s) x z <
              ENNReal.ofReal (1 / Real.sqrt (C * R)) →
            metricScalarAt (H.stageMetric (H.activeStage σ) s) z ≤ C * R) :
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage σ) σ) y (D / Real.sqrt R),
      ∀ s : ℝ, (σ : ℝ) - T / R < s → s < σ → H.time (H.activeStage σ) < s →
        riemannianEDistOf (H.stageMetric (H.activeStage σ) s) o x ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ) o y +
            ENNReal.ofReal (Lg / Real.sqrt R) →
        ∀ z : (H.stageAt σ).Carrier,
          riemannianEDistOf (H.stageMetric (H.activeStage σ) s) x z <
              ENNReal.ofReal (1 / Real.sqrt (C' * R)) →
            metricScalarAt (H.stageMetric (H.activeStage σ) s) z ≤ C' * R := by
  intro x hx s hs1 hs2 hs3 hg z hz
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  have hle : 1 / Real.sqrt (C' * R) ≤ 1 / Real.sqrt (C * R) :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr (mul_pos hC0 hR))
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hCC hR.le))
  exact (h x hx s hs1 hs2 hs3 hg z (lt_of_lt_of_le hz (ENNReal.ofReal_le_ofReal hle))).trans
    (mul_le_mul_of_nonneg_right hCC hR.le)

/-- **stage-birth top 排除（`_P6AN2`，PROVED）**：外审 Q3(c) 的收窄——`hscalW` 的非空测试窗要求
`time (activeStage σ) < s < σ`；若 `σ` 不是 regular top（`¬ time (activeStage σ) < σ`，即
`time (activeStage σ) = σ`：stage-birth top），逐 n 体对任意 `C` 平凡成立（窗口空）。 -/
theorem hscalW_body_of_not_regularTop_P6AN2 (H : ObservedHistory.{u})
    (σ : Icc (0 : ℝ) H.horizon) (y o : (H.stageAt σ).Carrier) {R D T Lg C : ℝ}
    (hbirth : ¬ H.time (H.activeStage σ) < σ) :
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage σ) σ) y (D / Real.sqrt R),
      ∀ s : ℝ, (σ : ℝ) - T / R < s → s < σ → H.time (H.activeStage σ) < s →
        riemannianEDistOf (H.stageMetric (H.activeStage σ) s) o x ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ) o y +
            ENNReal.ofReal (Lg / Real.sqrt R) →
        ∀ z : (H.stageAt σ).Carrier,
          riemannianEDistOf (H.stageMetric (H.activeStage σ) s) x z <
              ENNReal.ofReal (1 / Real.sqrt (C * R)) →
            metricScalarAt (H.stageMetric (H.activeStage σ) s) z ≤ C * R := by
  intro x _ s _ hs2 hs3
  exact absurd (hs3.trans hs2) hbirth

/-- **stage-birth top 的等价刻画（`_P6AN2`，PROVED）**：`¬ time (activeStage σ) < σ ↔
time (activeStage σ) = σ`（`activeStage_time_le`）。 -/
theorem not_regularTop_iff_stageBirth_P6AN2 {H : ObservedHistory.{u}}
    {σ : Icc (0 : ℝ) H.horizon} :
    ¬ H.time (H.activeStage σ) < σ ↔ H.time (H.activeStage σ) = σ := by
  have hle := H.activeStage_time_le σ
  constructor
  · intro h
    exact le_antisymm hle (not_lt.mp h)
  · intro h
    rw [h]
    exact lt_irrefl _

/-- **final 体对 `C` 单调（`_P6AN2`，PROVED）**：`hscalW_final_P6M6` 的逐 n 体（多一个
`activeStage σ = last` 守卫、窗口下端 `time last < s`）。 -/
theorem hscalW_final_body_mono_P6AN2 (H : ObservedHistory.{u}) (σ : Icc (0 : ℝ) H.horizon)
    (y o : (H.stageAt σ).Carrier) {R D T Lg C C' : ℝ} (hR : 0 < R) (hC : 1 ≤ C) (hCC : C ≤ C')
    (h : H.activeStage σ = Fin.last H.eventCount →
      ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage σ) σ) y (D / Real.sqrt R),
      ∀ s : ℝ, (σ : ℝ) - T / R < s → s < σ → H.time (Fin.last H.eventCount) < s →
        riemannianEDistOf (H.stageMetric (H.activeStage σ) s) o x ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ) o y +
            ENNReal.ofReal (Lg / Real.sqrt R) →
        ∀ z : (H.stageAt σ).Carrier,
          riemannianEDistOf (H.stageMetric (H.activeStage σ) s) x z <
              ENNReal.ofReal (1 / Real.sqrt (C * R)) →
            metricScalarAt (H.stageMetric (H.activeStage σ) s) z ≤ C * R) :
    H.activeStage σ = Fin.last H.eventCount →
      ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage σ) σ) y (D / Real.sqrt R),
      ∀ s : ℝ, (σ : ℝ) - T / R < s → s < σ → H.time (Fin.last H.eventCount) < s →
        riemannianEDistOf (H.stageMetric (H.activeStage σ) s) o x ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ) o y +
            ENNReal.ofReal (Lg / Real.sqrt R) →
        ∀ z : (H.stageAt σ).Carrier,
          riemannianEDistOf (H.stageMetric (H.activeStage σ) s) x z <
              ENNReal.ofReal (1 / Real.sqrt (C' * R)) →
            metricScalarAt (H.stageMetric (H.activeStage σ) s) z ≤ C' * R := by
  intro hfin x hx s hs1 hs2 hs3 hg z hz
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  have hle : 1 / Real.sqrt (C' * R) ≤ 1 / Real.sqrt (C * R) :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr (mul_pos hC0 hR))
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hCC hR.le))
  exact (h hfin x hx s hs1 hs2 hs3 hg z (lt_of_lt_of_le hz (ENNReal.ofReal_le_ofReal hle))).trans
    (mul_le_mul_of_nonneg_right hCC hR.le)

/-- **final 体在非 final-regular-top 处平凡（`_P6AN2`，PROVED）**：`activeStage σ ≠ last`（守卫假）或
`¬ time last < σ`（final slab 的 stage-birth top，窗口 `time last < s < σ` 空）。 -/
theorem hscalW_final_body_of_not_finalTop_P6AN2 (H : ObservedHistory.{u})
    (σ : Icc (0 : ℝ) H.horizon) (y o : (H.stageAt σ).Carrier) {R D T Lg C : ℝ}
    (hnt : ¬ (H.activeStage σ = Fin.last H.eventCount ∧ H.time (Fin.last H.eventCount) < σ)) :
    H.activeStage σ = Fin.last H.eventCount →
      ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage σ) σ) y (D / Real.sqrt R),
      ∀ s : ℝ, (σ : ℝ) - T / R < s → s < σ → H.time (Fin.last H.eventCount) < s →
        riemannianEDistOf (H.stageMetric (H.activeStage σ) s) o x ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ) o y +
            ENNReal.ofReal (Lg / Real.sqrt R) →
        ∀ z : (H.stageAt σ).Carrier,
          riemannianEDistOf (H.stageMetric (H.activeStage σ) s) x z <
              ENNReal.ofReal (1 / Real.sqrt (C * R)) →
            metricScalarAt (H.stageMetric (H.activeStage σ) s) z ≤ C * R := by
  intro hfin x _ s _ hs2 hs3
  exact absurd ⟨hfin, hs3.trans hs2⟩ hnt

/-- **`hscalW_eventually_of_subseqDriver_P6AN2`（G1 主定理，PROVED）**：结论 = `hdistW_of_firstExit_P6DW`
的 `hscalW` binder **逐字**。唯一前提 `hdriver`：每个**全由 regular top 组成**（`time (activeStage σ) < σ`）的
子列 `φ`，有再子列 `ψ` 使 `∀ T > 0, DepthExtendable Kh σ y R (φ ∘ ψ) T`（= 子列 driver 输出；supplies 的
重索引见 `hdepth_toHistory_eventSlab_P6AN2` / round 1 `hdepth_of_driver_P6AN`）。证明 = 对角反证
`exists_const_eventually_of_subseq_mono_P6AN2`（`P n C` = hscalW 逐 n 体，单调性
`hscalW_body_mono_P6AN2`，stage-birth top 由 `hscalW_body_of_not_regularTop_P6AN2` 先排掉）+ 同 slab 换算
`scalar_le_of_tracedRegion_P6AN`（`C₀ = max (max 1 (9K)) ((e^{9KT}/D)²)`；ExitGuard 不用）。 -/
theorem hscalW_eventually_of_subseqDriver_P6AN2 (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hdriver : ∀ φ : ℕ → ℕ, StrictMono φ →
      (∀ k, (Kh (φ k)).time ((Kh (φ k)).activeStage (σ (φ k))) < σ (φ k)) →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ T : ℝ, 0 < T → DepthExtendable Kh σ y R (φ ∘ ψ) T) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ s : ℝ, (σ n : ℝ) - T / R n < s → s < σ n → (Kh n).time ((Kh n).activeStage (σ n)) < s →
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s)
            ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
              ((Kh n).activeStage_mono (hsT n))) x ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        ∀ z : ((Kh n).stageAt (σ n)).Carrier,
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) x z <
              ENNReal.ofReal (1 / Real.sqrt (C * R n)) →
            metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) z ≤ C * R n := by
  intro D T hD hT
  refine exists_const_eventually_of_subseq_mono_P6AN2
    (P := fun n C =>
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - T / R n < s → s < σ n → (Kh n).time ((Kh n).activeStage (σ n)) < s →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s)
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) →
          ∀ z : ((Kh n).stageAt (σ n)).Carrier,
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) x z <
                ENNReal.ofReal (1 / Real.sqrt (C * R n)) →
              metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) z ≤ C * R n)
    (G := fun n => (Kh n).time ((Kh n).activeStage (σ n)) < σ n)
    (fun n hn C => hscalW_body_of_not_regularTop_P6AN2 (Kh n) (σ n) (y n) _ hn)
    (fun n C C' hC hCC h => hscalW_body_mono_P6AN2 (Kh n) (σ n) (y n) _ (hR n) hC hCC h) ?_
  intro φ hφ hreg
  obtain ⟨ψ, hψ, hdep⟩ := hdriver φ hφ hreg
  obtain ⟨K, hK, hev⟩ := hdep T hT (2 * D) (by positivity)
  refine ⟨ψ, hψ, max (max 1 (9 * K)) ((Real.exp (9 * K * T) / D) ^ 2),
    (le_max_left _ _).trans (le_max_left _ _), ?_⟩
  filter_upwards [hev] with i hi
  intro x hx s hs1 hs2 hs3 _hguard z hz
  exact (Kh (φ (ψ i))).scalar_le_of_tracedRegion_P6AN (σ (φ (ψ i))) (y (φ (ψ i)))
    (hR (φ (ψ i))) hD hK ((le_max_left _ _).trans (le_max_left _ _))
    ((le_max_right _ _).trans (le_max_left _ _)) (le_max_right _ _) hi x hx s hs1 hs2 hs3 z hz

/-- **final 孪生（`_P6AN2`，PROVED）**：结论 = `hscalW_final_P6M6`（显式 Prop，展开）。前提只要求
**final-slab regular top 子列**（`activeStage σ = last ∧ time last < σ`）上的子列 driver——其余指标上
final 体平凡（`hscalW_final_body_of_not_finalTop_P6AN2`）。同 slab 换算在 final slab 内同样适用
（外审 Q3(b)：同 slab 引理不排除最后一个 stage）。 -/
theorem hscalW_final_eventually_of_subseqDriver_P6AN2 (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hdriverF : ∀ φ : ℕ → ℕ, StrictMono φ →
      (∀ k, (Kh (φ k)).activeStage (σ (φ k)) = Fin.last (Kh (φ k)).eventCount ∧
        (Kh (φ k)).time (Fin.last (Kh (φ k)).eventCount) < σ (φ k)) →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ T : ℝ, 0 < T → DepthExtendable Kh σ y R (φ ∘ ψ) T) :
    ObservedHistory.hscalW_final_P6M6 Kh Tn aSeed σ haT hsT has pT seedTrace y R L := by
  intro D T hD hT
  refine exists_const_eventually_of_subseq_mono_P6AN2
    (P := fun n C => (Kh n).activeStage (σ n) = Fin.last (Kh n).eventCount →
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - T / R n < s → s < σ n →
          (Kh n).time (Fin.last (Kh n).eventCount) < s →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s)
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) →
          ∀ z : ((Kh n).stageAt (σ n)).Carrier,
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) x z <
                ENNReal.ofReal (1 / Real.sqrt (C * R n)) →
              metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) z ≤ C * R n)
    (G := fun n => (Kh n).activeStage (σ n) = Fin.last (Kh n).eventCount ∧
      (Kh n).time (Fin.last (Kh n).eventCount) < σ n)
    (fun n hn C => hscalW_final_body_of_not_finalTop_P6AN2 (Kh n) (σ n) (y n) _ hn)
    (fun n C C' hC hCC h => hscalW_final_body_mono_P6AN2 (Kh n) (σ n) (y n) _ (hR n) hC hCC h) ?_
  intro φ hφ hreg
  obtain ⟨ψ, hψ, hdep⟩ := hdriverF φ hφ hreg
  obtain ⟨K, hK, hev⟩ := hdep T hT (2 * D) (by positivity)
  refine ⟨ψ, hψ, max (max 1 (9 * K)) ((Real.exp (9 * K * T) / D) ^ 2),
    (le_max_left _ _).trans (le_max_left _ _), ?_⟩
  filter_upwards [hev] with i hi
  intro hfin x hx s hs1 hs2 hs3 _hguard z hz
  have hs3' : (Kh (φ (ψ i))).time ((Kh (φ (ψ i))).activeStage (σ (φ (ψ i)))) < s := by
    rw [hfin]
    exact hs3
  exact (Kh (φ (ψ i))).scalar_le_of_tracedRegion_P6AN (σ (φ (ψ i))) (y (φ (ψ i)))
    (hR (φ (ψ i))) hD hK ((le_max_left _ _).trans (le_max_left _ _))
    ((le_max_right _ _).trans (le_max_left _ _)) (le_max_right _ _) hi x hx s hs1 hs2 hs3' z hz

/-- **R-AN-3（`_P6AN2`，PROVED，搬运路线）**：P6CD 层（K 层）supplies ⇒ `toHistory` 上的子列全深度
`DepthExtendable`。证明 = `false_of_selection_eventSlab_late_prefix_cond_P6CD` 的步骤 1–2 逐字：
K 层 `hseed / hkappa / hwitC / hbcadC` 经 `*_seq_of_eventPrefix_P6M/P6CD` 下推到 extendAt history
`Hs n = (K n).eventPrefix (j n) (t n)`，在 `Hs` 上跑 `exists_subseq_htraced_extendAt_late_cond_P6CD`
（`hsurvive / hextend / hpinch / hderiv` 是树内 extendAt 实例），再经 `depthExtendable_of_eventPrefix_P6M`
把 `DepthExtendable` 搬回 `(K n).toHistory`（traced region 只用 `≤ σ` 的时刻：`eventPrefix` 在 `t n` 截断）。
具名 binder：`hanchor0`（G-flow 形，可由 G2 `hanchor0_event_of_shortSLT_top_P6AN2` 供）与 `hbcadC`。 -/
theorem exists_subseq_depth_toHistory_eventSlab_P6AN2 :
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      {ε : ℝ} → (hε : 0 < ε) → (hεX : ε ≤ crossingWindowNeckAccuracy.{u}) →
      (hεN : ε ≤ crossingNeckAccuracy.{u}) →
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {j : ∀ n, Fin (K n).eventCount} → {t : ℕ → ℝ} →
      (hjt : ∀ n, (K n).time (j n).castSucc < t n) → (htj : ∀ n, t n < (K n).time (j n).succ) →
      {D θcap qcan T₀ : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} → {δb : ℕ → ℝ} →
      {records : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
        T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
        GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (p n)} →
      (recordsF : ∀ n i, GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (pF n)) →
      {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier} →
      {a₀ : ℝ} → (ha₀ : 0 < a₀) →
      (hHI : ∀ n x,
        InFixedHamiltonIveyRegion (((K n).prefixAt (j n).castSucc).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt (((K n).prefixAt (j n).castSucc).initialMetric 0) x) →
      (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow) →
      (hδF : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
        T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
        (pF n).delta (((K n).prefixAt (j n).castSucc).time i.succ) ≤ δb n) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscale : ∀ (n : ℕ) i hi b,
        ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinch : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsPinched phi ∧
        Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
          (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ)) phi) →
      (hslab : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsDerivative Ctime (qcan n)
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount)) →
      (hderG : ∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore (2 * Ctime)
        (2 * qcan n) (t n)) →
      (hqR : ∀ n, qcan n < ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
        (hi : T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
        (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
        (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
          (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
        (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
          t n - ((K n).prefixAt (j n).castSucc).time i.succ ≤
            θcap n * (((records n i hi).static b).neck.scale)⁻¹) →
      (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
        t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hRt : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) *
        t n) atTop atTop) →
      (hanchor0 : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
        ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
            (yG n)
            (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
          ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
            Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      {r₀ w : ℝ} → (hr₀ : 0 < r₀) → (hw : 0 < w) →
      (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Kh n).stageAt (σ n)).Carrier
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
              (r₀ / Real.sqrt (R n)))) →
      {κ : ℝ} → (hκ : 0 < κ) → (ρnc : ℕ → ℝ) →
      (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop) →
      (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'') →
      {C1s C2s Cs : ℝ} → {qs : ℕ → ℝ} → (hqs : ∀ n, qs n ≤ Cs * R n) →
      (hwitC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) ε C1s C2s
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε) →
      (hbcadC : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T Kc : ℝ, -σ' < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (Kc * R n)) →
        ∀ᶠ n in map φ atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₂),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ C * R n) →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ T : ℝ, 0 < T → DepthExtendable Kh σ y R ψ T := by
  intro Ctime phi ε hε hεX hεN hphi K j t hjt htj D θcap qcan T₀ p pF δb records recordsF yG a₀ ha₀
    hHI hcan hδF hqcan hpar hscale hθcap hpinch hslab hderG hqR hnot hT₀ hRt hanchor0 Kh hKh σ y R
    hσ hyG hRn r₀ w hr₀ hw hseed κ hκ ρnc hradii hkappa C1s C2s Cs qs hqs hwitC hbcadC
  subst hKh
  -- E 层（`Hs n = (K n).eventPrefix (j n) (t n)`）的基点对象
  let Hs : ℕ → ObservedHistory.{u} := fun n =>
    ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory
  let ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon := fun n =>
    ((K n).prefixAt (j n).castSucc).extendAtTime ((K n).prefixAt_time_last _)
      ((K n).toHistory.event (j n)).incoming ((K n).event_initial (j n)) (hjt n) (htj n)
  have hσ' : ∀ n, (ts n : ℝ) = σ n := fun n => (hσ n).symm
  have hidx : ∀ n, Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ (j n).castSucc.isLt))
      ((Hs n).activeStage (ts n)) = (K n).toHistory.activeStage (σ n) := fun n =>
    Fin.ext ((K n).eventPrefix_activeStage_val (j n) (hjt n) (htj n) (ts n) (σ n) (hσ' n))
  let ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier := fun n =>
    cast (congrArg (fun m => ((K n).stage m).Carrier) (hidx n)).symm (y n)
  have hysK : ∀ n, HEq (ys n) (y n) := fun n => cast_heq _ _
  have hys : ∀ n, HEq (ys n) (yG n) := fun n => (hysK n).trans (hyG n)
  have hHs' : ∀ n, Hs n = ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory :=
    fun _ => rfl
  -- 1. P6D2 G3 在 E 上给 htraced（E 层 trace-local 前提由 G3 桥从 K 层拉回）
  obtain ⟨ψ, hψ, hall⟩ := exists_subseq_htraced_extendAt_late_cond_P6CD
    (H := fun n => (K n).prefixAt (j n).castSucc)
    (G := fun n => ((K n).toHistory.event (j n)).incoming)
    (s := fun n => (K n).time (j n).succ) (y := yG) hphi recordsF ha₀ hHI
    (fun n => (K n).prefixAt_time_last _) (fun n => (K n).event_initial (j n)) hcan hδF hqcan hpar
    hscale hθcap hpinch hslab hjt htj hderG hqR hnot hT₀ hRt hanchor0 Hs ts ys R rfl HEq.rfl hys
    hRn
    hr₀ hw (hseed_seq_of_eventPrefix_P6M hHs' hσ' hysK hseed) hκ ρnc hradii
    (hkappa_seq_of_eventPrefix_P6M hHs' hσ' hysK hkappa) hε hεX hεN hqs
    (hwitC_seq_of_eventPrefix_P6CD hHs' hσ' hysK hwitC)
    (hbcadC_seq_of_eventPrefix_P6CD hHs' hσ' hysK hbcadC)
  exact ⟨ψ, hψ, fun T hT => depthExtendable_of_eventPrefix_P6M hHs' hσ' hysK (hall T hT)⟩

/-- **schedule 重索引（`_P6AN2`，PROVED）**：严格增 `φ` 有 `n ≤ φ n`；P6CD 的 `n` 依赖 schedule
（`hqcan`：`n + 1 ≤ qcan n`；`hpar`：精度 `≤ 1/(n+1)`、半径 `≥ n + 1`、阶 `≥ n + 2`；`hθcap`：
`θcap n ≥ 1 − 1/(n+2)`）都对 `n` 单调变强，故沿 `φ` 重索引后仍成立（外审 Q4 第四组"核实 driver 其余
supplies 的重索引稳定性"）。 -/
theorem natCast_le_strictMono_P6AN2 {φ : ℕ → ℕ} (hφ : StrictMono φ) (n : ℕ) :
    (n : ℝ) ≤ (φ n : ℝ) := by
  exact_mod_cast hφ.id_le n

/-- **遗传子列形（`_P6AN2`，PROVED）**：`exists_subseq_depth_toHistory_eventSlab_P6AN2` 的前提**全部**
重索引到任意严格增子列 `φ`（逐 n 前提取 `φ n`；eventually / `Tendsto` 前提沿 `φ` 复合；条件形
`hwitC / hbcadC` 取 `φ ∘ φ'`；schedule 前提 `hqcan / hpar / hscale / hθcap` 用 `n ≤ φ n` 单调性），再跑一次 ⇒
`∀ φ ↑, ∃ ψ ↑, ∀ T > 0, DepthExtendable Kh σ y R (φ ∘ ψ) T`——正是 G1 `hdriver` 的形状。 -/
theorem hdepth_toHistory_eventSlab_P6AN2 :
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      {ε : ℝ} → (hε : 0 < ε) → (hεX : ε ≤ crossingWindowNeckAccuracy.{u}) →
      (hεN : ε ≤ crossingNeckAccuracy.{u}) →
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {j : ∀ n, Fin (K n).eventCount} → {t : ℕ → ℝ} →
      (hjt : ∀ n, (K n).time (j n).castSucc < t n) → (htj : ∀ n, t n < (K n).time (j n).succ) →
      {D θcap qcan T₀ : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} → {δb : ℕ → ℝ} →
      {records : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
        T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
        GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (p n)} →
      (recordsF : ∀ n i, GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (pF n)) →
      {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier} →
      {a₀ : ℝ} → (ha₀ : 0 < a₀) →
      (hHI : ∀ n x,
        InFixedHamiltonIveyRegion (((K n).prefixAt (j n).castSucc).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt (((K n).prefixAt (j n).castSucc).initialMetric 0) x) →
      (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow) →
      (hδF : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
        T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
        (pF n).delta (((K n).prefixAt (j n).castSucc).time i.succ) ≤ δb n) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscale : ∀ (n : ℕ) i hi b,
        ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinch : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsPinched phi ∧
        Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
          (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ)) phi) →
      (hslab : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsDerivative Ctime (qcan n)
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount)) →
      (hderG : ∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore (2 * Ctime)
        (2 * qcan n) (t n)) →
      (hqR : ∀ n, qcan n < ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
        (hi : T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
        (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
        (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
          (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
        (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
          t n - ((K n).prefixAt (j n).castSucc).time i.succ ≤
            θcap n * (((records n i hi).static b).neck.scale)⁻¹) →
      (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
        t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hRt : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) *
        t n) atTop atTop) →
      (hanchor0 : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
        ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
            (yG n)
            (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
          ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
            Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      {r₀ w : ℝ} → (hr₀ : 0 < r₀) → (hw : 0 < w) →
      (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Kh n).stageAt (σ n)).Carrier
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
              (r₀ / Real.sqrt (R n)))) →
      {κ : ℝ} → (hκ : 0 < κ) → (ρnc : ℕ → ℝ) →
      (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop) →
      (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'') →
      {C1s C2s Cs : ℝ} → {qs : ℕ → ℝ} → (hqs : ∀ n, qs n ≤ Cs * R n) →
      (hwitC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) ε C1s C2s
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε) →
      (hbcadC : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T Kc : ℝ, -σ' < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (Kc * R n)) →
        ∀ᶠ n in map φ atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₂),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ C * R n) →
      ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∀ T : ℝ, 0 < T → DepthExtendable Kh σ y R (φ ∘ ψ) T := by
  intro Ctime phi ε hε hεX hεN hphi K j t hjt htj D θcap qcan T₀ p pF δb records recordsF yG a₀ ha₀
    hHI hcan hδF hqcan hpar hscale hθcap hpinch hslab hderG hqR hnot hT₀ hRt hanchor0 Kh hKh σ y R
    hσ hyG hRn r₀ w hr₀ hw hseed κ hκ ρnc hradii hkappa C1s C2s Cs qs hqs hwitC hbcadC φ hφ
  subst hKh
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hφn := natCast_le_strictMono_P6AN2 hφ
  have hqcan' : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan (φ n) := fun n => by linarith [hqcan (φ n), hφn n]
  have hpar' : ∀ n : ℕ, (p (φ n)).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D (φ n) ∧
      D (φ n) ≤ (p (φ n)).modelRadius ∧ n + 2 ≤ (p (φ n)).modelOrder ∧
      δb (φ n) ≤ 1 / ((n : ℝ) + 1) := fun n => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hpar (φ n)
    have hdiv : 1 / ((φ n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith [hφn n])
    exact ⟨h1.trans hdiv, by linarith [hφn n], h3, (Nat.add_le_add_right (hφ.id_le n) 2).trans h4,
      h5.trans hdiv⟩
  have hscale' : ∀ (n : ℕ) i hi b,
      ((n : ℝ) + 1) * qcan (φ n) ≤ ((records (φ n) i hi).static b).neck.scale := fun n i hi b => by
    have hq0 : 0 ≤ qcan (φ n) := by
      linarith [hqcan (φ n), (Nat.cast_nonneg (φ n) : (0 : ℝ) ≤ φ n)]
    exact (mul_le_mul_of_nonneg_right (by linarith [hφn n]) hq0).trans (hscale (φ n) i hi b)
  have hθcap' : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap (φ n) := fun n => by
    have hdiv : 1 / ((φ n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 2) :=
      one_div_le_one_div_of_le (by positivity) (by linarith [hφn n])
    linarith [hθcap (φ n)]
  obtain ⟨ψ, hψ, hdep⟩ := exists_subseq_depth_toHistory_eventSlab_P6AN2 hε hεX hεN hphi
    (K := fun n => K (φ n)) (j := fun n => j (φ n)) (t := fun n => t (φ n))
    (fun n => hjt (φ n)) (fun n => htj (φ n)) (D := fun n => D (φ n))
    (θcap := fun n => θcap (φ n)) (qcan := fun n => qcan (φ n)) (T₀ := fun n => T₀ (φ n))
    (p := fun n => p (φ n)) (pF := fun n => pF (φ n)) (δb := fun n => δb (φ n))
    (records := fun n => records (φ n)) (fun n => recordsF (φ n)) (yG := fun n => yG (φ n)) ha₀
    (fun n => hHI (φ n)) (fun n => hcan (φ n)) (fun n => hδF (φ n)) hqcan' hpar' hscale' hθcap'
    (fun n => hpinch (φ n)) (fun n => hslab (φ n)) (fun n => hderG (φ n)) (fun n => hqR (φ n))
    (fun n => hnot (φ n)) (fun B => hφt.eventually (hT₀ B)) (hRt.comp hφt)
    (fun A hA => by
      obtain ⟨Q, hQ, hev⟩ := hanchor0 A hA
      exact ⟨Q, hQ, hφt.eventually hev⟩)
    (fun n => (K (φ n)).toHistory) rfl (fun n => σ (φ n)) (fun n => y (φ n)) (fun n => R (φ n))
    (fun n => hσ (φ n)) (fun n => hyG (φ n)) (fun n => hRn (φ n)) hr₀ hw (hφt.eventually hseed)
    hκ (fun n => ρnc (φ n)) (hradii.comp hφt)
    (fun D T hD hT => hφt.eventually (hkappa D T hD hT)) (qs := fun n => qs (φ n))
    (fun n => hqs (φ n)) (fun φ' hφ' => hwitC (φ ∘ φ') (hφ.comp hφ'))
    (fun A Dd hA hDd => by
      obtain ⟨C, hC⟩ := hbcadC A Dd hA hDd
      exact ⟨C, fun φ' hφ' => hC (φ ∘ φ') (hφ.comp hφ')⟩)
  exact ⟨ψ, hψ, hdep⟩

/-- **组合 G1 ∘ G3（`_P6AN2`，PROVISIONAL：binder = G-flow `hanchor0` + `hbcadC`；其余为 P6CD 层 supplies）**：
event-slab selection 族上，结论 = `hdistW_of_firstExit_P6DW` 的 `hscalW` binder **逐字**（`Kh = toHistory`）。
每个 `n` 都是 event-interior regular top（`hjt`），子列 driver = `hdepth_toHistory_eventSlab_P6AN2`。 -/
theorem hscalW_eventSlab_of_supplies_P6AN2 :
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      {ε : ℝ} → (hε : 0 < ε) → (hεX : ε ≤ crossingWindowNeckAccuracy.{u}) →
      (hεN : ε ≤ crossingNeckAccuracy.{u}) →
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {j : ∀ n, Fin (K n).eventCount} → {t : ℕ → ℝ} →
      (hjt : ∀ n, (K n).time (j n).castSucc < t n) → (htj : ∀ n, t n < (K n).time (j n).succ) →
      {D θcap qcan T₀ : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} → {δb : ℕ → ℝ} →
      {records : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
        T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
        GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (p n)} →
      (recordsF : ∀ n i, GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (pF n)) →
      {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier} →
      {a₀ : ℝ} → (ha₀ : 0 < a₀) →
      (hHI : ∀ n x,
        InFixedHamiltonIveyRegion (((K n).prefixAt (j n).castSucc).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt (((K n).prefixAt (j n).castSucc).initialMetric 0) x) →
      (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow) →
      (hδF : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
        T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
        (pF n).delta (((K n).prefixAt (j n).castSucc).time i.succ) ≤ δb n) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscale : ∀ (n : ℕ) i hi b,
        ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinch : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsPinched phi ∧
        Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
          (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ)) phi) →
      (hslab : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsDerivative Ctime (qcan n)
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount)) →
      (hderG : ∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore (2 * Ctime)
        (2 * qcan n) (t n)) →
      (hqR : ∀ n, qcan n < ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
        (hi : T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
        (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
        (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
          (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
        (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
          t n - ((K n).prefixAt (j n).castSucc).time i.succ ≤
            θcap n * (((records n i hi).static b).neck.scale)⁻¹) →
      (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
        t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hRt : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) *
        t n) atTop atTop) →
      (hanchor0 : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
        ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
            (yG n)
            (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
          ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
            Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      {r₀ w : ℝ} → (hr₀ : 0 < r₀) → (hw : 0 < w) →
      (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Kh n).stageAt (σ n)).Carrier
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
              (r₀ / Real.sqrt (R n)))) →
      {κ : ℝ} → (hκ : 0 < κ) → (ρnc : ℕ → ℝ) →
      (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop) →
      (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'') →
      {C1s C2s Cs : ℝ} → {qs : ℕ → ℝ} → (hqs : ∀ n, qs n ≤ Cs * R n) →
      (hwitC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) ε C1s C2s
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε) →
      (hbcadC : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T Kc : ℝ, -σ' < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (Kc * R n)) →
        ∀ᶠ n in map φ atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₂),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ C * R n) →
      ∀ (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
        (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
        (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
        (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
          ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n)) (L : ℕ → ℝ),
      ∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ s : ℝ, (σ n : ℝ) - T / R n < s → s < σ n → (Kh n).time ((Kh n).activeStage (σ n)) < s →
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s)
            ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
              ((Kh n).activeStage_mono (hsT n))) x ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        ∀ z : ((Kh n).stageAt (σ n)).Carrier,
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) x z <
              ENNReal.ofReal (1 / Real.sqrt (C * R n)) →
            metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) z ≤ C * R n := by
  intro Ctime phi ε hε hεX hεN hphi K j t hjt htj D θcap qcan T₀ p pF δb records recordsF yG a₀ ha₀
    hHI hcan hδF hqcan hpar hscale hθcap hpinch hslab hderG hqR hnot hT₀ hRt hanchor0 Kh hKh σ y R
    hσ hyG hRn r₀ w hr₀ hw hseed κ hκ ρnc hradii hkappa C1s C2s Cs qs hqs hwitC hbcadC Tn aSeed haT
    hsT has pT seedTrace L
  have hR : ∀ n, 0 < R n := fun n => by
    rw [hRn n]
    exact (lt_of_lt_of_le (by positivity) (hqcan n)).trans (hqR n)
  exact hscalW_eventually_of_subseqDriver_P6AN2 Kh Tn aSeed σ haT hsT has pT seedTrace y R L hR
    (fun φ hφ _ => hdepth_toHistory_eventSlab_P6AN2 hε hεX hεN hphi hjt htj recordsF ha₀ hHI hcan
      hδF hqcan hpar hscale hθcap hpinch hslab hderG hqR hnot hT₀ hRt hanchor0 Kh hKh σ y R hσ hyG
      hRn hr₀ hw hseed hκ ρnc hradii hkappa hqs hwitC hbcadC φ hφ)

/-- **组合 G1 ∘ G2 ∘ G3（`_P6AN2`，PROVISIONAL：binder = `ShortSLT_C11KS β` + `TopAnchorInputs_P6AN2 β`
（event 构形）+ `hbcadC`；其余为 P6CD 层 supplies）**：`hscalW_eventSlab_of_supplies_P6AN2` 的 `hanchor0`
由 top-anchor adapter `hanchor0_event_of_shortSLT_top_P6AN2` 供。结论 = `hscalW` binder 逐字。非循环：
`hanchor0` 不经 `hdistW ← hscalW`。 -/
theorem hscalW_eventSlab_of_shortSLT_top_P6AN2 :
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      {ε : ℝ} → (hε : 0 < ε) → (hεX : ε ≤ crossingWindowNeckAccuracy.{u}) →
      (hεN : ε ≤ crossingNeckAccuracy.{u}) →
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {j : ∀ n, Fin (K n).eventCount} → {t : ℕ → ℝ} →
      (hjt : ∀ n, (K n).time (j n).castSucc < t n) → (htj : ∀ n, t n < (K n).time (j n).succ) →
      {D θcap qcan T₀ : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} → {δb : ℕ → ℝ} →
      {records : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
        T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
        GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (p n)} →
      (recordsF : ∀ n i, GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (pF n)) →
      {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier} →
      {a₀ : ℝ} → (ha₀ : 0 < a₀) →
      (hHI : ∀ n x,
        InFixedHamiltonIveyRegion (((K n).prefixAt (j n).castSucc).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt (((K n).prefixAt (j n).castSucc).initialMetric 0) x) →
      (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow) →
      (hδF : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
        T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
        (pF n).delta (((K n).prefixAt (j n).castSucc).time i.succ) ≤ δb n) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscale : ∀ (n : ℕ) i hi b,
        ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinch : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsPinched phi ∧
        Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
          (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ)) phi) →
      (hslab : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsDerivative Ctime (qcan n)
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount)) →
      (hderG : ∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore (2 * Ctime)
        (2 * qcan n) (t n)) →
      (hqR : ∀ n, qcan n < ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
        (hi : T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
        (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
        (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
          (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
        (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
          t n - ((K n).prefixAt (j n).castSucc).time i.succ ≤
            θcap n * (((records n i hi).static b).neck.scale)⁻¹) →
      (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
        t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hRt : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) *
        t n) atTop atTop) →
      {β : ℝ} → (hX : ShortSLT_C11KS.{u} β) →
      (hin : TopAnchorInputs_P6AN2 β (fun n => (K n).prefixAt (j n).castSucc)
        (fun n => (K n).prefixAt_time_last _) (fun n => (K n).time (j n).succ)
        (fun n => ((K n).toHistory.event (j n)).incoming) (fun n => (K n).event_initial (j n)) t
        yG) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      {r₀ w : ℝ} → (hr₀ : 0 < r₀) → (hw : 0 < w) →
      (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Kh n).stageAt (σ n)).Carrier
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
              (r₀ / Real.sqrt (R n)))) →
      {κ : ℝ} → (hκ : 0 < κ) → (ρnc : ℕ → ℝ) →
      (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop) →
      (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'') →
      {C1s C2s Cs : ℝ} → {qs : ℕ → ℝ} → (hqs : ∀ n, qs n ≤ Cs * R n) →
      (hwitC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) ε C1s C2s
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε) →
      (hbcadC : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T Kc : ℝ, -σ' < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (Kc * R n)) →
        ∀ᶠ n in map φ atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₂),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ C * R n) →
      ∀ (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
        (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
        (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
        (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
          ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n)) (L : ℕ → ℝ),
      ∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ s : ℝ, (σ n : ℝ) - T / R n < s → s < σ n → (Kh n).time ((Kh n).activeStage (σ n)) < s →
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s)
            ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
              ((Kh n).activeStage_mono (hsT n))) x ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        ∀ z : ((Kh n).stageAt (σ n)).Carrier,
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) x z <
              ENNReal.ofReal (1 / Real.sqrt (C * R n)) →
            metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) z ≤ C * R n := by
  intro Ctime phi ε hε hεX hεN hphi K j t hjt htj D θcap qcan T₀ p pF δb records recordsF yG a₀ ha₀
    hHI hcan hδF hqcan hpar hscale hθcap hpinch hslab hderG hqR hnot hT₀ hRt β hX hin Kh hKh σ y R
    hσ hyG hRn r₀ w hr₀ hw hseed κ hκ ρnc hradii hkappa C1s C2s Cs qs hqs hwitC hbcadC
  exact hscalW_eventSlab_of_supplies_P6AN2 hε hεX hεN hphi hjt htj recordsF ha₀ hHI hcan hδF hqcan
    hpar hscale hθcap hpinch hslab hderG hqR hnot hT₀ hRt
    (hanchor0_event_of_shortSLT_top_P6AN2 hX hjt htj hin) Kh hKh σ y R hσ hyG hRn hr₀ hw hseed hκ
    ρnc hradii hkappa hqs hwitC hbcadC


/-- **R-AN-3 final slab 孪生（`_P6AN2`，PROVED，搬运路线）**：FINCOND
`false_of_selection_finalSlab_lateHI_prefix_cond_P6FC` 的步骤 1–2 逐字：final E 层
`Hs n = ((K n).prefixAt last).extendAt (finalSlab …)`，K 层 `hseed / hkappa / hwitC / hbcadC` 经
`*_seq_final_P6M / *_seq_final_P6FC` 下推，跑 `exists_subseq_htraced_extendAt_lateHI_cond_P6CD`
（`s := horizon`），`depthExtendable_final_P6M` 搬回 `(K n).toHistory`。具名 binder：G-flow `hanchor0`
（G2 final 版可供）与 `hbcadC`。 -/
theorem exists_subseq_depth_toHistory_finalSlab_P6AN2 :
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      {ε : ℝ} → (hε : 0 < ε) → (hεX : ε ≤ crossingWindowNeckAccuracy.{u}) →
      (hεN : ε ≤ crossingNeckAccuracy.{u}) →
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {t : ℕ → ℝ} →
      (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) →
      (htK : ∀ n, t n < (K n).horizon) →
      {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
        ((K n).time (Fin.last (K n).eventCount)) (K n).horizon} →
      (hG : ∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
        ((htl n).trans (htK n)) le_rfl) →
      {D θcap qcan T₀ : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} → {δb : ℕ → ℝ} →
      {records : ∀ n (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount),
        T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ →
        GeometricCutoffRecord ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i (p n)} →
      (recordsF : ∀ n i, GeometricCutoffRecord ((K n).prefixAt (Fin.last (K
        n).eventCount)).toHistory i (pF n)) →
      {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier} →
      {a₀ : ℕ → ℝ} →
      (hHI : ∀ n x,
        InFixedHamiltonIveyRegion (((K n).prefixAt (Fin.last (K n).eventCount)).initialMetric 0) (a₀
          n) x ∧
        -3 / a₀ n ≤ metricScalarAt (((K n).prefixAt (Fin.last (K n).eventCount)).initialMetric 0) x)
          →
      (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow) →
      (hδF : ∀ n (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount),
        T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ →
        (pF n).delta (((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ) ≤ δb n) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscale : ∀ (n : ℕ) i hi b,
        ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale) →
      (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
        1 ≤ a₀ n * ((records n i hi).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount,
          Perelman.PhiAlmostNonnegative
            (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).incoming.flow
            (Ico (((K n).prefixAt (Fin.last (K n).eventCount)).time i.castSucc)
              (((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ) ∩ Ici (T₀ n)) phi) ∧
        Perelman.PhiAlmostNonnegative (G n).flow
          (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) phi) →
      (hslab : ∀ n, ((K n).prefixAt (Fin.last (K n).eventCount)).EventSlabsDerivative Ctime (qcan n)
        (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)) →
      (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime)
        (2 * qcan n) (t n)) →
      (hqR : ∀ n, qcan n < (G n).flow.scalar (t n) (yG n)) →
      (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
        (hi : T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ)
        (hl : i.succ ≤ Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
        (A : BackwardPointTrace ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i.succ
          (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount) hl (yG n))
        (b : (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
          t n - ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ ≤
            θcap n * (((records n i hi).static b).neck.scale)⁻¹) →
      (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
        t n - B / (G n).flow.scalar (t n) (yG n)) →
      (hRt : Tendsto (fun n => (G n).flow.scalar (t n) (yG n) *
        t n) atTop atTop) →
      (hanchor0 : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
        ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n))
            (yG n)
            (A / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
          (G n).flow.scalar (t n) z ≤
            Q * (G n).flow.scalar (t n) (yG n)) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n)) →
      {r₀ w : ℝ} → (hr₀ : 0 < r₀) → (hw : 0 < w) →
      (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Kh n).stageAt (σ n)).Carrier
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
              (r₀ / Real.sqrt (R n)))) →
      {κ : ℝ} → (hκ : 0 < κ) → (ρnc : ℕ → ℝ) →
      (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop) →
      (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'') →
      {C1s C2s Cs : ℝ} → {qs : ℕ → ℝ} → (hqs : ∀ n, qs n ≤ Cs * R n) →
      (hwitC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) ε C1s C2s
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε) →
      (hbcadC : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T Kc : ℝ, -σ' < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (Kc * R n)) →
        ∀ᶠ n in map φ atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₂),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ C * R n) →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ T : ℝ, 0 < T → DepthExtendable Kh σ y R ψ T := by
  intro Ctime phi ε hε hεX hεN hphi K t htl htK G hG D θcap qcan T₀ p pF δb records recordsF yG a₀
    hHI hcan hδF hqcan hpar hscale hbirthA hθcap hpinch hslab hderG hqR hnot hT₀ hRt hanchor0 Kh hKh
    σ y R hσ hyG hRn r₀ w hr₀ hw hseed κ hκ ρnc hradii hkappa C1s C2s Cs qs hqs hwitC hbcadC
  subst hKh
  obtain rfl : G = fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl := funext hG
  -- E 层（`Hs n` = final 截断 history）的基点对象
  let Hs : ℕ → ObservedHistory.{u} := fun n =>
    (((K n).prefixAt (Fin.last (K n).eventCount)).extendAt ((K n).prefixAt_time_last _)
      (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl ((htl n).trans (htK n))
        le_rfl) ((K n).final_initial ((htl n).trans (htK n))) (htl n) (htK n)).toHistory
  let ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon := fun n =>
    ((K n).prefixAt (Fin.last (K n).eventCount)).extendAtTime ((K n).prefixAt_time_last _)
      (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl ((htl n).trans (htK n))
        le_rfl) ((K n).final_initial ((htl n).trans (htK n))) (htl n) (htK n)
  have hσ' : ∀ n, (ts n : ℝ) = σ n := fun n => (hσ n).symm
  have hidx : ∀ n, @Eq (Fin ((K n).toHistory.eventCount + 1)) ((Hs n).activeStage (ts n))
      ((K n).toHistory.activeStage (σ n)) := fun n =>
    (K n).activeStage_final_P6M ((htl n).trans (htK n)) (htl n) (htK n) (ts n) (σ n) (hσ' n)
  let ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier := fun n =>
    cast (congrArg (fun m => ((K n).stage m).Carrier) (hidx n)).symm (y n)
  have hysK : ∀ n, HEq (ys n) (y n) := fun n => cast_heq _ _
  have hys : ∀ n, HEq (ys n) (yG n) := fun n => (hysK n).trans (hyG n)
  have hHs' : ∀ n, Hs n = (((K n).prefixAt (Fin.last (K n).eventCount)).extendAt
      ((K n).prefixAt_time_last _) (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming
        le_rfl ((htl n).trans (htK n)) le_rfl) ((K n).final_initial ((htl n).trans (htK n)))
      (htl n) (htK n)).toHistory := fun _ => rfl
  -- 1. lateHI kernel 在 E 上给 htraced（E 层 trace-local 前提由 final 桥从 K 层拉回）
  obtain ⟨ψ, hψ, hall⟩ := exists_subseq_htraced_extendAt_lateHI_cond_P6CD
    (H := fun n => (K n).prefixAt (Fin.last (K n).eventCount))
    (G := fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl)
    (s := fun n => (K n).horizon) (y := yG) hphi recordsF hHI
    (fun n => (K n).prefixAt_time_last _) (fun n => (K n).final_initial ((htl n).trans (htK n)))
      hcan hδF
    hqcan hpar hscale hbirthA hθcap hpinch hslab htl htK hderG hqR hnot hT₀ hRt hanchor0 Hs ts ys
    R rfl HEq.rfl hys hRn hr₀ hw (hseed_seq_final_P6M hHs' hσ' hysK hseed) hκ ρnc hradii
    (hkappa_seq_final_P6M hHs' hσ' hysK hkappa) hε hεX hεN hqs
    (hwitC_seq_final_P6FC hHs' hσ' hysK hwitC)
    (hbcadC_seq_final_P6FC hHs' hσ' hysK hbcadC)
  exact ⟨ψ, hψ, fun T hT => depthExtendable_final_P6M hHs' hσ' hysK (hall T hT)⟩

/-- **final 遗传子列形（`_P6AN2`，PROVED）**：`exists_subseq_depth_toHistory_finalSlab_P6AN2` 的前提全部
重索引到任意严格增 `φ`（含逐 n 的 `a₀`、eventually 的 `hbirthA`、schedule `hqcan / hpar / hscale / hθcap`）。 -/
theorem hdepth_toHistory_finalSlab_P6AN2 :
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      {ε : ℝ} → (hε : 0 < ε) → (hεX : ε ≤ crossingWindowNeckAccuracy.{u}) →
      (hεN : ε ≤ crossingNeckAccuracy.{u}) →
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {t : ℕ → ℝ} →
      (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) →
      (htK : ∀ n, t n < (K n).horizon) →
      {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
        ((K n).time (Fin.last (K n).eventCount)) (K n).horizon} →
      (hG : ∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
        ((htl n).trans (htK n)) le_rfl) →
      {D θcap qcan T₀ : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} → {δb : ℕ → ℝ} →
      {records : ∀ n (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount),
        T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ →
        GeometricCutoffRecord ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i (p n)} →
      (recordsF : ∀ n i, GeometricCutoffRecord ((K n).prefixAt (Fin.last (K
        n).eventCount)).toHistory i (pF n)) →
      {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier} →
      {a₀ : ℕ → ℝ} →
      (hHI : ∀ n x,
        InFixedHamiltonIveyRegion (((K n).prefixAt (Fin.last (K n).eventCount)).initialMetric 0) (a₀
          n) x ∧
        -3 / a₀ n ≤ metricScalarAt (((K n).prefixAt (Fin.last (K n).eventCount)).initialMetric 0) x)
          →
      (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow) →
      (hδF : ∀ n (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount),
        T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ →
        (pF n).delta (((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ) ≤ δb n) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscale : ∀ (n : ℕ) i hi b,
        ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale) →
      (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
        1 ≤ a₀ n * ((records n i hi).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount,
          Perelman.PhiAlmostNonnegative
            (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).incoming.flow
            (Ico (((K n).prefixAt (Fin.last (K n).eventCount)).time i.castSucc)
              (((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ) ∩ Ici (T₀ n)) phi) ∧
        Perelman.PhiAlmostNonnegative (G n).flow
          (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) phi) →
      (hslab : ∀ n, ((K n).prefixAt (Fin.last (K n).eventCount)).EventSlabsDerivative Ctime (qcan n)
        (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)) →
      (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime)
        (2 * qcan n) (t n)) →
      (hqR : ∀ n, qcan n < (G n).flow.scalar (t n) (yG n)) →
      (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
        (hi : T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ)
        (hl : i.succ ≤ Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
        (A : BackwardPointTrace ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i.succ
          (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount) hl (yG n))
        (b : (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
          t n - ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ ≤
            θcap n * (((records n i hi).static b).neck.scale)⁻¹) →
      (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
        t n - B / (G n).flow.scalar (t n) (yG n)) →
      (hRt : Tendsto (fun n => (G n).flow.scalar (t n) (yG n) *
        t n) atTop atTop) →
      (hanchor0 : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
        ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n))
            (yG n)
            (A / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
          (G n).flow.scalar (t n) z ≤
            Q * (G n).flow.scalar (t n) (yG n)) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n)) →
      {r₀ w : ℝ} → (hr₀ : 0 < r₀) → (hw : 0 < w) →
      (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Kh n).stageAt (σ n)).Carrier
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
              (r₀ / Real.sqrt (R n)))) →
      {κ : ℝ} → (hκ : 0 < κ) → (ρnc : ℕ → ℝ) →
      (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop) →
      (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'') →
      {C1s C2s Cs : ℝ} → {qs : ℕ → ℝ} → (hqs : ∀ n, qs n ≤ Cs * R n) →
      (hwitC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) ε C1s C2s
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε) →
      (hbcadC : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T Kc : ℝ, -σ' < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (Kc * R n)) →
        ∀ᶠ n in map φ atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₂),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ C * R n) →
      ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∀ T : ℝ, 0 < T → DepthExtendable Kh σ y R (φ ∘ ψ) T := by
  intro Ctime phi ε hε hεX hεN hphi K t htl htK G hG D θcap qcan T₀ p pF δb records recordsF yG a₀
    hHI hcan hδF hqcan hpar hscale hbirthA hθcap hpinch hslab hderG hqR hnot hT₀ hRt hanchor0 Kh hKh
    σ y R hσ hyG hRn r₀ w hr₀ hw hseed κ hκ ρnc hradii hkappa C1s C2s Cs qs hqs hwitC hbcadC φ hφ
  subst hKh
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hφn := natCast_le_strictMono_P6AN2 hφ
  have hqcan' : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan (φ n) := fun n => by linarith [hqcan (φ n), hφn n]
  have hpar' : ∀ n : ℕ, (p (φ n)).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D (φ n) ∧
      D (φ n) ≤ (p (φ n)).modelRadius ∧ n + 2 ≤ (p (φ n)).modelOrder ∧
      δb (φ n) ≤ 1 / ((n : ℝ) + 1) := fun n => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hpar (φ n)
    have hdiv : 1 / ((φ n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith [hφn n])
    exact ⟨h1.trans hdiv, by linarith [hφn n], h3, (Nat.add_le_add_right (hφ.id_le n) 2).trans h4,
      h5.trans hdiv⟩
  have hscale' : ∀ (n : ℕ) i hi b,
      ((n : ℝ) + 1) * qcan (φ n) ≤ ((records (φ n) i hi).static b).neck.scale := fun n i hi b => by
    have hq0 : 0 ≤ qcan (φ n) := by
      linarith [hqcan (φ n), (Nat.cast_nonneg (φ n) : (0 : ℝ) ≤ φ n)]
    exact (mul_le_mul_of_nonneg_right (by linarith [hφn n]) hq0).trans (hscale (φ n) i hi b)
  have hθcap' : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap (φ n) := fun n => by
    have hdiv : 1 / ((φ n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 2) :=
      one_div_le_one_div_of_le (by positivity) (by linarith [hφn n])
    linarith [hθcap (φ n)]
  obtain ⟨ψ, hψ, hdep⟩ := exists_subseq_depth_toHistory_finalSlab_P6AN2 hε hεX hεN hphi
    (K := fun n => K (φ n)) (t := fun n => t (φ n)) (fun n => htl (φ n)) (fun n => htK (φ n))
    (G := fun n => G (φ n)) (fun n => hG (φ n)) (D := fun n => D (φ n))
    (θcap := fun n => θcap (φ n)) (qcan := fun n => qcan (φ n)) (T₀ := fun n => T₀ (φ n))
    (p := fun n => p (φ n)) (pF := fun n => pF (φ n)) (δb := fun n => δb (φ n))
    (records := fun n => records (φ n)) (fun n => recordsF (φ n)) (yG := fun n => yG (φ n))
    (a₀ := fun n => a₀ (φ n)) (fun n => hHI (φ n)) (fun n => hcan (φ n)) (fun n => hδF (φ n))
    hqcan' hpar' hscale' (hφt.eventually hbirthA) hθcap' (fun n => hpinch (φ n))
    (fun n => hslab (φ n)) (fun n => hderG (φ n)) (fun n => hqR (φ n)) (fun n => hnot (φ n))
    (fun B => hφt.eventually (hT₀ B)) (hRt.comp hφt)
    (fun A hA => by
      obtain ⟨Q, hQ, hev⟩ := hanchor0 A hA
      exact ⟨Q, hQ, hφt.eventually hev⟩)
    (fun n => (K (φ n)).toHistory) rfl (fun n => σ (φ n)) (fun n => y (φ n)) (fun n => R (φ n))
    (fun n => hσ (φ n)) (fun n => hyG (φ n)) (fun n => hRn (φ n)) hr₀ hw (hφt.eventually hseed)
    hκ (fun n => ρnc (φ n)) (hradii.comp hφt)
    (fun D T hD hT => hφt.eventually (hkappa D T hD hT)) (qs := fun n => qs (φ n))
    (fun n => hqs (φ n)) (fun φ' hφ' => hwitC (φ ∘ φ') (hφ.comp hφ'))
    (fun A Dd hA hDd => by
      obtain ⟨C, hC⟩ := hbcadC A Dd hA hDd
      exact ⟨C, fun φ' hφ' => hC (φ ∘ φ') (hφ.comp hφ')⟩)
  exact ⟨ψ, hψ, hdep⟩

/-- **组合 G1 final ∘ G3 final（`_P6AN2`，PROVISIONAL：binder = G-flow `hanchor0` + `hbcadC`）**：
final-slab selection 族上，结论 = `hscalW_final_P6M6`（显式 Prop）。每个 `n` 都是 final-slab regular top
（`htl`），子列 driver = `hdepth_toHistory_finalSlab_P6AN2`。 -/
theorem hscalW_final_finalSlab_of_supplies_P6AN2 :
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      {ε : ℝ} → (hε : 0 < ε) → (hεX : ε ≤ crossingWindowNeckAccuracy.{u}) →
      (hεN : ε ≤ crossingNeckAccuracy.{u}) →
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {t : ℕ → ℝ} →
      (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) →
      (htK : ∀ n, t n < (K n).horizon) →
      {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
        ((K n).time (Fin.last (K n).eventCount)) (K n).horizon} →
      (hG : ∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
        ((htl n).trans (htK n)) le_rfl) →
      {D θcap qcan T₀ : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} → {δb : ℕ → ℝ} →
      {records : ∀ n (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount),
        T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ →
        GeometricCutoffRecord ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i (p n)} →
      (recordsF : ∀ n i, GeometricCutoffRecord ((K n).prefixAt (Fin.last (K
        n).eventCount)).toHistory i (pF n)) →
      {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier} →
      {a₀ : ℕ → ℝ} →
      (hHI : ∀ n x,
        InFixedHamiltonIveyRegion (((K n).prefixAt (Fin.last (K n).eventCount)).initialMetric 0) (a₀
          n) x ∧
        -3 / a₀ n ≤ metricScalarAt (((K n).prefixAt (Fin.last (K n).eventCount)).initialMetric 0) x)
          →
      (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow) →
      (hδF : ∀ n (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount),
        T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ →
        (pF n).delta (((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ) ≤ δb n) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscale : ∀ (n : ℕ) i hi b,
        ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale) →
      (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
        1 ≤ a₀ n * ((records n i hi).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount,
          Perelman.PhiAlmostNonnegative
            (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).incoming.flow
            (Ico (((K n).prefixAt (Fin.last (K n).eventCount)).time i.castSucc)
              (((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ) ∩ Ici (T₀ n)) phi) ∧
        Perelman.PhiAlmostNonnegative (G n).flow
          (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) phi) →
      (hslab : ∀ n, ((K n).prefixAt (Fin.last (K n).eventCount)).EventSlabsDerivative Ctime (qcan n)
        (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)) →
      (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime)
        (2 * qcan n) (t n)) →
      (hqR : ∀ n, qcan n < (G n).flow.scalar (t n) (yG n)) →
      (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
        (hi : T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ)
        (hl : i.succ ≤ Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
        (A : BackwardPointTrace ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i.succ
          (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount) hl (yG n))
        (b : (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
          t n - ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ ≤
            θcap n * (((records n i hi).static b).neck.scale)⁻¹) →
      (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
        t n - B / (G n).flow.scalar (t n) (yG n)) →
      (hRt : Tendsto (fun n => (G n).flow.scalar (t n) (yG n) *
        t n) atTop atTop) →
      (hanchor0 : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
        ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n))
            (yG n)
            (A / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
          (G n).flow.scalar (t n) z ≤
            Q * (G n).flow.scalar (t n) (yG n)) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n)) →
      {r₀ w : ℝ} → (hr₀ : 0 < r₀) → (hw : 0 < w) →
      (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Kh n).stageAt (σ n)).Carrier
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
              (r₀ / Real.sqrt (R n)))) →
      {κ : ℝ} → (hκ : 0 < κ) → (ρnc : ℕ → ℝ) →
      (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop) →
      (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'') →
      {C1s C2s Cs : ℝ} → {qs : ℕ → ℝ} → (hqs : ∀ n, qs n ≤ Cs * R n) →
      (hwitC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) ε C1s C2s
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε) →
      (hbcadC : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T Kc : ℝ, -σ' < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (Kc * R n)) →
        ∀ᶠ n in map φ atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₂),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ C * R n) →
      ∀ (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
        (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
        (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
        (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
          ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n)) (L : ℕ → ℝ),
      ObservedHistory.hscalW_final_P6M6 Kh Tn aSeed σ haT hsT has pT seedTrace y R L := by
  intro Ctime phi ε hε hεX hεN hphi K t htl htK G hG D θcap qcan T₀ p pF δb records recordsF yG a₀
    hHI hcan hδF hqcan hpar hscale hbirthA hθcap hpinch hslab hderG hqR hnot hT₀ hRt hanchor0 Kh hKh
    σ y R hσ hyG hRn r₀ w hr₀ hw hseed κ hκ ρnc hradii hkappa C1s C2s Cs qs hqs hwitC hbcadC Tn
    aSeed haT hsT has pT seedTrace L
  have hR : ∀ n, 0 < R n := fun n => by
    rw [hRn n]
    exact (lt_of_lt_of_le (by positivity) (hqcan n)).trans (hqR n)
  exact hscalW_final_eventually_of_subseqDriver_P6AN2 Kh Tn aSeed σ haT hsT has pT seedTrace y R L
    hR (fun φ hφ _ => hdepth_toHistory_finalSlab_P6AN2 hε hεX hεN hphi htl htK hG recordsF hHI hcan
      hδF hqcan hpar hscale hbirthA hθcap hpinch hslab hderG hqR hnot hT₀ hRt hanchor0 Kh hKh σ y R
      hσ hyG hRn hr₀ hw hseed hκ ρnc hradii hkappa hqs hwitC hbcadC φ hφ)

/-- **组合 final：G1 ∘ G2 ∘ G3（`_P6AN2`，PROVISIONAL：binder = `ShortSLT_C11KS β` +
`TopAnchorInputs_P6AN2 β`（final 构形）+ `hbcadC`）**：`hscalW_final_finalSlab_of_supplies_P6AN2` 的
`hanchor0` 由 `hanchor0_final_of_shortSLT_top_P6AN2` 供（先 `G := finalSlab …`）。
结论 = `hscalW_final_P6M6`。 -/
theorem hscalW_final_finalSlab_of_shortSLT_top_P6AN2 :
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      {ε : ℝ} → (hε : 0 < ε) → (hεX : ε ≤ crossingWindowNeckAccuracy.{u}) →
      (hεN : ε ≤ crossingNeckAccuracy.{u}) →
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {t : ℕ → ℝ} →
      (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) →
      (htK : ∀ n, t n < (K n).horizon) →
      {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
        ((K n).time (Fin.last (K n).eventCount)) (K n).horizon} →
      (hG : ∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
        ((htl n).trans (htK n)) le_rfl) →
      {D θcap qcan T₀ : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} → {δb : ℕ → ℝ} →
      {records : ∀ n (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount),
        T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ →
        GeometricCutoffRecord ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i (p n)} →
      (recordsF : ∀ n i, GeometricCutoffRecord ((K n).prefixAt (Fin.last (K
        n).eventCount)).toHistory i (pF n)) →
      {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier} →
      {a₀ : ℕ → ℝ} →
      (hHI : ∀ n x,
        InFixedHamiltonIveyRegion (((K n).prefixAt (Fin.last (K n).eventCount)).initialMetric 0) (a₀
          n) x ∧
        -3 / a₀ n ≤ metricScalarAt (((K n).prefixAt (Fin.last (K n).eventCount)).initialMetric 0) x)
          →
      (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow) →
      (hδF : ∀ n (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount),
        T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ →
        (pF n).delta (((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ) ≤ δb n) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscale : ∀ (n : ℕ) i hi b,
        ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale) →
      (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
        1 ≤ a₀ n * ((records n i hi).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount,
          Perelman.PhiAlmostNonnegative
            (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).incoming.flow
            (Ico (((K n).prefixAt (Fin.last (K n).eventCount)).time i.castSucc)
              (((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ) ∩ Ici (T₀ n)) phi) ∧
        Perelman.PhiAlmostNonnegative (G n).flow
          (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) phi) →
      (hslab : ∀ n, ((K n).prefixAt (Fin.last (K n).eventCount)).EventSlabsDerivative Ctime (qcan n)
        (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)) →
      (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime)
        (2 * qcan n) (t n)) →
      (hqR : ∀ n, qcan n < (G n).flow.scalar (t n) (yG n)) →
      (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
        (hi : T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ)
        (hl : i.succ ≤ Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
        (A : BackwardPointTrace ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i.succ
          (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount) hl (yG n))
        (b : (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
          t n - ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ ≤
            θcap n * (((records n i hi).static b).neck.scale)⁻¹) →
      (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
        t n - B / (G n).flow.scalar (t n) (yG n)) →
      (hRt : Tendsto (fun n => (G n).flow.scalar (t n) (yG n) *
        t n) atTop atTop) →
      {β : ℝ} → (hX : ShortSLT_C11KS.{u} β) →
      (hin : TopAnchorInputs_P6AN2 β (fun n => (K n).prefixAt (Fin.last (K n).eventCount))
        (fun n => (K n).prefixAt_time_last _) (fun n => (K n).horizon)
        (fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
          ((htl n).trans (htK n)) le_rfl)
        (fun n => (K n).final_initial ((htl n).trans (htK n))) t yG) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n)) →
      {r₀ w : ℝ} → (hr₀ : 0 < r₀) → (hw : 0 < w) →
      (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Kh n).stageAt (σ n)).Carrier
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
              (r₀ / Real.sqrt (R n)))) →
      {κ : ℝ} → (hκ : 0 < κ) → (ρnc : ℕ → ℝ) →
      (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop) →
      (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'') →
      {C1s C2s Cs : ℝ} → {qs : ℕ → ℝ} → (hqs : ∀ n, qs n ≤ Cs * R n) →
      (hwitC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) ε C1s C2s
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε) →
      (hbcadC : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T Kc : ℝ, -σ' < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (Kc * R n)) →
        ∀ᶠ n in map φ atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₂),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ C * R n) →
      ∀ (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
        (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
        (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
        (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
          ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n)) (L : ℕ → ℝ),
      ObservedHistory.hscalW_final_P6M6 Kh Tn aSeed σ haT hsT has pT seedTrace y R L := by
  intro Ctime phi ε hε hεX hεN hphi K t htl htK G hG D θcap qcan T₀ p pF δb records recordsF yG a₀
    hHI hcan hδF hqcan hpar hscale hbirthA hθcap hpinch hslab hderG hqR hnot hT₀ hRt β hX hin Kh hKh
    σ y R hσ hyG hRn r₀ w hr₀ hw hseed κ hκ ρnc hradii hkappa C1s C2s Cs qs hqs hwitC hbcadC
  obtain rfl : G = fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl := funext hG
  exact hscalW_final_finalSlab_of_supplies_P6AN2 hε hεX hεN hphi htl htK hG recordsF hHI hcan hδF
    hqcan hpar hscale hbirthA hθcap hpinch hslab hderG hqR hnot hT₀ hRt
    (hanchor0_final_of_shortSLT_top_P6AN2 hX htl htK hin) Kh hKh σ y R hσ hyG hRn hr₀ hw hseed hκ
    ρnc hradii hkappa hqs hwitC hbcadC

/-- **consumer（G1 event，`_P6AN2`）**：regular-top 子列 driver 经
`hscalW_eventually_of_subseqDriver_P6AN2` 喂 `hdistW_of_firstExit_P6DW` 的 `hscalW` 槽
（类型由 elaboration 核对）。 -/
example (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (r : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₀ + τ') x)
    (hσev : ∀ n, ∃ e : Fin (Kh n).eventCount, (Kh n).activeStage (σ n) = e.castSucc)
    (hdriver : ∀ φ : ℕ → ℕ, StrictMono φ →
      (∀ k, (Kh (φ k)).time ((Kh (φ k)).activeStage (σ (φ k))) < σ (φ k)) →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ T : ℝ, 0 < T → DepthExtendable Kh σ y R (φ ∘ ψ) T) :=
  ObservedHistory.hdistW_of_firstExit_P6DW Kh Tn aSeed σ haT hsT has pT seedTrace y R L hR r hL
    hsmall hclock hRr hwin ha₀ hpin hσev
    (hscalW_eventually_of_subseqDriver_P6AN2 Kh Tn aSeed σ haT hsT has pT seedTrace y R L hR
      hdriver)

/-- **consumer（G1 final，`_P6AN2`）**：final-slab regular-top 子列 driver 经
`hscalW_final_eventually_of_subseqDriver_P6AN2` 喂 `hdistW_of_firstExit_final_P6DW2` 的 `hscalW` 槽。 -/
example (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (r : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₀ + τ') x)
    (hσfin : ∀ n, (Kh n).activeStage (σ n) = Fin.last (Kh n).eventCount)
    (hσlt : ∀ n, (σ n : ℝ) < (Kh n).horizon)
    (hdriverF : ∀ φ : ℕ → ℕ, StrictMono φ →
      (∀ k, (Kh (φ k)).activeStage (σ (φ k)) = Fin.last (Kh (φ k)).eventCount ∧
        (Kh (φ k)).time (Fin.last (Kh (φ k)).eventCount) < σ (φ k)) →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ T : ℝ, 0 < T → DepthExtendable Kh σ y R (φ ∘ ψ) T) :=
  ObservedHistory.hdistW_of_firstExit_final_P6DW2 Kh Tn aSeed σ haT hsT has pT seedTrace y R L hR r
    hL hsmall hclock hRr hwin ha₀ hpin hσfin hσlt
    (hscalW_final_eventually_of_subseqDriver_P6AN2 Kh Tn aSeed σ haT hsT has pT seedTrace y R L hR
      hdriverF)

/-- **consumer（G2 final slab，`_P6AN2`）**：final 版 top adapter 的输出经 `hanchor0_of_extendAt_P6D2`
送到 final E 层（`(prefixAt last).extendAt (finalSlab …)` history）上 driver 的 `hanchor0` 形。 -/
example {β : ℝ} (hX : ShortSLT_C11KS.{u} β) {K : ℕ → RetainedCoreHistory.{u}} {t : ℕ → ℝ}
    (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) (htK : ∀ n, t n < (K n).horizon)
    {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier}
    (hin : TopAnchorInputs_P6AN2 β (fun n => (K n).prefixAt (Fin.last (K n).eventCount))
      (fun n => (K n).prefixAt_time_last _) (fun n => (K n).horizon)
      (fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
        ((htl n).trans (htK n)) le_rfl)
      (fun n => (K n).final_initial ((htl n).trans (htK n))) t yG)
    (Hs : ℕ → ObservedHistory.{u}) (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier) (R : ℕ → ℝ)
    (hHs : Hs = fun n => (((K n).prefixAt (Fin.last (K n).eventCount)).extendAt
      ((K n).prefixAt_time_last _) (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming
        le_rfl ((htl n).trans (htK n)) le_rfl) ((K n).final_initial ((htl n).trans (htK n)))
      (htl n) (htK n)).toHistory)
    (hts' : HEq ts (fun n => ((K n).prefixAt (Fin.last (K n).eventCount)).extendAtTime
      ((K n).prefixAt_time_last _) (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming
        le_rfl ((htl n).trans (htK n)) le_rfl) ((K n).final_initial ((htl n).trans (htK n)))
      (htl n) (htK n)))
    (hys : ∀ n, HEq (ys n) (yG n))
    (hRn : ∀ n, R n = (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl).flow.scalar (t n) (yG n)) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (A / Real.sqrt (R n)),
        metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) z ≤ Q * R n :=
  hanchor0_of_extendAt_P6D2 (H := fun n => (K n).prefixAt (Fin.last (K n).eventCount))
    (G := fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl) (s := fun n => (K n).horizon) (y := yG)
    (fun n => (K n).prefixAt_time_last _) (fun n => (K n).final_initial ((htl n).trans (htK n)))
    htl htK (hanchor0_final_of_shortSLT_top_P6AN2 hX htl htK hin) Hs ts ys R hHs hts' hys hRn

/-- **consumer（G3，`_P6AN2`）**：R-AN-3 的遗传子列形正是 round 1 `hscalW_of_depthExtendable_P6AN` 的
`hdepth` 形（`toHistory` 上，不再需要 extendAt ↔ toHistory 的额外接线）。 -/
example :
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      {ε : ℝ} → (hε : 0 < ε) → (hεX : ε ≤ crossingWindowNeckAccuracy.{u}) →
      (hεN : ε ≤ crossingNeckAccuracy.{u}) →
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {j : ∀ n, Fin (K n).eventCount} → {t : ℕ → ℝ} →
      (hjt : ∀ n, (K n).time (j n).castSucc < t n) → (htj : ∀ n, t n < (K n).time (j n).succ) →
      {D θcap qcan T₀ : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} → {δb : ℕ → ℝ} →
      {records : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
        T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
        GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (p n)} →
      (recordsF : ∀ n i, GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (pF n)) →
      {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier} →
      {a₀ : ℝ} → (ha₀ : 0 < a₀) →
      (hHI : ∀ n x,
        InFixedHamiltonIveyRegion (((K n).prefixAt (j n).castSucc).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt (((K n).prefixAt (j n).castSucc).initialMetric 0) x) →
      (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow) →
      (hδF : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
        T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
        (pF n).delta (((K n).prefixAt (j n).castSucc).time i.succ) ≤ δb n) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscale : ∀ (n : ℕ) i hi b,
        ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinch : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsPinched phi ∧
        Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
          (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ)) phi) →
      (hslab : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsDerivative Ctime (qcan n)
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount)) →
      (hderG : ∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore (2 * Ctime)
        (2 * qcan n) (t n)) →
      (hqR : ∀ n, qcan n < ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
        (hi : T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
        (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
        (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
          (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
        (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
          t n - ((K n).prefixAt (j n).castSucc).time i.succ ≤
            θcap n * (((records n i hi).static b).neck.scale)⁻¹) →
      (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
        t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hRt : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) *
        t n) atTop atTop) →
      (hanchor0 : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
        ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
            (yG n)
            (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
          ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
            Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      {r₀ w : ℝ} → (hr₀ : 0 < r₀) → (hw : 0 < w) →
      (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Kh n).stageAt (σ n)).Carrier
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
              (r₀ / Real.sqrt (R n)))) →
      {κ : ℝ} → (hκ : 0 < κ) → (ρnc : ℕ → ℝ) →
      (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop) →
      (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'') →
      {C1s C2s Cs : ℝ} → {qs : ℕ → ℝ} → (hqs : ∀ n, qs n ≤ Cs * R n) →
      (hwitC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) ε C1s C2s
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε) →
      (hbcadC : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T Kc : ℝ, -σ' < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (Kc * R n)) →
        ∀ᶠ n in map φ atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₂),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ C * R n) →
      ∀ (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
        (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
        (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
        (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
          ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n)) (L : ℕ → ℝ),
      ∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ s : ℝ, (σ n : ℝ) - T / R n < s → s < σ n → (Kh n).time ((Kh n).activeStage (σ n)) < s →
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s)
            ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
              ((Kh n).activeStage_mono (hsT n))) x ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        ∀ z : ((Kh n).stageAt (σ n)).Carrier,
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) x z <
              ENNReal.ofReal (1 / Real.sqrt (C * R n)) →
            metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) z ≤ C * R n := by
  intro Ctime phi ε hε hεX hεN hphi K j t hjt htj D θcap qcan T₀ p pF δb records recordsF yG a₀ ha₀
    hHI hcan hδF hqcan hpar hscale hθcap hpinch hslab hderG hqR hnot hT₀ hRt hanchor0 Kh hKh σ y R
    hσ hyG hRn r₀ w hr₀ hw hseed κ hκ ρnc hradii hkappa C1s C2s Cs qs hqs hwitC hbcadC Tn aSeed haT
    hsT has pT seedTrace L
  have hR : ∀ n, 0 < R n := fun n => by
    rw [hRn n]
    exact (lt_of_lt_of_le (by positivity) (hqcan n)).trans (hqR n)
  exact hscalW_of_depthExtendable_P6AN Kh Tn aSeed σ haT hsT has pT seedTrace y R L hR
    (hdepth_toHistory_eventSlab_P6AN2 hε hεX hεN hphi hjt htj recordsF ha₀ hHI hcan hδF hqcan hpar
      hscale hθcap hpinch hslab hderG hqR hnot hT₀ hRt hanchor0 Kh hKh σ y R hσ hyG hRn hr₀ hw hseed
      hκ ρnc hradii hkappa hqs hwitC hbcadC)

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AnchorThirdP6AN3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceHistoryBridgeFinalP6M

/-!
# ANCHOR 第四轮 G2：final 支 top `hlocal` producer（O-CH11-ANCHOR4，后缀 `_P6AN4`）

ANCHOR3 HANDOVER 第 8 项：C11PB picked-ball 合同只有 event 形（flow = `(K.event j).incoming`），final 构形
（`H n = (K n).prefixAt last`、`G n = ((K n).finalSlab h).restrictIncoming le_rfl h le_rfl`、
`s n = horizon`、top `t n ∈ (time last, horizon)`）的 `TopAnchorInputs_P6AN2`
（`hscalW_finalSlab_to_hdistW_P6AN3` 的 `hin`）仍是 binder。
* **合同 `PickedBallShortWindow_final_P6AN4`（PROVISIONAL，lead 简报登记）**：C11PB 合同的 final 形，σ 在 final
  slab：flow 换成 `(K.finalSlab h).restrictIncoming`，窗口 `(time last, v)`；三个字段 = witness（top 时刻 `v`）/
  梯度（窗口）/ κ（K 层 tested 形，`τ ∈ [v − β/q, v] ∩ (time last, horizon)`）。**不含** hpick（`PickedBallTop`）：
  它不进 `hlocal` / ShortSLT 输入面，且 top 点用它循环（ANCHOR3 G3 发现）。
* `hlocal_final_of_pickedBall_top_P6AN4`（PROVED ⇐ 显式输入）：`topAnchorInputs_of_local_P6AN2` 的 residual
  `hlocal` **逐字**（对构形 `(H, s, G, y)` 通用；final 实例见下）。输入 = witness / 梯度（`G` 形，阈值 `qthr`）、
  κ（extendHorizon 形，`U := B_t(y, Rad/√R)`）、导数（`hslab` 前缀 + `hderG` on `G`，合用 `2·Ctime`）、pinching
  （`∩ Ici (t − β/R)` 形，eventually）、`hradii`。
* `topAnchorInputs_final_of_pickedBall_P6AN4`（PROVISIONAL：binder = 合同 `hpb`）：FINCOND 层 supplies（与
  `hscalW_finalSlab_to_hdistW_P6AN3` 同名同形：`records / hcan / hqcan / hpar / hscale / hθcap /
  hpinch(∩ Ici T₀) / hslab / hderG / hqR / hnot / hT₀ / hRt`）+ `hpb` ⇒ final 构形
  `TopAnchorInputs_P6AN2 β`。κ 经树内
  `tested_noncollapse_final_P6M`（K 层 → extendHorizon 层），pinching 由 `T₀ ≤ t − β/R`（`hT₀ β`）缩窗。
* 全链 `hdistW_finalSlab_of_pickedBall_P6AN4`（PROVISIONAL）：`hscalW_finalSlab_to_hdistW_P6AN3` 的 `hin`
  换成 `hpb`（+ 合同常数），喂 ANCHOR2 final 孪生 `hscalW_final_finalSlab_of_topInputs_P6AN2` →
  `hdistW_of_firstExit_final_P6DW2`；结论 = `hdistW` 槽逐字（final 支）。
各字段来源（同 event 支）：witness ⇐ hgood（σ = t 在 final slab，`activeStage = last`）；κ ⇐ final `hkappa`
（同 stage 平凡 trace，照 ANCHOR3 G4）；梯度 ⇐ hgood + hseedTop（同 G1，BLOCKED 同因）。本文件只做合同 → `hlocal` 接线。
非循环：前提中无 `hdistW` 槽 / `HU` / `hgapJ` / `hclosG` / `CanonicalLateCore` / `hspine` /
`GradientBoundBefore`。
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

section FinalContract

/-- **合同 `PickedBallShortWindow_final_P6AN4`（`_P6AN4`，PROVISIONAL；lead 简报登记）**：C11PB
`PickedBallShortWindow_C11PB` 的 final 形（σ 在 final slab）。记
`G := (K.finalSlab h).restrictIncoming le_rfl h le_rfl`、`q := R_G(v, w)`、
球 `B_v(w, Rad/√q)`（`G` 的度量）。
三个字段：
(1) witness：球上 `R(v, ·) > qthr` 处 spatial canonical witness（neck chart）；
(2) 梯度：窗口 `v′ ∈ (time last, v)`、`v − β/q ≤ v′`、`R(v′, x) > qthr` 处 `|∇R| ≤ Cgrad R^{3/2}`；
(3) κ：`τ ∈ [v − β/q, v] ∩ (time last, horizon)`、球中心点、半径 `≤ ρ` 的 parabolically controlled ball
κ-noncollapsed（K 层 tested 形 = `tested_noncollapse_final_P6M` 的 `hK`）。
不含 hpick（不进 `hlocal` 输入面；top 点循环）。 -/
def PickedBallShortWindow_final_P6AN4 (β Rad qthr ρ κ ε C1 C2 : ℝ) (Cgrad : ℝ≥0)
    (K : RetainedCoreHistory.{u}) (h : K.time (Fin.last K.eventCount) < K.horizon) (v : ℝ)
    (w : (K.stage (Fin.last K.eventCount)).Carrier) : Prop :=
  (∀ x ∈ riemannianBallOf (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric v) w
      (Rad / Real.sqrt (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v w)),
    qthr < ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v x →
    ∃ W : SpatialCanonicalWitness
        (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric v) ε C1 C2 x,
      W.capTubeHasNeckChart ε) ∧
  (∀ x ∈ riemannianBallOf (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric v) w
      (Rad / Real.sqrt (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v w)),
    ∀ v' ∈ Ioo (K.time (Fin.last K.eventCount)) v,
    v - β / ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v w ≤ v' →
    qthr < ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v' x →
    ∀ ξ : TangentSpace ThreeModel x,
      |scalarDifferential ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow v' x ξ| ≤
        Cgrad * ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v' x *
          Real.sqrt (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v' x) *
          Real.sqrt
            ((((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric v').inner x
              ξ ξ)) ∧
  (∀ (τ : Icc (0 : ℝ) K.toHistory.horizon),
    v - β / ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v w ≤ (τ : ℝ) →
    (τ : ℝ) ≤ v → K.time (Fin.last K.eventCount) < τ → (τ : ℝ) < K.horizon →
    ∀ z ∈ riemannianBallOf (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric v) w
        (Rad / Real.sqrt (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v w)),
    ∀ zz : (K.toHistory.stageAt τ).Carrier, HEq zz z →
    ∀ b : ℝ, 0 < b → b ≤ ρ → K.toHistory.isParabolicallyRmControlledBall τ zz b →
      ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
        riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt τ).Carrier
          (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
          (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) zz b))

/-- **inhabitant（`_P6AN4`）**：`Rad = 0` 时三个字段都在空球上，平凡成立（定义一致性检查）。 -/
theorem pickedBallShortWindow_final_zero_P6AN4 (β qthr ρ κ ε C1 C2 : ℝ) (Cgrad : ℝ≥0)
    (K : RetainedCoreHistory.{u}) (h : K.time (Fin.last K.eventCount) < K.horizon) (v : ℝ)
    (w : (K.stage (Fin.last K.eventCount)).Carrier) :
    PickedBallShortWindow_final_P6AN4 β 0 qthr ρ κ ε C1 C2 Cgrad K h v w := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun τ _ _ _ _ z hz => ?_⟩
  · simp [riemannianBallOf] at hx
  · simp [riemannianBallOf] at hx
  · simp [riemannianBallOf] at hz

end FinalContract

section FinalLocal

/-- **`hlocal_final_of_pickedBall_top_P6AN4`（G2，PROVED ⇐ 显式输入）**：`topAnchorInputs_of_local_P6AN2` 的
residual `hlocal` **逐字**，对构形 `(H, s, G, y)` 通用（final 实例 `topAnchorInputs_final_of_pickedBall_P6AN4`
取 `H n = prefixAt last`、`G n = finalSlab.restrictIncoming`、`s n = horizon`）。逐分量：
`U := B_t(y, Rad/√R)`、`q := max (qthr n) (2 qcan n)`、`ρ := ρnc n`、`Ctime′ := 2 Ctime`、
`Cq′ := max Cq 2`；
witness / 梯度 ⇐ `hwg`（阈值 `qthr ≤ q` 单调）；前缀 event slab 导数 ⇐ `hslab`（`qcan ≤ q`，系数加倍）；
incoming 导数 ⇐ `hderG`（`2 qcan ≤ q`）；pinching ⇐ `hpin`；κ ⇐ `hkap`（`U` = 球）；`Λ ≤ ρ √R` ⇐ `hradii`。 -/
theorem hlocal_final_of_pickedBall_top_P6AN4 {β : ℝ} {s t : ℕ → ℝ}
    {H : ℕ → RetainedCoreHistory.{u}}
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon)
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    {ε : ℝ} (hε : ε ≤ coneAccuracy) {κ C1 C2 Cq : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {qcan qthr ρnc : ℕ → ℝ}
    (hqcan0 : ∀ n, 0 ≤ qcan n)
    (hslab : ∀ n, (H n).EventSlabsDerivative Ctime (qcan n) (Fin.last (H n).eventCount))
    (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime) (2 * qcan n) (t n))
    (hqR : ∀ n, qcan n < (G n).flow.scalar (t n) (y n))
    (hpin : ∀ᶠ n in atTop,
      (∀ j : Fin (H n).eventCount,
        Perelman.PhiAlmostNonnegative ((H n).toHistory.event j).incoming.flow
          (Ico ((H n).time j.castSucc) ((H n).time j.succ) ∩
            Ici (t n - β / (G n).flow.scalar (t n) (y n))) phi) ∧
      Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((H n).time (Fin.last (H n).eventCount)) (s n) ∩
          Ici (t n - β / (G n).flow.scalar (t n) (y n))) phi)
    (hqthr : ∀ n, 0 < qthr n ∧ qthr n ≤ Cq * (G n).flow.scalar (t n) (y n))
    (hradii : Tendsto (fun n => ρnc n * Real.sqrt ((G n).flow.scalar (t n) (y n))) atTop atTop)
    (hwg : ∀ Rad : ℝ, ∀ᶠ n in atTop,
      (∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
          (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        qthr n < (G n).flow.scalar (t n) x →
        ∃ W : SpatialCanonicalWitness ((G n).flow.base.metric (t n)) ε C1 C2 x,
          W.capTubeHasNeckChart ε) ∧
      (∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
          (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
        t n - β / (G n).flow.scalar (t n) (y n) ≤ v →
        qthr n < (G n).flow.scalar v x →
        ∀ w : TangentSpace ThreeModel x,
          |scalarDifferential (G n).flow v x w| ≤
            Cgrad * (G n).flow.scalar v x * Real.sqrt ((G n).flow.scalar v x) *
              Real.sqrt (((G n).flow.base.metric v).inner x w w)))
    (hkap : ∀ Rad : ℝ, ∀ᶠ n in atTop,
      ∀ (T : ℝ) (hT : (H n).time (Fin.last (H n).eventCount) < T) (hTs : T < s n), T ≤ t n →
        t n - β / (G n).flow.scalar (t n) (y n) ≤ T →
        let B := (H n).extendHorizon T ((hend n) ▸ hT.le) ((G n).closedPrefix T hT hTs) (hGi n)
        let tm : Icc (0 : ℝ) B.horizon :=
          ⟨T, (H n).horizon_nonneg.trans ((hend n) ▸ hT.le), le_rfl⟩
        ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
            (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        ∀ (yy : (B.toHistory.stageAt tm).Carrier), HEq yy z →
        ∀ (b : ℝ), 0 < b → b ≤ ρnc n →
          B.toHistory.isParabolicallyRmControlledBall tm yy b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
                (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                  yy b)) :
    ∃ ε : ℝ, ε ≤ coneAccuracy ∧ ∃ κ C1 C2 : ℝ, 0 < κ ∧
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
        Λ ≤ ρ * Real.sqrt ((G n).flow.scalar (t n) (y n)) := by
  refine ⟨ε, hε, κ, C1, C2, hκ, 2 * Ctime, Cgrad, phi, hphi, max Cq 2, fun Λ Rad _ => ?_⟩
  filter_upwards [hwg Rad, hkap Rad, hpin, hradii.eventually_ge_atTop Λ] with n hwgn hkn hpn hρn
  obtain ⟨hwit, hgrad⟩ := hwgn
  have hR0 : 0 ≤ (G n).flow.scalar (t n) (y n) := (hqcan0 n).trans (hqR n).le
  have hq2 : qcan n ≤ max (qthr n) (2 * qcan n) :=
    le_trans (by linarith [hqcan0 n]) (le_max_right _ _)
  have hqC : max (qthr n) (2 * qcan n) ≤ max Cq 2 * (G n).flow.scalar (t n) (y n) :=
    max_le ((hqthr n).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hR0))
      ((mul_le_mul_of_nonneg_left (hqR n).le (by norm_num : (0 : ℝ) ≤ 2)).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hR0))
  exact ⟨max (qthr n) (2 * qcan n), ρnc n, lt_max_of_lt_left (hqthr n).1, hqC,
    riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
      (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
    fun w hw => hw, fun x hx hqx => hwit x hx ((le_max_left _ _).trans_lt hqx),
    fun i first hf z _ B v hv _ hRv => le_two_mul_coe_mul_sq_P6AN3
      (hslab n i (Fin.castSucc_lt_last i) _ v hv (hq2.trans_lt hRv)),
    fun x _ v hv _ hRv => hderG n x v hv ((le_max_right _ _).trans_lt hRv),
    fun x hx v hv hvw hRv ξ => hgrad x hx v hv hvw ((le_max_left _ _).trans_lt hRv) ξ,
    hpn.1, hpn.2, hkn, hρn⟩

end FinalLocal

section FinalTop

/-- **`topAnchorInputs_final_of_pickedBall_P6AN4`（G2 组合，PROVISIONAL：binder = final 合同 `hpb`；
导数 supplies `hslab / hderG` 为旧全域背景，J10GEN 迁移义务）**：FINCOND 层 supplies
（与 `hscalW_finalSlab_to_hdistW_P6AN3`
同名同形）+ `hpb`（`v := t n`、`w := yG n`、阈值 `qthr`）⇒ final 构形 `TopAnchorInputs_P6AN2 β`（= 该链的 `hin`
逐字）。= `topAnchorInputs_of_local_P6AN2`（schedule 部分经 `selectionSchedule_P6AN2`）∘
`hlocal_final_of_pickedBall_top_P6AN4`；κ 经 `tested_noncollapse_final_P6M`
（窗口 `a := t − β/R`、`U` = 球），
pinching 由 `hT₀ β`（`T₀ ≤ t − β/R`）把 `∩ Ici T₀` 缩到 `∩ Ici (t − β/R)`。 -/
theorem topAnchorInputs_final_of_pickedBall_P6AN4 {β : ℝ} (hβ : β ≤ 1 / 2)
    {K : ℕ → RetainedCoreHistory.{u}} {t : ℕ → ℝ}
    (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) (htK : ∀ n, t n < (K n).horizon)
    {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon}
    (hG : ∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl)
    {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier}
    {D θcap qcan T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters} {δb : ℕ → ℝ}
    {records : ∀ n (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount),
      T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ →
      GeometricCutoffRecord ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i (p n)}
    (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow)
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n)
    (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hscale : ∀ (n : ℕ) i hi b,
      ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale)
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    {Ctime : ℝ≥0} {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    (hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount,
        Perelman.PhiAlmostNonnegative
          (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).incoming.flow
          (Ico (((K n).prefixAt (Fin.last (K n).eventCount)).time i.castSucc)
            (((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ) ∩ Ici (T₀ n)) phi) ∧
      Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) phi)
    (hslab : ∀ n, ((K n).prefixAt (Fin.last (K n).eventCount)).EventSlabsDerivative Ctime (qcan n)
      (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount))
    (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime) (2 * qcan n) (t n))
    (hqR : ∀ n, qcan n < (G n).flow.scalar (t n) (yG n))
    (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
      (hi : T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ)
      (hl : i.succ ≤ Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
      (A : BackwardPointTrace ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i.succ
        (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount) hl (yG n))
      (b : (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
        t n - ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ ≤
          θcap n * (((records n i hi).static b).neck.scale)⁻¹)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ t n - B / (G n).flow.scalar (t n) (yG n))
    (hRt : Tendsto (fun n => (G n).flow.scalar (t n) (yG n) * t n) atTop atTop)
    {ε : ℝ} (hε : ε ≤ coneAccuracy) {κ C1 C2 Cq : ℝ} (hκ : 0 < κ) {Cgrad : ℝ≥0}
    {qthr ρnc : ℕ → ℝ}
    (hqthr : ∀ n, 0 < qthr n ∧ qthr n ≤ Cq * (G n).flow.scalar (t n) (yG n))
    (hradii : Tendsto (fun n => ρnc n * Real.sqrt ((G n).flow.scalar (t n) (yG n))) atTop atTop)
    (hpb : ∀ Rad : ℝ, ∀ᶠ n in atTop,
      PickedBallShortWindow_final_P6AN4 β Rad (qthr n) (ρnc n) κ ε C1 C2 Cgrad (K n)
        ((htl n).trans (htK n)) (t n) (yG n)) :
    TopAnchorInputs_P6AN2 β (fun n => (K n).prefixAt (Fin.last (K n).eventCount))
      (fun n => (K n).prefixAt_time_last _) (fun n => (K n).horizon)
      (fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
        ((htl n).trans (htK n)) le_rfl)
      (fun n => (K n).final_initial ((htl n).trans (htK n))) t yG := by
  obtain rfl : G = fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl := funext hG
  have hqcan0 : ∀ n, 0 ≤ qcan n := fun n => by
    linarith [hqcan n, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  obtain ⟨hRlim, hDlim, hDrad, hord, hacc, hθ, -⟩ := selectionSchedule_P6AN2 hβ hqcan hqR hpar hθcap
  have hscale0 : ∀ n i hi b, 0 < ((records n i hi).static b).neck.scale := fun n i hi b =>
    lt_of_lt_of_le (mul_pos (by positivity) (lt_of_lt_of_le (by positivity) (hqcan n)))
      (hscale n i hi b)
  have hpin : ∀ᶠ n in atTop,
      (∀ i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount,
        Perelman.PhiAlmostNonnegative
          (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).incoming.flow
          (Ico (((K n).prefixAt (Fin.last (K n).eventCount)).time i.castSucc)
              (((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ) ∩
            Ici (t n - β / (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
              ((htl n).trans (htK n)) le_rfl).flow.scalar (t n) (yG n))) phi) ∧
      Perelman.PhiAlmostNonnegative (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming
          le_rfl ((htl n).trans (htK n)) le_rfl).flow
        (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩
          Ici (t n - β / (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
            ((htl n).trans (htK n)) le_rfl).flow.scalar (t n) (yG n))) phi := by
    filter_upwards [hT₀ β] with n hT
    exact ⟨fun i v hv => (hpinch n).1 i v ⟨hv.1, hT.trans hv.2⟩,
      fun v hv => (hpinch n).2 v ⟨hv.1, hT.trans hv.2⟩⟩
  refine topAnchorInputs_of_local_P6AN2
    (H := fun n => (K n).prefixAt (Fin.last (K n).eventCount))
    (G := fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl) (s := fun n => (K n).horizon) (y := yG)
    (fun n => (K n).prefixAt_time_last _) (fun n => (K n).final_initial ((htl n).trans (htK n)))
    records hcan hscale0 hRlim hRt (hT₀ β) hDlim hDrad hord hacc hθ hnot ?_
  refine hlocal_final_of_pickedBall_top_P6AN4 (fun n => (K n).prefixAt_time_last _)
    (fun n => (K n).final_initial ((htl n).trans (htK n))) hε hκ hphi hqcan0 hslab hderG hqR hpin
    hqthr hradii (fun Rad => (hpb Rad).mono fun n h => ⟨h.1, h.2.1⟩)
    (fun Rad => (hpb Rad).mono fun n h => ?_)
  exact (K n).tested_noncollapse_final_P6M ((htl n).trans (htK n))
    (a := t n - β / (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl).flow.scalar (t n) (yG n)) (t := t n) _ h.2.2
    ((K n).prefixAt_time_last _)

end FinalTop

section FinalChain

/-- **`hdistW_finalSlab_of_pickedBall_P6AN4`（G2 全链 final 支，PROVISIONAL：binder = final 合同 `hpb`
（+ 合同常数 `εp κp C1p C2p Cqp Cgradp qthr ρp`）+ `hbcadC` + FINCOND 层 supplies + K0 / HI 数据；
导数 `hslab / hderG` 是旧全域背景，J10GEN 迁移义务）**：= `hscalW_finalSlab_to_hdistW_P6AN3`，其 `hin`
（final 构形 `TopAnchorInputs_P6AN2 β`）由 `topAnchorInputs_final_of_pickedBall_P6AN4` 从 `hpb` 供
（同一组 FINCOND supplies：`hcan / hqcan / hpar / hscale / hθcap / hpinch / hslab / hderG / hqR / hnot /
hT₀ / hRt`）；之后经 ANCHOR2 final 孪生 `hscalW_final_finalSlab_of_topInputs_P6AN2` 与
`hdistW_of_firstExit_final_P6DW2`。结论 = `hdistW` 槽逐字（final 支）。 -/
theorem hdistW_finalSlab_of_pickedBall_P6AN4 :
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
      {β : ℝ} → (hβ : 0 < β) →
      (hβ2 : β ≤ 1 / 2) →
      {εp : ℝ} → (hεp : εp ≤ coneAccuracy) → {κp C1p C2p Cqp : ℝ} → (hκp : 0 < κp) →
      {Cgradp : ℝ≥0} → {qthr ρp : ℕ → ℝ} →
      (hqthr : ∀ n, 0 < qthr n ∧ qthr n ≤ Cqp * (G n).flow.scalar (t n) (yG n)) →
      (hradp : Tendsto (fun n => ρp n * Real.sqrt ((G n).flow.scalar (t n) (yG n))) atTop
        atTop) →
      (hpb : ∀ Rad : ℝ, ∀ᶠ n in atTop,
        PickedBallShortWindow_final_P6AN4 β Rad (qthr n) (ρp n) κp εp C1p C2p Cgradp (K n)
          ((htl n).trans (htK n)) (t n) (yG n)) →
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
          ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
      (L : ℕ → ℝ) (r : ℕ → ℝ),
      Tendsto L atTop atTop →
      (∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n)) →
      (∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2) →
      Tendsto (fun n => R n * r n ^ 2) atTop atTop →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) →
      ∀ {a₁ : ℝ}, 0 ≤ a₁ →
      (∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
        InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₁ + τ') x) →
      ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (Kh n).activeStage v = (Kh n).activeStage (σ n) →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) := by
  intro Ctime phi ε hε hεX hεN hphi K t htl htK G hG D θcap qcan T₀ p pF δb records recordsF yG a₀
    hHI hcan hδF hqcan hpar hscale hbirthA hθcap hpinch hslab hderG hqR hnot hT₀ hRt β hβ hβ2 εp
    hεp κp C1p C2p Cqp hκp Cgradp qthr ρp hqthr hradp hpb Kh hKh σ y R hσ hyG hRn r₀ w hr₀ hw
    hseed κ hκ ρnc hradii hkappa C1s C2s Cs qs hqs hwitC hbcadC Tn aSeed haT hsT has pT seedTrace
    L r hL hsmall hclock hRr hwin a₁ ha₁ hpin
  have hin := topAnchorInputs_final_of_pickedBall_P6AN4 hβ2 htl htK hG hcan hqcan hpar hscale
    hθcap hphi hpinch hslab hderG hqR hnot hT₀ hRt hεp hκp hqthr hradp hpb
  exact hscalW_finalSlab_to_hdistW_P6AN3 hε hεX hεN hphi htl htK hG recordsF hHI hcan hδF hqcan
    hpar hscale hbirthA hθcap hpinch hslab hderG hqR hnot hT₀ hRt hβ hin Kh hKh σ y R hσ hyG hRn
    hr₀ hw hseed hκ ρnc hradii hkappa hqs hwitC hbcadC Tn aSeed haT hsT has pT seedTrace L r hL
    hsmall hclock hRr hwin ha₁ hpin

/-- consumer（G2，`_P6AN4`）：final 合同在 `Rad = 0` 处由 inhabitant 付——`hpb` 的形与
`pickedBallShortWindow_final_zero_P6AN4` 同型（只作定义一致性；实际 `hpb` 需对所有 `Rad`）。 -/
example (β qthr ρ κ ε C1 C2 : ℝ) (Cgrad : ℝ≥0) (K : RetainedCoreHistory.{u})
    (h : K.time (Fin.last K.eventCount) < K.horizon) (v : ℝ)
    (w : (K.stage (Fin.last K.eventCount)).Carrier) :
    PickedBallShortWindow_final_P6AN4 β 0 qthr ρ κ ε C1 C2 Cgrad K h v w :=
  pickedBallShortWindow_final_zero_P6AN4 β qthr ρ κ ε C1 C2 Cgrad K h v w

end FinalChain

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

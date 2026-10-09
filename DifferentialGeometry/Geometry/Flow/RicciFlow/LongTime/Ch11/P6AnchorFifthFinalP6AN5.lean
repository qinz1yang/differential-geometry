import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AnchorFifthP6AN5
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AnchorFourthFinalHgoodP6AN4

/-!
# ANCHOR 第五轮 G1b：final 支去 `hqR`（O-CH11-ANCHOR5，后缀 `_P6AN5`）

`P6AnchorFifthP6AN5.lean`（event 支）的 final 孪生，口径相同（J10GEN / J10CORE：阈值 `q_sel = Cg·R`，
`hslab / hderG` 只作 cap-side B5 输入）。**不声称已去 J10**：prefix 导数的 `hslabSel` 是 J10 残余（阈值换皮），
见 event 文件头 (A′)：诚实修复 = SLT 核 `RetainedCoreHistory.eventually_scalar_bound_at_distance_window_P6M`
  的孪生（导数槽只在坏点尺度 `1/R(z)` 的 trace 上要），repair target，owner 与 J10GEN3 共用：
* `hlocal_final_noJ10_P6AN5`：ANCHOR4 `hlocal_final_of_pickedBall_top_P6AN4`（对构形 `(H, s, G, y)`
  通用，AN4Final:230–235
  用 `hqR` 证 `hR0` 与 `max qthr (2·qcan) ≤ max Cq 2 · R`）的孪生——`q := qthr n`，导数两子句 = q_sel 局域 binder
  `hderE / hderT`，结论逐字；
* final 时间导数 ⇐ hgood 时间分量 + hseedTop（`hderT_final_of_hgood_witness_P6AN5` / `_seq_`，PROVED；stage 桥
  `activeStage_eq_last_of_time_last_le` + `stageMetric_last_of_lt`）；prefix 导数 ⇐ `hslabSel`（J10
  残余（阈值换皮））
  （`hderE_of_slabSel_gen_P6AN5`，对构形通用）；
* 组合 `topAnchorInputs_final_of_pickedBall_noJ10_P6AN5`（AN4Final:259 孪生）、
  `topAnchorInputs_final_of_hgood_noJ10_P6AN5`（AN4FinalHgood:346 孪生）；final 全链 (c1)
  `hdistW_finalSlab_of_hgood_local_noJ10_P6AN5`（AN4FinalHgood:465 孪生；depth 半 = 显式 binder `hdepthAF`，
  repair = J10GEN2A 无 J10 late_cond driver 的 final 版；旧 `hdepth_toHistory_finalSlab_P6AN2`（带
  `hqR`）可填，见审计）。
非循环：前提中无 `hdistW` 槽 / `HU` / `hgapJ` / `hclosG` / `CanonicalLateCore` / `hspine` /
`GradientBoundBefore`，也无 `qcan < R` 形比较。hseedTop 仍 BLOCKED（owner KSWEXIT）。
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

section FinalLocal

/-- **`hlocal_final_noJ10_P6AN5`（G1b，PROVED ⇐ 显式输入；无 `hqR`）**：ANCHOR4
`hlocal_final_of_pickedBall_top_P6AN4` 的结论**逐字**（构形 `(H, s, G, y)` 通用）。`q := qthr n`（q_sel，
`hqthr` 直接给 `0 < q ≤ Cq·R`）、`Ctime′ := Ctime`、`Cq′ := Cq`；导数两子句 ⇐ q_sel 局域 binder `hderE / hderT`；
witness / 梯度 ⇐ `hwg`，κ ⇐ `hkap`，pinching ⇐ `hpin`，`Λ ≤ ρ√R` ⇐ `hradii`。不取 `max qthr (2·qcan)`，不比较
`qcan` 与 `R`。 -/
theorem hlocal_final_noJ10_P6AN5 {β : ℝ} {s t : ℕ → ℝ}
    {H : ℕ → RetainedCoreHistory.{u}}
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon)
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    {ε : ℝ} (hε : ε ≤ coneAccuracy) {κ C1 C2 Cq : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {qthr ρnc : ℕ → ℝ}
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
                  yy b))
    (hderE : ∀ Rad : ℝ, ∀ᶠ n in atTop,
      ∀ j : Fin (H n).eventCount,
        ∀ (first : Fin ((H n).eventCount + 1)) (hf : first ≤ j.castSucc),
        ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
            (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        ∀ B : BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
          (Fin.le_last first) z,
        ∀ v ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
        t n - β / (G n).flow.scalar (t n) (y n) ≤ v →
        qthr n < ((H n).toHistory.event j).incoming.flow.scalar v
          (B.point j.castSucc hf (Fin.le_last _)) →
        |derivWithin (fun w => ((H n).toHistory.event j).incoming.flow.scalar w
          (B.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
          Ctime * ((H n).toHistory.event j).incoming.flow.scalar v
            (B.point j.castSucc hf (Fin.le_last _)) ^ 2)
    (hderT : ∀ Rad : ℝ, ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
          (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
        t n - β / (G n).flow.scalar (t n) (y n) ≤ v →
        qthr n < (G n).flow.scalar v x →
        |derivWithin (fun w => (G n).flow.scalar w x) (Iic v) v| ≤
          Ctime * (G n).flow.scalar v x ^ 2) :
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
  refine ⟨ε, hε, κ, C1, C2, hκ, Ctime, Cgrad, phi, hphi, Cq, fun Λ Rad _ => ?_⟩
  filter_upwards [hwg Rad, hkap Rad, hpin, hradii.eventually_ge_atTop Λ, hderE Rad, hderT Rad]
    with n hwgn hkn hpn hρn hEn hTn
  obtain ⟨hwit, hgrad⟩ := hwgn
  exact ⟨qthr n, ρnc n, (hqthr n).1, (hqthr n).2,
    riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
      (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
    fun w hw => hw, fun x hx hqx => hwit x hx hqx,
    fun i first hf z hz B v hv hvw hRv => hEn i first hf z hz B v hv hvw hRv,
    fun x hx v hv hvw hRv => hTn x hx v hv hvw hRv,
    fun x hx v hv hvw hRv ξ => hgrad x hx v hv hvw hRv ξ,
    hpn.1, hpn.2, hkn, hρn⟩

/-- **prefix 导数 ⇐ 全局前缀背景 `hslabSel`（`_P6AN5`，PROVED 接线，构形通用；输入是 J10 残余（阈值换皮））**：`hslabSel`（`(H n)`
`EventSlabsDerivative Ctime (qthr n)`）⇒ `hlocal_final_noJ10_P6AN5` 的 `hderE` 槽。 -/
theorem hderE_of_slabSel_gen_P6AN5 {β : ℝ} {s t : ℕ → ℝ} {H : ℕ → RetainedCoreHistory.{u}}
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier} {Ctime : ℝ≥0} {qthr : ℕ → ℝ}
    (hslabSel : ∀ n, (H n).EventSlabsDerivative Ctime (qthr n) (Fin.last (H n).eventCount)) :
    ∀ Rad : ℝ, ∀ᶠ n in atTop,
      ∀ j : Fin (H n).eventCount,
        ∀ (first : Fin ((H n).eventCount + 1)) (hf : first ≤ j.castSucc),
        ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
            (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        ∀ B : BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
          (Fin.le_last first) z,
        ∀ v ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
        t n - β / (G n).flow.scalar (t n) (y n) ≤ v →
        qthr n < ((H n).toHistory.event j).incoming.flow.scalar v
          (B.point j.castSucc hf (Fin.le_last _)) →
        |derivWithin (fun w => ((H n).toHistory.event j).incoming.flow.scalar w
          (B.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
          Ctime * ((H n).toHistory.event j).incoming.flow.scalar v
            (B.point j.castSucc hf (Fin.le_last _)) ^ 2 :=
  fun _ => Eventually.of_forall fun n j _ _ _ _ _ v hv _ hRv =>
    hslabSel n j (Fin.castSucc_lt_last j) _ v hv hRv

/-- **final top 时间导数 ⇐ hgood + hseedTop 在 `n` 处（`_P6AN5`，PROVED）**：ANCHOR4
`pickedBallShortWindow_final_of_hgood_P6AN4` 梯度分支 (2) 的时间导数孪生。窗口点 `v′ ∈ (time last, t)`、
`t − β/R ≤ v′`、`R(v′, x) > Cg·R_n`：hseedTop 把 `x` 放进 hgood 区域（`activeStage σ = last`），hgood 在
`τ = v′`（`activeStage τ = last`、`time last < τ < horizon`）的时间分量给 `|∂_t R| ≤ Ctg R²`，
`stageMetric_last_of_lt` 换成 final slab 的 `restrictIncoming` flow。 -/
theorem hderT_final_of_hgood_witness_P6AN5 {Cg β Rad : ℝ} (K : ℕ → RetainedCoreHistory.{u})
    {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
    {pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier}
    {seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)}
    {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {eps C1 C2 : ℝ}
    {Ctg : ℝ≥0}
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctg) {t : ℕ → ℝ}
    (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) (htK : ∀ n, t n < (K n).horizon)
    {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier}
    (hσ : ∀ n, (σ n : ℝ) = t n) (hyG : ∀ n, HEq (y n) (yG n))
    (hRn : ∀ n, R n = (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl).flow.scalar (t n) (yG n))
    (n : ℕ) (hav : (aSeed n : ℝ) ≤ σ n - β / R n) (hvL : (σ n : ℝ) - L n ^ 2 / R n ≤ σ n - β / R n)
    (hW :
        ∀ x ∈ riemannianBallOf
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
            (Rad / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - β / R n ≤ s → s < σ n →
          (K n).toHistory.time ((K n).toHistory.activeStage (σ n)) < s →
          Cg * R n < metricScalarAt
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s) x →
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s)
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) x ≤
            riemannianEDistOf
                ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
                ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                  ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n))) :
    ∀ x ∈ riemannianBallOf ((((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
    ((htl n).trans (htK n)) le_rfl).flow.base.metric (t n)) (yG n)
        (Rad / Real.sqrt ((((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
            ((htl n).trans (htK n)) le_rfl).flow.scalar (t n) (yG n))),
      ∀ v ∈ Ioo ((K n).time (Fin.last (K n).eventCount)) (t n),
      t n - β / (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
          ((htl n).trans (htK n)) le_rfl).flow.scalar (t n) (yG n) ≤ v →
      Cg * R n < (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
          ((htl n).trans (htK n)) le_rfl).flow.scalar v x →
      |derivWithin (fun w => (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
          ((htl n).trans (htK n)) le_rfl).flow.scalar w x) (Iic v) v| ≤
        Ctg * (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
            ((htl n).trans (htK n)) le_rfl).flow.scalar v x ^ 2 := by
  have hfin : (K n).time (Fin.last (K n).eventCount) < (K n).horizon := (htl n).trans (htK n)
  have hv1 : (K n).time (Fin.last (K n).eventCount) < σ n := by
    rw [hσ n]
    exact htl n
  have hact : (K n).toHistory.activeStage (σ n) = Fin.last (K n).eventCount :=
    (K n).toHistory.activeStage_eq_last_of_time_last_le (σ n) hv1.le
  intro x hx v' hv' hwin hRx
  have hτ0 : 0 ≤ v' := ((K n).toHistory.time_nonneg _).trans hv'.1.le
  have hτh : v' < (K n).toHistory.horizon := hv'.2.trans (htK n)
  let τ : Icc (0 : ℝ) (K n).toHistory.horizon := ⟨v', hτ0, hτh.le⟩
  have hactτ : (K n).toHistory.activeStage τ = Fin.last (K n).eventCount :=
    (K n).toHistory.activeStage_eq_last_of_time_last_le τ hv'.1.le
  have hs1 : (σ n : ℝ) - β / R n ≤ v' := by
    rw [hσ n, hRn n]
    exact hwin
  have hs2 : v' < σ n := by
    rw [hσ n]
    exact hv'.2
  have hav' : aSeed n ≤ τ := by
    change (aSeed n : ℝ) ≤ v'
    linarith
  have hvs' : τ ≤ σ n := hs2.le
  have hvL' : (σ n : ℝ) - L n ^ 2 / R n ≤ (τ : ℝ) := by
    change (σ n : ℝ) - L n ^ 2 / R n ≤ v'
    linarith
  have h1 : (K n).toHistory.activeStage (aSeed n) ≤ Fin.last (K n).eventCount :=
    Fin.le_last _
  have h2 : Fin.last (K n).eventCount ≤ (K n).toHistory.activeStage (Tn n) :=
    hact ▸ (K n).toHistory.activeStage_mono (hsT n)
  have key2 : ∀ (k : Fin ((K n).eventCount + 1)) (hk : (K n).toHistory.activeStage (σ n) = k)
      (h1' : (K n).toHistory.activeStage (aSeed n) ≤ k)
      (h2' : k ≤ (K n).toHistory.activeStage (Tn n)) (x'' yk : ((K n).toHistory.stage k).Carrier),
      HEq (y n) yk →
      x'' ∈ riemannianBallOf ((K n).toHistory.stageMetric k (σ n)) yk (Rad / Real.sqrt (R n)) →
      (K n).toHistory.time k < v' →
      Cg * R n < metricScalarAt ((K n).toHistory.stageMetric k v') x'' →
      riemannianEDistOf ((K n).toHistory.stageMetric k v') ((seedTrace n).point k h1' h2') x'' ≤
        riemannianEDistOf
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
            ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
              ((K n).toHistory.activeStage_mono (has n))
              ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / Real.sqrt (R n)) := by
    intro k hk
    subst hk
    intro h1' h2' x'' yk hy hx'' htk hRk
    obtain rfl := eq_of_heq hy
    exact hW x'' hx'' v' hs1 hs2 htk hRk
  have hx' : x ∈ riemannianBallOf ((K n).toHistory.stageMetric (Fin.last (K n).eventCount)
      (σ n)) (yG n) (Rad / Real.sqrt (R n)) := by
    rw [ObservedHistory.stageMetric_last_of_lt (h := hfin), hσ n, hRn n]
    exact hx
  have hRv : Cg * R n < metricScalarAt ((K n).toHistory.stageMetric
      (Fin.last (K n).eventCount) v') x := by
    rw [ObservedHistory.stageMetric_last_of_lt (h := hfin)]
    exact hRx
  have hd := key2 (Fin.last (K n).eventCount) hact h1 h2 x (yG n) (hyG n) hx' hv'.1 hRv
  have key3 : ∀ (k : Fin ((K n).eventCount + 1)) (hk : (K n).toHistory.activeStage τ = k)
      (h1' : (K n).toHistory.activeStage (aSeed n) ≤ k)
      (h2' : k ≤ (K n).toHistory.activeStage (Tn n)) (x' : ((K n).toHistory.stage k).Carrier),
      riemannianEDistOf ((K n).toHistory.stageMetric k τ) ((seedTrace n).point k h1' h2') x' ≤
        riemannianEDistOf
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
            ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
              ((K n).toHistory.activeStage_mono (has n))
              ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / Real.sqrt (R n)) →
      Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric k τ) x' →
      (K n).toHistory.time k < (τ : ℝ) → (τ : ℝ) < (K n).toHistory.horizon →
      |derivWithin (fun s => metricScalarAt ((K n).toHistory.stageMetric k s) x')
          (Iic (τ : ℝ)) τ| ≤
        Ctg * metricScalarAt ((K n).toHistory.stageMetric k τ) x' ^ 2 := by
    intro k hk
    subst hk
    intro h1' h2' x' hd' hR'
    exact (hgood n τ hav' hvs' hvL' x' hd' hR').2
  have hres := key3 (Fin.last (K n).eventCount) hactτ h1 h2 x hd hRv.le hv'.1 hτh
  simp only [ObservedHistory.stageMetric_last_of_lt (H := (K n).toHistory) (h := hfin)] at hres
  exact hres

/-- **序列版（`_P6AN5`，PROVED ⇐ hgood + hseedTop）**：结论 =
`topAnchorInputs_final_of_pickedBall_noJ10_P6AN5`
的 `hderT` 槽（`qthr n := Cg·R_n`、`Ctime := Ctg`）。时间域同
`pickedBallShortWindow_final_seq_of_hgood_P6AN4`。 -/
theorem hderT_final_seq_of_hgood_P6AN5 {Cg β : ℝ} (K : ℕ → RetainedCoreHistory.{u})
    {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
    {pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier}
    {seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)}
    {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {eps C1 C2 : ℝ}
    {Ctg : ℝ≥0}
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctg) {t : ℕ → ℝ}
    (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) (htK : ∀ n, t n < (K n).horizon)
    {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier}
    (hσ : ∀ n, (σ n : ℝ) = t n) (hyG : ∀ n, HEq (y n) (yG n))
    (hRn : ∀ n, R n = (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl).flow.scalar (t n) (yG n))
    (hRpos : ∀ n, 0 < R n) (hβ : 0 < β)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hL : Tendsto L atTop atTop)
    (hseedTop : ∀ Rad : ℝ, ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
            (Rad / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - β / R n ≤ s → s < σ n →
          (K n).toHistory.time ((K n).toHistory.activeStage (σ n)) < s →
          Cg * R n < metricScalarAt
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s) x →
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s)
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) x ≤
            riemannianEDistOf
                ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
                ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                  ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n))) :
    ∀ Rad : ℝ, ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
    ((htl n).trans (htK n)) le_rfl).flow.base.metric (t n)) (yG n)
          (Rad / Real.sqrt ((((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
              ((htl n).trans (htK n)) le_rfl).flow.scalar (t n) (yG n))),
        ∀ v ∈ Ioo ((K n).time (Fin.last (K n).eventCount)) (t n),
        t n - β / (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
            ((htl n).trans (htK n)) le_rfl).flow.scalar (t n) (yG n) ≤ v →
        Cg * R n < (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
            ((htl n).trans (htK n)) le_rfl).flow.scalar v x →
        |derivWithin (fun w => (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
            ((htl n).trans (htK n)) le_rfl).flow.scalar w x) (Iic v) v| ≤
          Ctg * (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
              ((htl n).trans (htK n)) le_rfl).flow.scalar v x ^ 2 := by
  intro Rad
  filter_upwards [hseedTop Rad, hwin β hβ, hL.eventually_ge_atTop (max β 1)] with n hW ha hLn
  have hL1 : 1 ≤ L n := (le_max_right β 1).trans hLn
  have hβL : β ≤ L n ^ 2 := by nlinarith [le_max_left β 1]
  have hdiv : β / R n ≤ L n ^ 2 / R n := div_le_div_of_nonneg_right hβL (hRpos n).le
  exact hderT_final_of_hgood_witness_P6AN5 K hgood htl htK hσ hyG hRn n ha (by linarith) hW

end FinalLocal

section FinalTop

/-- **`topAnchorInputs_final_of_pickedBall_noJ10_P6AN5`（G1b 组合，PROVISIONAL：binder = final 合同 `hpb` +
q_sel 导数 `hderE / hderT` + `hRlim`；无 `hqR`、无 `hslab / hderG`）**：ANCHOR4
`topAnchorInputs_final_of_pickedBall_P6AN4` 的孪生；schedule 经
`selectionSchedule_noJ10_P6AN5`，`hlocal` 经
`hlocal_final_noJ10_P6AN5`。结论 = final 构形 `TopAnchorInputs_P6AN2 β` 逐字。 -/
theorem topAnchorInputs_final_of_pickedBall_noJ10_P6AN5 {β : ℝ} (hβ : β ≤ 1 / 2)
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
    (hRlim : Tendsto (fun n => (G n).flow.scalar (t n) (yG n)) atTop atTop)
    {ε : ℝ} (hε : ε ≤ coneAccuracy) {κ C1 C2 Cq : ℝ} (hκ : 0 < κ) {Cgrad : ℝ≥0}
    {qthr ρnc : ℕ → ℝ}
    (hqthr : ∀ n, 0 < qthr n ∧ qthr n ≤ Cq * (G n).flow.scalar (t n) (yG n))
    (hradii : Tendsto (fun n => ρnc n * Real.sqrt ((G n).flow.scalar (t n) (yG n))) atTop atTop)
    (hpb : ∀ Rad : ℝ, ∀ᶠ n in atTop,
      PickedBallShortWindow_final_P6AN4 β Rad (qthr n) (ρnc n) κ ε C1 C2 Cgrad (K n)
        ((htl n).trans (htK n)) (t n) (yG n))
    (hderE : ∀ Rad : ℝ, ∀ᶠ n in atTop,
      ∀ j : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount,
        ∀ (first : Fin (((K n).prefixAt (Fin.last (K n).eventCount)).eventCount + 1))
          (hf : first ≤ j.castSucc),
        ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (yG n)
            (Rad / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
        ∀ B : BackwardPointTrace ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory first
          (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount) (Fin.le_last first) z,
        ∀ v ∈ Ioo (((K n).prefixAt (Fin.last (K n).eventCount)).time j.castSucc)
          (((K n).prefixAt (Fin.last (K n).eventCount)).time j.succ),
        t n - β / (G n).flow.scalar (t n) (yG n) ≤ v →
        qthr n <
          (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event j).incoming.flow.scalar v
            (B.point j.castSucc hf (Fin.le_last _)) →
        |derivWithin (fun w =>
            (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event j).incoming.flow.scalar w
              (B.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
          Ctime *
            (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event j).incoming.flow.scalar v
              (B.point j.castSucc hf (Fin.le_last _)) ^ 2)
    (hderT : ∀ Rad : ℝ, ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (yG n)
          (Rad / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
        ∀ v ∈ Ioo ((K n).time (Fin.last (K n).eventCount)) (t n),
        t n - β / (G n).flow.scalar (t n) (yG n) ≤ v →
        qthr n < (G n).flow.scalar v x →
        |derivWithin (fun w => (G n).flow.scalar w x) (Iic v) v| ≤
          Ctime * (G n).flow.scalar v x ^ 2) :
    TopAnchorInputs_P6AN2 β (fun n => (K n).prefixAt (Fin.last (K n).eventCount))
      (fun n => (K n).prefixAt_time_last _) (fun n => (K n).horizon)
      (fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
        ((htl n).trans (htK n)) le_rfl)
      (fun n => (K n).final_initial ((htl n).trans (htK n))) t yG := by
  obtain rfl : G = fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl := funext hG
  obtain ⟨hDlim, hDrad, hord, hacc, hθ⟩ := selectionSchedule_noJ10_P6AN5 hβ hpar hθcap
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
  refine hlocal_final_noJ10_P6AN5 (fun n => (K n).prefixAt_time_last _)
    (fun n => (K n).final_initial ((htl n).trans (htK n))) hε hκ hphi hpin
    hqthr hradii (fun Rad => (hpb Rad).mono fun n h => ⟨h.1, h.2.1⟩)
    (fun Rad => (hpb Rad).mono fun n h => ?_) hderE hderT
  exact (K n).tested_noncollapse_final_P6M ((htl n).trans (htK n))
    (a := t n - β / (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl).flow.scalar (t n) (yG n)) (t := t n) _ h.2.2
    ((K n).prefixAt_time_last _)

/-- **`topAnchorInputs_final_of_hgood_noJ10_P6AN5`（G1b 组合，PROVISIONAL：binder = hseedTop（BLOCKED，
KSWEXIT）+ `hslabSel`（J10 残余（阈值换皮））+ final `hkappa` + hgood + FINCOND 层 supplies + `hR / hRlim`；无
`hqR`、
无 `hslab / hderG`、无 `GradientBoundBefore`）**：ANCHOR4 `topAnchorInputs_final_of_hgood_P6AN4`
的孪生。witness /
梯度 / κ ⇐ `pickedBallShortWindow_final_seq_of_hgood_P6AN4`，event 时间导数 ⇐
`hderT_final_seq_of_hgood_P6AN5`，
prefix 导数 ⇐ `hderE_of_slabSel_gen_P6AN5`；两条导数合用 `Ctime + Ctg`。 -/
theorem topAnchorInputs_final_of_hgood_noJ10_P6AN5 {β : ℝ} (hβ0 : 0 < β) (hβ : β ≤ 1 / 2)
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
    {Cg : ℝ} (hCg : 0 < Cg)
    {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
    {pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier}
    {seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)}
    {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {ε C1 C2 : ℝ}
    {Ctg : ℝ≥0}
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L ε C1 C2 Ctg)
    (hσ : ∀ n, (σ n : ℝ) = t n) (hyG : ∀ n, HEq (y n) (yG n))
    (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n))
    (hR : ∀ n, 0 < R n) (hRlim : Tendsto R atTop atTop)
    (hslabSel : ∀ n, ((K n).prefixAt (Fin.last (K n).eventCount)).EventSlabsDerivative Ctime
      (Cg * R n) (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount))
    (hL : Tendsto L atTop atTop) (hε : ε ≤ coneAccuracy) {κ : ℝ} (hκ : 0 < κ) {Cgrad : ℝ≥0}
    {ρnc : ℕ → ℝ} (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop)
    (hC2 : C2 ≤ (Cgrad : ℝ))
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hseedTop : ∀ Rad : ℝ, ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
            (Rad / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - β / R n ≤ s → s < σ n →
          (K n).toHistory.time ((K n).toHistory.activeStage (σ n)) < s →
          Cg * R n < metricScalarAt
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s) x →
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s)
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) x ≤
            riemannianEDistOf
                ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
                ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                  ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)))
    (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf
          ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
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
    TopAnchorInputs_P6AN2 β (fun n => (K n).prefixAt (Fin.last (K n).eventCount))
      (fun n => (K n).prefixAt_time_last _) (fun n => (K n).horizon)
      (fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
        ((htl n).trans (htK n)) le_rfl)
      (fun n => (K n).final_initial ((htl n).trans (htK n))) t yG := by
  obtain rfl : G = fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl := funext hG
  have hRlim' : Tendsto (fun n => (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl).flow.scalar (t n) (yG n)) atTop atTop :=
    hRlim.congr fun n => hRn n
  refine topAnchorInputs_final_of_pickedBall_noJ10_P6AN5 hβ htl htK (fun _ => rfl) hcan hqcan hpar
    hscale hθcap hphi hpinch hnot hT₀ hRt hRlim' hε hκ (Cq := Cg) (qthr := fun n => Cg * R n)
    (ρnc := ρnc) (Ctime := Ctime + Ctg) (fun n => ⟨mul_pos hCg (hR n), le_of_eq (by rw [hRn n])⟩) ?_
    (pickedBallShortWindow_final_seq_of_hgood_P6AN4 K hgood hC2 htl htK hσ hyG hRn hR hβ0 hκ.le
      hwin hL hseedTop hkappa)
    (fun Rad => (hderE_of_slabSel_gen_P6AN5 (β := β) (s := fun n => (K n).horizon)
      (H := fun n => (K n).prefixAt (Fin.last (K n).eventCount))
      (G := fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
        ((htl n).trans (htK n)) le_rfl) (y := yG) hslabSel Rad).mono
      fun _ h j first hf z hz B v hv hvw hRv =>
        le_add_coe_mul_sq_P6AN5 (h j first hf z hz B v hv hvw hRv))
    (fun Rad => (hderT_final_seq_of_hgood_P6AN5 K hgood htl htK hσ hyG hRn hR hβ0 hwin hL hseedTop
      Rad).mono fun _ h x hx v hv hvw hRv => le_add_coe_mul_sq'_P6AN5 (h x hx v hv hvw hRv))
  refine hradii.congr fun n => ?_
  rw [hRn n]

end FinalTop

section FinalChain

/-- **`hdistW_finalSlab_of_hgood_local_noJ10_P6AN5`（G1b final 全链 (c1)，PROVISIONAL：binder =
`hdepthAF`
（depth driver 槽，repair = J10GEN2A 无 J10 late_cond driver 的 final 版）+ hseedTop（BLOCKED，KSWEXIT）+
`hslabSel`（J10 残余（阈值换皮），repair 同 event 链）+ final `hkappa` + hgood + FINCOND 层 supplies + K0 / HI +
`hR / hRlim`；**无 `hqR`**）**：
ANCHOR4 `hdistW_finalSlab_of_hgood_local_P6AN4` 的孪生。top-anchor
半：`topAnchorInputs_final_of_hgood_noJ10_P6AN5`
→ KSW2 `hanchor0_final_of_topInputs_P6AN2`；depth 半：`hdepthAF hanchor0` 喂
`hscalW_final_eventually_of_subseqDriver_P6AN2`；`hσfin ∧ hσlt` 由 `hσfin_of_selection_P6AN3`；合成
`hdistW_of_firstExit_final_P6DW2`。旧 depth 链的 FINCOND supplies（`recordsF / hHI / a₀ / hδF / hbirthA
/ hslab /
hderG / hseed / hwitC / hbcadC / hqs` 与 `hqR`）收进 `hdepthAF` 的 producer。结论 = `hdistW` 槽逐字（final 支）。
-/
theorem hdistW_finalSlab_of_hgood_local_noJ10_P6AN5 :
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {t : ℕ → ℝ} →
      (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) →
      (htK : ∀ n, t n < (K n).horizon) →
      {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
        ((K n).time (Fin.last (K n).eventCount)) (K n).horizon} →
      (hG : ∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
        ((htl n).trans (htK n)) le_rfl) →
      {D θcap qcan T₀ : ℕ → ℝ} → {p : ℕ → CutoffParameters} → {δb : ℕ → ℝ} →
      {records : ∀ n (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount),
        T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ →
        GeometricCutoffRecord ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i (p n)} →
      {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier} →
      (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscale : ∀ (n : ℕ) i hi b,
        ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount,
          Perelman.PhiAlmostNonnegative
            (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).incoming.flow
            (Ico (((K n).prefixAt (Fin.last (K n).eventCount)).time i.castSucc)
              (((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ) ∩ Ici (T₀ n)) phi) ∧
        Perelman.PhiAlmostNonnegative (G n).flow
          (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) phi) →
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
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n)) →
      (hR : ∀ n, 0 < R n) → (hRlim : Tendsto R atTop atTop) →
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
      (hdepthAF : (∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
          ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (yG n)
              (A / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
            (G n).flow.scalar (t n) z ≤ Q * (G n).flow.scalar (t n) (yG n)) →
        ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          ∀ T : ℝ, 0 < T → ObservedHistory.DepthExtendable Kh σ y R (φ ∘ ψ) T) →
      ∀ (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
        (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
        (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
        (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
          ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
      (L : ℕ → ℝ) (r : ℕ → ℝ),
      ∀ {Cg εg C1g C2g : ℝ} {Ctg : ℝ≥0}, 0 < Cg → εg ≤ coneAccuracy →
      ObservedHistory.HgoodCg_C11SH Cg Kh Tn aSeed σ haT hsT has pT seedTrace y R L εg C1g C2g
        Ctg →
      (∀ n, ((K n).prefixAt (Fin.last (K n).eventCount)).EventSlabsDerivative Ctime (Cg * R n)
        (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)) →
      ∀ {Cgrad : ℝ≥0}, C2g ≤ (Cgrad : ℝ) →
      (∀ Rad : ℝ, ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Rad / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - β / R n ≤ s → s < σ n →
          (Kh n).time ((Kh n).activeStage (σ n)) < s →
          Cg * R n < metricScalarAt
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) x →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s)
              ((seedTrace n).point ((Kh n).activeStage (σ n))
                ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) x ≤
            riemannianEDistOf
                ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n))
                  ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n))) →
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
  intro Ctime phi hphi K t htl htK G hG D θcap qcan T₀ p δb records yG hcan hqcan hpar hscale hθcap
    hpinch hnot hT₀ hRt β hβ hβ2 Kh hKh σ y R hσ hyG hRn hR hRlim κ hκ ρnc hradii hkappa hdepthAF
    Tn aSeed haT hsT has pT seedTrace L r Cg εg C1g C2g Ctg hCg hεg hgood hslabSel Cgrad hC2
    hseedTop hL hsmall hclock hRr hwin a₁ ha₁ hpin
  subst hKh
  obtain rfl : G = fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl := funext hG
  have hin := topAnchorInputs_final_of_hgood_noJ10_P6AN5 hβ hβ2 htl htK (fun _ => rfl) hcan hqcan
    hpar hscale hθcap hphi hpinch hnot hT₀ hRt hCg hgood hσ hyG hRn hR hRlim hslabSel hL hεg hκ
    hradii hC2 hwin hseedTop hkappa
  have hanc := hanchor0_final_of_topInputs_P6AN2 hβ htl htK hin
  have hslabσ := hσfin_of_selection_P6AN3 htl htK (fun n => (K n).toHistory) rfl σ hσ
  exact ObservedHistory.hdistW_of_firstExit_final_P6DW2 (fun n => (K n).toHistory) Tn aSeed σ haT
    hsT has pT seedTrace y R L hR r hL hsmall hclock hRr hwin ha₁ hpin hslabσ.1 hslabσ.2
    (ObservedHistory.hscalW_final_eventually_of_subseqDriver_P6AN2 (fun n => (K n).toHistory) Tn
      aSeed σ haT hsT has pT seedTrace y R L hR (fun φ hφ _ => hdepthAF hanc φ hφ))

end FinalChain

/-- consumer（G1b，`_P6AN5`）：final 支 top-anchor 接口无
`hqR`——`topAnchorInputs_final_of_hgood_noJ10_P6AN5`
喂 KSW2 `hanchor0_final_of_topInputs_P6AN2`（final 全链即如此使用）。 -/
example := @hanchor0_final_of_topInputs_P6AN2.{u}

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

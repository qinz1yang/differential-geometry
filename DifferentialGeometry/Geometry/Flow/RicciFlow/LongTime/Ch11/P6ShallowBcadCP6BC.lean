import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ShallowPointPickC11PT
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AnchorThirdKappaP6AN3

/-!
# `hbcadC`（SHALLOW T0）⇐ driver 中心邻域合同 + T1 late-K 数据（O-CH11-HBCADC G1，后缀 `_P6BC`）

ANCHOR2 / ANCHOR3 的剩余 binder `hbcadC` 与 SHALLOW T0 `ShallowBcadC_C11SH Kh σ y R` 逐字相同
（`Kh = (K ·).toHistory`；量词序 `∀ A Dd ∃ C ∀ φ σ′ Dw T K`）。本文件装配：

* `ObservedHistory.hbcadC_of_pickedCenter_P6BC`（PROVISIONAL[`hPC` + T1 late-K 组 + `hdistQC`]）：
  P6L3 `shallowBcadC_of_sliceRC_C11SH`（T1 ⇒ T0，`η₃ Lc` 取它的 `∃`）∘ PICKT1
  `shallowSliceRC_of_pickedCenter_C11PT`（K-SW 已由 KSW2 `ksw_pos_C11KS2` 付，U 侧 `hUVC` ⇐ 合同族
  `hPC`）。
  P6L3 的两个附加前提由 binder 推出：`σ n < time last` ⇐ `htj` + `time_strictMono`；`1 ≤ R n` ⇐ `hqR`。
  binder = PICKT1 consumer 的 binder 去掉 `η₃ Lc hη₃ hLc`，结论换成 T0。
* `hdistW_eventSlab_of_pickedCenter_P6BC`（ANCHOR3 G4 全链 `hdistW_eventSlab_of_hgood_P6AN3`
  去 `hbcadC`）：`hdistW` 槽逐字（event 支），当前最小 binder 表见该定理 docstring。
* `ObservedHistory.hscalW_eventSlab_of_pickedCenter_P6BC`（ANCHOR2 G4
  `hscalW_eventSlab_of_topInputs_P6AN2` 去 `hbcadC`；T1 用独立 seed 组）：`hscalW` binder 逐字。

**只做 event 支**。final 支 BLOCKED：ANCHOR final 构形是 `time last < t n`，而 P6L3 要 `σ n < time last`，
PICKT1 合同也只有 event slice（`j′ : Fin eventCount`）⇒ repair target = final-slab 版 P6L3 孪生，或把 final
`hbcadC` 改成 E 层（`extendAt (finalSlab …)`）陈述（CXJF2 / CXUT 的 extendAt 形 ceiling 可接），见 state。

非循环：`hbcadC_of_pickedCenter_P6BC` 的前提里没有 `hdistW` / `HU` / `hanchor0` 的结论形，证明闭包不含任何 `_P6AN*` /
`_P6M3..6` / `HU_*` / `hscalW*` / `hscalU` / `hclosG` / `CanonicalLateCore` / `hspine` 常量（G2 审计
扫描）。`hdistQC` 是 **traced-conditioned**（`isTracedRegion` 在其自身量词里）、余量 `L/4`、跨 stage 的种子距离闭合，
owner = HDISTC `hdistC_of_traced_anySeed_C11G3`（取 `L ↦ L/4`），**不是** `hdistW`（`hdistW` 是同 stage
`activeStage v = activeStage σ`、无 traced 前提、余量 `L` 的结论，产自 hscalW ← `hbcadC`）。
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

section T0

/-- **`hbcadC` ⇐ PICKT1 consumer（`_P6BC`，PROVISIONAL[`hPC` + T1 late-K 组 + `hdistQC`]）**：结论 =
SHALLOW T0 `ShallowBcadC_C11SH (K ·).toHistory σ y R`
（= ANCHOR2 / ANCHOR3 的 `hbcadC` binder 逐字）。
证明 = P6L3 `shallowBcadC_of_sliceRC_C11SH`（取其 `η₃ Lc`）喂 PICKT1 `shallowSliceRC_of_pickedCenter_C11PT`
；
`σ n < time last` ⇐ `hσ` + `htj` + `time_strictMono`，`1 ≤ R n` ⇐ `hqR`（`n + 1 ≤ max (n+1) Q ≤ R`）。
已付清：K-SW（`ksw_pos_C11KS2`，PROVED）、U 侧 `hUVC`（⇐ `hPC`，`kswHU_of_pickedCenter_C11PT`）、T1 ⇒ T0。
剩余 binder（owner）：`hPC`（`PickedCenterNeighborhood_C11PT` 族 → PICKSEL：StepOne 接线 + 中心尺度窗口 seed
`PickedCenterWindowSeed_C11PT`）；late-K 组
`recordsK recordsF hHI hcanK hδF hacc hrad hord hscaleK hbirthA
hpinchK0 hslabK hqR hT₀`（整条 `K n`，selection K-route）；
seed 组 `Tn aSeed pT seedTrace L hL hwin`；
`ρV hρV`；`hdistQC`（HDISTC `hdistC_of_traced_anySeed_C11G3`，`L ↦ L/4`）。 -/
theorem ObservedHistory.hbcadC_of_pickedCenter_P6BC
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (htj : ∀ n, t n < (K n).time (j n).succ)
    {Q T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n))
    {a₀ : ℕ → ℝ}
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x)
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hδF : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1))
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
      1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime (Q n) (Fin.last (K n).eventCount))
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (y : ∀ n, ((K n).toHistory.stageAt
        (σ n)).Carrier)
    (R : ℕ → ℝ) (hσ : ∀ n, (σ n : ℝ) = t n) (hRpos : ∀ n, 0 < R n)
    (hqR : ∀ n : ℕ, max ((n : ℝ) + 1) (Q n) ≤ R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (ρV : ℕ → ℝ) (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop)
    (hdistQC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
          ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvs) x,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
                ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((K n).toHistory.activeStage v) le_rfl
                ((K n).toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (hPC : ∀ Rad σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n)
        (2 * Dw / Real.sqrt (R n)) (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      PickedCenterNeighborhood_C11PT Dw (Dd + Rad) (-σ₁) θ₀ (R n) (Cg * R n) (ρV n) κ ε C1 C2
        Cgrad (K n) (σ n) (y n)) :
    ObservedHistory.ShallowBcadC_C11SH (fun n => (K n).toHistory) σ y R := by
  obtain ⟨η₃, _, Lc, hη₃, _, hLc, hT0⟩ := ObservedHistory.shallowBcadC_of_sliceRC_C11SH.{u}
  refine hT0 (fun n => (K n).toHistory) σ y R hRpos ?_ ?_ ?_
  · refine Eventually.of_forall fun n => ?_
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    exact h1.trans ((le_max_left _ _).trans (hqR n))
  · intro n
    change (σ n : ℝ) < (K n).time (Fin.last (K n).eventCount)
    rw [hσ n]
    exact (htj n).trans_le ((K n).time_strictMono.monotone (Fin.le_last _))
  · exact ObservedHistory.shallowSliceRC_of_pickedCenter_C11PT (C1 := C1) (C2 := C2)
      (Cgrad := Cgrad) hθ₀ hεle hκ hphi hCg hη₃ hLc htj recordsF hHI hcanK hδF hacc hrad hord
      hscaleK hbirthA hpinchK0 hslabK σ y R hσ hRpos hqR hT₀ Tn aSeed haT hsT has pT seedTrace L
      hL hwin ρV hρV hdistQC hPC

end T0

section Anchor3

/-- **`hdistW_eventSlab_of_pickedCenter_P6BC`（ANCHOR3 全链，PROVISIONAL）**：
`hdistW_eventSlab_of_hgood_P6AN3` 的 `hbcadC` 由 `hbcadC_of_pickedCenter_P6BC` 付；
结论 = `hdistW` 槽逐字（event 支）。
**hdistW 当前最小 binder 表**（event 支；括号内 = owner）：
(A) ANCHOR3 G4 原有（`hbcadC` 已消）：
1. prefix schedule / records：`records recordsF hcan hδF hqcan hpar hscale hθcap hnot hT₀ hRt hqR`
   `hHI hpinch`   （selection / P6CD）；
2. 旧全域导数背景 `hslab hderG`（J10GEN 迁移义务）、梯度 `hgradG : GradientBoundBefore`（ANCHOR4 G1 以
   hgood witness + `hseedTop` 替换中）；
3. K 层 `hseed`（`r₀ w`）、`hkappa`（`κ ρnc hradii`）、`hwitC`（`qs ≤ Cs R`）（KAPPA / HFOOT / P6CD）；
4. hgood `HgoodCg_C11SH Cg …`（`εg ≤ coneAccuracy`）+ `hqg`（selection / SHALLOW）；
5. P6DW K0 / HI：`hsmall hclock hRr hwin hpin hL`（SEED / P6M4）。
(B) `hbcadC` 换成（本文件，T1 块，`K` 后缀 = 整条 `K n` 上而非 prefix 上）：
6. `hPC : PickedCenterNeighborhood_C11PT` 族（PICKSEL / `PickedCenterWindowSeed_C11PT`，
   R-C11-18 路线 (i)/(ii)）；
7. late-K 组 `recordsK recordsFK hHIK hcanK hδFK haccK hradK hordK hscaleK hbirthA hpinchK0 hslabK`
   `hqRK hT₀K`   （selection K-route；与 1 同源，只是落在整条 `K n`）；
8. `hdistQC`（traced-conditioned、`L/4`、跨 stage；HDISTC `hdistC_of_traced_anySeed_C11G3`，**非** hdistW）；
9. 常数 `θ₀ > 0`、`εK ≤ coneAccuracy`、`C1K C2K CgradK CtimeK`、`CgK ≥ 1`、`phiK`。
无损共享（(b)）：`κ ρnc hradii` 与 `hkappa` 共用（`hPC` κ 半与 `hkappa` 对 `κ`、`ρ` 同向单调，取 min 不损失）；
`K j t htj σ y R hσ` 与 seed 组 `Tn aSeed haT hsT has pT seedTrace L hL hwin` 共用；
`hRpos` 由 `hRn hqR hqcan` 推出。 -/
theorem hdistW_eventSlab_of_pickedCenter_P6BC :
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
      {β : ℝ} → (hβ : 0 < β) →
      (hβ2 : β ≤ 1 / 2) →
      (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) →
          (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      {r₀ w : ℝ} → (hr₀ : 0 < r₀) → (hw : 0 < w) →
      (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel
              ((K n).toHistory.stageAt (σ n)).Carrier
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
            (riemannianBallOf
                ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
              (r₀ / Real.sqrt (R n)))) →
      {κ : ℝ} → (hκ : 0 < κ) → (ρnc : ℕ → ℝ) →
      (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop) →
      (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
            ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (K n).toHistory.isParabolicallyRmControlledBall v
            (tr.point ((K n).toHistory.activeStage v) le_rfl
                ((K n).toHistory.activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume
                ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              (tr.point ((K n).toHistory.activeStage v) le_rfl
                  ((K n).toHistory.activeStage_mono hvt)) r'') →
      {C1s C2s Cs : ℝ} → {qs : ℕ → ℝ} → (hqs : ∀ n, qs n ≤ Cs * R n) →
      (hwitC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (K n).toHistory.time ((K n).toHistory.activeStage v) < v →
        ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
            ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvt) x,
          qs n < metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            (tr.point ((K n).toHistory.activeStage v) le_rfl
                ((K n).toHistory.activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness
              ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) ε C1s C2s
              (tr.point ((K n).toHistory.activeStage v) le_rfl
                  ((K n).toHistory.activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε) →
      ∀ (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
        (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
        (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
        (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
          ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
      (L : ℕ → ℝ) (r : ℕ → ℝ),
      ∀ {Cg εg C1g C2g : ℝ} {Ctg : ℝ≥0}, 0 < Cg → εg ≤ coneAccuracy →
      ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
          seedTrace y R L εg C1g C2g
        Ctg →
      ∀ {qg : ℕ → ℝ} {Cgrad : ℝ≥0}, (∀ n, qg n ≤ Cg * R n) →
      (∀ n, ((K n).toHistory.event (j n)).incoming.GradientBoundBefore Cgrad (qg n) (t n)) →
      Tendsto L atTop atTop →
      (∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) (r n)) →
      (∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2) →
      Tendsto (fun n => R n * r n ^ 2) atTop atTop →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) →
      ∀ {a₁ : ℝ}, 0 ≤ a₁ →
      (∀ n (τ' : Icc (0 : ℝ) (K n).toHistory.horizon) (x : ((K n).toHistory.stageAt τ').Carrier),
        InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ') τ')
            (a₁ + τ') x) →
      {θ₀ : ℝ} → (hθ₀ : 0 < θ₀) →
      {εK : ℝ} → (hεK : εK ≤ coneAccuracy) → {C1K C2K : ℝ} → {CtimeK CgradK : ℝ≥0} →
      {phiK : ℝ → ℝ} → (hphiK : Perelman.AdmissiblePinchingFunction phiK) →
      {CgK : ℝ} → (hCgK : 1 ≤ CgK) →
      {QK T₀K : ℕ → ℝ} → {pK pFK : ℕ → CutoffParameters} →
      {recordsK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (pK n)} →
      (recordsFK : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pFK n)) →
      {a₀K : ℕ → ℝ} →
      (hHIK : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀K n) x ∧
        -3 / a₀K n ≤ metricScalarAt ((K n).initialMetric 0) x) →
      (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (hδFK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
        (pFK n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) →
      (haccK : ∀ n : ℕ, (pK n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) →
      (hradK : ∀ n : ℕ, (n : ℝ) + 1 ≤ (pK n).modelRadius) →
      (hordK : ∀ n : ℕ, n + 2 ≤ (pK n).modelOrder) →
      (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (QK n) ≤
        ((recordsK n i hi).static b).neck.scale) →
      (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
        1 ≤ a₀K n * ((recordsK n i hi).static b).neck.scale) →
      (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
        ((K n).toHistory.event i).incoming.flow
        (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀K n)) phiK) →
      (hslabK : ∀ n, (K n).EventSlabsDerivative CtimeK (QK n) (Fin.last (K n).eventCount)) →
      (hqRK : ∀ n : ℕ, max ((n : ℝ) + 1) (QK n) ≤ R n) →
      (hT₀K : ∀ B : ℝ, ∀ᶠ n in atTop, T₀K n ≤ (σ n : ℝ) - B / R n) →
      (hdistQC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
            (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
          (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
            ((K n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono hvs) x,
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              ((seedTrace n).point ((K n).toHistory.activeStage v)
                  ((K n).toHistory.activeStage_mono hav)
                ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
              (tr.point ((K n).toHistory.activeStage v) le_rfl
                  ((K n).toHistory.activeStage_mono hvs)) ≤
            riemannianEDistOf
                ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
                ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                    ((K n).toHistory.activeStage_mono (has n))
                  ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / 4 / Real.sqrt (R n))) →
      (hPC : ∀ Rad σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n)
          (2 * Dw / Real.sqrt (R n)) (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
        PickedCenterNeighborhood_C11PT Dw (Dd + Rad) (-σ₁) θ₀ (R n) (CgK * R n) (ρnc n) κ εK C1K C2K
          CgradK (K n) (σ n) (y n)) →
      ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf
          ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (K n).toHistory.activeStage v = (K n).toHistory.activeStage (σ n) →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
          ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvs) x,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
                ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((K n).toHistory.activeStage v) le_rfl
                ((K n).toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) := by
  intro Ctime phi ε hε hεX hεN hphi K j t hjt htj D θcap qcan T₀ p pF δb records recordsF yG a₀ ha₀
    hHI hcan hδF hqcan hpar hscale hθcap hpinch hslab hderG hqR hnot hT₀ hRt β hβ hβ2 σ y R hσ hyG
    hRn r₀ w hr₀ hw hseed κ hκ ρnc hradii hkappa C1s C2s Cs qs hqs hwitC Tn aSeed haT hsT has pT
    seedTrace L r Cg εg C1g C2g Ctg hCg hεg hgood qg Cgrad hqg hgradG hL hsmall hclock hRr hwin a₁
    ha₁ hpin θ₀ hθ₀ εK hεK C1K C2K CtimeK CgradK phiK hphiK CgK hCgK QK T₀K pK pFK recordsK
    recordsFK a₀K hHIK hcanK hδFK haccK hradK hordK hscaleK hbirthA hpinchK0 hslabK hqRK hT₀K
    hdistQC hPC
  have hRpos : ∀ n, 0 < R n := fun n => by
    rw [hRn n]
    linarith [hqcan n, hqR n, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  exact hdistW_eventSlab_of_hgood_P6AN3 hε hεX hεN hphi hjt htj recordsF ha₀ hHI hcan hδF hqcan
    hpar hscale hθcap hpinch hslab hderG hqR hnot hT₀ hRt hβ hβ2 (fun n => (K n).toHistory) rfl σ y
    R hσ hyG hRn hr₀ hw hseed hκ ρnc hradii hkappa hqs hwitC
    (ObservedHistory.hbcadC_of_pickedCenter_P6BC (C1 := C1K) (C2 := C2K) (Cgrad := CgradK) hθ₀
      hεK hκ hphiK hCgK htj recordsFK hHIK hcanK hδFK haccK hradK hordK hscaleK hbirthA hpinchK0
      hslabK σ y R hσ hRpos hqRK hT₀K Tn aSeed haT hsT has pT seedTrace L hL hwin ρnc hradii
      hdistQC hPC)
    Tn aSeed haT hsT has pT seedTrace L r hCg hεg hgood hqg hgradG hL hsmall hclock hRr hwin ha₁
    hpin

end Anchor3

section Anchor2

/-- **ANCHOR2 consumer（`_P6BC`，PROVISIONAL）**：`hscalW_eventSlab_of_topInputs_P6AN2`
（ShortSLT 已由 KSW2 付）
的 `hbcadC` 槽由 `hbcadC_of_pickedCenter_P6BC` 付；T1 块用独立 seed 组 `TnK aSeedK … LK hLK hwinK`（ANCHOR2
结论自己的 seed 组在 `hbcadC` 之后才量化）。结论 = `hscalW` binder 逐字（event 支）。 -/
theorem ObservedHistory.hscalW_eventSlab_of_pickedCenter_P6BC :
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
      {β : ℝ} → (hβ : 0 < β) →
      (hin : TopAnchorInputs_P6AN2 β (fun n => (K n).prefixAt (j n).castSucc)
        (fun n => (K n).prefixAt_time_last _) (fun n => (K n).time (j n).succ)
        (fun n => ((K n).toHistory.event (j n)).incoming) (fun n => (K n).event_initial (j n)) t
        yG) →
      (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) →
          (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      {r₀ w : ℝ} → (hr₀ : 0 < r₀) → (hw : 0 < w) →
      (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel
              ((K n).toHistory.stageAt (σ n)).Carrier
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
            (riemannianBallOf
                ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
              (r₀ / Real.sqrt (R n)))) →
      {κ : ℝ} → (hκ : 0 < κ) → (ρnc : ℕ → ℝ) →
      (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop) →
      (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
            ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (K n).toHistory.isParabolicallyRmControlledBall v
            (tr.point ((K n).toHistory.activeStage v) le_rfl
                ((K n).toHistory.activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume
                ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              (tr.point ((K n).toHistory.activeStage v) le_rfl
                  ((K n).toHistory.activeStage_mono hvt)) r'') →
      {C1s C2s Cs : ℝ} → {qs : ℕ → ℝ} → (hqs : ∀ n, qs n ≤ Cs * R n) →
      (hwitC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (K n).toHistory.time ((K n).toHistory.activeStage v) < v →
        ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
            ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvt) x,
          qs n < metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            (tr.point ((K n).toHistory.activeStage v) le_rfl
                ((K n).toHistory.activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness
              ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) ε C1s C2s
              (tr.point ((K n).toHistory.activeStage v) le_rfl
                  ((K n).toHistory.activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε) →
      {θ₀ : ℝ} → (hθ₀ : 0 < θ₀) →
      {εK : ℝ} → (hεK : εK ≤ coneAccuracy) → {C1K C2K : ℝ} → {CtimeK CgradK : ℝ≥0} →
      {phiK : ℝ → ℝ} → (hphiK : Perelman.AdmissiblePinchingFunction phiK) →
      {CgK : ℝ} → (hCgK : 1 ≤ CgK) →
      {QK T₀K : ℕ → ℝ} → {pK pFK : ℕ → CutoffParameters} →
      {recordsK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (pK n)} →
      (recordsFK : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pFK n)) →
      {a₀K : ℕ → ℝ} →
      (hHIK : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀K n) x ∧
        -3 / a₀K n ≤ metricScalarAt ((K n).initialMetric 0) x) →
      (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (hδFK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
        (pFK n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) →
      (haccK : ∀ n : ℕ, (pK n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) →
      (hradK : ∀ n : ℕ, (n : ℝ) + 1 ≤ (pK n).modelRadius) →
      (hordK : ∀ n : ℕ, n + 2 ≤ (pK n).modelOrder) →
      (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (QK n) ≤
        ((recordsK n i hi).static b).neck.scale) →
      (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
        1 ≤ a₀K n * ((recordsK n i hi).static b).neck.scale) →
      (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
        ((K n).toHistory.event i).incoming.flow
        (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀K n)) phiK) →
      (hslabK : ∀ n, (K n).EventSlabsDerivative CtimeK (QK n) (Fin.last (K n).eventCount)) →
      (hqRK : ∀ n : ℕ, max ((n : ℝ) + 1) (QK n) ≤ R n) →
      (hT₀K : ∀ B : ℝ, ∀ᶠ n in atTop, T₀K n ≤ (σ n : ℝ) - B / R n) →
      (TnK aSeedK : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) →
      (haTK : ∀ n, aSeedK n ≤ TnK n) → (hsTK : ∀ n, σ n ≤ TnK n) → (hasK : ∀ n, aSeedK n ≤ σ n) →
      (pTK : ∀ n, ((K n).toHistory.stageAt (TnK n)).Carrier) →
      (seedTraceK : ∀ n, BackwardPointTrace (K n).toHistory
        ((K n).toHistory.activeStage (aSeedK n)) ((K n).toHistory.activeStage (TnK n))
        ((K n).toHistory.activeStage_mono (haTK n)) (pTK n)) →
      (LK : ℕ → ℝ) → (hLK : Tendsto LK atTop atTop) →
      (hwinK : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeedK n : ℝ) ≤ σ n - T / R n) →
      (hdistQC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
            (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeedK n ≤ v) (hvs : v ≤ σ n),
          (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
            ((K n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono hvs) x,
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              ((seedTraceK n).point ((K n).toHistory.activeStage v)
                  ((K n).toHistory.activeStage_mono hav)
                ((K n).toHistory.activeStage_mono (hvs.trans (hsTK n))))
              (tr.point ((K n).toHistory.activeStage v) le_rfl
                  ((K n).toHistory.activeStage_mono hvs)) ≤
            riemannianEDistOf
                ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
                ((seedTraceK n).point ((K n).toHistory.activeStage (σ n))
                    ((K n).toHistory.activeStage_mono (hasK n))
                  ((K n).toHistory.activeStage_mono (hsTK n))) (y n) +
              ENNReal.ofReal (LK n / 4 / Real.sqrt (R n))) →
      (hPC : ∀ Rad σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n)
          (2 * Dw / Real.sqrt (R n)) (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
        PickedCenterNeighborhood_C11PT Dw (Dd + Rad) (-σ₁) θ₀ (R n) (CgK * R n) (ρnc n) κ εK C1K C2K
          CgradK (K n) (σ n) (y n)) →
      ∀ (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
        (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
        (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
        (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
          ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
              (L : ℕ → ℝ),
      ∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf
          ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ s : ℝ, (σ n : ℝ) - T / R n < s → s < σ n → (K n).toHistory.time
          ((K n).toHistory.activeStage (σ n)) < s →
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s)
            ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
              ((K n).toHistory.activeStage_mono (hsT n))) x ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        ∀ z : ((K n).toHistory.stageAt (σ n)).Carrier,
          riemannianEDistOf
              ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s) x z <
              ENNReal.ofReal (1 / Real.sqrt (C * R n)) →
            metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s) z ≤
                C * R n := by
  intro Ctime phi ε hε hεX hεN hphi K j t hjt htj D θcap qcan T₀ p pF δb records recordsF yG a₀ ha₀
    hHI hcan hδF hqcan hpar hscale hθcap hpinch hslab hderG hqR hnot hT₀ hRt β hβ hin σ y R hσ hyG
    hRn r₀ w hr₀ hw hseed κ hκ ρnc hradii hkappa C1s C2s Cs qs hqs hwitC θ₀ hθ₀ εK hεK C1K C2K
    CtimeK CgradK phiK hphiK CgK hCgK QK T₀K pK pFK recordsK recordsFK a₀K hHIK hcanK hδFK haccK
    hradK hordK hscaleK hbirthA hpinchK0 hslabK hqRK hT₀K TnK aSeedK haTK hsTK hasK pTK seedTraceK
    LK hLK hwinK hdistQC hPC
  have hRpos : ∀ n, 0 < R n := fun n => by
    rw [hRn n]
    linarith [hqcan n, hqR n, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  exact ObservedHistory.hscalW_eventSlab_of_topInputs_P6AN2 hε hεX hεN hphi hjt htj recordsF ha₀
    hHI hcan hδF hqcan hpar hscale hθcap hpinch hslab hderG hqR hnot hT₀ hRt hβ hin
    (fun n => (K n).toHistory) rfl σ y R hσ hyG hRn hr₀ hw hseed hκ ρnc hradii hkappa hqs hwitC
    (ObservedHistory.hbcadC_of_pickedCenter_P6BC (C1 := C1K) (C2 := C2K) (Cgrad := CgradK) hθ₀
      hεK hκ hphiK hCgK htj recordsFK hHIK hcanK hδFK haccK hradK hordK hscaleK hbirthA hpinchK0
      hslabK σ y R hσ hRpos hqRK hT₀K TnK aSeedK haTK hsTK hasK pTK seedTraceK LK hLK hwinK ρnc
      hradii hdistQC hPC)

end Anchor2

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

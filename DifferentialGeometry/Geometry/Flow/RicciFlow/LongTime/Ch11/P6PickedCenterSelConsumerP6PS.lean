import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PickedCenterSelP6PS

/-!
# driver 中心邻域合同的三级 consumer + PICKSEL G1 文件说明

O-CH11-PICKSEL G2，由 O-CH11-AUDITFIX 编；后缀 `_P6PS`。

## `P6PickedCenterSelP6PS.lean`（PICKSEL G1，源文件不改；其文件头 docstring 是占位，此处补正文）

PICKT1 HANDOVER 1/3：T1 壳 `hsliceR_lateHI_core_pickedCenter_C11PT` 的 U 侧合同
`PickedCenterNeighborhood_C11PT`（driver 中心 `(σ n, y n)`、尺度 `R n`）与 12.1 Step 1 合同
`PickedCenterStepOne_C11PT` 的 producer。全部在固定 `n`：
* `seedDist_slice_P6PS`（PROVED）：`hdl`（`hdistQC` 在 `n` 处的体，traced 点余量 `L/4`）+ 三角不等式 ⇒
  slice 时刻 `v` 区域点 `x ∈ B_v(tr x₁, Dc/√R_n)` 的 seed 距离 `≤ dσ + (L/4 + Dc)/√R_n`；
* `witness_of_seedDist_P6PS` / `hasSCTC_of_seedDist_P6PS`（PROVED）：hgood（`HgoodCg_C11SH`）在 seed 域
  `dσ + L/√R_n`、时间 `[σ − L²/R_n, σ]`、阈值 `Cg·R_n` 上给 neck witness / `HasSpatialCanonicalTimeControl`；
* `pickedCenterStepOne_slice_of_hgood_P6PS`（**PROVED，无 binder**）：Step 1 合同的 slice 部分 `v′ = v`；
  `pickedCenterStepOne_of_hgood_P6PS`（PROVISIONAL[`hWS`]）：全合同，窗口部分 `v′ < v` 只经
  `PickedCenterWindowSeed_C11PT`；
* `pickedCenterFootprint_P6PS` / `pickedCenterKappa_of_fresh_P6PS`：κ 项 ⇐ PBKAPPA FRESH 的**原 seed**
  supply（`KappaSeedWindowFwd_C11PK`，不用 hpick）+ top gate `hdσ`（J11 同式）+ 中心 footprint（`hdl` + I.8.3(b)
  + 中心端点 Ricci `hRic`，`ℓ` 自由，门槛 `4(Dc + 8θ/(ℓ√R_n)) ≤ 3L`）；
* `pickedCenterNeighborhood_of_hgood_fresh_P6PS`（PROVISIONAL[`hWS`；`hRic` OPEN owner DIST]）：
  `PickedCenterNeighborhood_C11PT` 逐字（witness PROVED / grad ⇐ hgood + `hWS` + `C2 ≤ Cgrad` /
  κ ⇐ FRESH）；`pickedCenterNeighborhood_of_nonpos_P6PS`：`Dc ≤ 0` 平凡支。
deny（G1 审计 `O-CH11-PICKSELG1Audit.lean` 传递扫描 0 hit）：hpick、`PickedBallTop_C11PB`、hUVC / M4 链、
hclosG / hclosC、hscalU、HU_、hstop。

## 本文件（G2 consumer，三级）

* **filter 级** `hPC_filter_of_hgood_fresh_P6PS`：任意 `l ≤ atTop`，T1 核心形的 `hdl`（`σ + σ₁/R ≤ v`）+
  `hWS`/`hRic` 在 `l` 上 eventually ⇒ 核心形 hPC 槽
  `∀ᶠ n in l, PickedCenterNeighborhood_C11PT Dw (Dd + Rad) (−σ₁) θ₀ (R n) (Cg·R n) (ρV n) κ …`。
  常数：`Dc := Dd + Rad`（`≤ 0` 走 nonpos 支）、`Tc := −σ₁`、`θ := θ₀`、`qthr := Cg·R_n`；
  `hLR` ⇐ `hℓL : 32θ₀ ≤ L·(ℓ√R)` + `L ≥ 2Dc`，`hTL` ⇐ `L ≥ max 1 (θ₀ − σ₁)`（`L → ∞`），`haS` ⇐ `hwin`。
* **family 级** `hPC_of_hgood_fresh_P6PS`：`shallowSliceRC_of_pickedCenter_C11PT` 的 `hPC` 槽逐字
  （`Rad σ₁ σ₂ φ Dw Dd T Kc` + traced-region 前缀），`hdl` 由同一个 `hdistQC`（`L/4`）转出；consumer
  `shallowSliceRC_of_hgood_fresh_P6PS` 直接喂 C11PT 的 SHALLOW T1 壳。
* **core 级** `hsliceR_lateHI_core_pickedCenter_hgood_P6PS`：`hsliceR_lateHI_core_pickedCenter_C11PT`
  逐字（其余 binder 不动），hPC 前提换成 `l` 上的 `hWS` + `hRic`；新增 hgood（独立 `Ctg`）、`C2 ≤ Cgrad`、
  seed 位置 `O`/`hO`、FRESH（常数 `Aκ`，不与结论的 `∀ A` 冲突）。

剩余 binder（PROVISIONAL）：`PickedCenterWindowSeed_C11PT`（`hWS`，WindowSeed 路线待 R-C11-18 (i)/(ii)；
SEEDCL2 G3 = 路线 (i) 归纳步，缺 base case）；中心端点 Ricci `hRic`（`Ric ≤ 3/ℓ²`，取 `ℓ = 32θ/(L√R_n)` 时
`≈ L²R_n` 尺度，非 BCBD；OPEN，owner DIST）；FRESH supply（PBKAPPA）与 `hdistQC`（owner HDISTC）。

## 量词账目（lead 22:5x，R-C11-18 补充）

HSCALE 合同 `WindowNeckScaleBudget_P6HS H p T₀ a R`（`P6WindowScaleP6HS.lean:74`）=
`∀ e, T₀ ≤ τ_e → a < τ_e → R ≤ ρ(τ_e)⁻²`：**没有 `τ_e ≤ σ` 上界**，覆盖所有满足下界的后续 event（含 `σ`、`Tn`
之后的尾部）。producer 若只在短窗 `(a, σ]` 或 `(a, Tn]` 上证，须另补尾部论证；PARAMCOMPAT 的 δ-弱化路线
（`neckDelta_le_of_paramCompat_P6PC`）在 `τ > Tn` 支用 `ρ` antitone（合同第一分量）付尾部，零步形
`windowNeckScaleBudget_of_noStep_P6PC` 同理。本文件的中心邻域合同只在 `v ≤ σ` 的 slice / 窗口时刻上取值，
不消费 HSCALE 合同。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

section Consumer

variable {K : ℕ → RetainedCoreHistory.{u}}
  {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
  {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
  {pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier}
  {seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
    ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)}
  {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {eps C1 C2 : ℝ}
  {Ctime : ℝ≥0} {Cg : ℝ}

/-- **G2 filter 级 consumer（`_P6PS`，PROVISIONAL[`hWS`、`hRic` 在 `l` 上；FRESH supply]）**：T1 核心形
`hsliceR_lateHI_core_pickedCenter_C11PT` 的 hPC 槽（任意 `l ≤ atTop`）⇐ hgood + 核心形 `hdl` + `hWS` + `hRic`
+ FRESH。`Dd + Rad ≤ 0` 走 `pickedCenterNeighborhood_of_nonpos_P6PS`；否则逐 `n` 调
`pickedCenterNeighborhood_of_hgood_fresh_P6PS`（`hLR` ⇐ `hℓL` + `L ≥ 2(Dd + Rad)`，`hTL` ⇐ `L ≥ 1`、
`L ≥ θ₀ − σ₁`，`haS` ⇐ `hwin`，`hdl` 的 `σ − (−σ₁)/R` ↔ `σ + σ₁/R`）。 -/
theorem hPC_filter_of_hgood_fresh_P6PS
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctime)
    {θ₀ κ : ℝ} (hθ₀ : 0 < θ₀) (hκ : 0 ≤ κ) {Cgrad : ℝ≥0} (hC2 : C2 ≤ (Cgrad : ℝ))
    (hRpos : ∀ n, 0 < R n) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    {nr : ℝ → ℝ} {Aκ Tκ : ℝ}
    (O : ∀ n (j' : Fin (K n).eventCount), ((K n).stage j'.castSucc).Carrier)
    (hO : ∀ n (j' : Fin (K n).eventCount)
      (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
      (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n)),
      O n j' = (seedTrace n).point j'.castSucc h1 h2)
    (hWK : ∀ n, KappaSeedWindowFwd_C11PK nr Aκ κ Tκ (K n).toHistory)
    (ρV r ℓ : ℕ → ℝ) (hTκ : ∀ᶠ n in atTop, Tκ ≤ (Tn n : ℝ))
    (htimeS : ∀ n, 2 * r n ^ 2 < (Tn n : ℝ))
    (hsmallS : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) (r n))
    (hvolS : ∀ n, ENNReal.ofReal (Aκ⁻¹ * r n ^ 3) ≤ ballVolume ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (Tn n)) (Tn n)) (pT n) (r n))
    (hnrS : ∀ n (w : ℝ), (Tn n : ℝ) - r n ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr w ≤ r n)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hwinF : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ) - T / R n)
    (hρr : ∀ᶠ n in atTop, ρV n < r n / 100)
    (hdσ : ∀ᶠ n in atTop,
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r n))
    (hℓ : ∀ n, 0 < ℓ n) (hℓL : ∀ᶠ n in atTop, 32 * θ₀ ≤ L n * (ℓ n * Real.sqrt (R n)))
    {l : Filter ℕ} (hl : l ≤ atTop) {Dw Dd Rad σ₁ : ℝ} (hσ₁ : σ₁ < 0)
    (hdl : ∀ᶠ n in l,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
          (σ n : ℝ) + σ₁ / R n ≤ v →
        ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
            ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvs) x,
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              ((seedTrace n).point ((K n).toHistory.activeStage v)
                  ((K n).toHistory.activeStage_mono hav)
                ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
              (tr.point ((K n).toHistory.activeStage v) le_rfl
                  ((K n).toHistory.activeStage_mono hvs)) ≤
            riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
                (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (hWS : ∀ᶠ n in l,
      PickedCenterWindowSeed_C11PT Dw (Dd + Rad) (-σ₁) θ₀ (R n) (Cg * R n) (K n) (σ n) (y n)
        (O n) (riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
             (σ n))
           ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
             ((K n).toHistory.activeStage_mono (has n))
             ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / Real.sqrt (R n))))
    (hRic : ∀ᶠ n in l,
      ∀ (j' : Fin (K n).eventCount) (v : ℝ), (K n).time j'.castSucc < v →
        v < (K n).time j'.succ → (σ n : ℝ) - -σ₁ / R n ≤ v → v ≤ σ n →
      ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (K n).toHistory.activeStage (σ n))
        (tr : BackwardPointTrace (K n).toHistory j'.castSucc
          ((K n).toHistory.activeStage (σ n)) hjσ x₁),
      ∀ x ∈ riemannianBallOf (((K n).toHistory.event j').incoming.flow.base.metric v)
          (tr.point j'.castSucc le_rfl hjσ) ((Dd + Rad) / Real.sqrt (R n)),
      ∀ (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n)),
      ∀ t : ℝ, v - θ₀ / R n < t → t < v → (K n).time j'.castSucc < t →
      ∀ (yy : ((K n).stage j'.castSucc).Carrier) (ξ : TangentSpace ThreeModel yy),
        (riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric t)
            ((seedTrace n).point j'.castSucc h1 h2) yy < ENNReal.ofReal (ℓ n) ∨
          riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric t) x yy <
            ENNReal.ofReal (ℓ n)) →
        ricciTensor (((K n).toHistory.event j').incoming.flow.base.metric t) yy ξ ξ ≤
          (3 / (ℓ n) ^ 2) * (((K n).toHistory.event j').incoming.flow.base.metric t).inner yy ξ ξ) :
    ∀ᶠ n in l, PickedCenterNeighborhood_C11PT Dw (Dd + Rad) (-σ₁) θ₀ (R n) (Cg * R n) (ρV n) κ
      eps C1 C2 Cgrad (K n) (σ n) (y n) := by
  have hT : 0 < -σ₁ + θ₀ := by linarith
  have hLev : ∀ᶠ n in l, max 1 (max (-σ₁ + θ₀) (2 * (Dd + Rad))) ≤ L n :=
    hl (hL.eventually_ge_atTop _)
  filter_upwards [hdl, hWS, hRic, hLev, hl (hwin _ hT), hl hTκ, hl (hwinF _ hT), hl hρr, hl hdσ,
    hl hℓL] with n hdln hWSn hRicn hLn haSn hTκn hwinFn hρn hdσn hℓLn
  rcases le_or_gt (Dd + Rad) 0 with hDc | hDc
  · exact pickedCenterNeighborhood_of_nonpos_P6PS (K n) (σ n) (y n) hDc
  have hRn := hRpos n
  have hs : 0 < Real.sqrt (R n) := Real.sqrt_pos.2 hRn
  have hℓs : 0 < ℓ n * Real.sqrt (R n) := mul_pos (hℓ n) hs
  have hL1 : 1 ≤ L n := (le_max_left _ _).trans hLn
  have hL2 : -σ₁ + θ₀ ≤ L n := ((le_max_left _ _).trans (le_max_right _ _)).trans hLn
  have hL3 : 2 * (Dd + Rad) ≤ L n := ((le_max_right _ _).trans (le_max_right _ _)).trans hLn
  have h8 : 8 * θ₀ / (ℓ n * Real.sqrt (R n)) ≤ L n / 4 := by
    rw [div_le_iff₀ hℓs]
    nlinarith [hℓLn]
  have hLR : 4 * ((Dd + Rad) + 8 * θ₀ / (ℓ n * Real.sqrt (R n))) ≤ 3 * L n := by linarith
  have hTL : -σ₁ + θ₀ ≤ L n ^ 2 := by nlinarith [hL1, hL2]
  refine pickedCenterNeighborhood_of_hgood_fresh_P6PS (haT := haT) (hsT := hsT) (has := has)
    hgood n hRn hDc.le hθ₀.le (hℓ n) hLR hTL haSn le_rfl hC2 ?_ (O n) (hO n) hWSn (hWK n) hTκn
    (htimeS n) (hsmallS n) (hvolS n) (hnrS n) (hclock n) hwinFn hρn hκ hdσn hRicn
  intro x hx v hav hvs hv tr
  refine hdln x hx v hav hvs ?_ tr
  rwa [neg_div, sub_neg_eq_add] at hv

/-- **G2 family 级 consumer（`_P6PS`，PROVISIONAL[`hWSF`、`hRicF` 族；FRESH supply；`hdistQC`]）**：
`shallowSliceRC_of_pickedCenter_C11PT` 的 `hPC` 槽**逐字**（量词前缀 `Rad σ₁ σ₂ φ Dw Dd T Kc` + traced-region
前提）。`hdl` 由同一个 `hdistQC`（`L/4`，`T > −σ₁` ⇒ `σ − T/R ≤ σ + σ₁/R`）转出，其余交给
`hPC_filter_of_hgood_fresh_P6PS`（`l := map φ atTop`）。 -/
theorem hPC_of_hgood_fresh_P6PS
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctime)
    {θ₀ κ : ℝ} (hθ₀ : 0 < θ₀) (hκ : 0 ≤ κ) {Cgrad : ℝ≥0} (hC2 : C2 ≤ (Cgrad : ℝ))
    (hRpos : ∀ n, 0 < R n) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    {nr : ℝ → ℝ} {Aκ Tκ : ℝ}
    (O : ∀ n (j' : Fin (K n).eventCount), ((K n).stage j'.castSucc).Carrier)
    (hO : ∀ n (j' : Fin (K n).eventCount)
      (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
      (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n)),
      O n j' = (seedTrace n).point j'.castSucc h1 h2)
    (hWK : ∀ n, KappaSeedWindowFwd_C11PK nr Aκ κ Tκ (K n).toHistory)
    (ρV r ℓ : ℕ → ℝ) (hTκ : ∀ᶠ n in atTop, Tκ ≤ (Tn n : ℝ))
    (htimeS : ∀ n, 2 * r n ^ 2 < (Tn n : ℝ))
    (hsmallS : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) (r n))
    (hvolS : ∀ n, ENNReal.ofReal (Aκ⁻¹ * r n ^ 3) ≤ ballVolume ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (Tn n)) (Tn n)) (pT n) (r n))
    (hnrS : ∀ n (w : ℝ), (Tn n : ℝ) - r n ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr w ≤ r n)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hwinF : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ) - T / R n)
    (hρr : ∀ᶠ n in atTop, ρV n < r n / 100)
    (hdσ : ∀ᶠ n in atTop,
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r n))
    (hℓ : ∀ n, 0 < ℓ n) (hℓL : ∀ᶠ n in atTop, 32 * θ₀ ≤ L n * (ℓ n * Real.sqrt (R n)))
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
    (hWSF : ∀ Rad σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n)
        (2 * Dw / Real.sqrt (R n)) (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      PickedCenterWindowSeed_C11PT Dw (Dd + Rad) (-σ₁) θ₀ (R n) (Cg * R n) (K n) (σ n) (y n)
        (O n) (riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
             (σ n))
           ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
             ((K n).toHistory.activeStage_mono (has n))
             ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / Real.sqrt (R n))))
    (hRicF : ∀ Rad σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n)
        (2 * Dw / Real.sqrt (R n)) (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (j' : Fin (K n).eventCount) (v : ℝ), (K n).time j'.castSucc < v →
        v < (K n).time j'.succ → (σ n : ℝ) - -σ₁ / R n ≤ v → v ≤ σ n →
      ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (K n).toHistory.activeStage (σ n))
        (tr : BackwardPointTrace (K n).toHistory j'.castSucc
          ((K n).toHistory.activeStage (σ n)) hjσ x₁),
      ∀ x ∈ riemannianBallOf (((K n).toHistory.event j').incoming.flow.base.metric v)
          (tr.point j'.castSucc le_rfl hjσ) ((Dd + Rad) / Real.sqrt (R n)),
      ∀ (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n)),
      ∀ t : ℝ, v - θ₀ / R n < t → t < v → (K n).time j'.castSucc < t →
      ∀ (yy : ((K n).stage j'.castSucc).Carrier) (ξ : TangentSpace ThreeModel yy),
        (riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric t)
            ((seedTrace n).point j'.castSucc h1 h2) yy < ENNReal.ofReal (ℓ n) ∨
          riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric t) x yy <
            ENNReal.ofReal (ℓ n)) →
        ricciTensor (((K n).toHistory.event j').incoming.flow.base.metric t) yy ξ ξ ≤
          (3 / (ℓ n) ^ 2) * (((K n).toHistory.event j').incoming.flow.base.metric t).inner yy ξ ξ) :
    ∀ Rad σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n)
        (2 * Dw / Real.sqrt (R n)) (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      PickedCenterNeighborhood_C11PT Dw (Dd + Rad) (-σ₁) θ₀ (R n) (Cg * R n) (ρV n) κ eps C1 C2
        Cgrad (K n) (σ n) (y n) := by
  intro Rad σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd hT hKc htr
  refine hPC_filter_of_hgood_fresh_P6PS hgood hθ₀ hκ hC2 hRpos hL hwin O hO hWK ρV r ℓ hTκ htimeS
    hsmallS hvolS hnrS hclock hwinF hρr hdσ hℓ hℓL hφ.tendsto_atTop (by linarith) ?_
    (hWSF Rad σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd hT hKc htr)
    (hRicF Rad σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd hT hKc htr)
  filter_upwards [hdistQC φ hφ Dw T Kc hDw (by linarith) hKc htr] with n hn
  intro x hx v hav hvs hv tr
  refine hn x hx v hav hvs ?_ tr
  have h1 : -T / R n ≤ σ₁ / R n := div_le_div_of_nonneg_right (by linarith) (hRpos n).le
  rw [sub_eq_add_neg, ← neg_div]
  linarith

end Consumer

section Core

/-- **G2 core 级 consumer（`_P6PS`，PROVISIONAL[`hWS`、`hRic` 在 `l` 上；FRESH supply]）**：
`hsliceR_lateHI_core_pickedCenter_C11PT` 的结论逐字（其余 binder 逐字），只把核心形里的 hPC 前提
`∀ᶠ n in l, PickedCenterNeighborhood_C11PT …` 换成同一 `l` 上的 `hWS`（`PickedCenterWindowSeed_C11PT`）+
`hRic`（中心端点 Ricci）；新增 hgood（独立 `Ctg`）、`C2 ≤ Cgrad`、seed 位置 `O`/`hO`、FRESH（`Aκ`）。
证明 = C11PT 核心形 + `hPC_filter_of_hgood_fresh_P6PS`。 -/
theorem ObservedHistory.hsliceR_lateHI_core_pickedCenter_hgood_P6PS
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {Cg : ℝ} (hCg : 1 ≤ Cg) {η₃ Lc : ℝ}
    (hη₃ : 0 < η₃) (hLc : 0 < Lc)
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
    {Ctg : ℝ≥0}
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L ε C1 C2 Ctg)
    (hC2 : C2 ≤ (Cgrad : ℝ)) {nr : ℝ → ℝ} {Aκ Tκ : ℝ}
    (O : ∀ n (j' : Fin (K n).eventCount), ((K n).stage j'.castSucc).Carrier)
    (hO : ∀ n (j' : Fin (K n).eventCount)
      (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
      (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n)),
      O n j' = (seedTrace n).point j'.castSucc h1 h2)
    (hWK : ∀ n, KappaSeedWindowFwd_C11PK nr Aκ κ Tκ (K n).toHistory)
    (r ℓ : ℕ → ℝ) (hTκ : ∀ᶠ n in atTop, Tκ ≤ (Tn n : ℝ))
    (htimeS : ∀ n, 2 * r n ^ 2 < (Tn n : ℝ))
    (hsmallS : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) (r n))
    (hvolS : ∀ n, ENNReal.ofReal (Aκ⁻¹ * r n ^ 3) ≤ ballVolume ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (Tn n)) (Tn n)) (pT n) (r n))
    (hnrS : ∀ n (w : ℝ), (Tn n : ℝ) - r n ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr w ≤ r n)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hwinF : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ) - T / R n)
    (hρr : ∀ᶠ n in atTop, ρV n < r n / 100)
    (hdσ : ∀ᶠ n in atTop,
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r n))
    (hℓ : ∀ n, 0 < ℓ n) (hℓL : ∀ᶠ n in atTop, 32 * θ₀ ≤ L n * (ℓ n * Real.sqrt (R n))) :
    ∀ A Dd : ℝ, 1 ≤ A → 0 < Dd → ∃ QB Dcap D₂ Rad : ℝ, 0 ≤ QB ∧
      Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1) ≤ D₂ ∧
      ∀ l : Filter ℕ, l ≤ atTop → ∀ σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw : ℝ, 0 < Dw →
      (∀ᶠ n in l,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) + σ₁ / R n ≤ v →
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
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n))) →
      (∀ᶠ n in l,
      PickedCenterWindowSeed_C11PT Dw (Dd + Rad) (-σ₁) θ₀ (R n) (Cg * R n) (K n) (σ n) (y n)
        (O n) (riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
             (σ n))
           ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
             ((K n).toHistory.activeStage_mono (has n))
             ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / Real.sqrt (R n)))) →
      (∀ᶠ n in l,
      ∀ (j' : Fin (K n).eventCount) (v : ℝ), (K n).time j'.castSucc < v →
        v < (K n).time j'.succ → (σ n : ℝ) - -σ₁ / R n ≤ v → v ≤ σ n →
      ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (K n).toHistory.activeStage (σ n))
        (tr : BackwardPointTrace (K n).toHistory j'.castSucc
          ((K n).toHistory.activeStage (σ n)) hjσ x₁),
      ∀ x ∈ riemannianBallOf (((K n).toHistory.event j').incoming.flow.base.metric v)
          (tr.point j'.castSucc le_rfl hjσ) ((Dd + Rad) / Real.sqrt (R n)),
      ∀ (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n)),
      ∀ t : ℝ, v - θ₀ / R n < t → t < v → (K n).time j'.castSucc < t →
      ∀ (yy : ((K n).stage j'.castSucc).Carrier) (ξ : TangentSpace ThreeModel yy),
        (riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric t)
            ((seedTrace n).point j'.castSucc h1 h2) yy < ENNReal.ofReal (ℓ n) ∨
          riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric t) x yy <
            ENNReal.ofReal (ℓ n)) →
        ricciTensor (((K n).toHistory.event j').incoming.flow.base.metric t) yy ξ ξ ≤
          (3 / (ℓ n) ^ 2) * (((K n).toHistory.event j').incoming.flow.base.metric t).inner yy ξ ξ) →
      ∀ᶠ n in l,
      ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hvt : v ≤ σ n), (σ n : ℝ) + σ₁ / R n ≤ v →
        (v : ℝ) ≤ σ n + σ₂ / R n → (K n).toHistory.time ((K n).toHistory.activeStage v) < v →
      ∀ tr₁ : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
          ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvt) x₁,
        metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
          (tr₁.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono hvt))
              ≤ A * R n →
        ∃ CWP : ((K n).toHistory.stage ((K n).toHistory.activeStage v)).Carrier → Prop,
          (∀ w, riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              (tr₁.point ((K n).toHistory.activeStage v) le_rfl
                  ((K n).toHistory.activeStage_mono hvt)) w <
              ENNReal.ofReal (Dd / Real.sqrt (R n)) → ¬ CWP w →
            R n ≤ metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
                w → ∀ x,
            riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) w x <
              ENNReal.ofReal ((2 * Dd * Real.sqrt A + 1) /
                Real.sqrt (metricScalarAt ((K n).toHistory.stageMetric
                    ((K n).toHistory.activeStage v) v) w)) →
            metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) x ≤
              QB * metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
                  w) ∧
          (∀ w, riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              (tr₁.point ((K n).toHistory.activeStage v) le_rfl
                  ((K n).toHistory.activeStage_mono hvt)) w <
              ENNReal.ofReal (Dd / Real.sqrt (R n)) → CWP w →
            ∃ (Ξ : standardCapWindow D₂ → ((K n).toHistory.stage
                ((K n).toHistory.activeStage v)).Carrier)
              (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) (z₀ : standardCapWindow D₂),
              Injective Ξ ∧ Ξ z₀ = w ∧ ‖z₀.val‖ < Dcap + 1 ∧
              ∃ (lam : ℝ) (hlam : 0 < lam) (Q : StandardSolution) (τw : ℝ),
                τw ∈ Icc (0 : ℝ) (1 / 2) ∧
                ∀ (u : standardCapWindow D₂) (m : ℕ), m ≤ 2 →
                  metricDerivNorm m (localPullMetric (scaleMetric lam hlam
                      ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)) Ξ hΞ)
                    ((Q.val.metric τw).restrictOpen (standardCapWindow D₂))
                    (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η₃) := by
  intro A Dd hA hDd
  obtain ⟨QB, Dcap, D₂, Rad, hQB, hD₂, hcore⟩ :=
    ObservedHistory.hsliceR_lateHI_core_pickedCenter_C11PT (C1 := C1) (C2 := C2) (Cgrad := Cgrad)
      hθ₀ hεle hκ hphi hCg hη₃ hLc htj recordsF hHI hcanK hδF hacc hrad hord hscaleK hbirthA
      hpinchK0 hslabK σ y R hσ hRpos hqR hT₀ Tn aSeed haT hsT has pT seedTrace L hL hwin ρV hρV
      A Dd hA hDd
  refine ⟨QB, Dcap, D₂, Rad, hQB, hD₂, fun l hl σ₁ σ₂ h12 hσ₂ Dw hDw hdl hWS hRic => ?_⟩
  exact hcore l hl σ₁ σ₂ h12 hσ₂ Dw hDw hdl
    (hPC_filter_of_hgood_fresh_P6PS hgood hθ₀ hκ.le hC2 hRpos hL hwin O hO hWK ρV r ℓ hTκ
      htimeS hsmallS hvolS hnrS hclock hwinF hρr hdσ hℓ hℓL hl (by linarith) hdl hWS hRic)

/-- **G2 consumer（SHALLOW T1 壳，`_P6PS`，PROVISIONAL[`hWSF`、`hRicF` 族；FRESH supply；`hdistQC`]）**：
`shallowSliceRC_of_pickedCenter_C11PT` 的陈述逐字，`hPC` 合同族换成 `hWSF` + `hRicF`（同一量词前缀）+
hgood（独立 `Ctg`）+ FRESH；`hPC` 由 `hPC_of_hgood_fresh_P6PS`（同一 `hdistQC`）产出后喂 C11PT。
结论 = `ShallowSliceRC_C11SH` 逐字。 -/
theorem ObservedHistory.shallowSliceRC_of_hgood_fresh_P6PS
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {Cg : ℝ} (hCg : 1 ≤ Cg) {η₃ Lc : ℝ}
    (hη₃ : 0 < η₃) (hLc : 0 < Lc)
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
    {Ctg : ℝ≥0}
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L ε C1 C2 Ctg)
    (hC2 : C2 ≤ (Cgrad : ℝ)) {nr : ℝ → ℝ} {Aκ Tκ : ℝ}
    (O : ∀ n (j' : Fin (K n).eventCount), ((K n).stage j'.castSucc).Carrier)
    (hO : ∀ n (j' : Fin (K n).eventCount)
      (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
      (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n)),
      O n j' = (seedTrace n).point j'.castSucc h1 h2)
    (hWK : ∀ n, KappaSeedWindowFwd_C11PK nr Aκ κ Tκ (K n).toHistory)
    (r ℓ : ℕ → ℝ) (hTκ : ∀ᶠ n in atTop, Tκ ≤ (Tn n : ℝ))
    (htimeS : ∀ n, 2 * r n ^ 2 < (Tn n : ℝ))
    (hsmallS : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) (r n))
    (hvolS : ∀ n, ENNReal.ofReal (Aκ⁻¹ * r n ^ 3) ≤ ballVolume ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (Tn n)) (Tn n)) (pT n) (r n))
    (hnrS : ∀ n (w : ℝ), (Tn n : ℝ) - r n ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr w ≤ r n)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hwinF : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ) - T / R n)
    (hρr : ∀ᶠ n in atTop, ρV n < r n / 100)
    (hdσ : ∀ᶠ n in atTop,
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r n))
    (hℓ : ∀ n, 0 < ℓ n) (hℓL : ∀ᶠ n in atTop, 32 * θ₀ ≤ L n * (ℓ n * Real.sqrt (R n)))
    (hWSF : ∀ Rad σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n)
        (2 * Dw / Real.sqrt (R n)) (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      PickedCenterWindowSeed_C11PT Dw (Dd + Rad) (-σ₁) θ₀ (R n) (Cg * R n) (K n) (σ n) (y n)
        (O n) (riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
             (σ n))
           ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
             ((K n).toHistory.activeStage_mono (has n))
             ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / Real.sqrt (R n))))
    (hRicF : ∀ Rad σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n)
        (2 * Dw / Real.sqrt (R n)) (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (j' : Fin (K n).eventCount) (v : ℝ), (K n).time j'.castSucc < v →
        v < (K n).time j'.succ → (σ n : ℝ) - -σ₁ / R n ≤ v → v ≤ σ n →
      ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (K n).toHistory.activeStage (σ n))
        (tr : BackwardPointTrace (K n).toHistory j'.castSucc
          ((K n).toHistory.activeStage (σ n)) hjσ x₁),
      ∀ x ∈ riemannianBallOf (((K n).toHistory.event j').incoming.flow.base.metric v)
          (tr.point j'.castSucc le_rfl hjσ) ((Dd + Rad) / Real.sqrt (R n)),
      ∀ (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n)),
      ∀ t : ℝ, v - θ₀ / R n < t → t < v → (K n).time j'.castSucc < t →
      ∀ (yy : ((K n).stage j'.castSucc).Carrier) (ξ : TangentSpace ThreeModel yy),
        (riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric t)
            ((seedTrace n).point j'.castSucc h1 h2) yy < ENNReal.ofReal (ℓ n) ∨
          riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric t) x yy <
            ENNReal.ofReal (ℓ n)) →
        ricciTensor (((K n).toHistory.event j').incoming.flow.base.metric t) yy ξ ξ ≤
          (3 / (ℓ n) ^ 2) * (((K n).toHistory.event j').incoming.flow.base.metric t).inner yy ξ ξ) :
    ObservedHistory.ShallowSliceRC_C11SH η₃ Lc (fun n => (K n).toHistory) σ y R := by
  exact ObservedHistory.shallowSliceRC_of_pickedCenter_C11PT (C1 := C1) (C2 := C2)
    (Cgrad := Cgrad) hθ₀ hεle hκ hphi hCg hη₃ hLc htj recordsF hHI hcanK hδF hacc hrad hord
    hscaleK hbirthA hpinchK0 hslabK σ y R hσ hRpos hqR hT₀ Tn aSeed haT hsT has pT seedTrace L hL
    hwin ρV hρV hdistQC
    (hPC_of_hgood_fresh_P6PS hgood hθ₀ hκ.le hC2 hRpos hL hwin O hO hWK ρV r ℓ hTκ htimeS hsmallS
      hvolS hnrS hclock hwinF hρr hdσ hℓ hℓL hdistQC hWSF hRicF)

end Core

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

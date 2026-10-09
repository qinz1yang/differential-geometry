import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HbcadCFinalBodyTruncKFPHFT
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvResEngineSupplyHNS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KframeHelpersDrvHI
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DepthDriverAnyPosLocalP6DP4C2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HIPropagationP6HP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KernelSlabKTSupplyP6KT
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KernelBRowsA6K
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HpinRescaledP6HI

set_option autoImplicit false

/-!
# R4BCAD G1：R4 帧 hbcadC 的 producer（后缀 `_R4B`）

主定理 `hbcadC_R4center_Rc_R4B`（中心归一化泛型）：HTRSPAY R4 driver 的 hbcadC 残余，在 E2a′ 回调环境
（R4 中心 `(t, y′)`）内由 HFINDT G1 `hbcadC_final_of_guarded2T_HFT`（中心泛型，取 σ := t、y := y′、
归一化 := `Rc`、`Cg := 8`）付出。`Rc` 只需 `R/2 < Rc < 2R`、`k + 1 ≤ Rc k`、`√Rc → ∞`（R4NORM 取
`Rc = scalar(t, y′)`；HTP 现形取 `Rc := R`，即推论 `hbcadC_R4center_R4B`）；σ 侧数据（gate、天花板、
recent records、hgood′ 窗）仍以 σ 处 `R` 陈述；`σ − t ≤ Cc/R`、`d_t ≤ d_σ + B/√R`（常数 `Cc, B ≥ 0`）。
三项缺口：
(1) `hdistσ@t` ⇐ `hcompR` + σ 处 gate（`ofReal_div_sqrt_Rc_le_R4B` 因子 2 转换，`2L′ ≤ L − 2 − B`）；
    同源的 `hfinK`（`d_t ≠ ⊤`）⇐ `ne_top_of_comp_gate_R4B`；
(2) `∀ n` 的 `hroom@t` ⇐ 重选 `L′ := max 0 (min ((L − 2 − B)/2) √(max 0 (R(t − Tn + ½))/2))`（→ ∞）与逐 n
    半径 `r n := max 1 √(2(Tn − t + L′²/Rc))`（`∀ n` 室条件代数成立，eventually `r n = 1`）；
(3) 细 recordsK 包 ⇐ HNRSUP `drvResE_records_of_engine_HNS`（以 σ 处 `R` 调用，hrcs := recent 供给逐字；
    `Θ` 在 `∃ Θ` 处输出，由调用方并入 E2a′ 阈值序列；`σ̂ := max t (Tn − ½ + L′²/R)`，eventually `σ̂ = t`）。
其余：κ 族 ⇐ FRESH `hκR_K_DH` / `hκRF_K_DH`；`hslabK` / `hderF` ⇐ `hkernelDtT_of_supply_P6KT`；
pinching ⇐ `hpinch_of_initial_P6HP`；`hdistQC` ⇐ `hdistQC_anyPos_eventually_P6DP4C2`（中心 `(t, y′)`）。
无新 binder：前提全是 HTP driver 已有环境项（recent / hfine / TDS / FRESH / hanti / hδq）与回调字段。
生成器 build-logs/scratch/R4BCAD/gen/gG1b.py（+ gG1p.py）。
-/

noncomputable section

open Set Filter Function Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- 因子 2 转换（`_R4B`，PROVED）：`R/2 < Rc` ⇒ `x/Rc ≤ 2x/R`（`x ≥ 0`）。 -/
theorem div_Rc_le_R4B {R Rc x : ℝ} (hR : 0 < R) (h : R / 2 < Rc) (hx : 0 ≤ x) :
    x / Rc ≤ 2 * x / R := by
  have hRc : 0 < Rc := by linarith
  rw [div_le_div_iff₀ hRc hR]
  nlinarith

/-- 因子 2 转换（`_R4B`，PROVED）：`R/2 < Rc` ⇒ `ofReal (x/√Rc) ≤ ofReal (2x/√R)`（`x ≥ 0`）。 -/
theorem ofReal_div_sqrt_Rc_le_R4B {R Rc x : ℝ} (hR : 0 < R) (h : R / 2 < Rc) (hx : 0 ≤ x) :
    ENNReal.ofReal (x / Real.sqrt Rc) ≤ ENNReal.ofReal (2 * x / Real.sqrt R) := by
  have hRc : 0 < Rc := by linarith
  refine ENNReal.ofReal_le_ofReal ?_
  have h4 : Real.sqrt R ≤ 2 * Real.sqrt Rc := by
    have h1 : Real.sqrt R ≤ Real.sqrt (2 ^ 2 * Rc) := Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)] at h1
  rw [div_le_div_iff₀ (Real.sqrt_pos.2 hRc) (Real.sqrt_pos.2 hR)]
  nlinarith [Real.sqrt_nonneg R]

/-- **hfinK（`_R4B`，PROVED）**：R4 中心距离有限——`d_t(seed, y′) ≤ d_σ(seed, y) + ofReal u` 与
σ 处 gate `d_σ + ofReal v ≤ ofReal w` ⇒ `d_t ≠ ⊤`（R4J10 的 `hfinK` 与 hdistσ@t 同源）。 -/
theorem ne_top_of_comp_gate_R4B {dt ds : ℝ≥0∞} {u v w : ℝ} (hcomp : dt ≤ ds + ENNReal.ofReal u)
    (hgate : ds + ENNReal.ofReal v ≤ ENNReal.ofReal w) : dt ≠ ⊤ := by
  have hds : ds ≠ ⊤ := fun h => by
    rw [h, top_add] at hgate
    exact ENNReal.ofReal_ne_top (top_le_iff.mp hgate)
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hds, ENNReal.ofReal_ne_top⟩) hcomp

/-- **R4 帧 hbcadC producer，中心归一化泛型版（`_R4B`）**：结论以中心归一化序列 `Rc` 陈述
（R4NORM：`Rc k = scalar(t k, y′ k)`，`R/2 < Rc < 2R`）；σ 侧数据（gate、天花板、recent records、hgood′ 窗）
仍以 σ 处 `R` 陈述；`σ − t ≤ Cc/R`、`d_t ≤ d_σ + B/√R`。`Θ` 只依赖引擎数据，调用方须保证 `Θ k ≤ c k · Tn k`。 -/
theorem hbcadC_R4center_Rc_R4B {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hεle : ε ≤ coneAccuracy) (hC2 : 0 ≤ C2)
    (q : CutoffParameters) (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hδq : Tendsto q.delta atTop (𝓝 0))
    (recQ : ∀ n (e : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory e q)
    (hrecent : ∀ ε' : ℝ, 0 < ε' → ∃ T : ℝ, 0 < T ∧ ∀ t, T ≤ t →
      ∀ n (i : Fin (F.tower.history n).eventCount),
      (F.tower.history n).time i.succ ∈ Icc (t / 2) t →
      ∀ h, (recQ n i).nominalRadius h ≤ ε' * q.neckRadius t)
    (hfine : ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T₀ : ℝ, ∀ n, ∃ p : CutoffParameters,
      D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
      ∃ records' : ∀ i : Fin (F.tower.history n).eventCount,
          T₀ ≤ (F.tower.history n).time i.succ →
          GeometricCutoffRecord (F.tower.history n).toHistory i p,
        (∀ i hi b, ((records' i hi).static b).hasCanonicalWindow) ∧
        ∀ i hi b, ((records' i hi).static b).neck.scale = ((recQ n i).static b).neck.scale)
    (hTD : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hsupA : ∀ Aseed : ℝ, 1 < Aseed → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ,
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) (k : ℕ),
        KappaSeedWindowFwd_C11PK
          (fun w => q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k)) (Aseed + 7) κ
          (Tf / c k) ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory) :
    ∃ Θ : ℕ → ℝ, ∀ Aseed : ℝ, 1 < Aseed →
    ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
      let Kh : ℕ → ObservedHistory.{u} := fun k =>
        ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
      ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
        (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
      ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
        (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
        (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        (∀ k, ENNReal.ofReal (Aseed⁻¹ * 1 ^ 3) ≤
          riemannianVolumeMeasure ThreeModel ((Kh k).stageAt (Tn k)).Carrier
            ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k))
            (riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k))
              (pT k) 1)) →
        (∀ k, 2 < (Tn k : ℝ)) →
        (∀ k (w : ℝ), (Tn k : ℝ) - 1 ^ 2 / 2 ≤ w → w ≤ (Tn k : ℝ) →
          q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k) ≤ 1) →
        (∀ k, Θ k ≤ c k * (Tn k : ℝ)) →
      ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
          ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
        (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
        (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
        (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
        Tendsto L atTop atTop →
        (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
        Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
        (∀ k,
          riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
              ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                ((Kh k).activeStage_mono (hsT k))) (y k) +
            ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((Aseed + 3) * 1)) →
        (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
      ∀ (t : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y' : ∀ k, ((Kh k).stageAt (t k)).Carrier)
        (hat : ∀ k, aSeed k ≤ t k) (hts : ∀ k, t k ≤ σ k) (Rc : ℕ → ℝ) (Cc B : ℝ),
        0 ≤ Cc → 0 ≤ B → (∀ k, R k / 2 < Rc k) → (∀ k, Rc k < 2 * R k) →
        (∀ k : ℕ, (k : ℝ) + 1 ≤ Rc k) → Tendsto (fun k => 1 / 200 * Real.sqrt (Rc k)) atTop atTop →
        (∀ k, (σ k : ℝ) - t k ≤ Cc / R k) →
        (∀ k, riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k))
            ((seedTrace k).point ((Kh k).activeStage (t k)) ((Kh k).activeStage_mono (hat k))
              ((Kh k).activeStage_mono ((hts k).trans (hsT k)))) (y' k) ≤
          riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
              ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                ((Kh k).activeStage_mono (hsT k))) (y k) +
            ENNReal.ofReal (B / Real.sqrt (R k))) →
        (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvt : v ≤ t k),
          (t k : ℝ) - (L k - 2) ^ 2 / R k ≤ (v : ℝ) →
          ∀ z : ((Kh k).stageAt v).Carrier,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                  ((Kh k).activeStage_mono (hvt.trans ((hts k).trans (hsT k))))) z ≤
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k))
                  ((seedTrace k).point ((Kh k).activeStage (t k))
                    ((Kh k).activeStage_mono (hat k))
                    ((Kh k).activeStage_mono ((hts k).trans (hsT k)))) (y' k) +
                ENNReal.ofReal ((L k - 2) / Real.sqrt (R k)) →
            4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
            (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
      ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T K : ℝ, -σ' < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (t n) (y' n) (2 * Dw / Real.sqrt (Rc n))
          (T / Rc n) (K * Rc n)) →
        ∀ᶠ n in map φ atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (t n)) (t n)) (y' n)
            (Dw / Real.sqrt (Rc n)),
        ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (t n)) (t n)) (y' n)
            (Dw / Real.sqrt (Rc n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ t n), (v : ℝ) = t n + σ' / Rc n →
        ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (t n))
            ((Kh n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (t n))
            ((Kh n).activeStage_mono hvt) x₂),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * Rc n →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (Rc n)) →
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤
            C * Rc n := by
  classical
  obtain ⟨a₀, ha₀, hHI0⟩ := exists_initialHI_P6WR F
  obtain ⟨ΘH, hΘH⟩ := drvResE_records_of_engine_HNS recQ hrecent hanti hδq hfine ha₀ hHI0
    (fun n => (n : ℝ) + 1) (fun n => 1 / ((n : ℝ) + 1)) (fun n => (n : ℝ) + 1)
    (fun n => 1 / ((n : ℝ) + 1)) (fun n => n + 2) (fun n => by positivity)
    (fun n => by positivity)
  obtain ⟨Phi, hPhi, hP⟩ := hpinch_of_initial_P6HP.{u} (A := (1 : ℝ)) one_pos
  obtain ⟨ε₁, hε₁, hQC⟩ := hdistQC_anyPos_eventually_P6DP4C2.{u}
  refine ⟨fun k => 2 * max 0 (ΘH k), ?_⟩
  intro Aseed hA ind c hc Kh Tn pT hTc aSeed haT hclock hone hsm hvol hTn2 hnrS hΘ seedTrace σ y
    R hsT has L hRpos hRr hL haS hroomT hgate hceil t y' hat hts Rc Cc B hCc hB hRc1 hRc2 hRcr
    hradiiC hclose hcompR hgood'
  let K : ℕ → RetainedCoreHistory.{u} := fun n =>
    (F.tower.history (ind n)).rescale_P6N (c n) (hc n)
  have hRcpos : ∀ n, 0 < Rc n := fun n => by linarith [hRc1 n, hRpos n]
  have hR1 : ∀ n, (1 : ℝ) ≤ Rc n := fun n => by
    have := hRcr n
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hRlim : Tendsto Rc atTop atTop :=
    tendsto_atTop_mono hRcr (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hdivRc : ∀ n (x : ℝ), 0 ≤ x → x / Rc n ≤ 2 * x / R n := fun n x hx =>
    div_Rc_le_R4B (hRpos n) (hRc1 n) hx
  have hsT' : ∀ n, t n ≤ Tn n := fun n => (hts n).trans (hsT n)
  have hwinR : ∀ T' : ℝ, 0 < T' → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ t n - T' / R n := by
    intro T' hT'
    filter_upwards [haS (T' + Cc) (by linarith)] with n hn
    have h1 := hclose n
    have h2 : (T' + Cc) / R n = T' / R n + Cc / R n := add_div _ _ _
    linarith
  have hwin' : ∀ T' : ℝ, 0 < T' → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ t n - T' / Rc n := by
    intro T' hT'
    filter_upwards [hwinR (2 * T') (by linarith)] with n hn
    have := hdivRc n T' hT'.le
    linarith
  -- (2) 重选 L′ 与逐 n 半径 rr
  have hX : Tendsto (fun n => R n * ((t n : ℝ) - ((Tn n : ℝ) - 1 / 2))) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) (tendsto_atTop_add_const_right atTop (-Cc) hroomT)
    have h1 : R n * ((σ n : ℝ) - t n) ≤ Cc := by
      have := hclose n
      rw [le_div_iff₀ (hRpos n)] at this
      linarith
    have e : R n * ((t n : ℝ) - ((Tn n : ℝ) - 1 / 2)) =
        R n * ((σ n : ℝ) - ((Tn n : ℝ) - 1 ^ (2 : ℕ) / 2)) - R n * ((σ n : ℝ) - t n) := by ring
    rw [e]
    linarith
  obtain ⟨L', hL'def⟩ : ∃ L' : ℕ → ℝ, ∀ n, L' n =
      max 0 (min ((L n - 2 - B) / 2)
        (Real.sqrt (max 0 (R n * ((t n : ℝ) - ((Tn n : ℝ) - 1 / 2))) / 2))) :=
    ⟨_, fun _ => rfl⟩
  have hL'0 : ∀ n, 0 ≤ L' n := fun n => by rw [hL'def]; exact le_max_left _ _
  have hL'L : ∀ n, L' n ≤ max 0 ((L n - 2 - B) / 2) := fun n => by
    rw [hL'def]; exact max_le_max le_rfl (min_le_left _ _)
  have hL'X : ∀ n, 2 * L' n ^ 2 ≤ max 0 (R n * ((t n : ℝ) - ((Tn n : ℝ) - 1 / 2))) := fun n => by
    have h1 : L' n ≤ Real.sqrt (max 0 (R n * ((t n : ℝ) - ((Tn n : ℝ) - 1 / 2))) / 2) := by
      rw [hL'def]
      exact max_le (Real.sqrt_nonneg _) (min_le_right _ _)
    have h2 := pow_le_pow_left₀ (hL'0 n) h1 2
    rw [Real.sq_sqrt (div_nonneg (le_max_left _ _) zero_le_two)] at h2
    linarith
  have hL'lim : Tendsto L' atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    have hs := (Real.tendsto_sqrt_atTop.comp ((tendsto_atTop_mono (fun n => le_max_right 0 _)
      hX).atTop_div_const two_pos)).eventually_ge_atTop b
    filter_upwards [hL.eventually_ge_atTop (2 * b + 2 + B), hs] with n h1 h2
    rw [hL'def]
    exact le_max_of_le_right (le_min (by linarith) h2)
  have hroomEv : ∀ᶠ n in atTop, (Tn n : ℝ) - 1 / 2 + 2 * L' n ^ 2 / R n ≤ t n := by
    filter_upwards [hX.eventually_ge_atTop 0] with n hn
    have h1 := hL'X n
    rw [max_eq_right hn] at h1
    have h2 : 2 * L' n ^ 2 / R n ≤ (t n : ℝ) - ((Tn n : ℝ) - 1 / 2) := by
      rw [div_le_iff₀ (hRpos n)]
      linarith
    linarith
  obtain ⟨rr, hrrdef⟩ : ∃ rr : ℕ → ℝ, ∀ n,
      rr n = max 1 (Real.sqrt (2 * ((Tn n : ℝ) - t n + L' n ^ 2 / Rc n))) := ⟨_, fun _ => rfl⟩
  have hrr1 : ∀ᶠ n in atTop, rr n = 1 := by
    filter_upwards [hroomEv] with n hn
    rw [hrrdef]
    refine max_eq_left ?_
    have h3 := hdivRc n (L' n ^ 2) (sq_nonneg _)
    have h : 2 * ((Tn n : ℝ) - t n + L' n ^ 2 / Rc n) ≤ 1 := by linarith
    exact (Real.sqrt_le_sqrt h).trans_eq Real.sqrt_one
  have hroomAll : ∀ n, (Tn n : ℝ) - rr n ^ 2 / 2 ≤ t n - L' n ^ 2 / Rc n := by
    intro n
    by_cases h : 0 ≤ 2 * ((Tn n : ℝ) - t n + L' n ^ 2 / Rc n)
    · have h1 : Real.sqrt (2 * ((Tn n : ℝ) - t n + L' n ^ 2 / Rc n)) ≤ rr n := by
        rw [hrrdef]; exact le_max_right _ _
      have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
      rw [Real.sq_sqrt h] at h2
      linarith
    · push Not at h
      have : 0 ≤ rr n ^ 2 := sq_nonneg _
      linarith
  obtain ⟨sh, hshdef⟩ : ∃ sh : ℕ → ℝ, ∀ n,
      sh n = max (t n : ℝ) ((Tn n : ℝ) - 1 ^ 2 / 2 + L' n ^ 2 / R n) := ⟨_, fun _ => rfl⟩
  have hshEv : ∀ᶠ n in atTop, sh n = t n := by
    filter_upwards [hroomEv] with n hn
    rw [hshdef]
    have := div_nonneg (sq_nonneg (L' n)) (hRpos n).le
    have e : 2 * L' n ^ 2 / R n = 2 * (L' n ^ 2 / R n) := by ring
    exact max_eq_left (by norm_num; linarith)
  -- (3) 细 records（HNRSUP，同元组；σ̂ := sh）
  have hρK : ∀ n, R n ≤ c n * (q.neckRadius (c n * (Tn n : ℝ)) ^ 2)⁻¹ := fun n => by
    rw [← RetainedCoreHistory.neckRadius_rescale_inv_sq_P6X (hc n) q (Tn n : ℝ)]
    exact hceil n
  have hTΘ : ∀ n, max 0 (ΘH n) ≤ c n * (Tn n : ℝ) / 2 := fun n => by
    have := hΘ n
    linarith
  have hT₀a : ∀ n, max 0 (ΘH n) ≤ c n * (aSeed n : ℝ) := fun n => by
    have h1 := hTΘ n
    have h2 : c n * (Tn n : ℝ) / 2 ≤ c n * (aSeed n : ℝ) := by
      rw [hclock n]
      have := hTn2 n
      have := hc n
      nlinarith
    linarith
  obtain ⟨pp, recKHo, hpacc, hpD, hpord, hcanHo, hδK, hscK, hbK, hHIK⟩ :=
    hΘH (fun n => max 0 (ΘH n)) (fun n => le_max_right _ _) ind c sh L' R
      (fun n => (Tn n : ℝ)) (fun n => c n * (Tn n : ℝ)) hc (fun _ => rfl)
      (fun n => (mul_pos (hc n) (by linarith [hTn2 n])).le)
      (fun n => by
        have := hTn2 n
        have := hc n
        change 2 * c n < c n * (Tn n : ℝ)
        nlinarith)
      (fun n => by
        have := hTΘ n
        have : 0 ≤ c n * (Tn n : ℝ) := (mul_pos (hc n) (by linarith [hTn2 n])).le
        change max 0 (ΘH n) ≤ c n * (Tn n : ℝ)
        linarith)
      (fun n => by
        show (Tn n : ℝ) - 1 ^ 2 / 2 ≤ sh n - L' n ^ 2 / R n
        have := le_max_right (t n : ℝ) ((Tn n : ℝ) - 1 ^ 2 / 2 + L' n ^ 2 / R n)
        rw [← hshdef] at this
        linarith)
      hRr hρK
  let T₀K : ℕ → ℝ := fun n =>
    max 1 (max (max 0 (ΘH n)) (c n * (sh n - L' n / R n)) / c n)
  let recK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i ((pp n).rescale_P6N (c n) (hc n)) :=
    fun n => (F.tower.history (ind n)).recordsKRescale_P6X3 (hc n) (recKHo n)
  have hcanK : ∀ n i hi b, ((recK n i hi).static b).hasCanonicalWindow := fun n =>
    (F.tower.history (ind n)).hcanK_rescale_P6X3 (hc n) (recKHo n) (hcanHo n)
  have hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1)
      ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ ≤
      ((recK n i hi).static b).neck.scale := fun n i hi b => by
    have h := hscK n i hi b
    simp only [max_self] at h
    exact h
  have hT₀K : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀K n ≤ (t n : ℝ) - T / Rc n := by
    intro T hT
    have hw : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ sh n - T / R n := fun T hT =>
      (hwinR T hT).mono fun n hn => by
        have := le_max_left (t n : ℝ) ((Tn n : ℝ) - 1 ^ 2 / 2 + L' n ^ 2 / R n)
        rw [← hshdef] at this
        linarith
    filter_upwards [t0K_tail_HNS (T₀ := fun n => max 0 (ΘH n)) (a := fun n => (aSeed n : ℝ))
      hc hRpos hT₀a hone hw hL'lim (2 * T) (by linarith), hshEv] with n h1 h2
    have h3 := hdivRc n T hT.le
    calc T₀K n ≤ sh n - 2 * T / R n := h1
      _ = (t n : ℝ) - 2 * T / R n := by rw [h2]
      _ ≤ (t n : ℝ) - T / Rc n := by linarith
  have hT₀B : ∀ B' : ℝ, ∀ᶠ n in atTop, T₀K n ≤ (t n : ℝ) - B' / Rc n := by
    intro B'
    filter_upwards [hT₀K (max B' 1) (lt_of_lt_of_le one_pos (le_max_right B' 1))] with n hn
    have hBR : B' / Rc n ≤ max B' 1 / Rc n :=
      div_le_div_of_nonneg_right (le_max_left B' 1) (hRcpos n).le
    linarith
  have hsep : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀K n ≤ (K n).time i.succ) b,
        (t n : ℝ) - T / Rc n < (K n).time i.succ →
        2 * max (3 / (rr n / 100) ^ 2) (C * Rc n) < ((recK n i hi).static b).neck.scale := by
    intro T _ C hC
    obtain ⟨N, hN⟩ := exists_nat_gt (4 * C + 245)
    filter_upwards [hrr1, eventually_ge_atTop N] with n hr hn i hi b _
    rw [hr]
    have hs := hscaleK n i hi b
    have hQ := hceil n
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hRn := hRr n
    have hm : R n ≤ max ((n : ℝ) + 1) ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ :=
      hQ.trans (le_max_right _ _)
    have hn1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have h3 : ((n : ℝ) + 1) * R n ≤ ((recK n i hi).static b).neck.scale :=
      (mul_le_mul_of_nonneg_left hm hn1).trans hs
    have h4 : ((n : ℝ) + 1) * ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) * R n :=
      mul_le_mul_of_nonneg_left hRn hn1
    rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    refine max_lt ?_ ?_
    · norm_num
      nlinarith
    · have hRp := hRpos n
      have h5 : C * Rc n ≤ C * (2 * R n) := mul_le_mul_of_nonneg_left (hRc2 n).le hC
      have h6 : 0 < ((n : ℝ) + 1 - 4 * C) * R n := mul_pos (by linarith) hRp
      nlinarith [h6, h5, h3]
  -- hdistQC 于 (t, y′)
  have hRrr : Tendsto (fun n => Rc n * rr n ^ 2) atTop atTop :=
    hRlim.congr' (hrr1.mono fun n hn => by simp [hn])
  have hdistQC := hQC K t y' Rc rr (fun n => L' n / 4) Tn aSeed haT hsT' hat pT seedTrace
    (Filter.Eventually.of_forall fun n => by
      have := hroomAll n
      have := div_nonneg (sq_nonneg (L' n)) (hRcpos n).le
      linarith)
    (hrr1.mono fun n hn => by rw [hn]; linarith [hTn2 n])
    (Filter.Eventually.of_forall hRcpos) (hL'lim.atTop_div_const (by norm_num))
    (hrr1.mono fun n hn => by rw [hn]; exact hsm n)
    (hrr1.mono fun n hn => by rw [hn]; exact hclock n) hRrr le_rfl
    (Filter.Eventually.of_forall fun n =>
      ObservedHistory.hpin_rescaled_of_records_P6HI F recQ ind c hc n)
    (fun n => (pp n).rescale_P6N (c n) (hc n)) T₀K recK
    (Filter.Eventually.of_forall hcanK)
    (by
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε₁
      filter_upwards [eventually_ge_atTop N] with n hn
      have hNn : (N : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hn 1
      have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) hNn
      have h2 : (pp n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) := hpacc n
      change (pp n).modelAccuracy ≤ ε₁
      linarith)
    (Filter.Eventually.of_forall fun n => le_trans (Nat.le_add_left 2 n) (hpord n))
    (by
      obtain ⟨N, hN⟩ := exists_nat_gt (StandardCap.transitionEnd + 10)
      filter_upwards [eventually_ge_atTop N] with n hn
      have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
      have h2 : (n : ℝ) + 1 ≤ (pp n).modelRadius := hpD n
      change StandardCap.transitionEnd + 10 < (pp n).modelRadius
      linarith)
    hsep hT₀K
  -- κ 族（FRESH，Aseed + 3 窗）
  obtain ⟨κ, hκ, Tf, hsupK⟩ := hsupA (Aseed + 3) (by linarith)
  have hTf : ∀ᶠ k in atTop, Tf / c k ≤ (Tn k : ℝ) := by
    obtain ⟨N, hN⟩ := exists_nat_ge Tf
    filter_upwards [eventually_ge_atTop N] with k hk
    have h1 : (N : ℝ) ≤ k := by exact_mod_cast hk
    rw [div_le_iff₀ (hc k), mul_comm]
    linarith [hTc k]
  have hvolW : ∀ k, ENNReal.ofReal ((Aseed + 3 + 7)⁻¹ * (1 : ℝ) ^ 3) ≤
      ballVolume ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k)) (pT k) 1 :=
    fun k => le_trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (inv_anti₀ (by linarith) (by linarith)) (by norm_num))) (hvol k)
  have hκR1 := ObservedHistory.hκR_K_DH Kh hκ.le (by linarith : Aseed + 3 ≤ Aseed + 3 + 7)
    (nr := fun k w => q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k))
    (Tf := fun k => Tf / c k) (fun k => hsupK ind c hc k) Tn aSeed haT pT seedTrace
    (fun _ => 1) (fun _ => 1 / 200) hTf (fun k => by norm_num; linarith [hTn2 k]) hsm hvolW
    hclock (fun _ => by norm_num) (fun k w h1 h2 => hnrS k w h1 h2)
  have hκRF1 := ObservedHistory.hκRF_K_DH Kh hκ.le (by linarith : Aseed + 3 ≤ Aseed + 3 + 7)
    (nr := fun k w => q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k))
    (Tf := fun k => Tf / c k) (fun k => hsupK ind c hc k) Tn aSeed haT pT seedTrace
    (fun _ => 1) (fun _ => 1 / 200) hTf (fun k => by norm_num; linarith [hTn2 k]) hsm hvolW
    hclock (fun _ => by norm_num) (fun k w h1 h2 => hnrS k w h1 h2)
  -- hslabK / hderF ⇐ TDS（Q := ρ̃(Tn)⁻²）
  obtain ⟨G, hG⟩ : ∃ G : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon →
      ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
        ((K n).time (Fin.last (K n).eventCount)) (K n).horizon,
      ∀ n h, G n h = ((K n).finalSlab h).restrictIncoming le_rfl h le_rfl :=
    ⟨fun n h => ((K n).finalSlab h).restrictIncoming le_rfl h le_rfl, fun _ _ => rfl⟩
  obtain ⟨hslab0, hderF0⟩ := GC.LongTime.Ch11.hkernelDtT_of_supply_P6KT hTD le_rfl hanti
    q.neckRadius_pos ind c hc (fun n => (q.neckRadius (c n * (Tn n : ℝ)) ^ 2)⁻¹)
    (fun n => c n * (Tn n : ℝ)) (fun _ => le_rfl)
  have hTc' : ∀ n, c n * (Tn n : ℝ) / c n = (Tn n : ℝ) := fun n =>
    mul_div_cancel_left₀ _ (hc n).ne'
  have hQe : ∀ n, c n * (q.neckRadius (c n * (Tn n : ℝ)) ^ 2)⁻¹ =
      ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ := fun n =>
    (RetainedCoreHistory.neckRadius_rescale_inv_sq_P6X (hc n) q (Tn n : ℝ)).symm
  have hslabK : ∀ n (j₀ : Fin (K n).eventCount),
      ((K n).toHistory.event j₀).incoming.DerivativeBoundBefore Ctime
        ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹
        (min ((K n).time j₀.succ) (Tn n : ℝ)) := fun n j₀ => by
    have h := hslab0 n j₀
    beta_reduce at h
    rwa [hQe n, hTc' n] at h
  have hderF : ∀ n h, (G n h).DerivativeBoundBefore Ctime
      ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹
      (min (K n).horizon (Tn n : ℝ)) := fun n hf => by
    have h := hderF0 n hf
    beta_reduce at h
    rw [hQe n, hTc' n] at h
    rw [hG n hf]
    exact h
  -- pinching（同一 Phi）
  have ha₀K : ∀ n, 0 < a₀ / c n := fun n => div_pos ha₀ (hc n)
  have hT₀K1 : ∀ n, (1 : ℝ) ≤ a₀ / c n + T₀K n := fun n => by
    have h1 : (1 : ℝ) ≤ T₀K n := le_max_left _ _
    have h2 := (ha₀K n).le
    linarith
  have hrecF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (q.rescale_P6N (c n) (hc n)) :=
    fun n i => (recQ (ind n) i).rescale_P6M (c n) (hc n)
  have hpinchK0 := (hP K (fun n => q.rescale_P6N (c n) (hc n)) hrecF (fun n => a₀ / c n) T₀K
    ha₀K hT₀K1 hHIK).1
  have hGinit : ∀ n h, (G n h).flow.base.metric ((K n).time (Fin.last (K n).eventCount)) =
      (K n).initialMetric (Fin.last (K n).eventCount) := fun n h => by
    rw [hG n h]
    exact (K n).toHistory.final_initial h
  have hpinchF : ∀ n h, Perelman.PhiAlmostNonnegative (G n h).flow
      (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀K n)) Phi :=
    fun n h => (hP (fun _ => K n) (fun _ => q.rescale_P6N (c n) (hc n)) (fun _ => hrecF n)
      (fun _ => a₀ / c n) (fun _ => T₀K n) (fun _ => ha₀K n) (fun _ => hT₀K1 n)
      (fun _ => hHIK n)).2 (fun _ => (K n).horizon) (fun _ => G n h) (fun _ => hGinit n h) 0
  -- hgood@t（Rc 归一化，Cg := 8；2L′ ≤ L − 2）
  have h2L : ∀ n, 2 * L' n ≤ max 0 (L n - 2) := fun n => by
    have h1 := hL'L n
    rcases le_or_gt 0 ((L n - 2 - B) / 2) with h | h
    · rw [max_eq_right h] at h1
      exact le_max_of_le_right (by linarith)
    · rw [max_eq_left h.le] at h1
      exact le_max_of_le_left (by linarith)
  have hLsq : ∀ n, 2 * L' n ^ 2 ≤ (L n - 2) ^ 2 := fun n => by
    have h4 : (2 * L' n) ^ 2 ≤ (L n - 2) ^ 2 := by
      refine sq_le_sq.mpr ?_
      rw [abs_of_nonneg (by linarith [hL'0 n])]
      exact (h2L n).trans (max_le (abs_nonneg _) (le_abs_self _))
    nlinarith [sq_nonneg (L' n)]
  have hLd : ∀ n, ENNReal.ofReal (L' n / Real.sqrt (Rc n)) ≤
      ENNReal.ofReal ((L n - 2) / Real.sqrt (R n)) := fun n => by
    refine (ofReal_div_sqrt_Rc_le_R4B (hRpos n) (hRc1 n) (hL'0 n)).trans ?_
    rcases le_or_gt 0 (L n - 2) with h | h
    · refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _))
      have := h2L n
      rwa [max_eq_right h] at this
    · have h0 : 2 * L' n ≤ 0 := by
        have := h2L n
        rwa [max_eq_left h.le] at this
      have h0' : 2 * L' n / Real.sqrt (R n) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg h0 (Real.sqrt_nonneg _)
      rw [ENNReal.ofReal_of_nonpos h0']
      exact bot_le
  have hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ t n),
      (t n : ℝ) - L' n ^ 2 / Rc n ≤ (v : ℝ) →
      ∀ z : ((Kh n).stageAt v).Carrier,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT' n)))) z ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (t n)) (t n))
              ((seedTrace n).point ((Kh n).activeStage (t n)) ((Kh n).activeStage_mono (hat n))
                ((Kh n).activeStage_mono (hsT' n))) (y' n) +
            ENNReal.ofReal (L' n / Real.sqrt (Rc n)) →
        8 * Rc n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
        (Kh n).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z := by
    intro n v hav hvs hwv z hd hz
    refine hgood' n v hav hvs ?_ z (hd.trans (add_le_add le_rfl (hLd n))) (by linarith [hRc1 n])
    have h1 := hdivRc n (L' n ^ 2) (sq_nonneg _)
    have h2 : 2 * L' n ^ 2 / R n ≤ (L n - 2) ^ 2 / R n :=
      div_le_div_of_nonneg_right (hLsq n) (hRpos n).le
    linarith
  -- (1) hdistσ@t ⇐ hcompR + σ 处 gate（Rc 归一化）
  have hdistσ : ∀ᶠ n in atTop,
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (t n)) (t n))
          ((seedTrace n).point ((Kh n).activeStage (t n)) ((Kh n).activeStage_mono (hat n))
            ((Kh n).activeStage_mono (hsT' n))) (y' n) +
        ENNReal.ofReal ((L' n + 1) / Real.sqrt (Rc n)) ≤
          ENNReal.ofReal ((Aseed + 3) * rr n) := by
    filter_upwards [hrr1, hL.eventually_ge_atTop (2 + B)] with n hr hL2
    rw [hr]
    have hL'2 : 2 * L' n ≤ L n - 2 - B := by
      have := hL'L n
      rw [max_eq_right (by linarith)] at this
      linarith
    have hs := Real.sqrt_nonneg (R n)
    have hsum : B / Real.sqrt (R n) + 2 * (L' n + 1) / Real.sqrt (R n) =
        (B + 2 * (L' n + 1)) / Real.sqrt (R n) := by ring
    calc _ ≤ riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (t n)) (t n))
              ((seedTrace n).point ((Kh n).activeStage (t n)) ((Kh n).activeStage_mono (hat n))
                ((Kh n).activeStage_mono (hsT' n))) (y' n) +
          ENNReal.ofReal (2 * (L' n + 1) / Real.sqrt (R n)) :=
          add_le_add le_rfl (ofReal_div_sqrt_Rc_le_R4B (hRpos n) (hRc1 n)
            (by linarith [hL'0 n]))
      _ ≤ (riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (B / Real.sqrt (R n))) +
          ENNReal.ofReal (2 * (L' n + 1) / Real.sqrt (R n)) := add_le_add (hcompR n) le_rfl
      _ = riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal ((B + 2 * (L' n + 1)) / Real.sqrt (R n)) := by
          rw [add_assoc, ← ENNReal.ofReal_add (div_nonneg hB hs)
            (div_nonneg (by linarith [hL'0 n]) hs), hsum]
      _ ≤ riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) :=
          add_le_add le_rfl (ENNReal.ofReal_le_ofReal
            (div_le_div_of_nonneg_right (by linarith) hs))
      _ ≤ _ := hgate n
  have hRa : ∀ n, 1 ≤ Rc n * aSeed n := fun n =>
    one_le_mul_of_one_le_of_one_le (hR1 n) (hone n)
  exact ObservedHistory.hbcadC_final_of_guarded2T_HFT (Cg := 8)
    (pF := fun n => q.rescale_P6N (c n) (hc n)) (p := fun n => (pp n).rescale_P6N (c n) (hc n))
    (Q := fun n => ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹)
    (tK := fun n => (Tn n : ℝ)) (Aκ := Aseed + 3) (rX := 1) (G := G)
    hεle hκ hPhi (by norm_num) hG hrecF hHIK hcanK hδK hpacc hpD hpord hscaleK
    (Filter.Eventually.of_forall hbK) hpinchK0 hslabK hpinchF hderF Kh rfl t y' Rc hRcpos hRcr
    hT₀B Tn aSeed haT hsT' (fun _ => le_rfl) hat pT seedTrace L' hL'lim hwin' (fun _ => 1 / 200)
    hradiiC hdistQC hC2 rr hgood hroomAll hdistσ
    ((hκR1.and hrr1).mono fun n hn => by rw [hn.2]; exact hn.1)
    ((hκRF1.and hrr1).mono fun n hn => by rw [hn.2]; exact hn.1) one_pos hsm hclock (fun _ => 0)
    (fun _ => le_rfl) (fun n => ObservedHistory.hpin_rescaled_of_records_P6HI F recQ ind c hc n)
    hRa (fun _ => 0)
    (ObservedHistory.hT₀X_zero_A6K aSeed) (ObservedHistory.hOldX_kernel_A6K K _)

/-- **R4 帧 hbcadC producer（`_R4B`）**：见模块文档。`Θ` 只依赖引擎数据（不依赖 `ind`），调用方须保证
`Θ k ≤ c k · Tn k`（E2a′ 的阈值序列并入 `Θ`）。 -/
theorem hbcadC_R4center_R4B {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hεle : ε ≤ coneAccuracy) (hC2 : 0 ≤ C2)
    (q : CutoffParameters) (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hδq : Tendsto q.delta atTop (𝓝 0))
    (recQ : ∀ n (e : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory e q)
    (hrecent : ∀ ε' : ℝ, 0 < ε' → ∃ T : ℝ, 0 < T ∧ ∀ t, T ≤ t →
      ∀ n (i : Fin (F.tower.history n).eventCount),
      (F.tower.history n).time i.succ ∈ Icc (t / 2) t →
      ∀ h, (recQ n i).nominalRadius h ≤ ε' * q.neckRadius t)
    (hfine : ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T₀ : ℝ, ∀ n, ∃ p : CutoffParameters,
      D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
      ∃ records' : ∀ i : Fin (F.tower.history n).eventCount,
          T₀ ≤ (F.tower.history n).time i.succ →
          GeometricCutoffRecord (F.tower.history n).toHistory i p,
        (∀ i hi b, ((records' i hi).static b).hasCanonicalWindow) ∧
        ∀ i hi b, ((records' i hi).static b).neck.scale = ((recQ n i).static b).neck.scale)
    (hTD : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hsupA : ∀ Aseed : ℝ, 1 < Aseed → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ,
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) (k : ℕ),
        KappaSeedWindowFwd_C11PK
          (fun w => q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k)) (Aseed + 7) κ
          (Tf / c k) ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory) :
    ∃ Θ : ℕ → ℝ, ∀ Aseed : ℝ, 1 < Aseed →
    ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
      let Kh : ℕ → ObservedHistory.{u} := fun k =>
        ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
      ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
        (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
      ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
        (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
        (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        (∀ k, ENNReal.ofReal (Aseed⁻¹ * 1 ^ 3) ≤
          riemannianVolumeMeasure ThreeModel ((Kh k).stageAt (Tn k)).Carrier
            ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k))
            (riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k))
              (pT k) 1)) →
        (∀ k, 2 < (Tn k : ℝ)) →
        (∀ k (w : ℝ), (Tn k : ℝ) - 1 ^ 2 / 2 ≤ w → w ≤ (Tn k : ℝ) →
          q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k) ≤ 1) →
        (∀ k, Θ k ≤ c k * (Tn k : ℝ)) →
      ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
          ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
        (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
        (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
        (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
        Tendsto L atTop atTop →
        (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
        Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
        Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        (∀ k,
          riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
              ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                ((Kh k).activeStage_mono (hsT k))) (y k) +
            ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((Aseed + 3) * 1)) →
        (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
      ∀ (t : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y' : ∀ k, ((Kh k).stageAt (t k)).Carrier)
        (hat : ∀ k, aSeed k ≤ t k) (hts : ∀ k, t k ≤ σ k),
        (∀ k, (σ k : ℝ) - t k ≤ 1 / R k) →
        (∀ k, riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k))
            ((seedTrace k).point ((Kh k).activeStage (t k)) ((Kh k).activeStage_mono (hat k))
              ((Kh k).activeStage_mono ((hts k).trans (hsT k)))) (y' k) ≤
          riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
              ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                ((Kh k).activeStage_mono (hsT k))) (y k) +
            ENNReal.ofReal (1 / Real.sqrt (R k))) →
        (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvt : v ≤ t k),
          (t k : ℝ) - (L k - 2) ^ 2 / R k ≤ (v : ℝ) →
          ∀ z : ((Kh k).stageAt v).Carrier,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                  ((Kh k).activeStage_mono (hvt.trans ((hts k).trans (hsT k))))) z ≤
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k))
                  ((seedTrace k).point ((Kh k).activeStage (t k))
                    ((Kh k).activeStage_mono (hat k))
                    ((Kh k).activeStage_mono ((hts k).trans (hsT k)))) (y' k) +
                ENNReal.ofReal ((L k - 2) / Real.sqrt (R k)) →
            4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
            (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
      ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T K : ℝ, -σ' < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (t n) (y' n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (K * R n)) →
        ∀ᶠ n in map φ atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (t n)) (t n)) (y' n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (t n)) (t n)) (y' n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ t n), (v : ℝ) = t n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (t n))
            ((Kh n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (t n))
            ((Kh n).activeStage_mono hvt) x₂),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤
            C * R n := by
  obtain ⟨Θ, hΘg⟩ := hbcadC_R4center_Rc_R4B F hεle hC2 q hanti hδq recQ hrecent hfine hTD hsupA
  refine ⟨Θ, ?_⟩
  intro Aseed hA ind c hc Kh Tn pT hTc aSeed haT hclock hone hsm hvol hTn2 hnrS hΘ seedTrace σ y
    R hsT has L hRpos hRr hL haS hroomT hradii hgate hceil t y' hat hts hclose hcompR hgood'
  exact hΘg Aseed hA ind c hc Tn pT hTc aSeed haT hclock hone hsm hvol hTn2 hnrS hΘ seedTrace σ y
    R hsT has L hRpos hRr hL haS hroomT hgate hceil t y' hat hts R 1 1 zero_le_one zero_le_one
    (fun k => by linarith [hRpos k]) (fun k => by linarith [hRpos k]) hRr hradii hclose hcompR
    hgood'

/-- consumer。 -/
example : True := by
  have := @hbcadC_R4center_R4B.{0}
  have := @hbcadC_R4center_Rc_R4B.{0}
  trivial

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

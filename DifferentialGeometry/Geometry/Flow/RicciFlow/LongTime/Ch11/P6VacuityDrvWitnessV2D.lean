import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DextDriverDrvW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DextDriverQUniDT
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DextDriverDrvHI
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DextDriverDrvHIDHT
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DextDriverCgDC
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DextDriverQUniCgDC
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DextDriverDrvHICgDHT
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DextDriverDrvHIDHTCg
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DextDriverFinalDF
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DextDriverFinalQUniDF
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DextDriverFinalQUniCgDF
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ScaleSepP6SS

set_option autoImplicit false

/-!
# VAC2-DRV 审计见证（O-CH11-VAC2DRV，后缀 `_V2D`）：driver 族反证几何核的可满足性

对象：`DrvResE_DW / E_DT / E2_DW / E2_DT / E_Cg_DC / E_DT_Cg_DC / E2_Cg_DC / E2_DT_Cg_DC /
F_DW / F_DT / F_DT_Cg_DF`。全部形如 `∀ A > 1, ∀ ind, 反证序列 + 前提 → ∃ 包`，反证假设之外**无合取**。

* **hfin（GAP e）——条件反例**：E 族八个核的 `∃` 包含 `∃ hfin : ∀ n, (K n).time last < (K n).horizon`，
  对被访问层（`K n` 由外层 tower 决定）无产出自由、前提不蕴含（前提只把 `σ` 放在某事件之前）。
  `hfinTel_of_*_V2D` 把每个核投影到 hfin 望远镜 `DrvHfinE_V2D`（前提逐字复制自 `DrvResE_Cg_DC`；
  非 Cg 核取 `Cg := 4`、b 元组 = 主元组）；`not_*_of_hfinFail_V2D` 为条件反例。F 族由 `hevF` 自带
  （`hfin_of_hevF_V2D`），不受影响。
* **Q 元组冲突——条件反例**：带 `Q` 的四个 E 核（`E_DW / E2_DW / E_Cg_DC / E2_Cg_DC`）同一 `Q n` 既要
  `(n+1)·max(n+1, Q n) ≤ neck.scale`，又要整层 `EventSlabsDerivative Ctime (Q n) last`。
  `qslab_refuted_V2D`：σ 所在 slab 末事件上任意 record 有界尺度 `S n`、且整层在 `S n/(n+1)` 门槛
  导数界失败（∀ᶠ）⇒ 结论不成立；`not_*_of_qslabFail_V2D` 为条件反例。DT 孪生（`Q := ρ̃(Tn)⁻²`、删
  slab 导数合取）不含此项。
* **正例 / 非空真**：标量前提骨架可同时满足（`scalarPremises_V2D`）；`T₀K := T₀/c` 满足 `∃` 包的
  `∀ T, ∀ᶠ, T₀K ≤ σ − T/R`（`T₀K_eventually_V2D`，δ 合取经 Θ ≥ lateDelta 付）；`Cg > 1` 的守卫不触及
  反证点自身（`guard_excludes_center_V2D`）；任意 record 的尺度下界（`record_scaleSep_P6SS` 引用）。
* **hTRs conj1（无 ceiling，lead 追加）**：R8 recent 路线只产出 `scale ≥ N·ρ⁻²`；conj1 要比的是 `C·R(y)`。
  无 `R ≤ K₀·ρ⁻²` 时不可推（`recent_no_ceiling_gap_V2D`）；条件反例数值核 `conj1_concl_fail_V2D`；
  加 ceiling 即可付（`conj1_of_recent_ceiling_V2D`）。
生成器 `build-logs/scratch/VAC2DRV/gen/gen.py`。
-/

noncomputable section

open Set Function Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open ObservedHistory (DepthExtendable)

/-- **hfin 望远镜**：driver E 族前提（逐字，Cg / b 元组形）⇒ 每个被访问层有非退化 final slab。 -/
def DrvHfinE_V2D {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (q : CutoffParameters) (Cg ε C1 C2 : ℝ) (Ctime : ℝ≥0) (εb C1b C2b : ℝ) (Ctimeb : ℝ≥0)
    (T₀ Qt : ℕ → ℝ) : Prop :=
  ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
        let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
        ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
          (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
          (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
          (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
          (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
            ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
        let c : ℕ → ℝ := fun k => r k ^ 2
        let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
        let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
        let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
        let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
        let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
          (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl εb C1b C2b Ctimeb (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              Cg * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
          (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
          (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
          (∀ k, ∃ j : Fin (Kh k).eventCount, (Kh k).time j.castSucc < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).time j.succ) →
          (∀ k : ℕ, (k : ℝ) + 1 < R k) →
        ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon

/-- **Q-slab 望远镜**：driver E 族前提（逐字）⇒ 同一 `Q` 的 records 尺度下界 + 整层 slab 导数。 -/
def DrvQSlabE_V2D {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (q : CutoffParameters) (Cg ε C1 C2 : ℝ) (Ctime : ℝ≥0) (εb C1b C2b : ℝ) (Ctimeb : ℝ≥0)
    (T₀ Qt : ℕ → ℝ) : Prop :=
  ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
        let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
        ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
          (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
          (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
          (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
          (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
            ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
        let c : ℕ → ℝ := fun k => r k ^ 2
        let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
        let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
        let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
        let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
        let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
          (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl εb C1b C2b Ctimeb (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              Cg * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
          (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
          (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
          (∀ k, ∃ j : Fin (Kh k).eventCount, (Kh k).time j.castSucc < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).time j.succ) →
          (∀ k : ℕ, (k : ℝ) + 1 < R k) →
        ∃ (qK : ℕ → CutoffParameters) (T₀K : ℕ → ℝ)
          (recordsK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
            GeometricCutoffRecord (K n).toHistory i (qK n)),
          (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀K n ≤ (σ n : ℝ) - T / R n) ∧
          ∃ (Q : ℕ → ℝ),
          (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
            ((recordsK n i hi).static b).neck.scale) ∧
          (∀ n, (K n).EventSlabsDerivative Ctime (Q n) (Fin.last (K n).eventCount))

/-- 投影（`DrvResE_DW` ⇒ hfin 望远镜）：反证假设下 ∃ 包强制每个被访问层 `K n` 有非退化 final slab。 -/
theorem hfinTel_of_E_DW_V2D
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
    {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {T₀ Qt : ℕ → ℝ}
    (h : DrvResE_DW F q records ε C1 C2 Ctime T₀ Qt) :
    DrvHfinE_V2D F q 4 ε C1 C2 Ctime ε C1 C2 Ctime T₀ Qt := by
  intro A hA ind Ho Tno pTo r hr h1 h2 h3 h4 c hc K Kh Tn pT aSeed haT h5 h6 h7 h8 seedTrace σ y R
    hsT has L h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
  obtain ⟨qK, T₀K, recK, -, c2, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, Q,
    -, -, -, cs, -, -, csl, ⟨hfin, -⟩, -⟩ :=
    h
    A hA ind Tno pTo r hr h1 h2 h3 h4 aSeed haT h5 h6 h7 h8 seedTrace σ y R hsT has L h9 h10 h11
    h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
  exact hfin

/-- **条件反例（hfin，GAP e）**：hfin 望远镜不成立（某反证实例访问到末事件 = horizon 的层）
⇒ `¬ DrvResE_DW`。 -/
theorem not_E_DW_of_hfinFail_V2D
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
    {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {T₀ Qt : ℕ → ℝ}
    (hbad : ¬ DrvHfinE_V2D F q 4 ε C1 C2 Ctime ε C1 C2 Ctime T₀ Qt) :
    ¬ DrvResE_DW F q records ε C1 C2 Ctime T₀ Qt :=
  fun h => hbad (hfinTel_of_E_DW_V2D h)

/-- 投影（`DrvResE_DW` ⇒ Q-slab 望远镜）：同一 `Q` 同时压 records 尺度与整层 slab 导数门槛。 -/
theorem qslabTel_of_E_DW_V2D
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
    {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {T₀ Qt : ℕ → ℝ}
    (h : DrvResE_DW F q records ε C1 C2 Ctime T₀ Qt) :
    DrvQSlabE_V2D F q 4 ε C1 C2 Ctime ε C1 C2 Ctime T₀ Qt := by
  intro A hA ind Ho Tno pTo r hr h1 h2 h3 h4 c hc K Kh Tn pT aSeed haT h5 h6 h7 h8 seedTrace σ y R
    hsT has L h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
  obtain ⟨qK, T₀K, recK, -, c2, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, Q,
    -, -, -, cs, -, -, csl, ⟨hfin, -⟩, -⟩ :=
    h
    A hA ind Tno pTo r hr h1 h2 h3 h4 aSeed haT h5 h6 h7 h8 seedTrace σ y R hsT has L h9 h10 h11
    h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
  exact ⟨qK, T₀K, recK, c2, Q, cs, csl⟩

/-- **条件反例（Q 元组冲突，DRV-TRUNC）**：Q-slab 望远镜不成立 ⇒ `¬ DrvResE_DW`。 -/
theorem not_E_DW_of_qslabFail_V2D
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
    {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {T₀ Qt : ℕ → ℝ}
    (hbad : ¬ DrvQSlabE_V2D F q 4 ε C1 C2 Ctime ε C1 C2 Ctime T₀ Qt) :
    ¬ DrvResE_DW F q records ε C1 C2 Ctime T₀ Qt :=
  fun h => hbad (qslabTel_of_E_DW_V2D h)

/-- 投影（`DrvResE_DT` ⇒ hfin 望远镜）：反证假设下 ∃ 包强制每个被访问层 `K n` 有非退化 final slab。 -/
theorem hfinTel_of_E_DT_V2D
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
    {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {T₀ Qt : ℕ → ℝ}
    (h : DrvResE_DT F q records ε C1 C2 Ctime T₀ Qt) :
    DrvHfinE_V2D F q 4 ε C1 C2 Ctime ε C1 C2 Ctime T₀ Qt := by
  intro A hA ind Ho Tno pTo r hr h1 h2 h3 h4 c hc K Kh Tn pT aSeed haT h5 h6 h7 h8 seedTrace σ y R
    hsT has L h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
  obtain ⟨qK, T₀K, recK, -, c2, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, cs, -, -, ⟨hfin, -⟩, -⟩ :=
    h
    A hA ind Tno pTo r hr h1 h2 h3 h4 aSeed haT h5 h6 h7 h8 seedTrace σ y R hsT has L h9 h10 h11
    h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
  exact hfin

/-- **条件反例（hfin，GAP e）**：hfin 望远镜不成立（某反证实例访问到末事件 = horizon 的层）
⇒ `¬ DrvResE_DT`。 -/
theorem not_E_DT_of_hfinFail_V2D
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
    {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {T₀ Qt : ℕ → ℝ}
    (hbad : ¬ DrvHfinE_V2D F q 4 ε C1 C2 Ctime ε C1 C2 Ctime T₀ Qt) :
    ¬ DrvResE_DT F q records ε C1 C2 Ctime T₀ Qt :=
  fun h => hbad (hfinTel_of_E_DT_V2D h)

/-- 投影（`DrvResE2_DW` ⇒ hfin 望远镜）：反证假设下 ∃ 包强制每个被访问层 `K n` 有非退化 final slab。 -/
theorem hfinTel_of_E2_DW_V2D
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
    {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {T₀ Qt : ℕ → ℝ} {a₀ : ℝ}
    (h : DrvResE2_DW F q records ε C1 C2 Ctime T₀ Qt a₀) :
    DrvHfinE_V2D F q 4 ε C1 C2 Ctime ε C1 C2 Ctime T₀ Qt := by
  intro A hA ind Ho Tno pTo r hr h1 h2 h3 h4 c hc K Kh Tn pT aSeed haT h5 h6 h7 h8 seedTrace σ y R
    hsT has L h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
  obtain ⟨qK, T₀K, recK, -, c2, -, -, -, -, -, -, -, Q, cs, -, csl, ⟨hfin, -⟩, -⟩ :=
    h A hA
    ind Tno pTo r hr h1 h2 h3 h4 aSeed haT h5 h6 h7 h8 seedTrace σ y R hsT has L h9 h10 h11 h12
    h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
  exact hfin

/-- **条件反例（hfin，GAP e）**：hfin 望远镜不成立（某反证实例访问到末事件 = horizon 的层）
⇒ `¬ DrvResE2_DW`。 -/
theorem not_E2_DW_of_hfinFail_V2D
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
    {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {T₀ Qt : ℕ → ℝ} {a₀ : ℝ}
    (hbad : ¬ DrvHfinE_V2D F q 4 ε C1 C2 Ctime ε C1 C2 Ctime T₀ Qt) :
    ¬ DrvResE2_DW F q records ε C1 C2 Ctime T₀ Qt a₀ :=
  fun h => hbad (hfinTel_of_E2_DW_V2D h)

/-- 投影（`DrvResE2_DW` ⇒ Q-slab 望远镜）：同一 `Q` 同时压 records 尺度与整层 slab 导数门槛。 -/
theorem qslabTel_of_E2_DW_V2D
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
    {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {T₀ Qt : ℕ → ℝ} {a₀ : ℝ}
    (h : DrvResE2_DW F q records ε C1 C2 Ctime T₀ Qt a₀) :
    DrvQSlabE_V2D F q 4 ε C1 C2 Ctime ε C1 C2 Ctime T₀ Qt := by
  intro A hA ind Ho Tno pTo r hr h1 h2 h3 h4 c hc K Kh Tn pT aSeed haT h5 h6 h7 h8 seedTrace σ y R
    hsT has L h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
  obtain ⟨qK, T₀K, recK, -, c2, -, -, -, -, -, -, -, Q, cs, -, csl, ⟨hfin, -⟩, -⟩ :=
    h A hA
    ind Tno pTo r hr h1 h2 h3 h4 aSeed haT h5 h6 h7 h8 seedTrace σ y R hsT has L h9 h10 h11 h12
    h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
  exact ⟨qK, T₀K, recK, c2, Q, cs, csl⟩

/-- **条件反例（Q 元组冲突，DRV-TRUNC）**：Q-slab 望远镜不成立 ⇒ `¬ DrvResE2_DW`。 -/
theorem not_E2_DW_of_qslabFail_V2D
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
    {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {T₀ Qt : ℕ → ℝ} {a₀ : ℝ}
    (hbad : ¬ DrvQSlabE_V2D F q 4 ε C1 C2 Ctime ε C1 C2 Ctime T₀ Qt) :
    ¬ DrvResE2_DW F q records ε C1 C2 Ctime T₀ Qt a₀ :=
  fun h => hbad (qslabTel_of_E2_DW_V2D h)

/-- 投影（`DrvResE2_DT` ⇒ hfin 望远镜）：反证假设下 ∃ 包强制每个被访问层 `K n` 有非退化 final slab。 -/
theorem hfinTel_of_E2_DT_V2D
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
    {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {T₀ Qt : ℕ → ℝ} {a₀ : ℝ}
    (h : DrvResE2_DT F q records ε C1 C2 Ctime T₀ Qt a₀) :
    DrvHfinE_V2D F q 4 ε C1 C2 Ctime ε C1 C2 Ctime T₀ Qt := by
  intro A hA ind Ho Tno pTo r hr h1 h2 h3 h4 c hc K Kh Tn pT aSeed haT h5 h6 h7 h8 seedTrace σ y R
    hsT has L h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
  obtain ⟨qK, T₀K, recK, -, c2, -, -, -, -, -, -, -, cs, -, ⟨hfin, -⟩, -⟩ :=
    h A hA ind Tno
    pTo r hr h1 h2 h3 h4 aSeed haT h5 h6 h7 h8 seedTrace σ y R hsT has L h9 h10 h11 h12 h13 h14
    h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
  exact hfin

/-- **条件反例（hfin，GAP e）**：hfin 望远镜不成立（某反证实例访问到末事件 = horizon 的层）
⇒ `¬ DrvResE2_DT`。 -/
theorem not_E2_DT_of_hfinFail_V2D
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
    {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {T₀ Qt : ℕ → ℝ} {a₀ : ℝ}
    (hbad : ¬ DrvHfinE_V2D F q 4 ε C1 C2 Ctime ε C1 C2 Ctime T₀ Qt) :
    ¬ DrvResE2_DT F q records ε C1 C2 Ctime T₀ Qt a₀ :=
  fun h => hbad (hfinTel_of_E2_DT_V2D h)

/-- 投影（`DrvResE_Cg_DC` ⇒ hfin 望远镜）：反证假设下 ∃ 包强制每个被访问层 `K n` 有非退化 final slab。 -/
theorem hfinTel_of_E_Cg_DC_V2D
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
    {Cg ε C1 C2 : ℝ} {Ctime : ℝ≥0} {εb C1b C2b : ℝ} {Ctimeb : ℝ≥0} {T₀ Qt : ℕ → ℝ}
    (h : DrvResE_Cg_DC F q records Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt) :
    DrvHfinE_V2D F q Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt := by
  intro A hA ind Ho Tno pTo r hr h1 h2 h3 h4 c hc K Kh Tn pT aSeed haT h5 h6 h7 h8 seedTrace σ y R
    hsT has L h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
  obtain ⟨qK, T₀K, recK, -, c2, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, Q,
    -, -, -, cs, -, -, csl, ⟨hfin, -⟩, -⟩ :=
    h
    A hA ind Tno pTo r hr h1 h2 h3 h4 aSeed haT h5 h6 h7 h8 seedTrace σ y R hsT has L h9 h10 h11
    h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
  exact hfin

/-- **条件反例（hfin，GAP e）**：hfin 望远镜不成立（某反证实例访问到末事件 = horizon 的层）
⇒ `¬ DrvResE_Cg_DC`。 -/
theorem not_E_Cg_DC_of_hfinFail_V2D
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
    {Cg ε C1 C2 : ℝ} {Ctime : ℝ≥0} {εb C1b C2b : ℝ} {Ctimeb : ℝ≥0} {T₀ Qt : ℕ → ℝ}
    (hbad : ¬ DrvHfinE_V2D F q Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt) :
    ¬ DrvResE_Cg_DC F q records Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt :=
  fun h => hbad (hfinTel_of_E_Cg_DC_V2D h)

/-- 投影（`DrvResE_Cg_DC` ⇒ Q-slab 望远镜）：同一 `Q` 同时压 records 尺度与整层 slab 导数门槛。 -/
theorem qslabTel_of_E_Cg_DC_V2D
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
    {Cg ε C1 C2 : ℝ} {Ctime : ℝ≥0} {εb C1b C2b : ℝ} {Ctimeb : ℝ≥0} {T₀ Qt : ℕ → ℝ}
    (h : DrvResE_Cg_DC F q records Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt) :
    DrvQSlabE_V2D F q Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt := by
  intro A hA ind Ho Tno pTo r hr h1 h2 h3 h4 c hc K Kh Tn pT aSeed haT h5 h6 h7 h8 seedTrace σ y R
    hsT has L h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
  obtain ⟨qK, T₀K, recK, -, c2, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, Q,
    -, -, -, cs, -, -, csl, ⟨hfin, -⟩, -⟩ :=
    h
    A hA ind Tno pTo r hr h1 h2 h3 h4 aSeed haT h5 h6 h7 h8 seedTrace σ y R hsT has L h9 h10 h11
    h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
  exact ⟨qK, T₀K, recK, c2, Q, cs, csl⟩

/-- **条件反例（Q 元组冲突，DRV-TRUNC）**：Q-slab 望远镜不成立 ⇒ `¬ DrvResE_Cg_DC`。 -/
theorem not_E_Cg_DC_of_qslabFail_V2D
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
    {Cg ε C1 C2 : ℝ} {Ctime : ℝ≥0} {εb C1b C2b : ℝ} {Ctimeb : ℝ≥0} {T₀ Qt : ℕ → ℝ}
    (hbad : ¬ DrvQSlabE_V2D F q Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt) :
    ¬ DrvResE_Cg_DC F q records Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt :=
  fun h => hbad (qslabTel_of_E_Cg_DC_V2D h)

/-- 投影（`DrvResE_DT_Cg_DC` ⇒ hfin 望远镜）：反证假设下 ∃ 包强制每个被访问层 `K n` 有非退化 final slab。 -/
theorem hfinTel_of_E_DT_Cg_DC_V2D
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
    {Cg ε C1 C2 : ℝ} {Ctime : ℝ≥0} {εb C1b C2b : ℝ} {Ctimeb : ℝ≥0} {T₀ Qt : ℕ → ℝ}
    (h : DrvResE_DT_Cg_DC F q records Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt) :
    DrvHfinE_V2D F q Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt := by
  intro A hA ind Ho Tno pTo r hr h1 h2 h3 h4 c hc K Kh Tn pT aSeed haT h5 h6 h7 h8 seedTrace σ y R
    hsT has L h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
  obtain ⟨qK, T₀K, recK, -, c2, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, cs, -, -, ⟨hfin, -⟩, -⟩ :=
    h
    A hA ind Tno pTo r hr h1 h2 h3 h4 aSeed haT h5 h6 h7 h8 seedTrace σ y R hsT has L h9 h10 h11
    h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
  exact hfin

/-- **条件反例（hfin，GAP e）**：hfin 望远镜不成立（某反证实例访问到末事件 = horizon 的层）
⇒ `¬ DrvResE_DT_Cg_DC`。 -/
theorem not_E_DT_Cg_DC_of_hfinFail_V2D
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
    {Cg ε C1 C2 : ℝ} {Ctime : ℝ≥0} {εb C1b C2b : ℝ} {Ctimeb : ℝ≥0} {T₀ Qt : ℕ → ℝ}
    (hbad : ¬ DrvHfinE_V2D F q Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt) :
    ¬ DrvResE_DT_Cg_DC F q records Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt :=
  fun h => hbad (hfinTel_of_E_DT_Cg_DC_V2D h)

/-- 投影（`DrvResE2_Cg_DC` ⇒ hfin 望远镜）：反证假设下 ∃ 包强制每个被访问层 `K n` 有非退化 final slab。 -/
theorem hfinTel_of_E2_Cg_DC_V2D
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
    {Cg ε C1 C2 : ℝ} {Ctime : ℝ≥0} {εb C1b C2b : ℝ} {Ctimeb : ℝ≥0} {T₀ Qt : ℕ → ℝ} {a₀ : ℝ}
    (h : DrvResE2_Cg_DC F q records Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt a₀) :
    DrvHfinE_V2D F q Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt := by
  intro A hA ind Ho Tno pTo r hr h1 h2 h3 h4 c hc K Kh Tn pT aSeed haT h5 h6 h7 h8 seedTrace σ y R
    hsT has L h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
  obtain ⟨qK, T₀K, recK, -, c2, -, -, -, -, -, -, -, Q, cs, -, csl, ⟨hfin, -⟩, -⟩ :=
    h A hA
    ind Tno pTo r hr h1 h2 h3 h4 aSeed haT h5 h6 h7 h8 seedTrace σ y R hsT has L h9 h10 h11 h12
    h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
  exact hfin

/-- **条件反例（hfin，GAP e）**：hfin 望远镜不成立（某反证实例访问到末事件 = horizon 的层）
⇒ `¬ DrvResE2_Cg_DC`。 -/
theorem not_E2_Cg_DC_of_hfinFail_V2D
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
    {Cg ε C1 C2 : ℝ} {Ctime : ℝ≥0} {εb C1b C2b : ℝ} {Ctimeb : ℝ≥0} {T₀ Qt : ℕ → ℝ} {a₀ : ℝ}
    (hbad : ¬ DrvHfinE_V2D F q Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt) :
    ¬ DrvResE2_Cg_DC F q records Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt a₀ :=
  fun h => hbad (hfinTel_of_E2_Cg_DC_V2D h)

/-- 投影（`DrvResE2_Cg_DC` ⇒ Q-slab 望远镜）：同一 `Q` 同时压 records 尺度与整层 slab 导数门槛。 -/
theorem qslabTel_of_E2_Cg_DC_V2D
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
    {Cg ε C1 C2 : ℝ} {Ctime : ℝ≥0} {εb C1b C2b : ℝ} {Ctimeb : ℝ≥0} {T₀ Qt : ℕ → ℝ} {a₀ : ℝ}
    (h : DrvResE2_Cg_DC F q records Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt a₀) :
    DrvQSlabE_V2D F q Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt := by
  intro A hA ind Ho Tno pTo r hr h1 h2 h3 h4 c hc K Kh Tn pT aSeed haT h5 h6 h7 h8 seedTrace σ y R
    hsT has L h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
  obtain ⟨qK, T₀K, recK, -, c2, -, -, -, -, -, -, -, Q, cs, -, csl, ⟨hfin, -⟩, -⟩ :=
    h A hA
    ind Tno pTo r hr h1 h2 h3 h4 aSeed haT h5 h6 h7 h8 seedTrace σ y R hsT has L h9 h10 h11 h12
    h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
  exact ⟨qK, T₀K, recK, c2, Q, cs, csl⟩

/-- **条件反例（Q 元组冲突，DRV-TRUNC）**：Q-slab 望远镜不成立 ⇒ `¬ DrvResE2_Cg_DC`。 -/
theorem not_E2_Cg_DC_of_qslabFail_V2D
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
    {Cg ε C1 C2 : ℝ} {Ctime : ℝ≥0} {εb C1b C2b : ℝ} {Ctimeb : ℝ≥0} {T₀ Qt : ℕ → ℝ} {a₀ : ℝ}
    (hbad : ¬ DrvQSlabE_V2D F q Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt) :
    ¬ DrvResE2_Cg_DC F q records Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt a₀ :=
  fun h => hbad (qslabTel_of_E2_Cg_DC_V2D h)

/-- 投影（`DrvResE2_DT_Cg_DC` ⇒ hfin 望远镜）：反证假设下 ∃ 包强制每个被访问层 `K n` 有非退化 final slab。 -/
theorem hfinTel_of_E2_DT_Cg_DC_V2D
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
    {Cg ε C1 C2 : ℝ} {Ctime : ℝ≥0} {εb C1b C2b : ℝ} {Ctimeb : ℝ≥0} {T₀ Qt : ℕ → ℝ} {a₀ : ℝ}
    (h : DrvResE2_DT_Cg_DC F q records Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt a₀) :
    DrvHfinE_V2D F q Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt := by
  intro A hA ind Ho Tno pTo r hr h1 h2 h3 h4 c hc K Kh Tn pT aSeed haT h5 h6 h7 h8 seedTrace σ y R
    hsT has L h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
  obtain ⟨qK, T₀K, recK, -, c2, -, -, -, -, -, -, -, cs, -, ⟨hfin, -⟩, -⟩ :=
    h A hA ind Tno
    pTo r hr h1 h2 h3 h4 aSeed haT h5 h6 h7 h8 seedTrace σ y R hsT has L h9 h10 h11 h12 h13 h14
    h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
  exact hfin

/-- **条件反例（hfin，GAP e）**：hfin 望远镜不成立（某反证实例访问到末事件 = horizon 的层）
⇒ `¬ DrvResE2_DT_Cg_DC`。 -/
theorem not_E2_DT_Cg_DC_of_hfinFail_V2D
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
    {Cg ε C1 C2 : ℝ} {Ctime : ℝ≥0} {εb C1b C2b : ℝ} {Ctimeb : ℝ≥0} {T₀ Qt : ℕ → ℝ} {a₀ : ℝ}
    (hbad : ¬ DrvHfinE_V2D F q Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt) :
    ¬ DrvResE2_DT_Cg_DC F q records Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt a₀ :=
  fun h => hbad (hfinTel_of_E2_DT_Cg_DC_V2D h)


/-- `EventSlabsDerivative` 对门槛单调（门槛升高、条件变弱）。 -/
theorem eventSlabsDerivative_mono_V2D {H : RetainedCoreHistory.{u}} {Ctime : ℝ≥0} {Q Q' : ℝ}
    {k : Fin (H.eventCount + 1)} (h : H.EventSlabsDerivative Ctime Q k) (hQ : Q ≤ Q') :
    H.EventSlabsDerivative Ctime Q' k := by
  intro j hj y t ht hR
  exact h j hj y t ht (lt_of_le_of_lt hQ hR)

/-- **Q 冲突（结论级）**：σ 所在 slab 的末事件 `j n` 上任意 record 有 boundary 尺度 `≤ S n`，且整层
在门槛 `S n / (n+1)` 处 slab 导数界终于失败 ⇒ Q-slab 结论（DW 族 `∃` 包的子合取）不成立。 -/
theorem qslab_refuted_V2D (K : ℕ → RetainedCoreHistory.{u}) (Ctime : ℝ≥0) (s R : ℕ → ℝ)
    (hR : ∀ n, 0 < R n) (j : ∀ n, Fin (K n).eventCount)
    (hj : ∀ n, s n < (K n).time (j n).succ) (S : ℕ → ℝ)
    (hS : ∀ n (p : CutoffParameters) (rec : GeometricCutoffRecord (K n).toHistory (j n) p),
      ∃ b, (rec.static b).neck.scale ≤ S n)
    (hD : ∀ᶠ n in atTop,
      ¬ (K n).EventSlabsDerivative Ctime (S n / ((n : ℝ) + 1)) (Fin.last (K n).eventCount)) :
    ¬ ∃ (qK : ℕ → CutoffParameters) (T₀K : ℕ → ℝ)
      (recordsK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (qK n)),
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀K n ≤ s n - T / R n) ∧
      ∃ (Q : ℕ → ℝ),
      (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
        ((recordsK n i hi).static b).neck.scale) ∧
      (∀ n, (K n).EventSlabsDerivative Ctime (Q n) (Fin.last (K n).eventCount)) := by
  rintro ⟨qK, T₀K, recK, hT, Q, hsc, hsl⟩
  obtain ⟨n, hn1, hn2⟩ := ((hT 1 one_pos).and hD).exists
  have hpos : 0 < 1 / R n := div_pos one_pos (hR n)
  have hi : T₀K n ≤ (K n).time (j n).succ := by linarith [hj n]
  obtain ⟨b, hb⟩ := hS n (qK n) (recK n (j n) hi)
  have h1 := hsc n (j n) hi b
  have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hmx : ((n : ℝ) + 1) * Q n ≤ ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hn0.le
  have hQ : Q n ≤ S n / ((n : ℝ) + 1) := by
    rw [le_div_iff₀ hn0]
    linarith
  exact hn2 (eventSlabsDerivative_mono_V2D (hsl n) hQ)

/-- F 族：`hevF` 自带 hfin（GAP e 在 final 不存在）。 -/
theorem hfin_of_hevF_V2D (Kh : ℕ → ObservedHistory.{u}) (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon)
    (hevF : ∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (σ k : ℝ) ∧
      (σ k : ℝ) < (Kh k).horizon) :
    ∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (Kh k).horizon :=
  fun k => (hevF k).1.trans (hevF k).2

/-- **正例（δ / T₀K）**：前提 `T₀ ≤ c·aSeed` 与 `∀ T, ∀ᶠ, aSeed ≤ σ − T/R` ⇒ 取 `T₀K := T₀ / c`
满足 `∃` 包第二合取（δ 合取于是只用到 `T₀ ≥ Θ ≥ lateDelta` 的时刻）。 -/
theorem T₀K_eventually_V2D (T₀ c aSeed s R : ℕ → ℝ) (hc : ∀ k, 0 < c k)
    (h8 : ∀ k, T₀ k ≤ c k * aSeed k)
    (h16 : ∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, aSeed k ≤ s k - T / R k) :
    ∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, T₀ k / c k ≤ s k - T / R k := fun T hT =>
  (h16 T hT).mono fun k hk => (div_le_iff₀ (hc k)).2 <| by
    have := mul_le_mul_of_nonneg_left hk (hc k).le
    linarith [h8 k]

/-- **正例（守卫）**：`1 < Cg`（DW: 4；Cg 族: 8）时守卫 `Cg·R ≤ R(z)` 不覆盖反证点 `(σ, y)` 本身。 -/
theorem guard_excludes_center_V2D {Cg R : ℝ} (hCg : 1 < Cg) (hR : 0 < R) : ¬ Cg * R ≤ R := by
  intro h
  nlinarith

/-- `T / R k ≤ 1/4` 终于成立（`R k = 4(k+1)² + 4`）。 -/
theorem small_div_V2D (T : ℝ) (hT : 0 < T) :
    ∀ᶠ k : ℕ in atTop, T / (4 * ((k : ℝ) + 1) ^ 2 + 4) ≤ 1 / 4 := by
  refine Filter.eventually_atTop.2 ⟨⌈4 * T⌉₊, fun k hk => ?_⟩
  have hk' : 4 * T ≤ (k : ℝ) := (Nat.ceil_le).1 hk
  have hpos : (0 : ℝ) < 4 * ((k : ℝ) + 1) ^ 2 + 4 := by positivity
  rw [div_le_iff₀ hpos]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith [sq_nonneg ((k : ℝ))]

/-- **正例（标量前提骨架，F241 型核对）**：`Tn = k+3`、`aSeed = k+2`、`σ = k + 11/4`、
`R = 4(k+1)² + 4`、`L = k+1`（`r = c = 1`、`Tno = Tn`、`Qt = 0`）同时满足 driver 前提里全部纯数值条件。 -/
theorem scalarPremises_V2D :
    ∃ (Tn aSeed s R L : ℕ → ℝ),
      (∀ k, aSeed k = Tn k - 1 ^ 2) ∧ (∀ k, 1 ≤ aSeed k) ∧ (∀ k, aSeed k ≤ s k) ∧
      (∀ k, s k ≤ Tn k) ∧ (∀ k : ℕ, (k : ℝ) + 1 ≤ Tn k) ∧ (∀ k, 2 * (1 : ℝ) ^ 2 < Tn k) ∧
      (∀ k, 0 < R k) ∧ (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) ∧ (∀ k : ℕ, (k : ℝ) + 1 < R k) ∧
      (∀ k, (0 : ℝ) < R k) ∧ Tendsto L atTop atTop ∧
      (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, aSeed k ≤ s k - T / R k) ∧
      (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, Tn k - 1 ^ 2 / 2 ≤ s k - T / R k) ∧
      Tendsto (fun k => R k * (s k - (Tn k - 1 ^ 2 / 2))) atTop atTop ∧
      Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop ∧
      (∀ k, Tn k - 1 ^ 2 / 2 ≤ s k - L k ^ 2 / R k) := by
  refine ⟨fun k => (k : ℝ) + 3, fun k => (k : ℝ) + 2, fun k => (k : ℝ) + 11 / 4,
    fun k => 4 * ((k : ℝ) + 1) ^ 2 + 4, fun k => (k : ℝ) + 1, ?_⟩
  have hk0 : ∀ k : ℕ, (0 : ℝ) ≤ k := fun k => Nat.cast_nonneg k
  have hRp : ∀ k : ℕ, (0 : ℝ) < 4 * ((k : ℝ) + 1) ^ 2 + 4 := fun k => by positivity
  refine ⟨fun k => by norm_num; ring, fun k => by linarith [hk0 k], fun k => by linarith,
    fun k => by linarith, fun k => by linarith, fun k => by norm_num; linarith [hk0 k],
    hRp, fun k => by nlinarith [hk0 k], fun k => by nlinarith [hk0 k], hRp,
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop, ?_, ?_, ?_, ?_, ?_⟩
  · intro T hT
    exact (small_div_V2D T hT).mono fun k hk => by linarith
  · intro T hT
    exact (small_div_V2D T hT).mono fun k hk => by norm_num; linarith
  · refine tendsto_atTop_mono (fun k => ?_) tendsto_natCast_atTop_atTop
    norm_num
    nlinarith [hk0 k]
  · refine tendsto_atTop_mono (fun k => ?_)
      (tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 100))
    have h2 : 2 * ((k : ℝ) + 1) ≤ Real.sqrt (4 * ((k : ℝ) + 1) ^ 2 + 4) :=
      Real.le_sqrt_of_sq_le (by nlinarith)
    linarith
  · intro k
    rw [show (k : ℝ) + 3 - 1 ^ 2 / 2 = (k : ℝ) + 11 / 4 - 1 / 4 by norm_num; ring]
    have : ((k : ℝ) + 1) ^ 2 / (4 * ((k : ℝ) + 1) ^ 2 + 4) ≤ 1 / 4 := by
      rw [div_le_iff₀ (hRp k)]
      nlinarith
    linarith


/-! ### hTRs conj1（无 ceiling）：R8 recent 路线的精确缺口（lead 追加） -/

/-- **conj1 结论失败判据**：若 σ 处事件的 record 尺度频繁 `≤ M·R`，则 conj1 结论（`∀ C ≥ 0, ∀ᶠ k,
2·max(3·10⁴, C·R) < scale`）不成立（条件反例的数值核）。 -/
theorem conj1_concl_fail_V2D (R S : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hfreq : ∃ᶠ k in atTop, S k ≤ M * R k) :
    ¬ ∀ C : ℝ, 0 ≤ C → ∀ᶠ k in atTop, 2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R k) < S k := by
  intro h
  obtain ⟨k, hk1, hk2⟩ := (hfreq.and_eventually (h M hM)).exists
  have h3 : (0 : ℝ) < 3 / ((1 : ℝ) / 100) ^ 2 := by norm_num
  have hm1 := le_max_left (3 / ((1 : ℝ) / 100) ^ 2) (M * R k)
  have hm2 := le_max_right (3 / ((1 : ℝ) / 100) ^ 2) (M * R k)
  linarith

/-- **缺口见证（无 ceiling）**：recent 路线的产出形（∀ N, ∀ᶠ, `N·ρ⁻² ≤ scale`，ρ⁻² ≡ 1）与
`R ≥ k+1` 相容，却不蕴含 conj1 结论（`scale = R = k+1`）。 -/
theorem recent_no_ceiling_gap_V2D :
    ∃ (R S ρ2 : ℕ → ℝ), (∀ k, 0 < ρ2 k) ∧
      (∀ N : ℝ, ∀ᶠ k in atTop, N * ρ2 k ≤ S k) ∧ (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) ∧
      ¬ ∀ C : ℝ, 0 ≤ C → ∀ᶠ k in atTop, 2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R k) < S k := by
  refine ⟨fun k => (k : ℝ) + 1, fun k => (k : ℝ) + 1, fun _ => 1, fun _ => one_pos,
    fun N => ?_, fun _ => le_rfl, ?_⟩
  · refine Filter.eventually_atTop.2 ⟨⌈N⌉₊, fun k hk => ?_⟩
    have := (Nat.ceil_le).1 hk
    linarith
  · exact conj1_concl_fail_V2D _ _ 1 zero_le_one
      (Filter.Eventually.frequently (Filter.Eventually.of_forall fun k => by simp))

/-- **充分性（加 ceiling 后 recent 路线可付 conj1）**：`R ≤ K₀·ρ⁻²`、`1 ≤ ρ⁻²` 与 recent 产出
`∀ N, ∀ᶠ, N·ρ⁻² ≤ scale` ⇒ conj1 结论。 -/
theorem conj1_of_recent_ceiling_V2D (R S ρ2 : ℕ → ℝ) (K₀ : ℝ) (hK₀ : 0 ≤ K₀)
    (hρ1 : ∀ k, 1 ≤ ρ2 k) (hceil : ∀ k, R k ≤ K₀ * ρ2 k)
    (hrec : ∀ N : ℝ, ∀ᶠ k in atTop, N * ρ2 k ≤ S k) :
    ∀ C : ℝ, 0 ≤ C → ∀ᶠ k in atTop, 2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R k) < S k := by
  intro C hC
  refine (hrec (2 * (3 / ((1 : ℝ) / 100) ^ 2 + C * K₀) + 1)).mono fun k hk => ?_
  have hCR : C * R k ≤ C * K₀ * ρ2 k := by
    have := mul_le_mul_of_nonneg_left (hceil k) hC
    linarith
  have hρ0 : (0 : ℝ) ≤ C * K₀ := mul_nonneg hC hK₀
  have h3 : (3 / ((1 : ℝ) / 100) ^ 2) ≤ (3 / ((1 : ℝ) / 100) ^ 2) * ρ2 k := by
    have : (0 : ℝ) ≤ 3 / ((1 : ℝ) / 100) ^ 2 := by norm_num
    nlinarith [hρ1 k]
  have hmax : max (3 / ((1 : ℝ) / 100) ^ 2) (C * R k) ≤
      (3 / ((1 : ℝ) / 100) ^ 2 + C * K₀) * ρ2 k := by
    refine max_le ?_ ?_ <;> nlinarith [hρ1 k]
  nlinarith [hρ1 k]

/-- **正例（任意 record 尺度下界，引用 PROVED）**：θ₀ 合取对引擎 `records` 的 ∀ 量化无害——
任意 `GeometricCutoffRecord` 在天花板 + δ 门槛下即有尺度分离。 -/
example {H : ObservedHistory.{u}} {i : Fin H.eventCount} {pp : CutoffParameters}
    (Rc : GeometricCutoffRecord H i pp) {QA R : ℝ} (hQA : 0 < QA)
    (hceil : R ≤ (pp.neckRadius (H.time i.succ) ^ 2)⁻¹)
    (hδ : pp.delta (H.time i.succ) ≤ 1 / (8646 * (QA + 1))) (j) :
    QA * R < (1 - 4323 * Rc.delta j) * (Rc.neck j).scale :=
  (GeometricCutoffRecord.record_scaleSep_P6SS Rc hQA hceil hδ).2 j

/-- consumer：Q 冲突引理与 hfin 投影可并用（E_DW）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {q : CutoffParameters} {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
    {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {T₀ Qt : ℕ → ℝ}
    (h : DrvResE_DW F q records ε C1 C2 Ctime T₀ Qt) :
    DrvHfinE_V2D F q 4 ε C1 C2 Ctime ε C1 C2 Ctime T₀ Qt ∧
      DrvQSlabE_V2D F q 4 ε C1 C2 Ctime ε C1 C2 Ctime T₀ Qt :=
  ⟨hfinTel_of_E_DW_V2D h, qslabTel_of_E_DW_V2D h⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

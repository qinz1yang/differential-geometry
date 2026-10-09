import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvSlotsR4J
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvResEngineSupplyT0K
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvResDiagDTRXHND
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GapWireKP6WR

/-!
# TRSJ10 G2：R4 帧产出侧 producer——J10 槽（R_c 形）由 T0K 引擎供给 + hnot 残余付（后缀 `_TJ`）

`P6R4DriverGateMTR` 的 J10 槽 `J10Blk_JT K t y′ R_c` 由 `drvSlots_Rc_of_J10_R4J` 付，其 K 帧数据包
（qK / T₀K / recordsK / hscaleK / hbirthAK / hHIK / hcanK / hδFK / hpinchK / hslabT / hfinK / hsep /
hT₀K / hT₀X）在回调环境（**含 hceil、hTn2、hgateP、hcompR**，比 MTR 的 J10 槽前提更富）下：

* qK := `(p n).rescale_P6N`、recordsK := `recordsKRescale_P6X3`、T₀K := `max 1 (c·aSeed/c) = aSeed`、
  Q n := `ρ̃(Tn)⁻²`、a₀K := `a₀/c`，由 T0K `drvResE_records_of_engine_T0K` 供给（元组
  `Nf = n+1`、`ζ = δ₀ = 1/(n+1)`、`Rn = n+1`、`m₀ = n+2`；σ 只经 hroom / hwin 进入，取 dummy
  `σ' = Tn − 1/2 + L²/R`，供给输出里 σ' 形的 hT₀X / tail 不用）；
* hslabT ⇐ `hslabK_of_tds_HND`（TDS 先验，`Q = ρ̃(Tn)⁻²`）；hfinK ⇐ hgateP + hcompR（∀ n）；
  hsep ⇐ hscaleK + hceil（`scale ≥ (n+1)·R`）；hT₀K ⇐ hwin（`T₀K = aSeed`）；hT₀X ⇐ `hTnS 1` + hclose；
  hpinchK ⇐ 驱动的 `hpinK`（`Ici (1/2)` ⊇ `Ici T₀K`）；
* 供给的合同下界 `Θ n ≤ c n·aSeed n`：槽带 `∃ Θ'`，驱动把 `2·Θ'` 并入 hG1 的阈值序列
  （`Θ ≤ c·Tn` 且 `Tn > 2` ⇒ `Θ/2 ≤ c·aSeed`）。

残余仅一项：**`R4HnotC_TJ`**（J10ResE3_JT 于 R4 中心 `(t, y′)`；HNR 元组形：先定 n 依赖常数
`(Nf, ζ, Rn, δ₀, m₀)`，再对任意满足 canonical window / 精度 / 半径 / 阶 / HI / 晚期 δ / birth / 导数界的
K 帧 records 断言）。filler 先取该元组，再与 `1/(n+1)`、`n+1`、`n+2` 取 min / max 喂 T0K 供给。
无新顶层 binder。生成器 build-logs/scratch/O-CH11-TRSJ10/gen/g2.py。
-/

set_option autoImplicit false

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

/-- **R4 中心 hnot 残余（`_TJ`，逐字缩写 def，非合同 Prop）**：形同 HNR 核（`hnotK_seq_a0_HNF`）——
先定 n 依赖常数元组 `(Nf, ζ, Rn, δ₀, m₀)`（只依赖 `(ε, C1, C2, Ctime)`，在一切序列数据之前），再对回调环境
（同 `R4Slot_TJ`，但不含 hceil，以抽象 `Q` + `∀ k, R k ≤ Q k` 代之）下**任意**满足 canonical window /
精度 `≤ ζ n` / 半径 `≥ Rn n` / 阶 `≥ m₀ n` / HI（`a₀K`）/ 晚期 δ `≤ δ₀ n` / birth 下界 `Nf n · Q n ≤ scale`、
`1 ≤ a₀K n · scale` / 事件 slab 导数界（同一 `Q`）/ `T₀K ≤ aSeed` 的 K 帧 records `(qK, T₀K, recordsK)`，
断言 `J10ResE3_JT K t y′ qK T₀K recordsK`（hnot 于 R4 中心）。
PROVISIONAL：本车道不证；预期由「`R_c ≈ R ≤ Q ≪ Nf n · Q ≤ scale`（canonical window 内标量 ≈ scale）与导数界」
的标量失配得（不需 ¬HasSTC 于中心）；小 `n` 的 ∀ n 需 `raiseT0` 式有限前段抬高。 -/
def R4HnotC_TJ {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (ε C1 C2 : ℝ) (Ctime : ℝ≥0) : Prop :=
  ∃ (Nf ζ Rn δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ), (∀ n, 0 < Nf n) ∧ (∀ n, 0 < ζ n) ∧ (∀ n, 0 < δ₀ n) ∧
  ∀ (Aseed : ℝ),
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, 2 < (Tn k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ k, riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
              ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                ((Kh k).activeStage_mono (hsT k))) (y k) +
            ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((Aseed + 3) * 1)) →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ (pm : ∀ k, ((Kh k).stage (i k).castSucc).Carrier)
          (t : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y' : ∀ k, ((Kh k).stageAt (t k)).Carrier)
          (hat : ∀ k, aSeed k ≤ t k) (hts : ∀ k, t k ≤ σ k),
          (∀ k, HEq (y' k) (pm k)) →
          (∀ k, ∃ wp : ((Kh k).stage (i k).succ).Carrier, HEq (y k) wp ∧
            ((Kh k).event (i k)).RegularCrossing (pm k) wp) →
          (∀ k, (Kh k).time (i k).castSucc < (t k : ℝ) ∧ (t k : ℝ) < (Kh k).time (i k).succ) →
          (∀ k, (σ k : ℝ) - t k ≤ 1 / R k) →
          (∀ k, riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k))
              ((seedTrace k).point ((Kh k).activeStage (t k)) ((Kh k).activeStage_mono (hat k))
                ((Kh k).activeStage_mono ((hts k).trans (hsT k)))) (y' k) ≤
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal (1 / Real.sqrt (R k))) →
          (∀ k, metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k)) (y' k) <
            2 * R k) →
          (∀ k, R k / 2 <
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k)) (y' k)) →
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
      ∀ (Q : ℕ → ℝ), (∀ k, R k ≤ Q k) →
      let K : ℕ → RetainedCoreHistory.{u} := fun k =>
        (F.tower.history (ind k)).rescale_P6N (c k) (hc k)
      ∀ (qK : ℕ → CutoffParameters) (T₀K : ℕ → ℝ)
        (recordsK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
          GeometricCutoffRecord (K n).toHistory i (qK n))
        (pF : ℕ → CutoffParameters) (a₀K : ℕ → ℝ),
      (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ n : ℕ, (qK n).modelAccuracy ≤ ζ n) → (∀ n : ℕ, Rn n ≤ (qK n).modelRadius) →
      (∀ n : ℕ, m₀ n ≤ (qK n).modelOrder) →
      (∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀K n) x ∧
        -3 / a₀K n ≤ metricScalarAt ((K n).initialMetric 0) x) →
      (∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
        (pF n).delta ((K n).time i.succ) ≤ δ₀ n) →
      (∀ (n : ℕ) i hi b, Nf n * Q n ≤ ((recordsK n i hi).static b).neck.scale) →
      (∀ (n : ℕ) i hi b, 1 ≤ a₀K n * ((recordsK n i hi).static b).neck.scale) →
      (∀ n (i : Fin (K n).eventCount),
        ((K n).toHistory.event i).incoming.DerivativeBoundBefore Ctime (Q n)
          (min ((K n).time i.succ) (Tn n : ℝ))) →
      (∀ n, T₀K n ≤ (aSeed n : ℝ)) →
      J10ResE3_JT K t y' qK T₀K recordsK

/-- **R4 J10 槽（`_TJ`，逐字缩写 def，非合同 Prop）**：回调环境（含 hceil、hTn2、hgateP、hcompR）+
阈值前提 `Θ' k ≤ c k · Tn k` ⇒ `J10Blk_JT K t y′ R_c`（= MTR 驱动 J10 槽的结论）。
`r4Slot_of_engine_TJ` 证其在引擎数据 + `R4HnotC_TJ` 下成立。 -/
def R4Slot_TJ {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (q : CutoffParameters) (ε C1 C2 : ℝ) (Ctime : ℝ≥0) (Θ' : ℕ → ℝ) : Prop :=
  ∀ (Aseed : ℝ),
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, 2 < (Tn k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ k, riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
              ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                ((Kh k).activeStage_mono (hsT k))) (y k) +
            ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((Aseed + 3) * 1)) →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ (pm : ∀ k, ((Kh k).stage (i k).castSucc).Carrier)
          (t : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y' : ∀ k, ((Kh k).stageAt (t k)).Carrier)
          (hat : ∀ k, aSeed k ≤ t k) (hts : ∀ k, t k ≤ σ k),
          (∀ k, HEq (y' k) (pm k)) →
          (∀ k, ∃ wp : ((Kh k).stage (i k).succ).Carrier, HEq (y k) wp ∧
            ((Kh k).event (i k)).RegularCrossing (pm k) wp) →
          (∀ k, (Kh k).time (i k).castSucc < (t k : ℝ) ∧ (t k : ℝ) < (Kh k).time (i k).succ) →
          (∀ k, (σ k : ℝ) - t k ≤ 1 / R k) →
          (∀ k, riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k))
              ((seedTrace k).point ((Kh k).activeStage (t k)) ((Kh k).activeStage_mono (hat k))
                ((Kh k).activeStage_mono ((hts k).trans (hsT k)))) (y' k) ≤
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal (1 / Real.sqrt (R k))) →
          (∀ k, metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k)) (y' k) <
            2 * R k) →
          (∀ k, R k / 2 <
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k)) (y' k)) →
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
      (∀ k, Θ' k ≤ c k * (Tn k : ℝ)) →
      J10Blk_JT (fun k => (F.tower.history (ind k)).rescale_P6N (c k) (hc k)) t y'
        (centerScalar_R4J (fun k => (F.tower.history (ind k)).rescale_P6N (c k) (hc k)) t y')

/-! ## 小引理（PROVED） -/

/-- hfinK：`d_t ≤ d_σ + c`、`d_σ + d ≤ e`（有限）⇒ `d_t ≠ ⊤`。 -/
theorem ne_top_of_compR_TJ {a b c d e : ℝ≥0∞} (hc : c ≠ ⊤) (he : e ≠ ⊤) (h1 : a ≤ b + c)
    (h2 : b + d ≤ e) : a ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ne_top_of_le_ne_top he (le_trans le_self_add h2), hc⟩)
    h1

/-- hsep 数值核：`s ≥ (n+1)·R` 且 `n ≥ N` ⇒ `2·max (3/(1/100)²) (C·R) < s`。 -/
theorem sepBound_TJ {R : ℕ → ℝ} (hR : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n) (C : ℝ) (hC : 0 ≤ C) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ s : ℝ, ((n : ℝ) + 1) * R n ≤ s →
      2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R n) < s := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (3 / ((1 : ℝ) / 100) ^ 2 + C))
  refine ⟨N, fun n hn s hs => ?_⟩
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hR1 : (1 : ℝ) ≤ R n := by linarith [hR n, Nat.cast_nonneg (α := ℝ) n]
  have hRpos : 0 < R n := by linarith
  set A : ℝ := 3 / ((1 : ℝ) / 100) ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  have hmax : max A (C * R n) ≤ (A + C) * R n := by
    refine max_le ?_ ?_
    · nlinarith [mul_nonneg hC hRpos.le, mul_nonneg hA0 hRpos.le]
    · nlinarith [mul_nonneg hC hRpos.le, mul_nonneg hA0 hRpos.le]
  have h1 : 2 * (A + C) < (n : ℝ) + 1 := by linarith
  have h2 : 2 * max A (C * R n) < ((n : ℝ) + 1) * R n := by
    nlinarith [mul_pos hRpos (sub_pos.2 h1)]
  linarith

/-! ## 主定理：引擎数据 + `R4HnotC_TJ` ⇒ J10 槽 -/

/-- **R4 J10 槽 producer（`_TJ`，PROVISIONAL[`R4HnotC_TJ` + 引擎级 `hfine` / `hrecent` / `hTD` /
`hpinK`]）**：T0K 供给 + 小引理 ⇒ `∃ Θ', R4Slot_TJ`。见模块文档。 -/
theorem r4Slot_of_engine_TJ {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) {ε C1 C2 : ℝ} {Ctime : ℝ≥0} (hC2 : 0 ≤ C2)
    (q : CutoffParameters) (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hδq : Tendsto q.delta atTop (𝓝 0))
    (recQ : GC.LongTime.Ch11.CutoffRecords_C11S F q)
    (hrecent : GC.LongTime.Ch11.RecentCutoffSupply_C11S recQ)
    (hfine : ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T₀ : ℝ, ∀ n, ∃ p : CutoffParameters,
      D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
      ∃ records' : ∀ i : Fin (F.tower.history n).eventCount,
          T₀ ≤ (F.tower.history n).time i.succ →
          GeometricCutoffRecord (F.tower.history n).toHistory i p,
        (∀ i hi b, ((records' i hi).static b).hasCanonicalWindow) ∧
        ∀ i hi b, ((records' i hi).static b).neck.scale = ((recQ n i).static b).neck.scale)
    (hTD : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    (hpinK : ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) (k : ℕ)
      (i' : Fin ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory.eventCount),
      Perelman.PhiAlmostNonnegative
        (((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory.event i').incoming.flow
        (Ico (((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory.time i'.castSucc)
          (((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory.time i'.succ) ∩
          Ici (1 / 2)) phi)
    (hnotC : R4HnotC_TJ F ε C1 C2 Ctime) :
    ∃ Θ' : ℕ → ℝ, R4Slot_TJ F q ε C1 C2 Ctime Θ' := by
  obtain ⟨Nf, ζ, Rn, δ₀, m₀, hNf, hζ, hδ₀, hnot⟩ := hnotC
  obtain ⟨a₀, ha₀, hHI⟩ := exists_initialHI_P6WR F
  obtain ⟨Θ, hΘ⟩ := drvResE_records_of_engine_T0K recQ hrecent hanti hδq hfine ha₀ hHI
    Nf (fun n => min (ζ n) (1 / ((n : ℝ) + 1))) (fun n => max (Rn n) ((n : ℝ) + 1))
    (fun n => min (δ₀ n) (1 / ((n : ℝ) + 1))) (fun n => max (m₀ n) (n + 2))
    (fun n => lt_min (hζ n) (by positivity)) (fun n => lt_min (hδ₀ n) (by positivity))
  refine ⟨fun k => 2 * Θ k, ?_⟩
  intro Aseed ind c hc Kh Tn pT hTc aSeed haT hclock hone hsm hTn2 seedTrace σ y R hsT has L hRdef
    hRpos hRr hL hsel hgood haS hTnS hroom hradii hgateP hceil i hi pm t y' hat hts hy' hcross
    hslab hclose hcompR hcmp hcmpL hgood' hΘ'
  -- 数值前提（供给的合同）
  have hTnc : ∀ n, 0 ≤ c n * (Tn n : ℝ) := fun n => mul_nonneg (hc n).le (Tn n).2.1
  have h2c : ∀ n, 2 * c n < c n * (Tn n : ℝ) := fun n => by
    have := hTn2 n
    nlinarith [hc n]
  have hΘc : ∀ n, Θ n ≤ c n * (aSeed n : ℝ) := fun n => by
    have h1 := hΘ' n
    have h2 := hTn2 n
    have h3 := hclock n
    nlinarith [hc n, mul_pos (hc n) (sub_pos.2 h2)]
  have hRρ : ∀ n, R n ≤ c n * (q.neckRadius (c n * (Tn n : ℝ)) ^ 2)⁻¹ := fun n => by
    have := hceil n
    rwa [RetainedCoreHistory.neckRadius_rescale_inv_sq_P6X (hc n) q (Tn n)] at this
  have hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop,
      (aSeed n : ℝ) ≤ ((Tn n : ℝ) - 1 ^ 2 / 2 + L n ^ 2 / R n) - T / R n := by
    intro T hT
    filter_upwards [hL.eventually_ge_atTop (max T 1)] with n hn
    have hLT : T ≤ L n := (le_max_left _ _).trans hn
    have hL1 : 1 ≤ L n := (le_max_right _ _).trans hn
    have hLL : T ≤ L n ^ 2 := by nlinarith
    have hnn : 0 ≤ (L n ^ 2 - T) / R n := div_nonneg (by linarith) (hRpos n).le
    have : L n ^ 2 / R n - T / R n = (L n ^ 2 - T) / R n := by ring
    have h3 := hclock n
    linarith
  obtain ⟨p, recKHo, hacc, hrad, hord, hcan, hδ, hbirth, hbirthA, hHIk, -, -⟩ :=
    hΘ (fun n => c n * (aSeed n : ℝ)) hΘc ind c (fun n => (Tn n : ℝ) - 1 ^ 2 / 2 + L n ^ 2 / R n)
      L R (fun n => (Tn n : ℝ)) (fun n => c n * (Tn n : ℝ)) (fun n => (aSeed n : ℝ)) hc
      (fun n => rfl) hTnc h2c hclock hone (fun n => le_rfl) (fun n => le_of_eq (by ring)) hRr hRρ
      hwin
  -- K 帧数据包
  have hT0eq : ∀ n, max 1 (c n * (aSeed n : ℝ) / c n) = (aSeed n : ℝ) := fun n =>
    t0K_eq_aSeed_T0K (hc n) (hone n)
  have hcanK : ∀ n i hi b, (((F.tower.history (ind n)).recordsKRescale_P6X3 (hc n) (recKHo n)
      i hi).static b).hasCanonicalWindow := fun n =>
    (F.tower.history (ind n)).hcanK_rescale_P6X3 (hc n) (recKHo n) (hcan n)
  have hQpos : ∀ n, 0 < ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ := fun n =>
    lt_of_lt_of_le (hRpos n) (hceil n)
  have hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) *
      max ((n : ℝ) + 1) (((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹) ≤
      (((F.tower.history (ind n)).recordsKRescale_P6X3 (hc n) (recKHo n) i hi).static b
        ).neck.scale := fun n i hi b =>
    le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (le_trans (by positivity) (le_max_left _ _))) (hbirth n i hi b)
  have hNfQ : ∀ (n : ℕ) i hi b, Nf n *
      ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ ≤
      (((F.tower.history (ind n)).recordsKRescale_P6X3 (hc n) (recKHo n) i hi).static b
        ).neck.scale := fun n i hi b =>
    le_trans (mul_le_mul (le_max_right _ _) (le_max_right _ _) (hQpos n).le
      (le_trans (by positivity) (le_max_left _ _))) (hbirth n i hi b)
  have hslabT : ∀ n (i : Fin ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).eventCount),
      ((((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).toHistory.event i).incoming
        ).DerivativeBoundBefore Ctime
        (((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹)
        (min (((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time i.succ) (Tn n : ℝ)) :=
    fun n i => hslabK_of_tds_HND hanti hTD ind c hc (fun n => (Tn n : ℝ)) n i
  have haccN : ∀ n : ℕ, ((p n).rescale_P6N (c n) (hc n)).modelAccuracy ≤ 1 / ((n : ℝ) + 1) :=
    fun n => (hacc n).trans (min_le_right _ _)
  have hradN : ∀ n : ℕ, (n : ℝ) + 1 ≤ ((p n).rescale_P6N (c n) (hc n)).modelRadius :=
    fun n => (le_max_right _ _).trans (hrad n)
  have hordN : ∀ n : ℕ, n + 2 ≤ ((p n).rescale_P6N (c n) (hc n)).modelOrder :=
    fun n => (le_max_right _ _).trans (hord n)
  have h3 := hnot Aseed ind c hc Tn pT hTc aSeed haT hclock hone hsm hTn2 seedTrace σ y R hsT has
    L hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii hgateP i hi pm t y' hat hts hy' hcross
    hslab hclose hcompR hcmp hcmpL hgood'
    (fun n => ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹) hceil
    (fun n => (p n).rescale_P6N (c n) (hc n)) (fun n => max 1 (c n * (aSeed n : ℝ) / c n))
    (fun n i hi => (F.tower.history (ind n)).recordsKRescale_P6X3 (hc n) (recKHo n) i hi)
    (fun n => q.rescale_P6N (c n) (hc n)) (fun n => a₀ / c n) hcanK
    (fun n => (hacc n).trans (min_le_left _ _)) (fun n => (le_max_left _ _).trans (hrad n))
    (fun n => (le_max_left _ _).trans (hord n))
    hHIk (fun n i hi => (hδ n i hi).trans (min_le_left _ _)) hNfQ hbirthA hslabT
    (fun n => (hT0eq n).le)
  -- 其余派生项
  have hfinK : ∀ n, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (t n)) (t n))
      ((seedTrace n).point ((Kh n).activeStage (t n)) ((Kh n).activeStage_mono (hat n))
        ((Kh n).activeStage_mono ((hts n).trans (hsT n)))) (y' n) ≠ ⊤ := fun n =>
    ne_top_of_compR_TJ ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top (hcompR n) (hgateP n)
  have hsep : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (j : Fin ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).eventCount)
        (hj : max 1 (c n * (aSeed n : ℝ) / c n) ≤
          ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time j.succ) b,
        (σ n : ℝ) - T / R n < ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time j.succ →
        2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R n) <
          (((F.tower.history (ind n)).recordsKRescale_P6X3 (hc n) (recKHo n) j hj).static b
            ).neck.scale := by
    intro T _ C hC
    obtain ⟨N, hN⟩ := sepBound_TJ hRr C hC
    filter_upwards [eventually_ge_atTop N] with n hn j hj b _
    refine hN n hn _ ?_
    have h1 := hscaleK n j hj b
    have h2 : R n ≤ max ((n : ℝ) + 1) (((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹) :=
      (hceil n).trans (le_max_right _ _)
    exact le_trans (mul_le_mul_of_nonneg_left h2 (by positivity)) h1
  have hT₀K : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop,
      max 1 (c n * (aSeed n : ℝ) / c n) ≤ (σ n : ℝ) - T / R n := by
    intro T hT
    filter_upwards [haS T hT] with n hn
    rw [hT0eq n]
    exact hn
  have hT₀X : ∀ᶠ n in atTop,
      max 1 (c n * (aSeed n : ℝ) / c n) ≤ (t n : ℝ) - (1 / 100 : ℝ) ^ 2 := by
    filter_upwards [hTnS 1 one_pos] with n hn
    rw [hT0eq n]
    have h1 := hclose n
    have h2 := hclock n
    have h3 : (1 : ℝ) / R n = 1 / R n := rfl
    nlinarith [h1, h2, hn]
  exact drvSlots_Rc_of_J10_R4J (K := fun n => (F.tower.history (ind n)).rescale_P6N (c n) (hc n))
    (Ctime := Ctime) (ε := ε) (C1 := C1) (C2 := C2) hC2
    (qK := fun n => (p n).rescale_P6N (c n) (hc n))
    (T₀K := fun n => max 1 (c n * (aSeed n : ℝ) / c n))
    (recordsK := fun n i hi =>
      (F.tower.history (ind n)).recordsKRescale_P6X3 (hc n) (recKHo n) i hi)
    hcanK haccN hradN hordN (pF := fun n => q.rescale_P6N (c n) (hc n))
    (fun n i => (recQ (ind n) i).rescale_P6M (c n) (hc n))
    (fun n i hi => (hδ n i hi).trans (min_le_right _ _)) hphi
    (Q := fun n => ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹)
    (a₀K := fun n => a₀ / c n) hHIk hscaleK (Filter.Eventually.of_forall hbirthA)
    (fun n i t ht x => hpinK ind c hc n i t ⟨ht.1, (by norm_num : (1 / 2 : ℝ) ≤ 1).trans
      ((le_max_left _ _).trans ht.2)⟩ x)
    Tn aSeed haT pT seedTrace hslabT hclock hone hsm σ t y' hsT hat hts hRpos hRr hL i hslab hclose
    hcmp hcmpL hTnS hgood' hfinK hsep hT₀K (fun n => div_pos ha₀ (hc n)) hT₀X h3


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KframeHelpersDrvHI

/-!
# DRVHI G2：`DrvResE2_DW`（`DrvResE_DW` 的剩余项更少的孪生）+ `hDrvJ` / `hDext` 桥（`_DH`）

`DrvResE_DW`（P6DextDriverDrvW）的存在量化去掉 HI / rescale / κ 族，改在桥内付：
* `hHI`（`a₀K := a₀/c`）⇐ `hHI_rescale_P6X3`（`a₀`、`hHI0` 为引擎上下文已有的顶层 `{a₀}` + HI）；
* `hpinch`（`Phi`）/ `hpinchK0` / `hpinchK0′` / `hpinchF` / `hphi`：**同一个** `Phi`
  （`hpinch_of_initial_P6HP`，`A := 1`），同一组 records（引擎 `records` 经 `rescale_P6M`）、同一
  `a₀/c`；`hpinch` ⇐ K 帧引理 `curvatureOperatorLowerBoundAt_stage_of_pinched_DH`；
  `T₀K ↦ T₁ := max (max 1 (T₀/c)) T₀K`（recordsK 限制定义域，hsep / hcanK 同证据）使 `1 ≤ a₀/c + T₁`；
* `hδF` ⇐ `hδF_rescale_P6X3` + 引擎级 `hT₀δ`（`T₀ n ≤ s → q.delta s ≤ 1/(n+1)`，引擎取 `T₀` 时付）；
* `hκR` / `hκRF` ⇐ 逐 `n` FRESH 窗口（`hκR_K_DH` / `hκRF_K_DH`）；`κU := κ`（与 `hkappaC` 同一 κ）；
* `hseed` ⇐ `hsurvive`（A=2，小 T）+ `hanchor0` + `hkappaC`（`hseed_of_tracedKappa_smallT_DH`）。
残余仍含：records 包 hsep/hT₀K/hcanK/hacc/hrad/hord、`hsurvive` / `hextend`、`Q` 元组（hscaleK / hbirthA /
hslabK / hderF）、**GAP e `hfin` + `G`**、`θ₀`/`hsepρ`。状态 PROVISIONAL[`DrvResE2_DW` + 引擎级项]。
生成器 `build-logs/scratch/DRVHI/gen/g2.py`。
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

open ObservedHistory (DepthExtendable)

/-- **driver 剩余前提核 2（`_DW`）**：`DrvResE_DW` 去掉 `r₀ w hseed`、`Phi hpinch`、`κU phi`、`a₀K hHI`、
`hδF`、`hpinchK0`、`hpinchF`、`hκR`、`hκRF`、`hpinchK0′`（桥内付）；`hbirthA` 写成 `a₀/c n`。
逐字缩写，非合同 Prop。 -/
def DrvResE2_DW {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (q : CutoffParameters) (records : GC.LongTime.Ch11.CutoffRecords_C11S F q) (ε C1 C2 : ℝ)
    (Ctime : ℝ≥0) (T₀ Qt : ℕ → ℝ) (a₀ : ℝ) : Prop :=
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
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
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
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
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
          (∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
            ∀ (i : Fin (K n).eventCount) (hi : T₀K n ≤ (K n).time i.succ) b,
              (σ n : ℝ) - T / R n < (K n).time i.succ →
              2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R n) <
                ((recordsK n i hi).static b).neck.scale) ∧
          (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀K n ≤ (σ n : ℝ) - T / R n) ∧
          (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) ∧
          (∀ n : ℕ, (qK n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) ∧
          (∀ n : ℕ, (n : ℝ) + 1 ≤ (qK n).modelRadius) ∧
          (∀ n : ℕ, n + 2 ≤ (qK n).modelOrder) ∧
          ∃ (Cst : ℝ≥0),
          (∀ A T Q : ℝ, 0 < A → 0 < T → 2 ≤ Q → 4 * (Cst : ℝ) * Q * T ≤ 1 →
            ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
              (∀ z ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
                  (A / Real.sqrt (R n)),
                metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) z ≤ Q * R n) →
              (Kh n).isTracedRegion (σ n) (y n) (A / Real.sqrt (R n)) (T / R n) (K * R n)) ∧
          (∀ σs : ℕ → ℕ, StrictMono σs → ∀ Tstar M : ℝ, 0 < Tstar → 0 ≤ M →
            (∀ T : ℝ, 0 < T → T < Tstar → DepthExtendable Kh σ y R σs T) →
            (∀ T' : ℝ, 0 < T' → T' < Tstar → ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
            ∀ x ∈ riemannianBallOf ((Kh (σs i)).stageMetric
                ((Kh (σs i)).activeStage (σ (σs i))) (σ (σs i))) (y (σs i))
                (A / Real.sqrt (R (σs i))),
            ∀ (w : Icc (0 : ℝ) (Kh (σs i)).horizon),
              (w : ℝ) = σ (σs i) - T' / R (σs i) →
            ∀ (hwt : w ≤ σ (σs i))
              (Bt : BackwardPointTrace (Kh (σs i)) ((Kh (σs i)).activeStage w)
                ((Kh (σs i)).activeStage (σ (σs i)))
                ((Kh (σs i)).activeStage_mono hwt) x),
              metricScalarAt ((Kh (σs i)).stageMetric ((Kh (σs i)).activeStage w) w)
                (Bt.point ((Kh (σs i)).activeStage w) le_rfl
                  ((Kh (σs i)).activeStage_mono hwt)) ≤
                M * R (σs i)) →
            DepthExtendable Kh σ y R σs (Tstar + 1 / (32 * ((Cst : ℝ) + 1) * (M + 1)))) ∧
          ∃ (Q : ℕ → ℝ),
          (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
            ((recordsK n i hi).static b).neck.scale) ∧
          (∀ᶠ n in atTop, ∀ i hi b,
            1 ≤ a₀ / c n * ((recordsK n i hi).static b).neck.scale) ∧
          (∀ n, (K n).EventSlabsDerivative Ctime (Q n) (Fin.last (K n).eventCount)) ∧
          (∃ (hfin : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon)
            (G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
              ((K n).time (Fin.last (K n).eventCount)) (K n).horizon),
            (∀ n, G n = ((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl) ∧
            (∀ n, (G n).DerivativeBoundBefore Ctime (Q n) (K n).horizon)) ∧
          ∃ θ₀ : ℝ, 0 < θ₀ ∧ ∀ (j : ∀ k, Fin (K k).eventCount),
            (∀ k, (K k).time (j k).castSucc < (σ k : ℝ)) →
            (∀ k, (σ k : ℝ) < (K k).time (j k).succ) →
            ∀ B : ℝ, 0 < B → ∀ᶠ n in atTop,
              ∀ (i : Fin (K n).eventCount)
                (_hi : (Tn n : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2 ≤ (K n).time i.succ)
                (b : ((K n).toHistory.event i).RetainedBoundaryIndex), i.succ ≤ (j n).castSucc →
                ((σ n : ℝ) - B / R n ≤ (K n).time i.succ ∨
                  (σ n : ℝ) - (K n).time i.succ ≤ θ₀ * ((((records (ind n) i).rescale_P6M (c n)
                    (hc n)).static b).neck.scale)⁻¹) →
                ((n : ℝ) + 1) * max ((n : ℝ) + 1)
                    ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ (2 : ℕ))⁻¹ ≤
                  (((records (ind n) i).rescale_P6M (c n) (hc n)).static b).neck.scale

/-- **hDrvJ ⇐ guarded2 driver，`DrvResE2_DW` 版（`_DH`）**：结论同 `hDrvJ_of_drvRes_DW`；
HI / rescale / κ 族在桥内付。
PROVISIONAL[`DrvResE2_DW` + 引擎级 `hfresh / records / hfine / hder / hanti / hHI0 / hT₀δ`]。 -/
theorem hDrvJ_of_drvRes2_DH {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {T₀ Qt : ℕ → ℝ} {a₀ : ℝ}
    (hε : 0 < ε) (hεX : ε ≤ crossingWindowNeckAccuracy.{u}) (hεN : ε ≤ crossingNeckAccuracy.{u})
    (hεle : ε ≤ coneAccuracy) (hC2 : 0 ≤ C2)
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hder : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hfresh : ∀ A : ℝ, 0 < A → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ, ∀ n,
      KappaSeedWindowFwd_C11PK (fun w => q.neckRadius (4 * w / 3)) A κ Tf
        (F.tower.history n).toHistory)
    (records : GC.LongTime.Ch11.CutoffRecords_C11S F q)
    (hfine : ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T₀ : ℝ, ∀ n, ∃ p : CutoffParameters,
      D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
      ∃ records' : ∀ i : Fin (F.tower.history n).eventCount,
          T₀ ≤ (F.tower.history n).time i.succ →
          GeometricCutoffRecord (F.tower.history n).toHistory i p,
        (∀ i hi b, ((records' i hi).static b).hasCanonicalWindow) ∧
        ∀ i hi b, ((records' i hi).static b).neck.scale = ((records n i).static b).neck.scale)
    (ha₀ : 0 < a₀)
    (hHI0 : ∀ n x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
      -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x)
    (hT₀δ : ∀ (n : ℕ) (s : ℝ), T₀ n ≤ s → q.delta s ≤ 1 / ((n : ℝ) + 1))
    (hres : DrvResE2_DW F q records ε C1 C2 Ctime T₀ Qt a₀) :
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
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
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
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
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
          (∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
            ∀ (i : Fin (K n).eventCount) (hi : T₀K n ≤ (K n).time i.succ) b,
              (σ n : ℝ) - T / R n < (K n).time i.succ →
              2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R n) <
                ((recordsK n i hi).static b).neck.scale) ∧
          (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀K n ≤ (σ n : ℝ) - T / R n) ∧
          (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) ∧
          (∀ n : ℕ, (qK n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) ∧
          (∀ n : ℕ, (n : ℝ) + 1 ≤ (qK n).modelRadius) ∧
          (∀ n : ℕ, n + 2 ≤ (qK n).modelOrder) ∧
          ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
            ∀ T : ℝ, 0 < T → ObservedHistory.DepthExtendable Kh σ y R (φ ∘ ψ) T := by
  obtain ⟨Phi, hPhi, hP⟩ := hpinch_of_initial_P6HP.{u} (A := (1 : ℝ)) one_pos
  intro A hA ind Ho Tno pTo r hr hk h2r hsmo hvolo c hc K Kh Tn pT aSeed haT hclock h1 hsm hlate
    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
    hball hdistσ hev hlt
  obtain ⟨qK, T₀K, recK, hsep, hT₀K, hcanK, hacc, hrad, hord, Cst, hsurv, hext, Q, hscaleK,
    hbirthA, hslabK, ⟨hfin, G, hG, hderF⟩, θ₀, hθ₀, hsepρ⟩ :=
    hres A hA ind Tno pTo r hr hk h2r hsmo hvolo aSeed haT hclock h1 hsm hlate
      seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
      hball hdistσ hev hlt
  -- T₁ := max (max 1 (T₀/c)) T₀K：records 定义域限制，使 1 ≤ T₁ 且 δ 阈值过
  obtain ⟨T₁, hT₁a, hT₁b, hT₁c, hT₁ev⟩ : ∃ T₁ : ℕ → ℝ, (∀ n, 1 ≤ T₁ n) ∧
      (∀ n, T₀ n / c n ≤ T₁ n) ∧ (∀ n, T₀K n ≤ T₁ n) ∧
      ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₁ n ≤ (σ n : ℝ) - T / R n := by
    refine ⟨fun n => max (max 1 (T₀ n / c n)) (T₀K n),
      fun n => (le_max_left _ _).trans (le_max_left _ _),
      fun n => (le_max_right _ _).trans (le_max_left _ _), fun n => le_max_right _ _, ?_⟩
    intro T hT
    filter_upwards [hT₀K T hT, hwin T hT] with n hn1 hn2
    refine max_le (max_le ?_ ?_) hn1
    · linarith [h1 n]
    · have : T₀ n / c n ≤ (aSeed n : ℝ) := (div_le_iff₀ (hc n)).2 (by rw [mul_comm]; exact hlate n)
      linarith
  let recK' : ∀ n (i : Fin (K n).eventCount), T₁ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (qK n) :=
    fun n i hi => recK n i ((hT₁c n).trans hi)
  have hsep' : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₁ n ≤ (K n).time i.succ) b,
        (σ n : ℝ) - T / R n < (K n).time i.succ →
        2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R n) < ((recK' n i hi).static b).neck.scale :=
    fun T hT C hC => (hsep T hT C hC).mono fun n hn i hi b hlt => hn i ((hT₁c n).trans hi) b hlt
  have hcanK' : ∀ n i hi b, ((recK' n i hi).static b).hasCanonicalWindow :=
    fun n i hi b => hcanK n i _ b
  have hscaleK' : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recK' n i hi).static b).neck.scale := fun n i hi b => hscaleK n i _ b
  have hbirthA' : ∀ᶠ n in atTop, ∀ i hi b,
      1 ≤ a₀ / c n * ((recK' n i hi).static b).neck.scale :=
    hbirthA.mono fun n hn i hi b => hn i _ b
  choose j hjt htj using hev
  have hσH : ∀ k, (σ k : ℝ) < (Kh k).horizon := fun k =>
    lt_of_lt_of_le (htj k) ((Kh k).time_le_horizon_at _)
  have hA0 : (0 : ℝ) < A := by linarith
  have hR1 : ∀ k, (1 : ℝ) ≤ R k := fun k => by
    have := hRr k
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  obtain ⟨κ, hκ, Tf, hsup⟩ := hfresh (A + 3 + 7) (by linarith)
  have hsupK := GC.LongTime.Ch11.fresh_rescale_adapter_P6JA hsup ind c hc
  have hprep0 := fun k => ObservedHistory.freshK_prep_J11S hanti (Ho k) (Tno k) (pTo k) (hr k)
    hA0 (Tno k).2.1 (h2r k) (hvolo k) (hR1 k) (hRρ k)
  have hTf : ∀ᶠ k in atTop, Tf / c k ≤ (Tn k : ℝ) := by
    obtain ⟨N, hN⟩ := exists_nat_ge Tf
    filter_upwards [eventually_ge_atTop N] with k hkN
    have h1' : (N : ℝ) ≤ k := by exact_mod_cast hkN
    exact (ObservedHistory.freshK_prep_J11S hanti (Ho k) (Tno k) (pTo k) (hr k) hA0
      (by linarith [hk k]) (h2r k) (hvolo k) (hR1 k) (hRρ k)).1
  -- 同一个 Phi：HI、pinching（event / final）
  have ha₀K : ∀ n, 0 < a₀ / c n := fun n => div_pos ha₀ (hc n)
  have hHIK : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ / c n) x ∧
      -3 / (a₀ / c n) ≤ metricScalarAt ((K n).initialMetric 0) x :=
    fun n => (F.tower.history (ind n)).hHI_rescale_P6X3 (hc n) (hHI0 (ind n))
  have hrecF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (q.rescale_P6N (c n) (hc n)) :=
    fun n i => (records (ind n) i).rescale_P6M (c n) (hc n)
  have hP1 := hP K (fun n => q.rescale_P6N (c n) (hc n)) hrecF (fun n => a₀ / c n) T₁ ha₀K
    (fun n => by have := hT₁a n; have := (ha₀K n).le; linarith) hHIK
  have hpinchK0 := hP1.1
  have hGinit : ∀ n, (G n).flow.base.metric ((K n).time (Fin.last (K n).eventCount)) =
      (K n).initialMetric (Fin.last (K n).eventCount) := fun n => by
    rw [hG n]
    exact (K n).toHistory.final_initial (hfin n)
  have hpinchF : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₁ n)) Phi :=
    fun n => hP1.2 (fun n => (K n).horizon) G hGinit n
  have hpinchK0' : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩
        Ici ((Tn n : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2)) Phi :=
    (hP K (fun n => q.rescale_P6N (c n) (hc n)) hrecF (fun n => a₀ / c n)
      (fun n => (Tn n : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2) ha₀K
      (fun n => by
        have h2 := (hprep0 n).2.1
        have h3 := (ha₀K n).le
        norm_num at h2 ⊢
        linarith) hHIK).1
  have hpinch : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
        ((Kh n).activeStage_mono hvt) x,
        curvatureOperatorLowerBoundAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
          (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
          (metricAlgebraicCurvatureTensorAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
          (Phi (metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))) := by
    intro D T _ hT
    filter_upwards [hT₁ev T hT] with n hn x _ v hvt hv tr
    have hvh : (v : ℝ) < (K n).horizon := lt_of_le_of_lt hvt (hσH n)
    exact ObservedHistory.curvatureOperatorLowerBoundAt_stage_of_pinched_DH (K n) (hpinchK0 n)
      (hfin n) (by rw [← hG n]; exact hpinchF n) v (hn.trans hv) hvh _
  -- hanchor0 ⇐ RECUP（FRESH 经 rescale adapter）
  have hsupA : ∀ Aseed : ℝ, 1 < Aseed → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ,
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) (k : ℕ),
        KappaSeedWindowFwd_C11PK
          (fun w => q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k)) (Aseed + 7) κ
          (Tf / c k) ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory := by
    intro Aseed hAs
    obtain ⟨κ, hκ, Tf, hsup⟩ := hfresh (Aseed + 7) (by linarith)
    exact ⟨κ, hκ, Tf, GC.LongTime.Ch11.fresh_rescale_adapter_P6JA hsup⟩
  have hanc := hanchor0_hPN_frame_RU hεle hC2 hanti hder T₀ hsupA hPhi hθ₀ records hfine hA ind
    Tno pTo r hr hk h2r hsmo hvolo aSeed haT hclock h1 hsm hlate seedTrace σ y R hsT has L hRdef
    hRpos hRr hL hgood hwin hwin' hRρ hball hdistσ hpinchK0' j hjt htj (hsepρ j hjt htj)
  -- hkappaC ⇐ J11STAY（Aseed := A + 3）
  have hdσ' : ∀ᶠ k in atTop,
      riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
          ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
            ((Kh k).activeStage_mono (hsT k))) (y k) +
        ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3 + 3) * 1) :=
    hdistσ.mono fun k hk => hk.trans (ENNReal.ofReal_le_ofReal (by linarith))
  have hkap := ObservedHistory.hkappaC_driver_of_drv_J11S (Cg := 4) (haT := haT) hC2 K hclock h1
    hsm seedTrace σ y R hsT has L hRpos hRr hL hgood hσH
    (fun k τ x => ObservedHistory.hpin_rescaled_of_records_P6HI F records ind c hc k τ x)
    qK T₁ recK' hsep' hT₁ev hcanK' hacc hrad hord (by linarith : (0 : ℝ) < A + 3)
    (fun k w => q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k)) (fun k => Tf / c k)
    hsupK hTf (fun k => by simpa using (hprep0 k).2.1) (fun k => (hprep0 k).2.2.1)
    (fun k => (hprep0 k).2.2.2)
    hwin hwin' hdσ'
  -- hseed ⇐ hsurvive（A = 2·1，小 T）+ hanchor0 + hkappaC
  obtain ⟨Qa, hQa2, hQaev⟩ := hanc (2 * 1) (by norm_num)
  have hCst0 : (0 : ℝ) ≤ (Cst : ℝ) := NNReal.coe_nonneg Cst
  have hden : 0 < 4 * (Cst : ℝ) * Qa + 1 := by
    have := mul_nonneg hCst0 (by linarith : (0 : ℝ) ≤ Qa)
    linarith
  have hT0pos : 0 < 1 / (4 * (Cst : ℝ) * Qa + 1) := by positivity
  have hT04 : 4 * (Cst : ℝ) * Qa * (1 / (4 * (Cst : ℝ) * Qa + 1)) ≤ 1 := by
    rw [mul_one_div, div_le_one hden]
    linarith
  obtain ⟨K1, hK1, hev1⟩ := hsurv (2 * 1) (1 / (4 * (Cst : ℝ) * Qa + 1)) Qa (by norm_num) hT0pos
    hQa2 hT04
  have hTR1 : ∀ᶠ n in atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * 1 / Real.sqrt (R n))
      ((1 / (4 * (Cst : ℝ) * Qa + 1)) / R n) (K1 * R n) :=
    (hev1.and hQaev).mono fun n hn => hn.1 hn.2
  have hkap1 := hkap id strictMono_id 1 (1 / (4 * (Cst : ℝ) * Qa + 1)) K1 one_pos hT0pos hK1
    (by rw [Filter.map_id]; exact hTR1)
  rw [Filter.map_id] at hkap1
  have hr₀pos : 0 < min (min 1 (1 / (4 * (Cst : ℝ) * Qa + 1))) (1 / (K1 + 1)) :=
    lt_min (lt_min one_pos hT0pos) (by positivity)
  have hr₀1 : min (min 1 (1 / (4 * (Cst : ℝ) * Qa + 1))) (1 / (K1 + 1)) ≤ 1 :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hr₀T : min (min 1 (1 / (4 * (Cst : ℝ) * Qa + 1))) (1 / (K1 + 1)) ≤
      1 / (4 * (Cst : ℝ) * Qa + 1) := (min_le_left _ _).trans (min_le_right _ _)
  have hr₀K : min (min 1 (1 / (4 * (Cst : ℝ) * Qa + 1))) (1 / (K1 + 1)) * (K1 + 1) ≤ 1 := by
    have h := min_le_right (min 1 (1 / (4 * (Cst : ℝ) * Qa + 1))) (1 / (K1 + 1))
    have hK1' : 0 < K1 + 1 := by linarith
    calc _ ≤ 1 / (K1 + 1) * (K1 + 1) := mul_le_mul_of_nonneg_right h hK1'.le
      _ = 1 := by field_simp
  have hctrl := hTR1.mono fun n hn => ObservedHistory.controlled_of_traced_DH (Kh n) (σ n) (y n)
    (hRpos n) hK1 hr₀pos hr₀1 hr₀T hr₀K hn
  have hseed := ObservedHistory.hseed_of_tracedKappa_smallT_DH hRpos (fun _ : ℕ => (1 : ℝ) / 200)
    hradii hT0pos hkap1 hr₀pos hctrl
  -- hκR / hκRF ⇐ 逐 n FRESH 窗口
  have hvolW : ∀ k, ENNReal.ofReal ((A + 3 + 7)⁻¹ * (1 : ℝ) ^ 3) ≤
      ballVolume ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k)) (pT k) 1 :=
    fun k => le_trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (inv_anti₀ (by linarith) (by linarith)) (by norm_num))) (hprep0 k).2.2.1
  have hκR := ObservedHistory.hκR_K_DH Kh hκ.le (by linarith : A + 3 ≤ A + 3 + 7)
    (nr := fun k w => q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k)) hsupK Tn aSeed haT pT
    seedTrace (fun _ => 1) (fun _ => 1 / 200) hTf (fun k => by simpa using (hprep0 k).2.1) hsm
    hvolW hclock (fun _ => by norm_num) (fun k w h1 h2 => (hprep0 k).2.2.2 w h1 h2)
  have hκRF := ObservedHistory.hκRF_K_DH Kh hκ.le (by linarith : A + 3 ≤ A + 3 + 7)
    (nr := fun k w => q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k)) hsupK Tn aSeed haT pT
    seedTrace (fun _ => 1) (fun _ => 1 / 200) hTf (fun k => by simpa using (hprep0 k).2.1) hsm
    hvolW hclock (fun _ => by norm_num) (fun k w h1 h2 => (hprep0 k).2.2.2 w h1 h2)
  refine ⟨qK, T₁, recK', hsep', hT₁ev, hcanK', hacc, hrad, hord, ?_⟩
  -- 前缀直接付的 driver 输入
  have hRlim : Tendsto R atTop atTop :=
    tendsto_atTop_mono hRr (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hRr2 : Tendsto (fun n => R n * (fun _ : ℕ => (1 : ℝ)) n ^ 2) atTop atTop := by
    simpa using hRlim
  have hhalf : ∀ᶠ n in atTop, (Tn n : ℝ) - (fun _ : ℕ => (1 : ℝ)) n ^ 2 / 2 ≤ (σ n : ℝ) :=
    (hwin' 1 one_pos).mono fun n hn => by
      have := div_pos one_pos (hRpos n)
      change (Tn n : ℝ) - 1 ^ 2 / 2 ≤ (σ n : ℝ)
      linarith
  have htime : ∀ᶠ n in atTop, 2 * (fun _ : ℕ => (1 : ℝ)) n ^ 2 < (Tn n : ℝ) :=
    Filter.Eventually.of_forall fun n => (hprep0 n).2.1
  have hRa : ∀ n, 1 ≤ R n * aSeed n := fun n =>
    one_le_mul_of_one_le_of_one_le (hR1 n) (h1 n)
  have hdfin : ∀ n, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
      ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
        ((Kh n).activeStage_mono (hsT n))) (y n) ≠ ⊤ := fun n => ne_top_of_lt (hball n)
  have hδF' : ∀ n (i : Fin (K n).eventCount), T₁ n ≤ (K n).time i.succ →
      (q.rescale_P6N (c n) (hc n)).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1) :=
    fun n i hi => RetainedCoreHistory.hδF_rescale_P6X3 (F.tower.history (ind n)) (hc n)
      (fun i' hi' => hT₀δ n _ hi') i (max_le (hT₁a n) (hT₁b n) |>.trans hi)
  exact ObservedHistory.forall_subseq_depthExtendable_of_guarded2_DW
    (G := G)
    (Q := Q) (a₀ := fun n => a₀ / c n) (Aκ := A + 3) (pF := q) (rX := 1)
    F ind c hc K rfl Kh σ y R hRr hsurv hanc hext hr₀pos hκ hseed hκ (fun _ => 1 / 200) hradii
    hkap hPhi hpinch hε hεX hεN Tn aSeed haT hsT has pT seedTrace L hL hgood hwin rfl
    (fun _ => 1) hhalf htime (Filter.Eventually.of_forall hsm)
    (Filter.Eventually.of_forall hclock) hRr2
    records qK T₁ recK' hsep' hT₁ev hεle hκ hPhi hfin hG hHIK hcanK' hδF' hacc hrad hord
    hscaleK' hbirthA' hpinchK0 hslabK hpinchF hderF (fun _ => 1 / 200) hradii hC2 hroom hdistσ hκR
    hκRF one_pos hsm hclock hRa (fun _ => 0) (ObservedHistory.hT₀X_zero_A6K aSeed)
    (ObservedHistory.hOldX_kernel_A6K K _) hdfin


/-- **hDext ⇐ guarded2 driver，`DrvResE2_DW` 版（`_DH`）**：末合取。 -/
theorem hDext_of_drvRes2_DH {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {T₀ Qt : ℕ → ℝ} {a₀ : ℝ}
    (hε : 0 < ε) (hεX : ε ≤ crossingWindowNeckAccuracy.{u}) (hεN : ε ≤ crossingNeckAccuracy.{u})
    (hεle : ε ≤ coneAccuracy) (hC2 : 0 ≤ C2)
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hder : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hfresh : ∀ A : ℝ, 0 < A → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ, ∀ n,
      KappaSeedWindowFwd_C11PK (fun w => q.neckRadius (4 * w / 3)) A κ Tf
        (F.tower.history n).toHistory)
    (records : GC.LongTime.Ch11.CutoffRecords_C11S F q)
    (hfine : ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T₀ : ℝ, ∀ n, ∃ p : CutoffParameters,
      D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
      ∃ records' : ∀ i : Fin (F.tower.history n).eventCount,
          T₀ ≤ (F.tower.history n).time i.succ →
          GeometricCutoffRecord (F.tower.history n).toHistory i p,
        (∀ i hi b, ((records' i hi).static b).hasCanonicalWindow) ∧
        ∀ i hi b, ((records' i hi).static b).neck.scale = ((records n i).static b).neck.scale)
    (ha₀ : 0 < a₀)
    (hHI0 : ∀ n x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
      -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x)
    (hT₀δ : ∀ (n : ℕ) (s : ℝ), T₀ n ≤ s → q.delta s ≤ 1 / ((n : ℝ) + 1))
    (hres : DrvResE2_DW F q records ε C1 C2 Ctime T₀ Qt a₀) :
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
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
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
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
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
        (∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
            ∀ T : ℝ, 0 < T → DepthExtendable Kh σ y R (φ ∘ ψ) T) := by
  intro A hA ind Ho Tno pTo r hr hk h2r hsmo hvolo c hc K Kh Tn pT aSeed haT hclock h1 hsm hlate
    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
    hball hdistσ hev hlt
  obtain ⟨-, -, -, -, -, -, -, -, -, h⟩ := hDrvJ_of_drvRes2_DH hε hεX hεN hεle hC2 hanti hder
    hfresh records hfine ha₀ hHI0 hT₀δ hres A hA ind Tno pTo r hr hk h2r hsmo hvolo aSeed haT
    hclock h1 hsm hlate
      seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
      hball hdistσ hev hlt
  exact h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

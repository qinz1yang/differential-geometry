import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DextDriverFinalQUniCgDF

/-!
# FSUP G1：F 线 `DrvResF_DT` 的过渡形 ThS（后缀 `_FS`）

`DrvResF_DT` / `DrvResF_DT_Cg_DF`（final 帧 driver 剩余输入核，38 项断言）的缩小形
`DrvResF_DT_ThS_FS` / `DrvResF_DT_Cg_ThS_FS`：前提段逐字，结论只留 records 族
（`qK T₀K recordsK hsep hT₀K hcanK hacc hrad hord`）、`∃ Cst, hsurv ∧ hext`、`hscaleK hbirthA`、θ₀ 尾
（`a₀` 参数同 `DrvResE3_DT_HFT`）；其余 HI / κ / pinching 族由桥 `P6DrvResFThSFS` 内付。
**本 def 不是任何交付定理的假设**：它只是桥（`drvResF_DT_of_ThS_FS`）与引擎供给
（`drvResF_ThS_of_engine_FS`，`P6DrvResFEngFS`）之间的接口；引擎供给在 SCRS⁺ 实际 records 上直接证出它
（R-C11-26 F-26-1：不做 `∀ records` 槽核）。无新 binder，无新合同 Prop。
生成器 `build-logs/scratch/O-CH11-FSUP/gen/g1_defs.py`（切片 + 边界断言）。
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

/-- **F 线 θ₀ 尾核的过渡形 ThS（`_FS`，逐字缩写 def，非合同 Prop）**：`DrvResF_DT` 前提段逐字；
结论留 records 族（`qK T₀K recordsK hsep hT₀K hcanK hacc hrad hord`）+ `∃ Cst, hsurv ∧ hext` +
`hscaleK hbirthA` + θ₀ 尾（`DrvResE3_DT_HFT` 同构；HI / κ / pinching 族
`r₀ w hseed Phi hPhi κU phi a₀K hHI hδF hpinch* hκR hκRF` 由桥内付）。 -/
def DrvResF_DT_ThS_FS {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g)
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
          (hevF : ∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (σ k : ℝ) ∧
            (σ k : ℝ) < (Kh k).horizon) →
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
          (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1)
              ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ ≤
            ((recordsK n i hi).static b).neck.scale) ∧
          (∀ᶠ n in atTop, ∀ i hi b,
            1 ≤ a₀ / c n * ((recordsK n i hi).static b).neck.scale) ∧
          ∃ θ₀ : ℝ, 0 < θ₀ ∧
            ∀ B : ℝ, 0 < B → ∀ᶠ n in atTop,
              ∀ (i : Fin (K n).eventCount)
                (_hi : (Tn n : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2 ≤ (K n).time i.succ)
                (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
                i.succ ≤ Fin.last (K n).eventCount →
                ((σ n : ℝ) - B / R n ≤ (K n).time i.succ ∨
                  (σ n : ℝ) - (K n).time i.succ ≤ θ₀ * ((((records (ind n) i).rescale_P6M (c n)
                    (hc n)).static b).neck.scale)⁻¹) →
                ((n : ℝ) + 1) * max ((n : ℝ) + 1)
                    ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ (2 : ℕ))⁻¹ ≤
                  (((records (ind n) i).rescale_P6M (c n) (hc n)).static b).neck.scale

/-- **ThS，JF8 / Cg 版（`_FS`）**：`DrvResF_DT_Cg_DF` 前提段逐字，结论同 `DrvResF_DT_ThS_FS`。 -/
def DrvResF_DT_Cg_ThS_FS {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g)
    (q : CutoffParameters) (records : GC.LongTime.Ch11.CutoffRecords_C11S F q) (Cg ε C1 C2 : ℝ)
    (Ctime : ℝ≥0) (εb C1b C2b : ℝ) (Ctimeb : ℝ≥0) (T₀ Qt : ℕ → ℝ) (a₀ : ℝ) : Prop :=
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
          (hevF : ∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (σ k : ℝ) ∧
            (σ k : ℝ) < (Kh k).horizon) →
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
          (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1)
              ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ ≤
            ((recordsK n i hi).static b).neck.scale) ∧
          (∀ᶠ n in atTop, ∀ i hi b,
            1 ≤ a₀ / c n * ((recordsK n i hi).static b).neck.scale) ∧
          ∃ θ₀ : ℝ, 0 < θ₀ ∧
            ∀ B : ℝ, 0 < B → ∀ᶠ n in atTop,
              ∀ (i : Fin (K n).eventCount)
                (_hi : (Tn n : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2 ≤ (K n).time i.succ)
                (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
                i.succ ≤ Fin.last (K n).eventCount →
                ((σ n : ℝ) - B / R n ≤ (K n).time i.succ ∨
                  (σ n : ℝ) - (K n).time i.succ ≤ θ₀ * ((((records (ind n) i).rescale_P6M (c n)
                    (hc n)).static b).neck.scale)⁻¹) →
                ((n : ℝ) + 1) * max ((n : ℝ) + 1)
                    ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ (2 : ℕ))⁻¹ ≤
                  (((records (ind n) i).rescale_P6M (c n) (hc n)).static b).neck.scale

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

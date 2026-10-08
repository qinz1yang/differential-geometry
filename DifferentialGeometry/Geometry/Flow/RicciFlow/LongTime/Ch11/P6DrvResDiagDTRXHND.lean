import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvResDiagDTRXHNR
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HnotPrefixProdHNF
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KernelSlabKTSupplyP6KT
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilHnRCH2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvResJ10JP

/-!
# HNOTDT G1（DT 线，`_HND`）：`DrvResE_DT_RX_HSX` 的 `hnot` 合取 + producer 组合

* `DrvResE_DT_RX_HSX_HNO`：`DrvResE_DT_RX_HSX` + 同元组 J10 `hnot` 合取
  （与 J10PAY `J10ResE2_DJ` 末合取同形，`T₀K` 不抬高）；
* `hslabK_of_tds_HND`（PROVED）：K 帧 `hslabK`（截断 `Tn`，`Q := ρ̃(Tn)⁻²`）
  ⇐ 先验 TDS（`hkernelDtT_of_supply_P6KT`）；
* `drvDTRX_HNO_at_seq_HND`（PROVED 组合）：`DrvResE_DT_RX_HSX_HNR` ⇒ `_HNO`，
  常数 `csSeq/ctSeq_CH2` 显式；
  hnotK 的两条前缀 Dt 由 TDS 的 hslabK 直接供给（DT 线无 `EventSlabsDerivative` 合取）；
* `drvDTRX_HNO_of_HNR_HND`（PROVED）：`∃ (Ctime₀, Cs)` 形（与 `drvRX_HNO_of_HNR` 同形）；
* `j10ResE2_of_hnot_HND`（PROVED）：HNO 的 hnot 合取 = `J10ResE2_DJ` 末合取（对齐）。
无新顶层 binder；`hanti`、`hder` 为 DRVTRUNC 桥原有前提。生成器 `build-logs/scratch/HNOTDT/gen/gen.py`。
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

/-- **`DrvResE_DT_RX_HSX` + `hnot` 合取（`_HNO`，逐字缩写 def）**：`DrvResE_DT_RX_HSX` 逐字，在 `∃ a₀K` 之后加一条同元组
`(qK, T₀K, recordsK)` 的 J10 `hnot` 合取（prefix 帧、`θcap = 1 − 1/(n+2)`、`D = n+1`、
records = `prefixLateRecords_P6N (recordsK n)`、`T₀K` 不抬高；与 `J10ResE2_DJ` 末合取同形）。DT 线无
`EventSlabsDerivative` 合取：Dt 由先验 TDS 供给（见 `hslabK_of_tds_HND`）。 -/
def DrvResE_DT_RX_HSX_HNO {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g)
    (q : CutoffParameters) (records : GC.LongTime.Ch11.CutoffRecords_C11S F q) (ε C1 C2 : ℝ)
    (Ctime : ℝ≥0) (T₀ Qt : ℕ → ℝ) : Prop :=
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
          J10ResE_RX_HSX K σ y R qK T₀K ∧
          ∃ (r₀ w : ℝ), 0 < r₀ ∧ 0 < w ∧
          (∀ᶠ n in atTop,
              ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
                Integral.Measure.riemannianVolumeMeasure ThreeModel ((Kh n).stageAt (σ n)).Carrier
                  ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                  (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
                    (r₀ / Real.sqrt (R n)))) ∧
          ∃ (Phi : ℝ → ℝ), Perelman.AdmissiblePinchingFunction Phi ∧
          (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
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
                    (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))))) ∧
          ∃ (κU : ℝ) (phi : ℝ → ℝ), 0 < κU ∧ Perelman.AdmissiblePinchingFunction phi ∧
          ∃ (a₀K : ℕ → ℝ),
          (∀ (j : ∀ k, Fin (K k).eventCount) (_hjt : ∀ k, (K k).time (j k).castSucc < (σ k : ℝ))
            (_htj : ∀ k, (σ k : ℝ) < (K k).time (j k).succ)
            (yG : ∀ k, ((K k).stage (j k).castSucc).Carrier), (∀ k, HEq (y k) (yG k)) →
            ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
              (hi : T₀K n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
              (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
              (A' : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
                (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
              (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
              (x : standardCapWindow (qK n).modelRadius),
              A'.point i.succ le_rfl hl =
                  (((K n).prefixLateRecords_P6N (j n).castSucc (recordsK n) i hi).static
                    b).window x ∧
                ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
                (σ n : ℝ) - ((K n).prefixAt (j n).castSucc).time i.succ ≤
                  (1 - 1 / ((n : ℝ) + 2)) *
                    ((((K n).prefixLateRecords_P6N (j n).castSucc (recordsK n) i hi).static
                      b).neck.scale)⁻¹) ∧
          (∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀K n) x ∧
            -3 / a₀K n ≤ metricScalarAt ((K n).initialMetric 0) x) ∧
          (∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
            (q.rescale_P6N (c n) (hc n)).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) ∧
          (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1)
              ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ ≤
            ((recordsK n i hi).static b).neck.scale) ∧
          (∀ᶠ n in atTop, ∀ i hi b,
            1 ≤ a₀K n * ((recordsK n i hi).static b).neck.scale) ∧
          (∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
            ((K n).toHistory.event i).incoming.flow
            (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀K n)) phi) ∧
          (∃ (hfin : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon)
            (G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
              ((K n).time (Fin.last (K n).eventCount)) (K n).horizon),
            (∀ n, G n = ((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl) ∧
            (∀ n, Perelman.PhiAlmostNonnegative (G n).flow
            (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀K n)) phi)) ∧
          (∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
            (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
            (Tn n : ℝ) - (1 : ℝ) ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
            (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
              (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
              ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
                riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
                  ENNReal.ofReal ρU) →
            (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
              (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
              ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
                riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                    ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
                      ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
                  ENNReal.ofReal ((A + 3) * 1)) →
            ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
              (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
              ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
              ∀ b : ℝ, 0 < b → b ≤ (1 / 200 : ℝ) → (Kh n).isParabolicallyRmControlledBall τ zz b →
                ENNReal.ofReal κU * ENNReal.ofReal b ^ 3 ≤
                  riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
                    ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                    (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)) ∧
          (∀ᶠ n in atTop, ∀ (c : ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier)
            (U : Set ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier) (a t ρU : ℝ),
            (Tn n : ℝ) - (1 : ℝ) ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
            (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
              (Kh n).time (Fin.last (Kh n).eventCount) < τ → (τ : ℝ) < (Kh n).horizon →
              ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
                riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
                  ENNReal.ofReal ρU) →
            (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
              (Kh n).time (Fin.last (Kh n).eventCount) < τ → (τ : ℝ) < (Kh n).horizon →
              ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
                riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                    ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
                      ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
                  ENNReal.ofReal ((A + 3) * 1)) →
            ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
              (Kh n).time (Fin.last (Kh n).eventCount) < τ → (τ : ℝ) < (Kh n).horizon →
              ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
              ∀ b : ℝ, 0 < b → b ≤ (1 / 200 : ℝ) → (Kh n).isParabolicallyRmControlledBall τ zz b →
                ENNReal.ofReal κU * ENNReal.ofReal b ^ 3 ≤
                  riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
                    ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                    (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)) ∧
          (∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
            ((K n).toHistory.event i).incoming.flow
            (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩
              Ici ((Tn n : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2)) phi) ∧
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

/-- **K 帧 `hslabK`（截断于 `Tn`）⇐ 先验 TDS（`_HND`，PROVED）**：`hkernelDtT_of_supply_P6KT`，
原尺度天花板 `tKo := c·T`、`Qo := ρ(c·T)⁻²`，K 帧阈值 `c·Qo = ρ̃(T)⁻²`（§0.4 同一 `Q`）。与 DRVTRUNC 桥
`hDrvJ_of_drvRes_DT` 的 `hslabK` 同形；前提 `hanti`、`hder` 为桥原有，非新顶层 binder。 -/
theorem hslabK_of_tds_HND {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {Ctd : ℝ≥0}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hder : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctd)
    (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (T : ℕ → ℝ) (n : ℕ)
    (j₀ : Fin ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).eventCount) :
    ((((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).toHistory.event j₀).incoming
      ).DerivativeBoundBefore Ctd ((q.rescale_P6N (c n) (hc n)).neckRadius (T n) ^ 2)⁻¹
      (min (((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time j₀.succ) (T n)) := by
  obtain ⟨hslab0, -⟩ := GC.LongTime.Ch11.hkernelDtT_of_supply_P6KT hder le_rfl hanti
    q.neckRadius_pos ind c hc (fun n => (q.neckRadius (c n * T n) ^ 2)⁻¹)
    (fun n => c n * T n) (fun _ => le_rfl)
  have hTc : c n * T n / c n = T n := mul_div_cancel_left₀ _ (hc n).ne'
  have hQe : c n * (q.neckRadius (c n * T n) ^ 2)⁻¹ =
      ((q.rescale_P6N (c n) (hc n)).neckRadius (T n) ^ 2)⁻¹ :=
    (RetainedCoreHistory.neckRadius_rescale_inv_sq_P6X (hc n) q (T n)).symm
  have h := hslab0 n j₀
  beta_reduce at h
  rwa [hQe, hTc] at h

/-- **`hnot` 项由 hnotK producer 付，DT 线，常数处规格（`_HND`，PROVED 组合）**：`hnotK_seq_a0_HNF`
的 choose 常数 `csSeq_CH2 / ctSeq_CH2`（显式）；孪生 `DrvResE_DT_RX_HSX_HNR` ⇒ `DrvResE_DT_RX_HSX_HNO`。
Dt：`hslabK_of_tds_HND`（TDS 先验，`Q n := ρ̃(Tn)⁻²`）；`Nf := Cb⁻¹`。前提 `hanti`、`hder` 为桥原有（非新顶层 binder）；
`Ctd` 为 TDS 常数（producer 的 `C` 独立于 `Ctime`）。 -/
theorem drvDTRX_HNO_at_seq_HND
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {q : CutoffParameters} {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
    {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {T₀ Qt : ℕ → ℝ} {Ctd : ℝ≥0}
    (hε : 0 < ε) (hε' : ε < 1 / 11)
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hder : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctd)
    (hC1 : GC.LongTime.Ch11.csSeq_CH2.{u} ε ≤ C1) (hC2 : GC.LongTime.Ch11.csSeq_CH2.{u} ε ≤ C2)
    (hCt : GC.LongTime.Ch11.ctSeq_CH2.{u} ε ≤ Ctime)
    (h : DrvResE_DT_RX_HSX_HNR F q records ε C1 C2 Ctime T₀ Qt) :
    DrvResE_DT_RX_HSX_HNO F q records ε C1 C2 Ctime T₀ Qt := by
  have hX := RetainedCoreHistory.hnotK_seq_a0_HNF.{u} hε hε'
  have e1 : GC.LongTime.Ch11.csSeq_CH2.{u} ε =
      Classical.choose (Classical.choose_spec hX) := by
    unfold GC.LongTime.Ch11.csSeq_CH2; rw [dite_eq_left ⟨hε, hε'⟩]
  have e2 : GC.LongTime.Ch11.ctSeq_CH2.{u} ε = Classical.choose hX := by
    unfold GC.LongTime.Ch11.ctSeq_CH2; rw [dite_eq_left ⟨hε, hε'⟩]
  rw [e1] at hC1 hC2
  rw [e2] at hCt
  obtain ⟨-, -, hall⟩ := Classical.choose_spec (Classical.choose_spec hX)
  obtain ⟨Cb, Rn0, ζ0, δ0, m0, hCb, hRn0, hζ0, hδ0, hprod⟩ :=
    hall Ctd (θ := fun n => 1 - 1 / ((n : ℝ) + 2)) RetainedCoreHistory.thetaCap_lt_one_HNF
  have h' := h (fun n => (Cb n)⁻¹) (fun n => min (ζ0 n) (1 / ((n : ℝ) + 1)))
    (fun n => max (Rn0 n) ((n : ℝ) + 1)) (fun n => min (δ0 n) (1 / ((n : ℝ) + 1)))
    (fun n => max (m0 n) (n + 2)) (fun n => lt_min (hζ0 n) (by positivity))
    (fun n => lt_min (hδ0 n) (by positivity)) (fun n => min_le_right _ _)
    (fun n => min_le_right _ _) (fun n => le_max_right _ _) (fun n => le_max_right _ _)
  intro A hA ind Ho Tno pTo r hr hk h2r hsmo hvolo c hc K Kh Tn pT aSeed haT hclock hone hsm hlate
    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
    hball hdistσ hev hlt
  obtain ⟨qK, T₀K, recK, hsep, hT₀K, hcanK, hacc, hrad, hord, hJ, r₀, w, hr0, hw, hvol, Phi, hPhi,
    hcurv, κU, phi, hκ, hphi, a₀K, hHI, hδ, hb, hbA, hPhiA, hrest2⟩ :=
    h' A hA ind Tno pTo r hr hk h2r hsmo hvolo aSeed haT hclock hone hsm hlate
      seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
      hball hdistσ hev hlt
  have hQp : ∀ n : ℕ,
      0 < ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ := fun n =>
    inv_pos.mpr (pow_pos ((q.rescale_P6N (c n) (hc n)).neckRadius_pos _ (Tn n).2.1) 2)
  have hQm : ∀ n : ℕ, 0 < max ((n : ℝ) + 1)
      ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ := fun n =>
    lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨qK, T₀K, recK, hsep, hT₀K, hcanK, fun n => (hacc n).trans (min_le_right _ _),
    fun n => (le_max_right _ _).trans (hrad n), fun n => (le_max_right _ _).trans (hord n), hJ, r₀,
    w, hr0, hw, hvol, Phi, hPhi, hcurv, κU, phi, hκ, hphi, a₀K, ?_, hHI,
    fun n i hi => (hδ n i hi).trans (min_le_right _ _),
    fun n i hi b => ((mul_le_mul_of_nonneg_right (le_max_left _ _)
      (le_of_lt (hQm n))).trans (hb n i hi b)),
    Filter.Eventually.of_forall fun n i hi b => hbA n i hi b, hPhiA, hrest2⟩
  intro j hjt htj yG hyG
  have hslabK := hslabK_of_tds_HND hanti hder ind c hc (fun n => (Tn n : ℝ))
  have hD1 : ∀ n, (K n).EventSlabsDerivative Ctd
      ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ (j n).castSucc := fun n i hi => by
    have hle : i.succ ≤ (j n).castSucc := Fin.castSucc_lt_iff_succ_le.mp hi
    have ht : (K n).time i.succ ≤ (Tn n : ℝ) :=
      (((K n).toHistory.time_strictMono.monotone hle).trans (hjt n).le).trans
        (Subtype.coe_le_coe.mpr (hsT n))
    exact ((K n).toHistory.event i).incoming.derivativeBoundBefore_mono (le_min le_rfl ht)
      (hslabK n i)
  have hD2 : ∀ n, (((K n).toHistory.event (j n)).incoming).DerivativeBoundBefore Ctd
      ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ (σ n) := fun n =>
    ((K n).toHistory.event (j n)).incoming.derivativeBoundBefore_mono
      (le_min (htj n).le (Subtype.coe_le_coe.mpr (hsT n))) (hslabK n (j n))
  refine RetainedCoreHistory.hnot_prefix_of_hnotK_HNF (t := fun n => (σ n : ℝ))
    (θ := fun n => 1 - 1 / ((n : ℝ) + 2)) (D := fun n => (n : ℝ) + 1) j recK yG (fun _ => le_rfl)
    (fun _ => le_rfl) ?_
  exact hprod hC1 hC2 hCt σ hjt htj
    (Q := fun n => ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹) (T₀ := T₀K)
    (p := qK) (pF := fun n => q.rescale_P6N (c n) (hc n)) (recordsK := recK)
    (fun n i => (records (ind n) i).rescale_P6M (c n) (hc n)) (a₀ := a₀K) hHI hcanK
    (fun n i hi => (hδ n i hi).trans (min_le_left _ _))
    (fun n => (hacc n).trans (min_le_left _ _)) (fun n => (le_max_left _ _).trans (hrad n))
    (fun n => (le_max_left _ _).trans (hord n)) hQp hD1 hD2
    (fun n i hi b _ _ => by
      have h1 := hb n i hi b
      have h2 : (Cb n)⁻¹ * ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ ≤
          ((recK n i hi).static b).neck.scale :=
        ((mul_le_mul (le_max_right _ _) (le_max_right _ _) (hQp n).le
          ((by positivity : (0 : ℝ) ≤ (n : ℝ) + 1).trans (le_max_left _ _))).trans h1)
      exact (inv_mul_le_iff₀ (hCb n)).mp h2)
    (fun n i hi b _ _ => hbA n i hi b) y hyG hsel

/-- **`∃ (Ctime₀, Cs)` 形（`_HND`，PROVED）**：与 `drvRX_HNO_of_HNR` 同形；常数取
`ctSeq_CH2 / csSeq_CH2`。 -/
theorem drvDTRX_HNO_of_HNR_HND {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) :
    ∃ (Ctime₀ : ℝ≥0) (Cs : ℝ), 0 < Ctime₀ ∧ 1 ≤ Cs ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
      {q : CutoffParameters} {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
      {C1 C2 : ℝ} {Ctime : ℝ≥0} {T₀ Qt : ℕ → ℝ} {Ctd : ℝ≥0},
      AntitoneOn q.neckRadius (Ici 0) →
      GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctd →
      Cs ≤ C1 → Cs ≤ C2 → Ctime₀ ≤ Ctime →
      DrvResE_DT_RX_HSX_HNR F q records ε C1 C2 Ctime T₀ Qt →
      DrvResE_DT_RX_HSX_HNO F q records ε C1 C2 Ctime T₀ Qt := by
  have hX := RetainedCoreHistory.hnotK_seq_a0_HNF.{u} hε hε'
  have e2 : GC.LongTime.Ch11.ctSeq_CH2.{u} ε = Classical.choose hX := by
    unfold GC.LongTime.Ch11.ctSeq_CH2; rw [dite_eq_left ⟨hε, hε'⟩]
  refine ⟨GC.LongTime.Ch11.ctSeq_CH2.{u} ε, GC.LongTime.Ch11.csSeq_CH2.{u} ε, ?_,
    GC.LongTime.Ch11.one_le_csSeq_CH2.{u} ε, fun hanti hder h1 h2 h3 h => ?_⟩
  · rw [e2]; exact (Classical.choose_spec (Classical.choose_spec hX)).1
  · exact drvDTRX_HNO_at_seq_HND hε hε' hanti hder h1 h2 h3 h

/-- **对齐 `J10ResE2_DJ`（`_HND`，PROVED）**：`DrvResE_DT_RX_HSX_HNO` 的 `hnot` 合取与 J10PAY
`J10ResE2_DJ` 的末合取同形（`T₀K` 不抬高）；加 `a₀K > 0`、`transitionEnd + 10 < modelRadius`、`T₀K ≤ σ − 10⁻⁴` 即得
`J10ResE2_DJ`。 -/
theorem j10ResE2_of_hnot_HND {K : ℕ → RetainedCoreHistory.{u}}
    {σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {yK : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {qK : ℕ → CutoffParameters}
    {T₀K : ℕ → ℝ}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (qK n)} {a₀K : ℕ → ℝ}
    (ha : ∀ n, 0 < a₀K n) (hrad : ∀ n, StandardCap.transitionEnd + 10 < (qK n).modelRadius)
    (hT : ∀ n, T₀K n ≤ (σ n : ℝ) - (1 / 100 : ℝ) ^ 2)
    (hnot :
      (∀ (j : ∀ k, Fin (K k).eventCount) (_hjt : ∀ k, (K k).time (j k).castSucc < (σ k : ℝ))
            (_htj : ∀ k, (σ k : ℝ) < (K k).time (j k).succ)
            (yG : ∀ k, ((K k).stage (j k).castSucc).Carrier), (∀ k, HEq (yK k) (yG k)) →
            ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
              (hi : T₀K n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
              (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
              (A' : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
                (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
              (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
              (x : standardCapWindow (qK n).modelRadius),
              A'.point i.succ le_rfl hl =
                  (((K n).prefixLateRecords_P6N (j n).castSucc (recordsK n) i hi).static
                    b).window x ∧
                ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
                (σ n : ℝ) - ((K n).prefixAt (j n).castSucc).time i.succ ≤
                  (1 - 1 / ((n : ℝ) + 2)) *
                    ((((K n).prefixLateRecords_P6N (j n).castSucc (recordsK n) i hi).static
                      b).neck.scale)⁻¹)) :
    J10ResE2_DJ K σ yK qK T₀K recordsK a₀K :=
  ⟨ha, hrad, hT, hnot⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

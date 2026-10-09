import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvResJ10DTRXHSX
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HnotPrefixProdHNF
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KDataSupplyP6D

/-!
# HNOTRES（DTRX）：`DrvResE_DT_RX_HSX` 档参数化孪生 `_HNR`

* `DrvResE_DT_RX_HSX_HNR`：预给序列 `Nf ζ Rn δ₀ m₀`（`∀ A` 之前）的档参数化孪生（G-a / G-b）；
* `drvDTRX_of_HNR`（PROVED）：孪生 ⇒ 原核（取标准档 `1/(n+1)`、`n+1`、`n+2`、`1/(n+1)`、`Nf = n+1`）；
（DT 线 `hnot` 合取需 Dt 由先验 TDS 付，未做。）
无新顶层 binder；不假设 `hqR`。生成器 `build-logs/scratch/HNOTRES/gen/gen.py`。
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

/-- **`DrvResE_DT_RX_HSX` 的档参数化孪生（`_HNR`，逐字缩写 def，非合同 Prop）**：`DrvResE_DT_RX_HSX` 逐字，改动：
(i) 预给序列 `Nf ζ Rn δ₀ m₀` 放在 `∀ A` 之前（带 `ζ ≤ 1/(n+1)`、`δ₀ ≤ 1/(n+1)`、`n+1 ≤ Rn`、`n+2 ≤ m₀`
档约束，故记录输出蕴含原档）；(ii) records 输出的精度 / 半径 / 阶 / late δ 档换成 `ζ n`、`Rn n`、`m₀ n`、`δ₀ n`；
(iii) birth 因子 `n+1` 换 `max (n+1) (Nf n)`（R19）；(iv) `1 ≤ a₀K·scale` 由 `∀ᶠ` 加强为 `∀ n`（T₀K 前段抬高可付）。
供给侧：细 records 由 `hfine_of_scrsPlus_RU`（SCRS⁺ (9)）/ P5L `diagonalPack` 在逐 `n` 档处付，因子 `Nf` 由
`birth_on_tail_of_recent_P6HN`（P6BirthOnTailP6HN）付。 -/
def DrvResE_DT_RX_HSX_HNR {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g)
    (q : CutoffParameters) (records : GC.LongTime.Ch11.CutoffRecords_C11S F q) (ε C1 C2 : ℝ)
    (Ctime : ℝ≥0) (T₀ Qt : ℕ → ℝ) : Prop :=
  ∀ (Nf ζ Rn δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ), (∀ n, 0 < ζ n) → (∀ n, 0 < δ₀ n) →
    (∀ n : ℕ, ζ n ≤ 1 / ((n : ℝ) + 1)) → (∀ n : ℕ, δ₀ n ≤ 1 / ((n : ℝ) + 1)) →
    (∀ n : ℕ, (n : ℝ) + 1 ≤ Rn n) → (∀ n : ℕ, n + 2 ≤ m₀ n) →
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
          (∀ n : ℕ, (qK n).modelAccuracy ≤ ζ n) ∧
          (∀ n : ℕ, Rn n ≤ (qK n).modelRadius) ∧
          (∀ n : ℕ, m₀ n ≤ (qK n).modelOrder) ∧
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
          (∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀K n) x ∧
            -3 / a₀K n ≤ metricScalarAt ((K n).initialMetric 0) x) ∧
          (∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
            (q.rescale_P6N (c n) (hc n)).delta ((K n).time i.succ) ≤ δ₀ n) ∧
          (∀ (n : ℕ) i hi b, max ((n : ℝ) + 1) (Nf n) * max ((n : ℝ) + 1)
              ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ ≤
            ((recordsK n i hi).static b).neck.scale) ∧
          (∀ n i hi b,
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


/-- **孪生 ⇒ 原核（`_HNR`，PROVED）**：取标准档。 -/
theorem drvDTRX_of_HNR {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {T₀ Qt : ℕ → ℝ} (h : DrvResE_DT_RX_HSX_HNR F q records ε C1 C2 Ctime T₀ Qt) :
    DrvResE_DT_RX_HSX F q records ε C1 C2 Ctime T₀ Qt := by
  have h' := h (fun n => (n : ℝ) + 1) (fun n => 1 / ((n : ℝ) + 1)) (fun n => (n : ℝ) + 1)
    (fun n => 1 / ((n : ℝ) + 1)) (fun n => n + 2) (fun n => by positivity) (fun n => by positivity)
    (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl)
  intro A hA ind Ho Tno pTo r hr hk h2r hsmo hvolo c hc K Kh Tn pT aSeed haT hclock h1 hsm hlate
    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
    hball hdistσ hev hlt
  obtain ⟨qK, T₀K, recK, hsep, hT₀K, hcanK, hacc, hrad, hord, hJ, r₀, w, hr0, hw, hvol, Phi, hPhi,
    hcurv, κU, phi, hκ, hphi, a₀K, hHI, hδ, hb, hbA, hrest⟩ :=
    h' A hA ind Tno pTo r hr hk h2r hsmo hvolo aSeed haT hclock h1 hsm hlate
      seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
      hball hdistσ hev hlt
  refine ⟨qK, T₀K, recK, hsep, hT₀K, hcanK, hacc, hrad, hord, hJ, r₀, w, hr0, hw, hvol, Phi, hPhi,
    hcurv, κU, phi, hκ, hphi, a₀K, hHI, hδ, fun n i hi b => ?_,
    Filter.Eventually.of_forall fun n i hi b => hbA n i hi b, hrest⟩
  simpa only [max_self] using hb n i hi b

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10TailJT
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvResJ10DJ3JT
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvResJ10DJ2JP

/-!
# HT0X G1：DW / DT 线 `hT₀X` 合同孪生 `DrvResE_{,DT_}DJ4_T0X`、转换（PROVED）与桥孪生

* `hT0X_of_contract_T0X`（PROVED）：合同 `T₀ k ≤ c k·aSeed k`、`aSeed = Tn − 1`、`1 ≤ aSeed`、`hroom`
  与 `T₀K ≤ max 1 (T₀/c)` ⇒ `∀ n, T₀K n ≤ σ n − (1/100)²`；
* `DrvResE_DJ4_T0X` / `DrvResE_DT_DJ4_T0X`：`DrvResE_*_DJ3_JT` 逐字，仅 `∀ᶠ hT₀X` 合取换成
  `∀ n, T₀K n ≤ max 1 (T₀ n / c n)`（producer 不抬 recent 分量）；
* `drvResE_{DW,DT}_of_DJ4_T0X`（PROVED）、桥 `hDrvJ/hDext_of_drvRes_{,DT_}DJ4_T0X`（结论逐字）；
* `hns_T0K_not_le_T0X`（PROVED）：HNS 的 `max 1 (max T₀ (c(σ−L/R))/c)` 取法与 `hT₀X` 冲突（精确障碍）。
无新顶层 binder。生成器 `build-logs/scratch/HT0X/gen/g.py`。
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

/-- **`hT₀X` 的合同核（`_T0X`，PROVED）**：K 帧 `aSeed = Tn − 1`、`1 ≤ aSeed`、`T₀ ≤ c·aSeed`
（DrvResE 合同假设）、`hroom`（`Tn − 1/2 ≤ σ − L²/R`）与 `T₀K ≤ max 1 (T₀/c)` 蕴含
`∀ n, T₀K n ≤ σ n − (1/100)²`（实际上窗口 `σ − aSeed ≥ 1/2`）。 -/
theorem hT0X_of_contract_T0X {T₀ c a Tn σ L R T₀K : ℕ → ℝ} (hc : ∀ n, 0 < c n)
    (hR : ∀ n, 0 < R n) (hlate : ∀ n, T₀ n ≤ c n * a n) (hclock : ∀ n, a n = Tn n - 1 ^ 2)
    (h1 : ∀ n, 1 ≤ a n) (hroom : ∀ n, Tn n - 1 ^ 2 / 2 ≤ σ n - L n ^ 2 / R n)
    (hT : ∀ n, T₀K n ≤ max 1 (T₀ n / c n)) :
    ∀ n, T₀K n ≤ σ n - (1 / 100 : ℝ) ^ 2 := fun n => by
  have hLR : 0 ≤ L n ^ 2 / R n := div_nonneg (sq_nonneg _) (hR n).le
  have hTa : T₀ n / c n ≤ a n := (div_le_iff₀ (hc n)).2 (by rw [mul_comm]; exact hlate n)
  have hm : max 1 (T₀ n / c n) ≤ a n := max_le (h1 n) hTa
  have := hclock n
  have := hroom n
  have := hT n
  nlinarith

/-- 从 `hroom` 与 `σ ≤ Tn` 得 `L²/R ≤ 1/2`。 -/
theorem Lsq_div_le_T0X {Tn σ L R : ℕ → ℝ} (hsT : ∀ n, σ n ≤ Tn n)
    (hroom : ∀ n, Tn n - 1 ^ 2 / 2 ≤ σ n - L n ^ 2 / R n) (n : ℕ) : L n ^ 2 / R n ≤ 1 / 2 := by
  have := hsT n
  have := hroom n
  linarith

/-- **HNS 取法的障碍（`_T0X`，PROVED）**：`T₀K n := max 1 (max (T₀ n) (c n (σ n − L n/R n)) / c n)`
（`t0K_tail_HNS` 的阈值）满足 `σ n − (1/100)² < T₀K n` 终将成立（`L → ∞` 且 `L²/R ≤ 1/2` ⇒
`L/R → 0`），故 `hT₀X` 对该取法为假：recent 窗 `L/R` 远小于固定窗 `(1/100)²`。 -/
theorem hns_T0K_not_le_T0X {T₀ c σ L R : ℕ → ℝ} (hc : ∀ n, 0 < c n) (hR : ∀ n, 0 < R n)
    (hL : Filter.Tendsto L Filter.atTop Filter.atTop)
    (hLR : ∀ n, L n ^ 2 / R n ≤ 1 / 2) :
    ∀ᶠ n in Filter.atTop,
      σ n - (1 / 100 : ℝ) ^ 2 < max 1 (max (T₀ n) (c n * (σ n - L n / R n)) / c n) := by
  filter_upwards [hL.eventually_gt_atTop 5000] with n hn
  have hRn := hR n
  have hcn := hc n
  have h2 : L n ^ 2 ≤ 1 / 2 * R n := (div_le_iff₀ hRn).1 (hLR n)
  have h3 : L n / R n < (1 / 100 : ℝ) ^ 2 := by
    rw [div_lt_iff₀ hRn]
    nlinarith [mul_pos (by linarith : (0:ℝ) < L n) (by linarith : (0:ℝ) < L n - 5000)]
  have h4 : σ n - L n / R n ≤ max (T₀ n) (c n * (σ n - L n / R n)) / c n := by
    rw [le_div_iff₀ hcn, mul_comm]
    exact le_max_right _ _
  have := le_max_right (1 : ℝ) (max (T₀ n) (c n * (σ n - L n / R n)) / c n)
  linarith

/-- **`DrvResE_DJ2_JP` 的尾平移孪生（`_T0X`，逐字缩写 def，非合同 Prop）**：`DrvResE_DJ2_JP` 逐字，改动：
(i) 参数 `a₀`（引擎级，DRV-HI 同元组）与合取 `∀ n, a₀K n = a₀ / c n`；(ii) J10 槽 `J10ResE2_DJ` 换成
`J10ResE3_JT`（逐点 hnot）+ `∀ᶠ n, T₀K n ≤ σ n − (1/100)²`（原 ∀ n）。 -/
def DrvResE_DJ4_T0X {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
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
          ∃ (Q a₀K : ℕ → ℝ),
          (∀ n, a₀K n = a₀ / c n) ∧
          (∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀K n) x ∧
            -3 / a₀K n ≤ metricScalarAt ((K n).initialMetric 0) x) ∧
          (∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
            (q.rescale_P6N (c n) (hc n)).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) ∧
          (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
            ((recordsK n i hi).static b).neck.scale) ∧
          (∀ᶠ n in atTop, ∀ i hi b,
            1 ≤ a₀K n * ((recordsK n i hi).static b).neck.scale) ∧
          (∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
            ((K n).toHistory.event i).incoming.flow
            (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀K n)) phi) ∧
          J10ResE3_JT K σ y qK T₀K recordsK ∧
          (∀ n, T₀K n ≤ max 1 (T₀ n / c n)) ∧
          (∀ n, (K n).EventSlabsDerivative Ctime (Q n) (Fin.last (K n).eventCount)) ∧
          (∃ (hfin : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon)
            (G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
              ((K n).time (Fin.last (K n).eventCount)) (K n).horizon),
            (∀ n, G n = ((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl) ∧
            (∀ n, Perelman.PhiAlmostNonnegative (G n).flow
            (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀K n)) phi) ∧
            (∀ n, (G n).DerivativeBoundBefore Ctime (Q n) (K n).horizon)) ∧
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

/-- **`DrvResE_DT_DJ2_JP` 的尾平移孪生（`_T0X`，逐字缩写 def，非合同 Prop）**：同 `DrvResE_DJ4_T0X` 改动。 -/
def DrvResE_DT_DJ4_T0X {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
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
          (∀ n, a₀K n = a₀ / c n) ∧
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
          J10ResE3_JT K σ y qK T₀K recordsK ∧
          (∀ n, T₀K n ≤ max 1 (T₀ n / c n)) ∧
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

/-- **`DrvResE_DJ4_T0X → DrvResE_DW`（`_T0X`，PROVED）**：J10 块由 `j10Blk_of_tail_JT`（尾平移）付；
`a₀K > 0` 由引擎级 `ha₀` + `a₀K = a₀ / c`（`a0K_pos_JT`）付。 -/
theorem drvResE_DW_of_DJ4_T0X
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {T₀ Qt : ℕ → ℝ} {a₀ : ℝ}
    (ha₀ : 0 < a₀) (hC2 : 0 ≤ C2) (h : DrvResE_DJ4_T0X F q records ε C1 C2 Ctime T₀ Qt a₀) :
    DrvResE_DW F q records ε C1 C2 Ctime T₀ Qt := by
  intro A hA ind Ho Tno pTo r hr hk h2r hsmo hvolo c hc K Kh Tn pT aSeed haT hclock h1 hsm hlate
    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
    hball hdistσ hev hlt
  obtain ⟨qK, T₀K, recK, hsep, hT₀K, hcanK, hacc, hrad, hord, r₀, w, hr₀, hw, hvol, Phi, hPhi,
    hPhiK, κU, phi, hκU, hphi, Q, a₀K, ha₀K, hHI, hδ, hscale, hbirth, hpinchK, hJ3, hT₀X,
    hrest⟩ :=
    h A hA ind Tno pTo r hr hk h2r hsmo hvolo aSeed haT hclock h1 hsm hlate
      seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
      hball hdistσ hev hlt
  have hslabT : ∀ n (i : Fin (K n).eventCount),
      ((K n).toHistory.event i).incoming.DerivativeBoundBefore Ctime (Q n)
        (min ((K n).time i.succ) (Tn n : ℝ)) := fun n i =>
    OrientedThreeStage.IncomingSlab.DerivativeBoundBefore.mono_JP _
      (hrest.1 n i (Fin.castSucc_lt_last i)) le_rfl le_rfl (min_le_left _ _)
  have hfinK : ∀ n, riemannianEDistOf ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n))
      ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
        ((K n).toHistory.activeStage_mono (has n)) ((K n).toHistory.activeStage_mono (hsT n)))
      (y n) ≠ ⊤ := fun n => ne_top_of_lt (hball n)
  have hhalf := ObservedHistory.hhalf_of_room_one_A6K σ Tn R L hRpos hroom
  have hT₀X' : ∀ᶠ n in atTop, T₀K n ≤ (σ n : ℝ) - (1 / 100 : ℝ) ^ 2 :=
    Filter.Eventually.of_forall (hT0X_of_contract_T0X (fun n => hc n) hRpos hlate hclock h1
      hroom hT₀X)
  obtain ⟨Cst, hsurv, hext⟩ := j10Blk_of_tail_JT (Cg := 4) (ε := ε) (C1 := C1) (C2 := C2) hC2
    hcanK hacc hrad hord hT₀K (fun n i => (records (ind n) i).rescale_P6M (c n) (hc n)) hδ hphi
    hHI hscale hbirth hpinchK Tn aSeed haT hsT has pT seedTrace hslabT hclock h1 hsm hhalf hL
    hgood hRdef hRpos hRr hfinK hsep hev (a0K_pos_JT ha₀ hc ha₀K) hT₀X' hJ3
  exact ⟨qK, T₀K, recK, hsep, hT₀K, hcanK, hacc, hrad, hord, Cst, hsurv, hext, r₀, w, hr₀, hw,
    hvol, Phi, hPhi, hPhiK, κU, phi, hκU, hphi, Q, a₀K, hHI, hδ, hscale, hbirth, hpinchK, hrest⟩

/-- **`DrvResE_DT_DJ4_T0X → DrvResE_DT`（`_T0X`，PROVED）**：同 DW 线；`hslabT` ⇐
`hkernelDtT_of_supply_P6KT`（`hder` / `hanti`，桥原有前提）。 -/
theorem drvResE_DT_of_DJ4_T0X
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {T₀ Qt : ℕ → ℝ} {a₀ : ℝ}
    (hder : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hanti : AntitoneOn q.neckRadius (Ici 0)) (ha₀ : 0 < a₀) (hC2 : 0 ≤ C2)
    (h : DrvResE_DT_DJ4_T0X F q records ε C1 C2 Ctime T₀ Qt a₀) :
    DrvResE_DT F q records ε C1 C2 Ctime T₀ Qt := by
  intro A hA ind Ho Tno pTo r hr hk h2r hsmo hvolo c hc K Kh Tn pT aSeed haT hclock h1 hsm hlate
    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
    hball hdistσ hev hlt
  obtain ⟨qK, T₀K, recK, hsep, hT₀K, hcanK, hacc, hrad, hord, r₀, w, hr₀, hw, hvol, Phi, hPhi,
    hPhiK, κU, phi, hκU, hphi, a₀K, ha₀K, hHI, hδ, hscale, hbirth, hpinchK, hJ3, hT₀X, hrest⟩ :=
    h A hA ind Tno pTo r hr hk h2r hsmo hvolo aSeed haT hclock h1 hsm hlate
      seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
      hball hdistσ hev hlt
  obtain ⟨hslab0, -⟩ := GC.LongTime.Ch11.hkernelDtT_of_supply_P6KT hder le_rfl hanti
    q.neckRadius_pos ind c hc (fun n => (q.neckRadius (c n * (Tn n : ℝ)) ^ 2)⁻¹)
    (fun n => c n * (Tn n : ℝ)) (fun _ => le_rfl)
  have hTc : ∀ n, c n * (Tn n : ℝ) / c n = (Tn n : ℝ) := fun n =>
    mul_div_cancel_left₀ _ (hc n).ne'
  have hQe : ∀ n, c n * (q.neckRadius (c n * (Tn n : ℝ)) ^ 2)⁻¹ =
      ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ := fun n =>
    (RetainedCoreHistory.neckRadius_rescale_inv_sq_P6X (hc n) q (Tn n : ℝ)).symm
  have hslabT : ∀ n (i : Fin (K n).eventCount),
      ((K n).toHistory.event i).incoming.DerivativeBoundBefore Ctime
        ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹
        (min ((K n).time i.succ) (Tn n : ℝ)) := fun n i => by
    have h := hslab0 n i
    beta_reduce at h
    rwa [hQe n, hTc n] at h
  have hfinK : ∀ n, riemannianEDistOf ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n))
      ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
        ((K n).toHistory.activeStage_mono (has n)) ((K n).toHistory.activeStage_mono (hsT n)))
      (y n) ≠ ⊤ := fun n => ne_top_of_lt (hball n)
  have hhalf := ObservedHistory.hhalf_of_room_one_A6K σ Tn R L hRpos hroom
  have hT₀X' : ∀ᶠ n in atTop, T₀K n ≤ (σ n : ℝ) - (1 / 100 : ℝ) ^ 2 :=
    Filter.Eventually.of_forall (hT0X_of_contract_T0X (fun n => hc n) hRpos hlate hclock h1
      hroom hT₀X)
  obtain ⟨Cst, hsurv, hext⟩ := j10Blk_of_tail_JT (Cg := 4) (ε := ε) (C1 := C1) (C2 := C2) hC2
    hcanK hacc hrad hord hT₀K (fun n i => (records (ind n) i).rescale_P6M (c n) (hc n)) hδ hphi
    hHI hscale hbirth hpinchK Tn aSeed haT hsT has pT seedTrace hslabT hclock h1 hsm hhalf hL
    hgood hRdef hRpos hRr hfinK hsep hev (a0K_pos_JT ha₀ hc ha₀K) hT₀X' hJ3
  exact ⟨qK, T₀K, recK, hsep, hT₀K, hcanK, hacc, hrad, hord, Cst, hsurv, hext, r₀, w, hr₀, hw,
    hvol, Phi, hPhi, hPhiK, κU, phi, hκU, hphi, a₀K, hHI, hδ, hscale, hbirth, hpinchK, hrest⟩

/-- **桥孪生（`_T0X`）**：`hDrvJ_of_drvRes_RX_HSX_JP` 陈述逐字，`hres` 换 `_DJ3_JT` 版 + 引擎级 `ha₀`；
证明 = 既有全局核桥 `hDrvJ_of_drvRes_DW` ∘ 尾平移转换。 -/
theorem hDrvJ_of_drvRes_DJ4_T0X {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {T₀ Qt : ℕ → ℝ}
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
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hres : DrvResE_DJ4_T0X F q records ε C1 C2 Ctime T₀ Qt a₀) :
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
            ∀ T : ℝ, 0 < T → ObservedHistory.DepthExtendable Kh σ y R (φ ∘ ψ) T :=
  hDrvJ_of_drvRes_DW hε hεX hεN hεle hC2 hanti hder hfresh records hfine
    (drvResE_DW_of_DJ4_T0X ha₀ hC2 hres)

/-- **桥孪生（`_T0X`）**：`hDext_of_drvRes_RX_HSX_JP` 陈述逐字，`hres` 换 `_DJ3_JT` 版 + 引擎级 `ha₀`；
证明 = 既有全局核桥 `hDext_of_drvRes_DW` ∘ 尾平移转换。 -/
theorem hDext_of_drvRes_DJ4_T0X {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {T₀ Qt : ℕ → ℝ}
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
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hres : DrvResE_DJ4_T0X F q records ε C1 C2 Ctime T₀ Qt a₀) :
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
            ∀ T : ℝ, 0 < T → DepthExtendable Kh σ y R (φ ∘ ψ) T) :=
  hDext_of_drvRes_DW hε hεX hεN hεle hC2 hanti hder hfresh records hfine
    (drvResE_DW_of_DJ4_T0X ha₀ hC2 hres)

/-- **桥孪生（`_T0X`）**：`hDrvJ_of_drvRes_DT_RX_HSX_JP` 陈述逐字，`hres` 换 `_DJ3_JT` 版 + 引擎级 `ha₀`；
证明 = 既有全局核桥 `hDrvJ_of_drvRes_DT` ∘ 尾平移转换。 -/
theorem hDrvJ_of_drvRes_DT_DJ4_T0X {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {T₀ Qt : ℕ → ℝ}
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
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hres : DrvResE_DT_DJ4_T0X F q records ε C1 C2 Ctime T₀ Qt a₀) :
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
            ∀ T : ℝ, 0 < T → ObservedHistory.DepthExtendable Kh σ y R (φ ∘ ψ) T :=
  hDrvJ_of_drvRes_DT hε hεX hεN hεle hC2 hanti hder hfresh records hfine
    (drvResE_DT_of_DJ4_T0X hder hanti ha₀ hC2 hres)

/-- **桥孪生（`_T0X`）**：`hDext_of_drvRes_DT_RX_HSX_JP` 陈述逐字，`hres` 换 `_DJ3_JT` 版 + 引擎级 `ha₀`；
证明 = 既有全局核桥 `hDext_of_drvRes_DT` ∘ 尾平移转换。 -/
theorem hDext_of_drvRes_DT_DJ4_T0X {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {T₀ Qt : ℕ → ℝ}
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
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hres : DrvResE_DT_DJ4_T0X F q records ε C1 C2 Ctime T₀ Qt a₀) :
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
            ∀ T : ℝ, 0 < T → DepthExtendable Kh σ y R (φ ∘ ψ) T) :=
  hDext_of_drvRes_DT hε hεX hεN hεle hC2 hanti hder hfresh records hfine
    (drvResE_DT_of_DJ4_T0X hder hanti ha₀ hC2 hres)

/-- consumer（`_T0X`）：取 `T₀K n := max 1 (T₀ n / c n)`，`hT₀X` 由合同核直接付。 -/
example {T₀ c a Tn σ L R : ℕ → ℝ} (hc : ∀ n, 0 < c n) (hR : ∀ n, 0 < R n)
    (hlate : ∀ n, T₀ n ≤ c n * a n) (hclock : ∀ n, a n = Tn n - 1 ^ 2) (h1 : ∀ n, 1 ≤ a n)
    (hroom : ∀ n, Tn n - 1 ^ 2 / 2 ≤ σ n - L n ^ 2 / R n) :
    ∀ n, max 1 (T₀ n / c n) ≤ σ n - (1 / 100 : ℝ) ^ 2 :=
  hT0X_of_contract_T0X (T₀K := fun n => max 1 (T₀ n / c n)) hc hR hlate hclock h1 hroom
    (fun _ => le_rfl)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

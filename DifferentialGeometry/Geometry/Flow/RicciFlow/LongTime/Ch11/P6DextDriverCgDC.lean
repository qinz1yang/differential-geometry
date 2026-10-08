import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DextDriverDrvW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DriverReindexCgDC
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HanchorCgDC

/-!
# DRVWIRE：hDrvJ / hDext ⇐ guarded2 driver，Cg 参数化（`_DC`）

DRVWIRE GAP (a)：hres 事件核 `hDrvJ` / `hDext` ⇐ guarded2 driver 的 hgood 阈值 `Cg` 版（#7，见 state G0
表）：`DrvResE_DW` / `hDrvJ_of_drvRes_DW` / `hDext_of_drvRes_DW` 的孪生。`¬ HasSTC` 常数组参数化以便 J8（粗常数）
实例化；其余逐字。**无新 binder**。生成器 `build-logs/scratch/DRVCG8/gen/g4.py`。
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

/-- **driver 剩余前提核，阈值 `Cg·R` 版（`_Cg_DC`）**：`DrvResE_DW` 的 hgood `4` → `Cg`；`¬ HasSTC` 的
常数组改为独立参数 `(εb C1b C2b Ctimeb)`（J8：粗常数；`Cg = 4` 且 `= (ε C1 C2 Ctime)` 即原版）。
逐字缩写，非合同 Prop；仅作 binder 缩写，不新增义务。 -/
def DrvResE_Cg_DC {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (q : CutoffParameters) (records : GC.LongTime.Ch11.CutoffRecords_C11S F q) (Cg ε C1 C2 : ℝ)
    (Ctime : ℝ≥0) (εb C1b C2b : ℝ) (Ctimeb : ℝ≥0) (T₀ Qt : ℕ → ℝ) : Prop :=
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

/-- **hDrvJ ⇐ guarded2 driver，阈值 `Cg·R` 版（`_Cg_DC`）**：`hDrvJ_of_drvRes_DW` 的 hgood `4` → `Cg`
（`4 ≤ Cg`）；`hkappaC` ⇐ J11STAY `(Cg := Cg)`，`hanchor0` ⇐ `hanchor0_hPN_frame_RU_Cg_DC`，driver ⇐
`forall_subseq_depthExtendable_of_guarded2_Cg_DC`；`¬ HasSTC` 常数组独立（`εb C1b C2b Ctimeb`）。
PROVISIONAL[`DrvResE_Cg_DC` + 引擎级 `hfresh / records / hfine / hder / hanti` + ε 常数]。 -/
theorem hDrvJ_of_drvRes_Cg_DC {Cg : ℝ} (hCg : 4 ≤ Cg)
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {εb C1b C2b : ℝ} {Ctimeb : ℝ≥0} {T₀ Qt : ℕ → ℝ}
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
    (hres : DrvResE_Cg_DC F q records Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt) :
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
  intro A hA ind Ho Tno pTo r hr hk h2r hsmo hvolo c hc K Kh Tn pT aSeed haT hclock h1 hsm hlate
    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
    hball hdistσ hev hlt
  obtain ⟨qK, T₀K, recK, hsep, hT₀K, hcanK, hacc, hrad, hord, Cst, hsurv, hext, r₀, w, hr₀, hw,
    hseed, Phi, hPhi, hpinch, κU, phi, hκU, hphi, Q, a₀K, hHI, hδF, hscaleK, hbirthA, hpinchK0,
    hslabK, ⟨hfin, G, hG, hpinchF, hderF⟩, hκR, hκRF, hpinchK0', θ₀, hθ₀, hsepρ⟩ :=
    hres A hA ind Tno pTo r hr hk h2r hsmo hvolo aSeed haT hclock h1 hsm hlate
      seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
      hball hdistσ hev hlt
  refine ⟨qK, T₀K, recK, hsep, hT₀K, hcanK, hacc, hrad, hord, ?_⟩
  choose j hjt htj using hev
  have hσH : ∀ k, (σ k : ℝ) < (Kh k).horizon := fun k =>
    lt_of_lt_of_le (htj k) ((Kh k).time_le_horizon_at _)
  have hA0 : (0 : ℝ) < A := by linarith
  have hR1 : ∀ k, (1 : ℝ) ≤ R k := fun k => by
    have := hRr k
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  -- hanchor0 ⇐ RECUP（FRESH 经 rescale adapter）
  have hsupA : ∀ Aseed : ℝ, 1 < Aseed → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ,
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) (k : ℕ),
        KappaSeedWindowFwd_C11PK
          (fun w => q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k)) (Aseed + 7) κ
          (Tf / c k) ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory := by
    intro Aseed hAs
    obtain ⟨κ, hκ, Tf, hsup⟩ := hfresh (Aseed + 7) (by linarith)
    exact ⟨κ, hκ, Tf, GC.LongTime.Ch11.fresh_rescale_adapter_P6JA hsup⟩
  have hanc := hanchor0_hPN_frame_RU_Cg_DC (by linarith) hεle hC2 hanti hder
    T₀ hsupA hphi hθ₀ records hfine hA ind
    Tno pTo r hr hk h2r hsmo hvolo aSeed haT hclock h1 hsm hlate seedTrace σ y R hsT has L hRdef
    hRpos hRr hL hgood hwin hwin' hRρ hball hdistσ hpinchK0' j hjt htj (hsepρ j hjt htj)
  -- hkappaC ⇐ J11STAY（Aseed := A + 3）
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
  have hdσ' : ∀ᶠ k in atTop,
      riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
          ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
            ((Kh k).activeStage_mono (hsT k))) (y k) +
        ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3 + 3) * 1) :=
    hdistσ.mono fun k hk => hk.trans (ENNReal.ofReal_le_ofReal (by linarith))
  have hkap := ObservedHistory.hkappaC_driver_of_drv_J11S (Cg := Cg) (haT := haT) hC2 K hclock h1
    hsm seedTrace σ y R hsT has L hRpos hRr hL hgood hσH
    (fun k τ x => ObservedHistory.hpin_rescaled_of_records_P6HI F records ind c hc k τ x)
    qK T₀K recK hsep hT₀K hcanK hacc hrad hord (by linarith : (0 : ℝ) < A + 3)
    (fun k w => q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k)) (fun k => Tf / c k)
    hsupK hTf (fun k => by simpa using (hprep0 k).2.1) (fun k => (hprep0 k).2.2.1)
    (fun k => (hprep0 k).2.2.2)
    hwin hwin' hdσ'
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
  exact ObservedHistory.forall_subseq_depthExtendable_of_guarded2_Cg_DC hCg
    (G := G)
    (Q := Q) (a₀ := a₀K) (Aκ := A + 3) (pF := q) (rX := 1)
    F ind c hc K rfl Kh σ y R hRr hsurv hanc hext hr₀ hw hseed hκ (fun _ => 1 / 200) hradii hkap
    hPhi hpinch hε hεX hεN Tn aSeed haT hsT has pT seedTrace L hL hgood hwin rfl (fun _ => 1)
    hhalf htime (Filter.Eventually.of_forall hsm) (Filter.Eventually.of_forall hclock) hRr2
    records qK T₀K recK hsep hT₀K hεle hκU hphi hfin hG hHI hcanK hδF hacc hrad hord
    hscaleK hbirthA hpinchK0 hslabK hpinchF hderF (fun _ => 1 / 200) hradii hC2 hroom hdistσ hκR
    hκRF one_pos hsm hclock hRa (fun _ => 0) (ObservedHistory.hT₀X_zero_A6K aSeed)
    (ObservedHistory.hOldX_kernel_A6K K _) hdfin

/-- **hDext ⇐ guarded2 driver，阈值 `Cg·R` 版（`_Cg_DC`）**：
`hDext_of_drvRes_DW` 同法（= `hDrvJ_of_drvRes_Cg_DC` 末合取）。 -/
theorem hDext_of_drvRes_Cg_DC {Cg : ℝ} (hCg : 4 ≤ Cg)
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {εb C1b C2b : ℝ} {Ctimeb : ℝ≥0} {T₀ Qt : ℕ → ℝ}
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
    (hres : DrvResE_Cg_DC F q records Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt) :
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
        (∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
            ∀ T : ℝ, 0 < T → DepthExtendable Kh σ y R (φ ∘ ψ) T) := by
  intro A hA ind Ho Tno pTo r hr hk h2r hsmo hvolo c hc K Kh Tn pT aSeed haT hclock h1 hsm hlate
    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
    hball hdistσ hev hlt
  obtain ⟨-, -, -, -, -, -, -, -, -, h⟩ := hDrvJ_of_drvRes_Cg_DC hCg hε hεX hεN hεle hC2 hanti hder
    hfresh
    records hfine hres A hA ind Tno pTo r hr hk h2r hsmo hvolo aSeed haT hclock h1 hsm hlate
      seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
      hball hdistσ hev hlt
  exact h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

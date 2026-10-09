import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6BCDStayWinGateHCTD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6BCDBootstrapBallHCTD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DistLargeWinDLW

/-!
# D3：hdistL_large / hdistLA 窗形的 hTR‴ gate + 天花板孪生（O-CH11-HCTD，后缀 `_HCTD`）

* `hdistL_large_win_gate_HCTD`：`hdistL_large_win_DLW` 逐字，`hfamT` / `hTR` / 结论三处 frame 换 hTR‴ 形
  （`hsm` 后 gate 块，`hradii` 后 `hdσ` 与 `hceil`；`q`、`Aseed` 隐式），调用换 D1 / D2 孪生；stay 调用在
  `L/2` 处的 `hdσ` 由 `hdσ` 与 `L → ∞`（`0 ≤ L` eventually）单调导出。
* `hdistLA_win_of_TRs_gate_HCTD`：`hdistLA_win_of_TRs_DLW` 逐字，前提 `hTRs` 的 `hcon` 部分换
  `∀ Aseed > 1`（Aseed 在外层）+ hTR‴ frame，`hsep`（driver hsepWK）部分不变；结论槽 `hdistLA` 的 frame 在
  `hdσ` 之后加 `hceil`（= `hdistLA‴`，与 HCT 的 FOOT4 gate 链槽形一致）。证明：`Aseed` 取槽的 `Aseed`，
  gate 块与 `hceil` 原样传给 `hTRf` 与 `hdistL_large`；`hfamT` 构造忽略新前缀。
槽形收窄 = 义务变弱（§0.2）；旧 → 新由忽略新前缀得。无新 binder / Prop。
生成器 build-logs/scratch/O-CH11-HCTD/gen/gen_d3.py。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology


universe u

open GC.GeneralFlow (ClosedBirthConstants)
open GC.LongTime.Ch11 (p6CoarseC_C11GT6 p6FineEta_C11GT6 p6FineEta_pos_C11GT6 epsW_CXOU2)
open GC.LongTime.Ch11 (BlockTower_C11W capWindowRadius_C11E FineOf_C11G2 BudgetCertificate_C11GT2
  SameConstructionRetentionSupplyPlus_C11GT6 chainDiagonal_C11A C1P6_C11GT6 C2P6_C11GT6
  p6X1std_C11GT6 p6X2std_C11GT6 p6Ctime_C11G7B p6BadC_C11G2 htransMBad_C11G7B)
open Perelman.CanonicalNeighborhood.FiniteHorn

/-- **G4b G1 孪生（`_DLW`，PROVISIONAL[`hTR`, `hfamT` 窗形]）**。 -/
theorem hdistL_large_win_gate_HCTD :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
      {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {qp : CutoffParameters} {Ktr : ℝ → ℝ → ℝ}
      {q : CutoffParameters} {Aseed : ℝ},
    1 ≤ C2 → StandardCap.transitionEnd + 10 < qp.modelRadius → qp.modelAccuracy ≤ ε₀ →
    2 ≤ qp.modelOrder → Tendsto qp.delta atTop (𝓝 0) →
    (∀ r T, 0 ≤ Ktr r T) →
    (
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
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((Aseed + 3) * 1)) →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
        ∃ (a₀ T₀ : ℕ → ℝ) (records : ∀ k (e : Fin (Kh k).eventCount),
            T₀ k ≤ (Kh k).time e.succ →
              GeometricCutoffRecord (Kh k) e (qp.rescale_P6N (c k) (hc k))),
          (∀ k, 0 ≤ a₀ k) ∧
          (∀ k (τ : Icc (0 : ℝ) (Kh k).horizon) (x : ((Kh k).stageAt τ).Carrier),
            InFixedHamiltonIveyRegion ((Kh k).stageMetric ((Kh k).activeStage τ) τ)
              (a₀ k + τ) x) ∧
          (∀ k, T₀ k ≤ (aSeed k : ℝ)) ∧
          (∀ k (e : Fin (Kh k).eventCount), T₀ k ≤ (Kh k).time e.succ →
            ((Kh k).event e).old = ((Kh k).event e).transition.trace.retainedCore) ∧
          (∀ k (e : Fin (Kh k).eventCount) (he : T₀ k ≤ (Kh k).time e.succ) b,
            ((records k e he).static b).hasCanonicalWindow) ∧
          ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
          ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ k in atTop,
            ∀ (e : Fin (Kh k).eventCount) (he : T₀ k ≤ (Kh k).time e.succ) b,
              (σ k : ℝ) - T / R k < (Kh k).time e.succ →
              2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R k) <
                ((records k e he).static b).neck.scale
    ) →
    (
      ∀ (T r : ℝ), 0 < T → 0 < r →
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
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((Aseed + 3) * 1)) →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            ∀ (tt : Icc (0 : ℝ) (Kh k).horizon), (tt : ℝ) = t →
            ∀ y' : ((Kh k).stageAt tt).Carrier, HEq y' p' →
              (Kh k).isTracedRegion tt y' (r / Real.sqrt (R k)) (T / R k) (Ktr r T * R k)
    ) →
      ∀ (T r : ℝ), 0 < T → 0 < r →
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
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((Aseed + 3) * 1)) →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        (∀ᶠ k in atTop, riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) (y k) ≠ ⊤) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ (h1 : (Kh k).activeStage (aSeed k) ≤ (i k).castSucc)
            (h2 : (i k).castSucc ≤ (Kh k).activeStage (Tn k)),
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ, ∀ τ : ℝ,
            t - T / R k ≤ τ → τ ≤ t → (Kh k).time (i k).castSucc < τ →
            ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                (r / Real.sqrt (R k)),
              riemannianEDistOf (((Kh k).event (i k)).incoming.flow.base.metric τ)
                  ((seedTrace k).point (i k).castSucc h1 h2) z ≤
                riemannianEDistOf (((Kh k).event (i k)).incoming.flow.base.metric t)
                  ((seedTrace k).point (i k).castSucc h1 h2) z + ENNReal.ofReal 1 := by
  obtain ⟨ε₀, hε₀, hST⟩ := hstopE_deep_tower_win_gate_HCTD.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro P g F ε C1 C2 Ctime qp Ktr q Aseed hC2 hDm hacc hm hδlim hK hfamT hTR T r hT hr ind c hc
    Kh Tn pT
    hTc aSeed haT hclock hone hsm hvolG h2G hnrG seedTrace σ y R hsT has L hRdef hRpos hRr hL hsel
      hgood haS hTnS
    hroom hradii hdσ hceil i hi hfinE
  obtain ⟨a₀, _T₀, _records, ha₀, hpin, -, -, -, -⟩ := hfamT ind c hc Tn pT hTc
    aSeed haT hclock hone hsm hvolG h2G hnrG seedTrace σ y R hsT has L hRdef hRpos hRr hL hsel
      hgood haS hTnS
    hroom hradii hdσ hceil
  -- stay 用 L/2（hgood 对 L 反单调）
  have hL2 : Tendsto (fun k => L k / 2) atTop atTop := hL.atTop_div_const two_pos
  have hdσ2 : ∀ᶠ k in atTop,
      riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
          ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
            ((Kh k).activeStage_mono (hsT k))) (y k) +
        ENNReal.ofReal ((L k / 2 + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((Aseed + 3) * 1) :=
    (hdσ.and (hL.eventually_ge_atTop 0)).mono fun k hk =>
      le_trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right (by linarith [hk.2]) (Real.sqrt_nonneg _)))) hk.1
  have hgood2 : ∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
      (σ k : ℝ) - (L k / 2) ^ (2 : ℕ) / R k ≤ (v : ℝ) →
      ∀ z : ((Kh k).stageAt v).Carrier,
        riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
            ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
              ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
          riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
              ((seedTrace k).point ((Kh k).activeStage (σ k))
                ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
            ENNReal.ofReal (L k / 2 / Real.sqrt (R k)) →
        4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
        (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z := by
    intro k v hav hvs hvL z hz hRz
    refine hgood k v hav hvs ?_ z (hz.trans (add_le_add le_rfl ?_)) hRz
    · have h1 : (L k / 2) ^ (2 : ℕ) / R k ≤ L k ^ (2 : ℕ) / R k :=
        div_le_div_of_nonneg_right (by have := sq_nonneg (L k); linarith) (hRpos k).le
      linarith
    · rcases le_total 0 (L k) with h0 | h0
      · exact ENNReal.ofReal_le_ofReal
          (div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))
      · rw [ENNReal.ofReal_of_nonpos
          (div_nonpos_of_nonpos_of_nonneg (by linarith) (Real.sqrt_nonneg _))]
        exact zero_le
  have hb := betaStar_P6BB (Ctime := Ctime) (Cball := fun r => 9 * Ktr r 1)
    (Cgrid := fun r T => 9 * Ktr r T)
  have hstay := hST (Cball := fun r => 9 * Ktr r 1) (Cgrid := fun r T => 9 * Ktr r T)
    (β := fun r T => gridStep_P6BB Ctime (fun r => 9 * Ktr r 1) (fun r T => 9 * Ktr r T) r T)
    (by linarith) hDm hacc hm hδlim hb.1 hb.2 hfamT (hballT_of_tracedRegion_gate_HCTD hK hTR)
    (hgridTr_of_tracedRegion_gate_HCTD hK hTR) T r hT hr ind c hc Tn pT hTc aSeed haT hclock hone
      hsm hvolG h2G hnrG
    seedTrace σ y R hsT has (fun k => L k / 2) hRdef hRpos hRr hL2 hsel hgood2 haS hTnS hroom
    hradii hdσ2 hceil i hi hfinE
  have htr := hTR T r hT hr ind c hc Tn pT hTc aSeed haT hclock hone hsm hvolG h2G hnrG seedTrace
    σ y R hsT has
    L hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii hdσ hceil i hi
  -- 显式常数 Q
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = max (max (9 * Ktr r T) 4) 1 := ⟨_, rfl⟩
  have hQ1 : (1 : ℝ) ≤ Q := hQ ▸ le_max_right _ _
  have hQ4 : (4 : ℝ) ≤ Q := hQ ▸ (le_max_right _ _).trans (le_max_left _ _)
  have hQ9 : 9 * Ktr r T ≤ Q := hQ ▸ (le_max_left _ _).trans (le_max_left _ _)
  filter_upwards [hstay, htr, hfinE, haS (2 * T) (by linarith),
    hL.eventually_ge_atTop (16 * Real.sqrt (cDist_P6DL2 C2 Q) + 2 + 2 * T),
    hradii.eventually_ge_atTop (8 * T * Real.sqrt (cDist_P6DL2 C2 Q))]
    with k hstk htrk hfk haSk hLk hRk
  intro p' q hq hcross h1 h2
  have hcs : (Kh k).time (i k).castSucc < (Kh k).time (i k).succ :=
    (Kh k).time_strictMono Fin.castSucc_lt_succ
  have hσ' : (σ k : ℝ) = (Kh k).time (i k).succ := hi k
  have hRk0 := hRpos k
  have hR1 : (1 : ℝ) ≤ R k := by
    have h0 := hRr k
    have h00 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hTR0 : 0 < T / R k := div_pos hT hRk0
  have e2 : 2 * T / R k = T / R k + T / R k := by ring
  have hsc0 := Real.sqrt_nonneg (cDist_P6DL2 C2 Q)
  filter_upwards [hstk p' q hq hcross, htrk p' q hq hcross,
    Ioo_mem_nhdsLT (show max ((Kh k).time (i k).castSucc) ((σ k : ℝ) - T / R k) <
      (Kh k).time (i k).succ from max_lt hcs (by linarith))] with t hst htr' hti
  intro τ hτ1 hτ2 hτ3 z hz
  have ht1 : (Kh k).time (i k).castSucc < t := lt_of_le_of_lt (le_max_left _ _) hti.1
  have htσ0 : (σ k : ℝ) - T / R k < t := lt_of_le_of_lt (le_max_right _ _) hti.1
  have ht0 : 0 ≤ t := ((Kh k).time_nonneg _).trans ht1.le
  have hth : t ≤ (Kh k).horizon := hti.2.le.trans ((hi k) ▸ (σ k).2.2)
  let tt : Icc (0 : ℝ) (Kh k).horizon := ⟨t, ht0, hth⟩
  have htt : (tt : ℝ) = t := rfl
  have he : (Kh k).activeStage tt = (i k).castSucc :=
    (Kh k).activeStage_eq_of_mem_slab_P6F3 (i k) tt ht1.le hti.2
  have htσ : tt ≤ σ k := by
    change t ≤ (σ k : ℝ)
    linarith [hti.2]
  obtain ⟨y', hy'⟩ := (Kh k).exists_heq_stageAt_P6JW he p'
  obtain ⟨z', hz'⟩ := (Kh k).exists_heq_stageAt_P6JW he z
  have hzy : z' ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage tt) tt) y'
      (r / Real.sqrt (R k)) := by
    rw [ObservedHistory.ball_transport_P6BB he htt z' y' z p' hz' hy',
      ObservedHistory.stageMetric_castSucc_apply]
    exact hz
  obtain ⟨-, -, a₁, ha₁t, ha₁eq, hreg⟩ := htr' tt htt y' hy'
  obtain ⟨A₁, -⟩ := hreg z' hzy
  have ha₁eq' : (a₁ : ℝ) = t - T / R k := ha₁eq
  have haSa₁ : aSeed k ≤ a₁ := by
    change (aSeed k : ℝ) ≤ a₁
    linarith
  have hP : ∀ zc : ((Kh k).stage (i k).castSucc).Carrier, HEq z' zc →
      zc ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
        (r / Real.sqrt (R k)) := by
    intro zc hzc
    have hzc' : zc = z := eq_of_heq (hzc.symm.trans hz')
    rw [hzc']
    exact hz
  have hstay' := hst tt htt htσ a₁ haSa₁ ha₁t (le_of_eq ha₁eq'.symm) z' hP A₁
  -- 整窗逐点界（hTR，∀ 深度）+ 整窗 stay，搬到 slab 形
  have hpt : ∀ s ∈ Icc τ t,
      ((Kh k).event (i k)).incoming.flow.scalar s z ≤ Q * R k ∧
      riemannianEDistOf (((Kh k).event (i k)).incoming.flow.base.metric s)
          ((seedTrace k).point (i k).castSucc h1 h2) z ≤
        riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) (y k) +
          ENNReal.ofReal (L k / 2 / Real.sqrt (R k)) := by
    intro s hs
    have hs0 : 0 ≤ s := ((Kh k).time_nonneg _).trans (hτ3.le.trans hs.1)
    have hsh : s ≤ (Kh k).horizon := hs.2.trans hth
    let sI : Icc (0 : ℝ) (Kh k).horizon := ⟨s, hs0, hsh⟩
    have hsI : (sI : ℝ) = s := rfl
    have hes : (Kh k).activeStage sI = (i k).castSucc :=
      (Kh k).activeStage_eq_of_mem_slab_P6F3 (i k) sI (hτ3.le.trans hs.1)
        (lt_of_le_of_lt hs.2 hti.2)
    have ha₁s : a₁ ≤ sI := by
      change (a₁ : ℝ) ≤ s
      linarith [hs.1]
    have hst' : sI ≤ tt := by
      change s ≤ t
      exact hs.2
    have hAz : HEq (A₁.point ((Kh k).activeStage sI) ((Kh k).activeStage_mono ha₁s)
        ((Kh k).activeStage_mono hst')) z :=
      (trace_point_heq_P6DL2 (a := a₁) (t := tt) (hat := ha₁t) A₁ ha₁s hst'
        (hes.trans he.symm)).trans hz'
    have haSs : aSeed k ≤ sI := haSa₁.trans ha₁s
    have hsTn : sI ≤ Tn k := (hst'.trans htσ).trans (hsT k)
    obtain ⟨hd, hsc, -⟩ := (Kh k).transport_at_stage_P6JW (haT k) (seedTrace k) haSs hsTn hes
      hsI _ z hAz h1 h2
    have hb9 := (Kh k).hgrid_of_isTracedRegion_P6BB hRk0 (hK r T) (htr' tt htt y' hy') hzy ha₁t
      (le_of_eq ha₁eq.symm) A₁ sI ha₁s hst'
    rw [hsc, ObservedHistory.stageMetric_castSucc_apply] at hb9
    refine ⟨hb9.trans (mul_le_mul_of_nonneg_right hQ9 hRk0.le), ?_⟩
    have h := hstay' sI ha₁s hst'
    rw [hd, ObservedHistory.stageMetric_castSucc_apply] at h
    exact h
  -- 数值（E1）（E2）
  have hE1 : 8 * T * Real.sqrt (cDist_P6DL2 C2 Q) ≤ Real.sqrt (R k) := by
    have := Real.sqrt_nonneg (R k)
    linarith
  have hE2 : 16 * Real.sqrt (cDist_P6DL2 C2 Q) + 2 ≤ L k := by linarith
  obtain ⟨ℓ, K, h, hℓ, hℓM, hℓr, hKℓ, hKr, hKC, hh, hbud, hLc, hLs, hdrift⟩ :=
    large_numerics_P6DL2 Ctime hC2 hQ1 hR1 hT hE1 hE2
  have hLk1 : 1 ≤ L k := by
    have := Real.sqrt_nonneg (cDist_P6DL2 C2 Q)
    linarith
  have haτ : (aSeed k : ℝ) ≤ τ := by linarith
  have hLτ : (σ k : ℝ) - L k ^ 2 / R k ≤ τ := by
    have h2T : 2 * T ≤ L k ^ 2 := by
      calc 2 * T ≤ L k := by linarith
        _ = 1 * L k := (one_mul _).symm
        _ ≤ L k * L k := mul_le_mul_of_nonneg_right hLk1 (by linarith)
        _ = L k ^ 2 := (sq _).symm
    have : 2 * T / R k ≤ L k ^ 2 / R k := div_le_div_of_nonneg_right h2T hRk0.le
    have e : 2 * T / R k = T / R k + T / R k := by ring
    linarith
  have hMτ : 1 ≤ 2 * (Q * R k) * τ := by
    have hQR : 1 ≤ Q * R k := one_le_mul_of_one_le_of_one_le hQ1 hR1
    have hτ1' : 1 ≤ τ := (hone k).trans haτ
    have := mul_le_mul hQR hτ1' zero_le_one (by linarith)
    linarith
  have hmain := (Kh k).hdistL_large_single_P6DL2 (haT k) (hsT k) (has k) (hsm k) (hclock k)
    (seedTrace k) (ha₀ k) (hpin k) (y k) hRk0 (hgood k) (i k) h1 h2 z (τ₀ := τ) (t := t) hτ3 hti.2
    haτ (by linarith [hti.2]) hLτ (by positivity) (mul_le_mul_of_nonneg_right hQ4 hRk0.le) hC2
    (fun s hs => (hpt s hs).1) hh hbud hℓ hℓM hℓr hKℓ hKr hKC hMτ hLc (by linarith)
    (by linarith) hLs hfk (fun s hs => (hpt s hs).2) τ ⟨le_rfl, hτ2⟩
  refine hmain.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
  have hc8 : (0 : ℝ) ≤ 8 / ℓ := div_nonneg (by norm_num) hℓ.le
  calc 8 / ℓ * (t - τ) ≤ 8 / ℓ * (T / R k) := mul_le_mul_of_nonneg_left (by linarith) hc8
    _ ≤ 1 := hdrift

/-- **G4b 槽（`_DLW`，PROVISIONAL[`hTRs`]）**：顶层 `hdistLA` 槽逐字（εP6 ≤ ε₀）。 -/
theorem hdistLA_win_of_TRs_gate_HCTD :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric)
      (εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ), (∀ Γ Γf, εP6 Γ Γf ≤ ε₀) →
    (
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
      ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
        (T.block j) (T.lookahead j) (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∀ {ε C1 C2 : ℝ} {Ctime : ℝ≥0}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ →
      Ctime = p6Ctime_C11G7B.{u} Γ →
      ∀ (pF : CutoffParameters) (records : ∀ n (e : Fin (F.tower.history n).eventCount),
        GeometricCutoffRecord (F.tower.history n).toHistory e pF),
      pF.modelRadius = pB.modelRadius → pF.modelOrder = pB.modelOrder →
      pF.modelAccuracy = pB.modelAccuracy →
      (∀ t : ℝ, 0 ≤ t → pF.delta t = q.delta t ∧ pF.neckRadius t = q.neckRadius t) →
      (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
      (∀ n e b, ((records n e).static b).hasLinkedCanonicalWindow_C12X) →
      (∀ n e b, ((records n e).static b).witness.HasRadialCoordinates) →
      (∀ n e, ((F.tower.history n).toHistory.event e).old =
        ((F.tower.history n).toHistory.event e).transition.trace.retainedCore) →
      Tendsto pF.delta atTop (𝓝 0) →
      (∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
        ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
          (F.tower.history n).time e.succ ∈ Icc (t / 2) t →
          ∀ h, (records n e).nominalRadius h ≤ η * pF.neckRadius t) →
      (
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
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
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ k in atTop,
          ∀ (e : Fin (Kh k).eventCount) b, (σ k : ℝ) - T / R k < (Kh k).time e.succ →
            2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R k) <
              (((records (ind k) e).rescale_P6M (c k) (hc k)).static b).neck.scale)∧
      ∀ Aseed : ℝ, 1 < Aseed →
      ∀ (T r : ℝ), 0 < T → 0 < r → ∃ Kt : ℝ, 0 ≤ Kt ∧
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
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((Aseed + 3) * 1)) →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            ∀ (tt : Icc (0 : ℝ) (Kh k).horizon), (tt : ℝ) = t →
            ∀ y' : ((Kh k).stageAt tt).Carrier, HEq y' p' →
              (Kh k).isTracedRegion tt y' (r / Real.sqrt (R k)) (T / R k) (Kt * R k)
    ) →
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
      ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
        (T.block j) (T.lookahead j) (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∀ {ε C1 C2 : ℝ} {Ctime : ℝ≥0}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ →
      Ctime = p6Ctime_C11G7B.{u} Γ →
      ∀ Aseed : ℝ, 1 < Aseed →
        ∀ (T r : ℝ), 0 < T → 0 < r →
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
            (∀ᶠ k in atTop,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                  ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                    ((Kh k).activeStage_mono (hsT k))) (y k) +
                ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((Aseed + 3) * 1)) →
            (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
          ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
          ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
            (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
            ((Kh k).event (i k)).RegularCrossing p' q →
            ∀ (h1 : (Kh k).activeStage (aSeed k) ≤ (i k).castSucc)
              (h2 : (i k).castSucc ≤ (Kh k).activeStage (Tn k)),
            ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ, ∀ τ : ℝ,
              t - T / R k ≤ τ → τ ≤ t → (Kh k).time (i k).castSucc < τ →
              ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                  (r / Real.sqrt (R k)),
                riemannianEDistOf (((Kh k).event (i k)).incoming.flow.base.metric τ)
                    ((seedTrace k).point (i k).castSucc h1 h2) z ≤
                  riemannianEDistOf (((Kh k).event (i k)).incoming.flow.base.metric t)
                    ((seedTrace k).point (i k).castSucc h1 h2) z + ENNReal.ofReal 1 := by
  obtain ⟨ε₀, hε₀, hG1⟩ := hdistL_large_win_gate_HCTD.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro P g εP6 hle hTRs
    pB Γ Γf hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord ε C1 C2 Ctime
    hε hC1 hC2 hCt
  obtain ⟨pF, records, hprad, hpord, hpacc, hpq, hcan, hlink, hradl, hold, hδ, hrec⟩ :=
    GC.LongTime.Ch11.exists_records_of_prepared_chain_v3_C12R T.toChain F hF q hq
  obtain ⟨hsep, hcon⟩ := hTRs hfine hs hW Cdist εReserve T
    hcert hS F q hF hq hacc hrad hord hε hC1 hC2 hCt
    pF records hprad hpord hpacc hpq hcan hlink hradl hold hδ hrec
  have hC2' : 1 ≤ C2 := by
    rw [hC2]
    exact GC.LongTime.Ch11.one_le_C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ
  have hte : StandardCap.transitionEnd + 10 < capWindowRadius_C11E + 1 := by
    have := StandardCap.transitionEnd_pos
    unfold capWindowRadius_C11E
    linarith
  intro Aseed hA T r hT hr ind c hc Kh Tn pT hTc aSeed haT hclock hone hsm hvolG h2G hnrG
    seedTrace σ y R hsT has L hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii hdist hceil
    i hi
  obtain ⟨Ktr, hK, hTRf⟩ := exists_fun_of_forall_exists_DLW (hcon Aseed hA)
  have hfinE := hdist.mono fun k hk =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_self_add.trans hk)
  refine hG1 (F := F) (qp := pF) (q := q) (Aseed := Aseed)
    (Ktr := Ktr) hC2' (hprad ▸ hte.trans_le hrad)
    (hpacc ▸ hacc.trans (hle Γ Γf)) (hpord ▸ hord) hδ hK ?_ hTRf T r hT hr ind c hc Tn pT hTc
    aSeed haT hclock hone hsm hvolG h2G hnrG seedTrace σ y R hsT has L hRdef hRpos hRr hL hsel
    hgood haS hTnS hroom hradii hdist hceil i hi hfinE
  intro ind c hc Kh Tn pT hTc aSeed haT hclock hone hsm _ _ _ seedTrace σ y R hsT has L hRdef hRpos
    hRr hL hsel hgood haS hTnS hroom hradii _ _
  refine ⟨fun _ => 0, fun _ => 0, fun k e _ => (records (ind k) e).rescale_P6M (c k) (hc k),
    fun _ => le_rfl,
    fun k τ x => ObservedHistory.hpin_rescaled_of_records_P6HI F records ind c hc k τ x,
    fun k => (aSeed k).2.1,
    fun k e _ => ((records (ind k) e).rescale_P6M (c k) (hc k)).old_eq_retained,
    fun k e _ b => ((records (ind k) e).static b).hasCanonicalWindow_rescale_P6M (hcan (ind k) e b)
      (c k) (hc k), ?_⟩
  intro i hi T hT C hC
  exact (hsep
      ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L hRdef hRpos hRr hL
      hsel hgood haS hTnS hroom hradii i hi T hT C hC).mono
    fun k hk e _ b hlt => hk e b hlt


/-- consumer：常值选择子 `εP6 := ε₀` 时给 `hdistLA‴` 槽（hTRs‴ 前提）。 -/
example : True := by
  obtain ⟨ε₀, _hε₀, hDL⟩ := hdistLA_win_of_TRs_gate_HCTD.{u}
  have _h := fun (P : OrientedThreeStage.{u}) (g : P.Metric) =>
    hDL P g (fun _ _ => ε₀) (fun _ _ => le_rfl)
  trivial

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

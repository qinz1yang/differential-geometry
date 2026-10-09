import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DepthR4AssembleP6DP4E
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6R4KernelSeqHCT
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DepthR4NotTRP6DP4E2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DepthR4DiagP6DP4E2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6BCDBootstrapBallP6BB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDAlignCrossP6SB2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6StageStabP6ST
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.AdapterAgeRecord_P6M

/-!
# E1（R4 中心族）的 hTR‴ gate + 天花板孪生（O-CH11-HCEILT G2，后缀 `_HCT`）

lead R39/R41：hTR 合同收窄为 hTR‴ = 前缀 + Aseed gate 块（体积、`2 < Tn`、nr、`d_σ + (L+1)/√R ≤ Aseed + 3`）
+ 天花板 `R ≤ ρ̂(Tn)⁻²`（HP3 joint prefix `hQρ` 逐字）。E1 的反证/对角论证逐字，只把这些前缀项透传到
回调（gate 经对角 `Fd` 变逐点），并导出 R4 hcomp 与选择阈值 `Θ`、`2k+2 ≤ R`。无新 binder / Prop。
生成器 build-logs/scratch/O-CH11-HCEILT/gen/genB.py。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **E2a′ gate + 天花板孪生（`_HCT`，PROVED 相对同一环境前提）**：`exists_R4_center_family_of_notTR_P6DP4E2`
逐字，hTR 合同收窄为 hTR‴（前缀 + Aseed gate 块 + `hceil`，`q`、`Aseed` 为参数）；回调多收
gate 块（gate 逐点）、`hceil`、R4 hcomp（`d_t ≤ d_σ + 1/√R`）、阈值 `Θ k ≤ c k · Tn k` 与 `2k + 2 ≤ R k`
（对角选点并入 `Fd`）。 -/
theorem exists_R4_center_family_of_notTR_gate_HCT :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
      {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {pF : CutoffParameters}
      (records : ∀ n (e : Fin (F.tower.history n).eventCount),
        GeometricCutoffRecord (F.tower.history n).toHistory e pF),
      (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
      pF.modelAccuracy ≤ ε₀ → 2 ≤ pF.modelOrder →
      StandardCap.transitionEnd + 10 < pF.modelRadius →
      ∀ (q : CutoffParameters) (Aseed : ℝ) (Θ : ℕ → ℝ),
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
              (((records (ind k) e).rescale_P6M (c k) (hc k)).static b).neck.scale) →
      ∀ (T r : ℝ), 0 < T → 0 < r →
      (∀ m : ℕ, ¬ (
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
                (Kh k).isTracedRegion tt y' (r / Real.sqrt (R k)) (T / R k) ((m : ℝ) * R k))) →
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
          (∀ k,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
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
          (∀ k, ¬ (Kh k).isTracedRegion (t k) (y' k) (r / Real.sqrt (R k)) (T / R k)
            ((k : ℝ) * R k)) →
          (∀ k, Θ k ≤ c k * (Tn k : ℝ)) → (∀ k : ℕ, 2 * (k : ℝ) + 2 ≤ R k) →
          False) →
      False := by
  obtain ⟨ε₀, hε₀, hE1⟩ := exists_R4_center_family_hcomp_HCT.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro P g F ε C1 C2 Ctime pF records hcanF hacc hord hrad q Aseed Θ hsepWK T r hT hr hneg
    hcont
  have h0 := hneg
  simp only [not_forall, Filter.not_eventually, exists_prop] at h0
  choose ind c hc Tn pT hTc aSeed haT hclock hone hsm hvol hTn2 hnrS seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii hgate hceil i hi hbad using h0
  -- tower-frame hsepWK at the selection event, `C = 1`, threshold `T = 1`
  have hsep1 : ∀ m, ∀ᶠ k in atTop, ∀ b, 2 * max (3 / ((1 : ℝ) / 100) ^ 2) (1 * R m k) <
      (((records (ind m k) (i m k)).rescale_P6M (c m k) (hc m k)).static b).neck.scale := by
    intro m
    filter_upwards [hsepWK (ind m) (c m) (hc m) (Tn m) (pT m) (hTc m) (aSeed m) (haT m)
      (hclock m) (hone m) (hsm m) (seedTrace m) (σ m) (y m) (R m) (hsT m) (has m) (L m)
      (hRdef m) (hRpos m) (hRr m) (hL m) (hsel m) (hgood m) (haS m) (hTnS m) (hroom m)
      (hradii m) (i m) (hi m) 1 one_pos 1 zero_le_one] with k hk b
    refine hk (i m k) b ?_
    rw [← hi m k]
    have : 0 < 1 / R m k := one_div_pos.mpr (hRpos m k)
    linarith
  have hΘk : ∀ m, ∀ᶠ k in atTop, Θ m ≤ c m k * (Tn m k : ℝ) := fun m => by
    obtain ⟨N, hN⟩ := exists_nat_ge (Θ m)
    filter_upwards [eventually_ge_atTop N] with k hk
    have h1 : (N : ℝ) ≤ k := by exact_mod_cast hk
    linarith [hTc m k]
  let Kh' : ∀ m k, ObservedHistory.{u} := fun m k =>
    ((F.tower.history (ind m k)).rescale_P6N (c m k) (hc m k)).toHistory
  -- diagonal pick
  obtain ⟨κ, hκ⟩ := GC.LongTime.Ch11.exists_diag_pick_P6DP4E2 hbad
    (E := fun m T k => (aSeed m k : ℝ) ≤ σ m k - T / R m k ∧
      (Tn m k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ m k : ℝ) - T / R m k)
    (Fd := fun m T k => T + 1 ≤ L m k ∧
      T ≤ R m k * ((σ m k : ℝ) - ((Tn m k : ℝ) - 1 ^ (2 : ℕ) / 2)) ∧
      T ≤ 1 / 200 * Real.sqrt (R m k) ∧
      (∀ b, 2 * max (3 / ((1 : ℝ) / 100) ^ 2) (1 * R m k) <
        (((records (ind m k) (i m k)).rescale_P6M (c m k) (hc m k)).static b).neck.scale) ∧
      (riemannianEDistOf ((Kh' m k).stageMetric ((Kh' m k).activeStage (σ m k)) (σ m k))
          ((seedTrace m k).point ((Kh' m k).activeStage (σ m k))
            ((Kh' m k).activeStage_mono (has m k)) ((Kh' m k).activeStage_mono (hsT m k)))
            (y m k) +
        ENNReal.ofReal ((L m k + 1) / Real.sqrt (R m k)) ≤ ENNReal.ofReal ((Aseed + 3) * 1)) ∧
      Θ m ≤ c m k * (Tn m k : ℝ) ∧ 2 * m + 1 ≤ k)
    (fun m T hT => (haS m T hT).and (hTnS m T hT))
    (fun m T => ((hL m).eventually_ge_atTop (T + 1)).and (((hroom m).eventually_ge_atTop T).and
      (((hradii m).eventually_ge_atTop T).and ((hsep1 m).and ((hgate m).and
        ((hΘk m).and (eventually_ge_atTop (2 * m + 1))))))))
  -- the diagonal family satisfies the hTR prefix
  have hmk : ∀ m : ℕ, (m : ℝ) ≤ (κ m : ℝ) := fun m => by exact_mod_cast (hκ m).2.2.2
  have hRpos' : ∀ m, 0 < R m (κ m) := fun m => hRpos m (κ m)
  have hTc' : ∀ m : ℕ, (m : ℝ) + 1 ≤ c m (κ m) * (Tn m (κ m) : ℝ) := fun m =>
    le_trans (by linarith [hmk m]) (hTc m (κ m))
  have hRr' : ∀ m : ℕ, (m : ℝ) + 1 ≤ R m (κ m) := fun m =>
    le_trans (by linarith [hmk m]) (hRr m (κ m))
  have hL' : Tendsto (fun m => L m (κ m)) atTop atTop :=
    GC.LongTime.Ch11.tendsto_of_diag_P6DP4E2 fun m => by linarith [(hκ m).2.2.1.1]
  have hroom' : Tendsto (fun m => R m (κ m) * ((σ m (κ m) : ℝ) -
      ((Tn m (κ m) : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop :=
    GC.LongTime.Ch11.tendsto_of_diag_P6DP4E2
      (L := fun m k => R m k * ((σ m k : ℝ) - ((Tn m k : ℝ) - 1 ^ (2 : ℕ) / 2)))
      fun m => (hκ m).2.2.1.2.1
  have hradii' : Tendsto (fun m => 1 / 200 * Real.sqrt (R m (κ m))) atTop atTop :=
    GC.LongTime.Ch11.tendsto_of_diag_P6DP4E2 (L := fun m k => 1 / 200 * Real.sqrt (R m k))
      fun m => (hκ m).2.2.1.2.2.1
  have haS' : ∀ T : ℝ, 0 < T → ∀ᶠ m in atTop,
      (aSeed m (κ m) : ℝ) ≤ σ m (κ m) - T / R m (κ m) :=
    GC.LongTime.Ch11.eventually_of_diag_P6DP4E2
      (E := fun m T k => (aSeed m k : ℝ) ≤ σ m k - T / R m k)
      (fun m T T' k hTT' h => le_trans h (by
        have := div_le_div_of_nonneg_right hTT' (hRpos m k).le
        linarith)) fun m => (hκ m).2.1.1
  have hTnS' : ∀ T : ℝ, 0 < T → ∀ᶠ m in atTop,
      (Tn m (κ m) : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ m (κ m) : ℝ) - T / R m (κ m) :=
    GC.LongTime.Ch11.eventually_of_diag_P6DP4E2
      (E := fun m T k => (Tn m k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ m k : ℝ) - T / R m k)
      (fun m T T' k hTT' h => le_trans h (by
        have := div_le_div_of_nonneg_right hTT' (hRpos m k).le
        linarith)) fun m => (hκ m).2.1.2
  -- E1 environment on the diagonal family
  let K : ℕ → RetainedCoreHistory.{u} := fun m =>
    (F.tower.history (ind m (κ m))).rescale_P6N (c m (κ m)) (hc m (κ m))
  have hasl : ∀ m, (aSeed m (κ m) : ℝ) < σ m (κ m) := fun m => by
    have h1 := (hκ m).2.1.1
    have h2 : 0 < ((m : ℝ) + 1) / R m (κ m) := div_pos (by positivity) (hRpos m (κ m))
    linarith
  have hf : ∀ m, (K m).toHistory.activeStage (aSeed m (κ m)) ≤ (i m (κ m)).castSucc := fun m =>
    ObservedHistory.activeStage_le_castSucc_of_lt_P6ST (K m).toHistory (i m (κ m))
      ((hasl m).trans_eq (hi m (κ m)))
  have hl : ∀ m, (i m (κ m)).succ ≤ (K m).toHistory.activeStage (Tn m (κ m)) := fun m =>
    (activeStage_time_succ_P6DP4E (K m) (i m (κ m)) (σ m (κ m)) (hi m (κ m))).symm.le.trans
      ((K m).toHistory.activeStage_mono (hsT m (κ m)))
  obtain ⟨pm, t, y', hat, hts, hB, hy', hclose, hcompR, hgood'⟩ := hE1 (eps := ε) (C1' := C1)
    (C2' := C2) (Ctime' := Ctime) K (fun m => i m (κ m))
    (q := fun m => pF.rescale_P6N (c m (κ m)) (hc m (κ m)))
    (fun m => (records (ind m (κ m)) (i m (κ m))).rescale_P6M (c m (κ m)) (hc m (κ m)))
    (fun m => Tn m (κ m)) (fun m => aSeed m (κ m)) (fun m => σ m (κ m))
    (fun m => haT m (κ m)) (fun m => hsT m (κ m)) (fun m => has m (κ m))
    (fun m => pT m (κ m)) (fun m => seedTrace m (κ m)) (fun m => y m (κ m))
    (fun m => R m (κ m)) (fun m => L m (κ m)) hRpos'
    (fun m => by linarith [(hκ m).2.2.1.1, hmk m, (by positivity : (0 : ℝ) ≤ m)])
    hasl (fun m => hi m (κ m)) hf hl
    (fun m => ((records (ind m (κ m)) (i m (κ m))).rescale_P6M (c m (κ m))
      (hc m (κ m))).old_eq_retained)
    (fun m b => ((records (ind m (κ m)) (i m (κ m))).static b).hasCanonicalWindow_rescale_P6M
      (hcanF _ _ b) _ _)
    (fun _ => hacc) (fun _ => hord) (fun _ => hrad)
    (fun m b => by
      refine scalar_lt_half_scale_of_sep_seed_P6DP4E ((hκ m).2.2.1.2.2.2.1 b) ?_
      have h1 := ObservedHistory.seed_scalar_le_of_smallParabolic_C11G (K m).toHistory (haT m (κ m))
        (hsm m (κ m)) (hclock m (κ m)) (seedTrace m (κ m)) (σ m (κ m)) (has m (κ m))
        (hsT m (κ m)) (i m (κ m)).succ
        (activeStage_time_succ_P6DP4E (K m) (i m (κ m)) (σ m (κ m)) (hi m (κ m)))
        ((hf m).trans (Fin.castSucc_lt_succ (i := i m (κ m))).le) (hl m)
      rw [hi m (κ m), ObservedHistory.stageMetric_succ_time_C11G] at h1
      exact h1.trans (by norm_num))
    (fun m wp hwp b => by
      refine scalar_lt_half_scale_of_sep_P6DP4E ((hκ m).2.2.1.2.2.2.1 b) ?_
      have h := ObservedHistory.towerScale_eq_output_P6SB2 (K m).toHistory (i m (κ m))
        (σ m (κ m)) (hi m (κ m)) (y m (κ m)) wp hwp
      rw [← hRdef m (κ m)] at h
      rw [← h]
      linarith)
    (fun m => hgood m (κ m))
    (fun m pm' t' =>
      (∃ wp : ((K m).toHistory.stage (i m (κ m)).succ).Carrier, HEq (y m (κ m)) wp ∧
        ((K m).toHistory.event (i m (κ m))).RegularCrossing pm' wp) ∧
      ((K m).time (i m (κ m)).castSucc < t' ∧ t' < (K m).time (i m (κ m)).succ) ∧
      (∀ (tt : Icc (0 : ℝ) (K m).toHistory.horizon), (tt : ℝ) = t' →
        ∀ yy : ((K m).toHistory.stageAt tt).Carrier, HEq yy pm' →
          metricScalarAt ((K m).toHistory.stageMetric ((K m).toHistory.activeStage tt) tt) yy <
            2 * R m (κ m)) ∧
      (∀ (tt : Icc (0 : ℝ) (K m).toHistory.horizon), (tt : ℝ) = t' →
        ∀ yy : ((K m).toHistory.stageAt tt).Carrier, HEq yy pm' →
          R m (κ m) / 2 <
            metricScalarAt ((K m).toHistory.stageMetric ((K m).toHistory.activeStage tt) tt) yy) ∧
      ∃ tt : Icc (0 : ℝ) (K m).toHistory.horizon, (tt : ℝ) = t' ∧
        ∃ yy : ((K m).toHistory.stageAt tt).Carrier, HEq yy pm' ∧
          ¬ (K m).toHistory.isTracedRegion tt yy (r / Real.sqrt (R m (κ m)))
            (T / R m (κ m)) ((m : ℝ) * R m (κ m)))
    (fun m => by
      obtain ⟨p', q, hq, hcr, hfr⟩ := (hκ m).1
      refine ⟨p', q, hq, hcr, ?_⟩
      have hR2 : metricScalarAt ((K m).toHistory.event (i m (κ m))).outputMetric q <
          2 * R m (κ m) := by
        have h := ObservedHistory.towerScale_eq_output_P6SB2 (K m).toHistory (i m (κ m))
          (σ m (κ m)) (hi m (κ m)) (y m (κ m)) q hq
        rw [← hRdef m (κ m)] at h
        rw [← h]
        linarith [hRpos m (κ m)]
      have hcmp := ObservedHistory.eventually_centerScalar_lt_of_regularCrossing_P6SB2
        (K m).toHistory (i m (κ m)) hcr hR2
      have hR3 : R m (κ m) / 2 <
          metricScalarAt ((K m).toHistory.event (i m (κ m))).outputMetric q := by
        have h := ObservedHistory.towerScale_eq_output_P6SB2 (K m).toHistory (i m (κ m))
          (σ m (κ m)) (hi m (κ m)) (y m (κ m)) q hq
        rw [← hRdef m (κ m)] at h
        rw [← h]
        linarith [hRpos m (κ m)]
      have hcmpL := eventually_centerScalar_gt_of_regularCrossing_P6DP4E2
        (K m).toHistory (i m (κ m)) hcr hR3
      have hslab : ∀ᶠ t' in 𝓝[<] (K m).time (i m (κ m)).succ,
          t' ∈ Ioo ((K m).time (i m (κ m)).castSucc) ((K m).time (i m (κ m)).succ) :=
        Ioo_mem_nhdsLT ((K m).time_strictMono (Fin.castSucc_lt_succ (i := i m (κ m))))
      exact (hfr.and_eventually (hcmp.and (hcmpL.and hslab))).mono fun t' h =>
        ⟨⟨q, hq, hcr⟩, h.2.2.2, h.2.1, h.2.2.1, h.1⟩)
  have hcross := fun k => (hB k).1
  have hslab := fun k => (hB k).2.1
  have hcmp := fun k => (hB k).2.2.1 (t k) rfl (y' k) (hy' k)
  have hcmpL := fun k => (hB k).2.2.2.1 (t k) rfl (y' k) (hy' k)
  have hbadTR : ∀ k, ¬ (K k).toHistory.isTracedRegion (t k) (y' k) (r / Real.sqrt (R k (κ k)))
      (T / R k (κ k)) ((k : ℝ) * R k (κ k)) := by
    intro k
    obtain ⟨tt, htt, yy, hyy, hn⟩ := (hB k).2.2.2.2
    obtain rfl : tt = t k := Subtype.ext htt
    obtain rfl : yy = y' k := eq_of_heq (hyy.trans (hy' k).symm)
    exact hn
  exact hcont (fun m => ind m (κ m)) (fun m => c m (κ m)) (fun m => hc m (κ m))
    (fun m => Tn m (κ m)) (fun m => pT m (κ m)) hTc' (fun m => aSeed m (κ m))
    (fun m => haT m (κ m)) (fun m => hclock m (κ m)) (fun m => hone m (κ m))
    (fun m => hsm m (κ m)) (fun m => hvol m (κ m)) (fun m => hTn2 m (κ m))
    (fun m => hnrS m (κ m)) (fun m => seedTrace m (κ m)) (fun m => σ m (κ m))
    (fun m => y m (κ m)) (fun m => R m (κ m)) (fun m => hsT m (κ m)) (fun m => has m (κ m))
    (fun m => L m (κ m)) (fun m => hRdef m (κ m)) hRpos' hRr' hL' (fun m => hsel m (κ m))
    (fun m => hgood m (κ m)) haS' hTnS' hroom' hradii'
    (fun m => (hκ m).2.2.1.2.2.2.2.1) (fun m => hceil m (κ m)) (fun m => i m (κ m))
    (fun m => hi m (κ m)) pm t y' hat hts hy' hcross hslab hclose hcompR hcmp hcmpL hgood' hbadTR
    (fun m => (hκ m).2.2.1.2.2.2.2.2.1) (fun m => by
      have h1 : (2 * m + 1 : ℕ) ≤ κ m := (hκ m).2.2.1.2.2.2.2.2.2
      have h2 : (2 : ℝ) * m + 1 ≤ (κ m : ℝ) := by exact_mod_cast h1
      linarith [hRr m (κ m)])

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

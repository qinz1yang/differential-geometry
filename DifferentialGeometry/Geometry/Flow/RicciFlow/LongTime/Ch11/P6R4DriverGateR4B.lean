import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6R4DriverGateHTP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6R4BcadCProducerR4B

set_option autoImplicit false

/-!
# R4BCAD G2：R4 driver gate 孪生——hbcadC 在 driver 内付（后缀 `_R4B`）

`hTR_of_driver_gate_HTP`（HTRSPAY G2）逐字，只改：
(1) 删 hbcadC binder（R4 帧闭合）；driver 内由 R4BCAD G1 `hbcadC_R4center_R4B` 在 E2a′ 回调环境（R4 中心
    `(t, y′)`）付出，前提全是 driver 已有环境项（recent / hfine / TDS / FRESH / hanti / hδq）与回调字段；
(2) 传给 E2a′ 的阈值序列由 `max (Trec k) (2Tδ)` 改为 `max (max (Trec k) (2Tδ)) (Θb k)`（`Θb` 为 G1 输出），
    原 hK 调用取 `le_max_left`，G1 取 `le_max_right`。
F-24-8：同一元组 `(ind, c, Tn, aSeed, seedTrace, σ, y, R, L, t, y′)`，同一 recQ / hfine / hsupA。
生成器 build-logs/scratch/R4BCAD/gen/gD.py
（源 sha256 `0fc0b81d524abae828f3c8209ecfcee052204cfa74b3b899091aa856978c962e`）。
-/

noncomputable section

open Set Filter Function Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open ObservedHistory (DepthExtendable)

/-- **R4 driver gate 孪生（`_R4B`，PROVISIONAL[hsepWK（带 hceil）, hkappaC, hsurvive, hextend]；
hK / hpinch / hseed / hbcadC 在内付）**：`hTR_of_driver_gate_HTP` 逐字删 hbcadC binder；见模块文档。 -/
theorem hTR_of_driver_gate_R4B :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
      {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {pF : CutoffParameters}
      (records : ∀ n (e : Fin (F.tower.history n).eventCount),
        GeometricCutoffRecord (F.tower.history n).toHistory e pF),
      (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
      pF.modelAccuracy ≤ ε₀ → 2 ≤ pF.modelOrder →
      StandardCap.transitionEnd + 10 < pF.modelRadius →
      0 < ε → ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} →
      -- HCEILT 环境（R4 中心 kernel 内付 hK）：SCRS⁺ 投影 / FRESH / 数值
      ε ≤ coneAccuracy → 0 ≤ C2 →
      ∀ (q : CutoffParameters), AntitoneOn q.neckRadius (Ici 0) → Tendsto q.delta atTop (𝓝 0) →
      ∀ (recQ : ∀ n (e : Fin (F.tower.history n).eventCount),
        GeometricCutoffRecord (F.tower.history n).toHistory e q),
      (∀ ε' : ℝ, 0 < ε' → ∃ T : ℝ, 0 < T ∧ ∀ t, T ≤ t →
        ∀ n (i : Fin (F.tower.history n).eventCount),
        (F.tower.history n).time i.succ ∈ Icc (t / 2) t →
        ∀ h, (recQ n i).nominalRadius h ≤ ε' * q.neckRadius t) →
      (∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T₀ : ℝ, ∀ n, ∃ p : CutoffParameters,
        D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
        ∃ records' : ∀ i : Fin (F.tower.history n).eventCount,
            T₀ ≤ (F.tower.history n).time i.succ →
            GeometricCutoffRecord (F.tower.history n).toHistory i p,
          (∀ i hi b, ((records' i hi).static b).hasCanonicalWindow) ∧
          ∀ i hi b, ((records' i hi).static b).neck.scale = ((recQ n i).static b).neck.scale) →
      GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime →
      (∀ Aseed : ℝ, 1 < Aseed → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ,
        ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) (k : ℕ),
          KappaSeedWindowFwd_C11PK
            (fun w => q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k)) (Aseed + 7) κ
            (Tf / c k) ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory) →
      -- hsepWK（塔帧 (SEP-ρ)，owner HNOT-LOCALDT）
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
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ k in atTop,
          ∀ (e : Fin (Kh k).eventCount) b, (σ k : ℝ) - T / R k < (Kh k).time e.succ →
            2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R k) <
              (((records (ind k) e).rescale_P6M (c k) (hc k)).static b).neck.scale) →
      ∀ {Cst : ℝ≥0} {κ : ℝ}, 0 < κ →
      -- hsurvive（R4 帧闭合；driver / SB2 原文逐字）
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
        ∀ (pm : ∀ k, ((Kh k).stage (i k).castSucc).Carrier)
          (t : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y' : ∀ k, ((Kh k).stageAt (t k)).Carrier)
          (hat : ∀ k, aSeed k ≤ t k) (hts : ∀ k, t k ≤ σ k),
          (∀ k, HEq (y' k) (pm k)) →
          (∀ k, ∃ wp : ((Kh k).stage (i k).succ).Carrier, HEq (y k) wp ∧
            ((Kh k).event (i k)).RegularCrossing (pm k) wp) →
          (∀ k, (Kh k).time (i k).castSucc < (t k : ℝ) ∧ (t k : ℝ) < (Kh k).time (i k).succ) →
          (∀ k, (σ k : ℝ) - t k ≤ 1 / R k) →
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
      ∀ A T Q : ℝ, 0 < A → 0 < T → 2 ≤ Q → 4 * (Cst : ℝ) * Q * T ≤ 1 →
        ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
          (∀ z ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (t n)) (t n)) (y' n)
              (A / Real.sqrt (R n)),
            metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (t n)) (t n)) z ≤ Q * R n) →
          (Kh n).isTracedRegion (t n) (y' n) (A / Real.sqrt (R n)) (T / R n) (K * R n)) →
      -- hextend（R4 帧闭合；driver / SB2 原文逐字）
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
        ∀ (pm : ∀ k, ((Kh k).stage (i k).castSucc).Carrier)
          (t : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y' : ∀ k, ((Kh k).stageAt (t k)).Carrier)
          (hat : ∀ k, aSeed k ≤ t k) (hts : ∀ k, t k ≤ σ k),
          (∀ k, HEq (y' k) (pm k)) →
          (∀ k, ∃ wp : ((Kh k).stage (i k).succ).Carrier, HEq (y k) wp ∧
            ((Kh k).event (i k)).RegularCrossing (pm k) wp) →
          (∀ k, (Kh k).time (i k).castSucc < (t k : ℝ) ∧ (t k : ℝ) < (Kh k).time (i k).succ) →
          (∀ k, (σ k : ℝ) - t k ≤ 1 / R k) →
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
      ∀ σ : ℕ → ℕ, StrictMono σ → ∀ Tstar M : ℝ, 0 < Tstar → 0 ≤ M →
        (∀ T : ℝ, 0 < T → T < Tstar → DepthExtendable Kh t y' R σ T) →
        (∀ T' : ℝ, 0 < T' → T' < Tstar → ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
        ∀ x ∈ riemannianBallOf ((Kh (σ i)).stageMetric
            ((Kh (σ i)).activeStage (t (σ i))) (t (σ i))) (y' (σ i))
            (A / Real.sqrt (R (σ i))),
        ∀ (w : Icc (0 : ℝ) (Kh (σ i)).horizon),
          (w : ℝ) = t (σ i) - T' / R (σ i) →
        ∀ (hwt : w ≤ t (σ i))
          (Bt : BackwardPointTrace (Kh (σ i)) ((Kh (σ i)).activeStage w)
            ((Kh (σ i)).activeStage (t (σ i)))
            ((Kh (σ i)).activeStage_mono hwt) x),
          metricScalarAt ((Kh (σ i)).stageMetric ((Kh (σ i)).activeStage w) w)
            (Bt.point ((Kh (σ i)).activeStage w) le_rfl
              ((Kh (σ i)).activeStage_mono hwt)) ≤
            M * R (σ i)) →
        DepthExtendable Kh t y' R σ (Tstar + 1 / (32 * ((Cst : ℝ) + 1) * (M + 1)))) →
      -- hkappaC（R4 帧闭合；driver / SB2 原文逐字）
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
        ∀ (pm : ∀ k, ((Kh k).stage (i k).castSucc).Carrier)
          (t : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y' : ∀ k, ((Kh k).stageAt (t k)).Carrier)
          (hat : ∀ k, aSeed k ≤ t k) (hts : ∀ k, t k ≤ σ k),
          (∀ k, HEq (y' k) (pm k)) →
          (∀ k, ∃ wp : ((Kh k).stage (i k).succ).Carrier, HEq (y k) wp ∧
            ((Kh k).event (i k)).RegularCrossing (pm k) wp) →
          (∀ k, (Kh k).time (i k).castSucc < (t k : ℝ) ∧ (t k : ℝ) < (Kh k).time (i k).succ) →
          (∀ k, (σ k : ℝ) - t k ≤ 1 / R k) →
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
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (t n) (y' n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (t n)) (t n)) (y' n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ t n), (t n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (t n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ (1 / 200) →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'') →
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
                (Kh k).isTracedRegion tt y' (r / Real.sqrt (R k)) (T / R k) (Kt * R k) := by
  obtain ⟨ε₁, hε₁, hG1⟩ := exists_R4_center_family_of_notTR_gate_HTP.{u}
  obtain ⟨ε₂, hε₂, hW⟩ := hwitC_hderivC_of_hPN_anyPos_le_P6DP4E2.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro P g F ε C1 C2 Ctime pF records hcanF hacc hord hrad hε hεX hεN hεcone hC20 q hanti hδq
    recQ hrecent hfine hTD hsupA hsepWK Cst κ hκ hsurvive hextend hkappaC Aseed hA T r
    hT hr
  -- recent 阈值（η_k = 1/(2(k+1))）、late recenter、HI、FRESH
  choose Trec hTrec0 hTrec using fun k : ℕ =>
    hrecent (1 / (2 * ((k : ℝ) + 1))) (by positivity)
  obtain ⟨Tδ, hTδ0, hTδ⟩ := exists_late_recenter_CXW hδq
  obtain ⟨phi, hphi, hpinK, -⟩ := hpinch_core_of_HIProp_P6HP2 F
    (fun n => by
      obtain ⟨a, ha, h⟩ := exists_initialHI_P6WR F
      exact ⟨a, ha, fun x => h n x⟩)
    (fun n => ⟨pF, ⟨records n⟩⟩)
  obtain ⟨κA, hκA, Tf, hsupK⟩ := hsupA Aseed hA
  -- hbcadC producer（R4BCAD G1）：Θb 并入 E2a′ 阈值序列
  obtain ⟨Θb, hΘb⟩ := hbcadC_R4center_R4B F hεcone hC20 q hanti hδq recQ hrecent hfine hTD hsupA
  by_contra hcon
  refine hG1 (ε := ε) (C1 := C1) (C2 := C2) (Ctime := Ctime) F records hcanF
    (hacc.trans (min_le_left _ _)) hord hrad q Aseed
    (fun k => max (max (Trec k) (2 * Tδ)) (Θb k)) hsepWK T r
    hT hr (fun m hm => hcon ⟨(m : ℝ), Nat.cast_nonneg m, hm⟩) ?_
  intro ind c hc Kh Tn pT hTc aSeed haT hclock hone hsm hvol hTn2 hnrS seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii hgateP hceil i hi pm t y' hat hts hy' hcross
    hslab hclose hcompR hcmp hcmpL hgood' hbadTR hΘ h2R
  have hhsurvive := hsurvive ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi pm t y' hat hts hy' hcross hslab hclose
    hcmp hcmpL hgood'
  have hhextend := hextend ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi pm t y' hat hts hy' hcross hslab hclose
    hcmp hcmpL hgood'
  have hhkappaC := hkappaC ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi pm t y' hat hts hy' hcross hslab hclose
    hcmp hcmpL hgood'
  have hhbcadC := hΘb Aseed hA ind c hc Tn pT hTc aSeed haT hclock hone hsm hvol hTn2 hnrS
    (fun k => (le_max_right _ _).trans (hΘ k)) seedTrace σ y R hsT has L hRpos hRr hL haS hroom
    hradii hgateP hceil t y' hat hts hclose hcompR hgood'
  have hsepWK' := hsepWK ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii hceil i hi
  let K : ℕ → RetainedCoreHistory.{u} := fun n =>
    (F.tower.history (ind n)).rescale_P6N (c n) (hc n)
  have hRlim : Tendsto R atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith [hRr n]) tendsto_natCast_atTop_atTop
  -- hanchor0 ⇐ SLICE-BCBD2 G5 (C = 2), kernel frame (K, i, t, pm)
  have hact : ∀ n, (Kh n).activeStage (t n) = (i n).castSucc := fun n =>
    RetainedCoreHistory.activeStage_eq_castSucc_of_mem_P6FF (H := K n) (i n) (t n) (hslab n)
  have hRc : ∀ n, 0 < ((Kh n).event (i n)).incoming.flow.scalar (t n) (pm n) := fun n => by
    have h := (K n).scalar_of_incoming_P6X (i n) (hact n).symm (t n) (pm n) (y' n) (hy' n)
    rw [← h]
    linarith [hcmpL n, hRpos n]
  have hhK := hK_R4center_of_env_HCT F records hεcone hC20 q hanti recQ hfine hTD hTrec hTδ hpinK
    hphi hA hκA hsupK ind c hc Tn pT hTc aSeed haT hclock hone hsm hvol hTn2 hnrS seedTrace σ y
    R hsT has L hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii hgateP hceil i hi pm t y' hat
    hts hy' hcross hslab hclose hcompR hcmp hcmpL hgood'
    (fun k => (le_max_left _ _).trans (hΘ k)) h2R
  have hanchor0 := ObservedHistory.hanchor0_driver_of_kernel_comparable_P6SB2 Kh (K := K) rfl t y'
    (j := i) (yG := pm) (fun n => (hslab n).1) (fun n => (hslab n).2) hy'
    (fun n => ((Kh n).event (i n)).incoming.flow.scalar (t n) (pm n)) hRc (fun _ => rfl) R hRpos
    two_pos (Filter.Eventually.of_forall fun n => (hcmp n).le) hhK
  -- window / half-depth / seed-clock data at the R4 center (r := 1)
  have hwin' : ∀ T' : ℝ, 0 < T' → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ t n - T' / R n := by
    intro T' hT'
    filter_upwards [haS (T' + 1) (by linarith)] with n hn
    have h1 := hclose n
    have h2 : (T' + 1) / R n = T' / R n + 1 / R n := add_div _ _ _
    linarith
  have hhalf : ∀ᶠ n in atTop, (Tn n : ℝ) - (1 : ℝ) ^ 2 / 2 ≤ (t n : ℝ) := by
    filter_upwards [haS 1 one_pos, hTnS 1 one_pos] with n _ hn
    linarith [hclose n]
  have htime : ∀ᶠ n in atTop, 2 * (1 : ℝ) ^ 2 ≤ (Tn n : ℝ) :=
    Filter.Eventually.of_forall fun n => by linarith [hclock n, hone n]
  have hL2 : Tendsto (fun n => L n - 2) atTop atTop :=
    (tendsto_atTop_add_const_right atTop (-2) hL).congr fun n => by ring
  have hRr1 : Tendsto (fun n => R n * (1 : ℝ) ^ 2) atTop atTop := by simpa using hRlim
  obtain ⟨hwC, hdC⟩ := hW (eps := ε) (C1' := C1) (C2' := C2) (Ctime' := Ctime) K t y' R
    (fun _ => 1) (fun n => L n - 2) Tn aSeed haT (fun n => (hts n).trans (hsT n)) hat pT seedTrace
    hhalf htime hRpos hL2 (Filter.Eventually.of_forall hsm) (Filter.Eventually.of_forall hclock)
    hRr1 (a₀ := 0) le_rfl (Filter.Eventually.of_forall fun n =>
      ObservedHistory.hpin_rescaled_of_records_P6HI F records ind c hc n)
    (fun n => pF.rescale_P6N (c n) (hc n)) (fun _ => 0)
    (fun n e _ => (records (ind n) e).rescale_P6M (c n) (hc n))
    (Filter.Eventually.of_forall fun n e _ b =>
      ((records (ind n) e).static b).hasCanonicalWindow_rescale_P6M (hcanF _ _ b) _ _)
    (Filter.Eventually.of_forall fun _ => hacc.trans (min_le_right _ _))
    (Filter.Eventually.of_forall fun _ => hord) (Filter.Eventually.of_forall fun _ => hrad)
    (fun T' hT' C hC => by
      filter_upwards [hsepWK' (T' + 1) (by linarith) C hC] with n hn e _ b he
      refine hn e b ?_
      have h1 := hclose n
      have h2 : (T' + 1) / R n = T' / R n + 1 / R n := add_div _ _ _
      linarith)
    (fun T' hT' => by
      filter_upwards [hwin' T' hT'] with n hn
      linarith [hone n])
    hgood' hwin'
  -- hseed ⇐ hsurvive（A = 2·1，小 T）+ hanchor0 + hkappaC（DRV-HI 法，R4 中心 (t, y′)）
  obtain ⟨Qa, hQa2, hQaev⟩ := hanchor0 (2 * 1) (by norm_num)
  have hCst0 : (0 : ℝ) ≤ (Cst : ℝ) := NNReal.coe_nonneg Cst
  have hden : 0 < 4 * (Cst : ℝ) * Qa + 1 := by
    have := mul_nonneg hCst0 (by linarith : (0 : ℝ) ≤ Qa)
    linarith
  have hT0pos : 0 < 1 / (4 * (Cst : ℝ) * Qa + 1) := by positivity
  have hT04 : 4 * (Cst : ℝ) * Qa * (1 / (4 * (Cst : ℝ) * Qa + 1)) ≤ 1 := by
    rw [mul_one_div, div_le_one hden]
    linarith
  obtain ⟨K1, hK1, hev1⟩ := hhsurvive (2 * 1) (1 / (4 * (Cst : ℝ) * Qa + 1)) Qa (by norm_num)
    hT0pos hQa2 hT04
  have hTR1 : ∀ᶠ n in atTop, (Kh n).isTracedRegion (t n) (y' n) (2 * 1 / Real.sqrt (R n))
      ((1 / (4 * (Cst : ℝ) * Qa + 1)) / R n) (K1 * R n) :=
    (hev1.and hQaev).mono fun n hn => hn.1 hn.2
  have hkap1 := hhkappaC id strictMono_id 1 (1 / (4 * (Cst : ℝ) * Qa + 1)) K1 one_pos hT0pos hK1
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
  have hctrl := hTR1.mono fun n hn => ObservedHistory.controlled_of_traced_DH (Kh n) (t n) (y' n)
    (hRpos n) hK1 hr₀pos hr₀1 hr₀T hr₀K hn
  have hhseed := ObservedHistory.hseed_of_tracedKappa_smallT_DH hRpos (fun _ : ℕ => (1 : ℝ) / 200)
    hradii hT0pos hkap1 hr₀pos hctrl
  -- hpinch ⇐ HI（同一 phi；v ∈ [t − T/R, t] ⊂ event slab ∩ Ici ½）
  have hhpinch : ∀ D T' : ℝ, 0 < D → 0 < T' → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (t n)) (t n)) (y' n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ t n), (t n : ℝ) - T' / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (t n))
        ((Kh n).activeStage_mono hvt) x,
        curvatureOperatorLowerBoundAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
          (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
          (metricAlgebraicCurvatureTensorAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
          (phi (metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))) := by
    intro D T' _ hT'
    filter_upwards [hwin' T' hT'] with n hn x _ v hvt hv tr
    have hvw : (1 / 2 : ℝ) ≤ v := by linarith [hone n]
    have hvj : (v : ℝ) < (K n).time (i n).succ := lt_of_le_of_lt hvt (hslab n).2
    exact ObservedHistory.curvatureLB_stage_of_eventPinched_HTP (K n) (hpinK ind c hc n) v hvw
      (i n) hvj _
  obtain ⟨σd, hσd, hDE⟩ := ObservedHistory.exists_subseq_forall_depthExtendable_kappaC_P6KA Kh t y'
    R hRpos hRlim hhsurvive hanchor0 hhextend hr₀pos hκ hhseed hκ (fun _ => 1 / 200) hradii hhkappaC
    hphi hhpinch hε hεX hεN (Cs := 4) (qs := fun n => 4 * R n) (fun _ => le_rfl) hwC (Cq := 4)
    (qcan := fun n => 4 * R n) (fun _ => le_rfl) hdC hhbcadC
  exact false_of_depthExtendable_of_bad_P6DP4E2 hσd hr hRpos (hDE T hT) hbadTR

/-- consumer。 -/
example : True := by
  have := hTR_of_driver_gate_R4B.{0}
  trivial

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

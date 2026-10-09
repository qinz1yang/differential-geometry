import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HP6bAssemblyV2P6HPB2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6BCDBootstrapBallP6BB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6Foot3DerivSlotP6F5
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilHnDefsCHN

set_option autoImplicit false

/-!
# CHN G2i：hderivL 槽（TRonly，HN ceiling）

CEIL-HN 孪生（O-CH11-CEILHN，后缀 `_CHN`）：自 `P6Foot3DerivSlotP6F5.lean` 机械克隆
（生成器 `build-logs/scratch/CEILHN/gen/clone.py`），ceiling 常数换 HN 扩展。
-/

noncomputable section
open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
open Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow (ClosedBirthConstants)
open GC.LongTime.Ch11 (p6CoarseC_C11GT6 p6FineEta_C11GT6 p6FineEta_pos_C11GT6 epsW_CXOU2)
open GC.LongTime.Ch11 (BlockTower_C11W capWindowRadius_C11E FineOf_C11G2 BudgetCertificate_C11GT2
  SameConstructionRetentionSupplyPlus_C11GT6 chainDiagonal_C11A C1P6_C11GT6 C2P6_C11GT6
  p6X1HN_CHN p6X2HN_CHN p6CtimeHN_CHN p6BadCHN_CHN htransMBadHN_CHN)
namespace ObservedHistory
open GC.LongTime.Ch11 (p6CoarseCHN_CHN one_le_p6CoarseCHN_CHN p6CoarseC_le_p6CoarseCHN_CHN)

/-- **G1 `hderivL_slot_of_TRonly_P6F5_CHN`**（PROVISIONAL[`hfamTslot`, `hTRslot`]；选择子约束 `hCg4`）：
结论 = HP6B2 v2 `hderivL` 槽逐字；= BCDBOOT `hderivL_of_hgood_firstExit_TRonly_P6BB` 在 HP6b env 上
实例化（`Cder := C_t*(Γ)`，阈值 `4 ≤ Cg`）。 -/
theorem hderivL_slot_of_TRonly_P6F5_CHN (P : OrientedThreeStage.{u}) (g : P.Metric)
    (εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ)
    (Cgsel : ClosedBirthConstants → ClosedBirthConstants → ℝ)
    (hCg4 : ∀ Γ Γf, 4 ≤ Cgsel Γ Γf)
    (hfamTslot :
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
      C1 = C1P6_C11GT6.{u} p6X1HN_CHN.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2HN_CHN.{u} Γ →
      Ctime = p6CtimeHN_CHN.{u} Γ →
      ∀ ε₀ : ℝ, 0 < ε₀ → ∃ qp : CutoffParameters,
        StandardCap.transitionEnd + 10 < qp.modelRadius ∧ qp.modelAccuracy ≤ ε₀ ∧
        2 ≤ qp.modelOrder ∧ Tendsto qp.delta atTop (𝓝 0) ∧
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
          (∀ k, riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) (y k) ≠ ⊤) ∧
          ∀ᶠ k in atTop, WindowNeckScaleBudget_P6HS (Kh k) (qp.rescale_P6N (c k) (hc k))
            (T₀ k) (aSeed k : ℝ) (R k)
      ))
    (hTRslot :
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
      C1 = C1P6_C11GT6.{u} p6X1HN_CHN.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2HN_CHN.{u} Γ →
      Ctime = p6CtimeHN_CHN.{u} Γ →
      ∃ Ktr : ℝ → ℝ → ℝ, (∀ r T, 0 ≤ Ktr r T) ∧
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
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            ∀ (tt : Icc (0 : ℝ) (Kh k).horizon), (tt : ℝ) = t →
            ∀ y' : ((Kh k).stageAt tt).Carrier, HEq y' p' →
              (Kh k).isTracedRegion tt y' (r / Real.sqrt (R k)) (T / R k) (Ktr r T * R k)
      )) :
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
      C1 = C1P6_C11GT6.{u} p6X1HN_CHN.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2HN_CHN.{u} Γ →
      Ctime = p6CtimeHN_CHN.{u} Γ →
      ∀ {Cg : ℝ}, Cg = Cgsel Γ Γf →
      ∃ Cder : ℝ≥0,
        ∀ (T r : ℝ), 0 < T → 0 < r →
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
          ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
            (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
            ((Kh k).event (i k)).RegularCrossing p' q →
            ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
              (∀ (first : Fin ((Kh k).eventCount + 1)) (hfl : first ≤ (i k).castSucc),
                ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                    (r / Real.sqrt (R k)),
                ∀ (B : BackwardPointTrace (Kh k) first (i k).castSucc hfl z)
                  (i' : Fin (Kh k).eventCount) (hf : first ≤ i'.castSucc)
                  (hij : i'.castSucc < (i k).castSucc),
                ∀ v' ∈ Ioo ((Kh k).time i'.castSucc) ((Kh k).time i'.succ), t - T / R k ≤ v' →
                  Cg * R k < ((Kh k).event i').incoming.flow.scalar v'
                    (B.point i'.castSucc hf hij.le) →
                  |derivWithin (fun w' => ((Kh k).event i').incoming.flow.scalar w'
                      (B.point i'.castSucc hf hij.le)) (Iic v') v'| ≤
                    Cder * ((Kh k).event i').incoming.flow.scalar v'
                      (B.point i'.castSucc hf hij.le) ^ 2) ∧
              ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                  (r / Real.sqrt (R k)),
                ∀ v' ∈ Ioo ((Kh k).time (i k).castSucc) t, t - T / R k ≤ v' →
                  Cg * R k < ((Kh k).event (i k)).incoming.flow.scalar v' z →
                  |derivWithin (fun w' => ((Kh k).event (i k)).incoming.flow.scalar w' z)
                      (Iic v') v'| ≤
                    Cder * ((Kh k).event (i k)).incoming.flow.scalar v' z ^ 2 := by
  obtain ⟨ε₀, hε₀, hTRo⟩ := hderivL_of_hgood_firstExit_TRonly_P6BB.{u}
  intro pB Γ Γf hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord ε C1 C2 Ctime
    hε hC1 hC2 hCt Cg hCg
  obtain ⟨qp, hqr, hqa, hqo, hqδ, hfam⟩ :=
    hfamTslot hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord hε hC1 hC2 hCt ε₀ hε₀
  obtain ⟨Ktr, hK, htr⟩ :=
    hTRslot hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord hε hC1 hC2 hCt
  have hC2n : 0 ≤ C2 := by
    rw [hC2]
    exact zero_le_one.trans (GC.LongTime.Ch11.one_le_C2P6_C11GT6.{u} p6X2HN_CHN.{u} Γ)
  have h4 : (4 : ℝ) ≤ Cg := hCg ▸ hCg4 Γ Γf
  refine ⟨Ctime, ?_⟩
  intro Tw r hTw hr ind c hc Kh Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef
    hRpos hRr hL hsel hgood hwin hwin' hroom hradii i hi
  have hmain := hTRo (F := F) (ε := ε) (C1 := C1) (C2 := C2) (Ctime := Ctime) (qp := qp)
    (Ktr := Ktr) hC2n hqr hqa hqo hqδ hK hfam htr Tw r hTw hr ind c hc Tn pT hTc aSeed haT hclock
    h1 hsm seedTrace σ y R hsT has L hRdef hRpos hRr hL hsel hgood hwin hwin' hroom hradii i hi
  filter_upwards [hmain] with k hk
  intro p' q' hq' hcr
  filter_upwards [hk p' q' hq' hcr] with t ht
  have hlt : ∀ x : ℝ, Cg * R k < x → 4 * R k < x := fun x hx =>
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right h4 (hRpos k).le) hx
  exact ⟨fun first hfl z hz B i' hf hij v' hv' hvt hx =>
      ht.1 first hfl z hz B i' hf hij v' hv' hvt (hlt _ hx),
    fun z hz v' hv' hvt hx => ht.2 z hz v' hv' hvt (hlt _ hx)⟩
end ObservedHistory
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

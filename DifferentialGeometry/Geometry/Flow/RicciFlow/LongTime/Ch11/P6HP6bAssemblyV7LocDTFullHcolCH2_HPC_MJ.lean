import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HP6bAssemblyV7LocDTFullCH2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HgwResHFRXCH2_MJ
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DistLargeWinGateHcolCH2_HPC
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ParamCompatTwoP6SS

/-!
[O-CH11-MJ G1：自 `P6HP6bAssemblyV7LocDTFullHcolCH2_HPC.lean` 复制；只动 hresJ / hresJ8 两槽]
# CH2_HPC 引擎的 J / J8 槽合流孪生（后缀 `_MJ`）

hresJ 核 `HgwResE6_V11` → `HgwResE8_CH2_MJ`（HI × HFT × J10 RX × DT）；hresJ8 核 `HgwResJ8H_V11_CH2` →
`HgwResJ8H8_CH2_MJ`（+ Cg8）。引擎内 T₀ 选取并入 `Tδ`（`q.delta s ≤ 1/(n+1)`，DRV-HI 法）；两桥
`hgwResE4_of_E8_CH2_MJ` / `hgwResJ8H_CH2_of_J8H8_CH2_MJ` 用同一 SCRS⁺ 元组
（records / hfineR / hderC / ha₀ / hHI / hT₀δ）。hresJF / hresJF8 / hinit / hrecT / hdistLA 槽与其余证明逐字。
无新 binder / Prop。生成器 `build-logs/scratch/O-CH11-MJ/gen/gen_eng_g1.py`。
-/

/-!
[CEILHN2：自 `P6HP6bAssemblyV7LocDTFullHcolCHN_HPC.lean` 机械克隆]
# HPCCAP：v11m CHN 装配引擎的 hcap + hcollar 透传孪生（后缀 `_HPC`）

`hP6bTwoLevelTimeCollar_of_slots_v7_loc_v11m_V11_CH2` 逐字，只改四处：
(1) `hresJ` / `hresJ8` 槽的核在 `∃ Θ … ∀ {ε …}` 内、核前加 `SurgeryParamCompat_P6PC q 2 →`
（原槽 ⇒ 孪生平凡：`fun _ => h`；孪生槽的义务 = 原核去掉第一合取 hpc）；
(2) 结论合同在 `LateLinkedRecordsSupply` 后加 tower 的 cap 条款 `hcap`
（与 `HP6bTwoLevelTimeCollarHcap_P6KT3H` 同一条款、同一位置形）；
(3) `hpc := paramCompat_q_of_requestCap_P6SS hq (hcap ⇒ cap·r ≤ rNext)`，用同一 `T`、同一 `q`
（SCRS⁺ 解包，`hq` 即其 chainDiagonal 对齐）；(4) 两处 hres 取用点喂 hpc，其余证明逐字。
hdistLA 槽在 `2 ≤ pB.modelOrder` 后加 hcollar 前提（env 中的 `hcol` 传入）；hresJF / hresJF8 / hinit / hrecT 槽不动。
-/

set_option autoImplicit false

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
  p6X1HN_CH2 p6X2HN_CH2 p6CtimeHN_CH2 p6BadCH2_CH2 htransMBadHN_CH2)
namespace ObservedHistory
open GC.LongTime.Ch11
open GC.LongTime.Ch11 (p6CoarseCH2_CH2 one_le_p6CoarseCH2_CH2 p6CoarseC_le_p6CoarseCH2_CH2)

/-- 引擎孪生（W10）：基底引擎删 `hstaySlot`（HSTAY G9/G10 full producer）。 -/
theorem hP6bTwoLevelTimeCollar_of_slots_v7_loc_v11m_hcap_hcol_V11_CH2_HPC_MJ
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ)
    (hεP6 : ∀ Γ Γf, 0 < εP6 Γ Γf)
    (Cgsel : ClosedBirthConstants → ClosedBirthConstants → ℝ)
    (hCg4 : ∀ Γ Γf, 4 ≤ Cgsel Γ Γf)
    (hresJ :
      ∀ (Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ) (m₀ : ℝ≥0 → ℕ → ℕ),
      (∀ (C : ℝ≥0) (n : ℕ), 0 < Cb C n ∧ Cb C n ≤ 1 / ((n : ℝ) + 1) ^ (2 : ℕ)) →
      (∀ (C : ℝ≥0) (n : ℕ), 0 < ζ C n ∧ ζ C n ≤ 1 / ((n : ℝ) + 1)) →
      (∀ (C : ℝ≥0) (n : ℕ), 0 < δ₀ C n ∧ δ₀ C n ≤ 1 / ((n : ℝ) + 1)) →
      (∀ (C : ℝ≥0) (n : ℕ), (n : ℝ) + 1 ≤ Rn C n) → (∀ (C : ℝ≥0) (n : ℕ), n + 2 ≤ m₀ C n) →
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
      ∀ {a₀ : ℝ}, 0 < a₀ →
      (∀ n x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x) →
      ∃ Θ : ℕ → ℝ,
      ∀ {ε C1 C2 : ℝ} {Ctime Ctime₀ : ℝ≥0} {T₀ : ℕ → ℝ}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ →
      Ctime = p6CtimeHN_CH2.{u} Γ → Ctime₀ = Γf.Ctime → (∀ n, Θ n ≤ T₀ n) →
      SurgeryParamCompat_P6PC q 2 →
      HgwResE8_CH2_MJ F q ε C1 C2 Ctime Ctime₀ T₀ (fun _ => (0 : ℝ)) Cb Rn ζ δ₀ m₀
        a₀)
    (hresJ8 :
      ∀ (Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ) (m₀ : ℝ≥0 → ℕ → ℕ),
      (∀ (C : ℝ≥0) (n : ℕ), 0 < Cb C n ∧ Cb C n ≤ 1 / ((n : ℝ) + 1) ^ (2 : ℕ)) →
      (∀ (C : ℝ≥0) (n : ℕ), 0 < ζ C n ∧ ζ C n ≤ 1 / ((n : ℝ) + 1)) →
      (∀ (C : ℝ≥0) (n : ℕ), 0 < δ₀ C n ∧ δ₀ C n ≤ 1 / ((n : ℝ) + 1)) →
      (∀ (C : ℝ≥0) (n : ℕ), (n : ℝ) + 1 ≤ Rn C n) → (∀ (C : ℝ≥0) (n : ℕ), n + 2 ≤ m₀ C n) →
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
      ∀ {a₀ : ℝ}, 0 < a₀ →
      (∀ n x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x) →
      ∃ Θ : ℕ → ℝ,
      ∀ {ε C1 C2 : ℝ} {Ctime Ctime₀ : ℝ≥0} {T₀ : ℕ → ℝ}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ →
      Ctime = p6CtimeHN_CH2.{u} Γ → Ctime₀ = Γf.Ctime → (∀ n, Θ n ≤ T₀ n) →
      SurgeryParamCompat_P6PC q 2 →
      HgwResJ8H8_CH2_MJ F q ε C1 C2 Ctime Ctime₀ T₀ (fun _ => (0 : ℝ)) Cb Rn ζ δ₀
        m₀ a₀)
    (hresJF :
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
      ∀ {a₀ : ℝ}, 0 < a₀ →
      (∀ n x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x) →
      ∃ Θ : ℕ → ℝ,
      ∀ {ε C1 C2 : ℝ} {Ctime Ctime₀ : ℝ≥0} {T₀ : ℕ → ℝ}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ →
      Ctime = p6CtimeHN_CH2.{u} Γ → Ctime₀ = Γf.Ctime → (∀ n, Θ n ≤ T₀ n) →
      HgwResJFD_V11 F q ε C1 C2 Ctime T₀ (fun _ => (0 : ℝ)) a₀)
    (hresJF8 :
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
      ∀ {a₀ : ℝ}, 0 < a₀ →
      (∀ n x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x) →
      ∃ Θ : ℕ → ℝ,
      ∀ {ε C1 C2 : ℝ} {Ctime Ctime₀ : ℝ≥0} {T₀ : ℕ → ℝ}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ →
      Ctime = p6CtimeHN_CH2.{u} Γ → Ctime₀ = Γf.Ctime → (∀ n, Θ n ≤ T₀ n) →
      HgwResJF8D_V11_CH2 F q ε C1 C2 Ctime T₀ (fun _ => (0 : ℝ)) a₀)
    (hinit :
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
      ∀ n, ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ x,
        InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
          -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x)
    (hrecT :
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
      ∀ n, ∃ pF : CutoffParameters,
        Nonempty (∀ i, GeometricCutoffRecord (F.tower.history n).toHistory i pF))
    (hdistLA :
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
      GC.LongTime.Ch11.collarAdmitsAllOrders_C11E.{u} pB.fixed.collarLength pB.fixed.collar_pos →
      ∀ {ε C1 C2 : ℝ} {Ctime : ℝ≥0}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ →
      Ctime = p6CtimeHN_CH2.{u} Γ →
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
                    ((seedTrace k).point (i k).castSucc h1 h2) z + ENNReal.ofReal 1) :
  ∃ εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ,
    (∀ Γ Γf, 0 < εP6 Γ Γf) ∧
    ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
    Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} → ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
      (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
    (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j (T.block j) (T.lookahead j)
      (T.request j)) →
    SameConstructionRetentionSupplyPlus_C11GT6 T →
    ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
    (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
    GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q →
    (∀ j : ℕ, (T.request j).accuracyCap * (T.block j).radius * ((3 : ℝ) ^ j + 1) ≤
        (T.lookahead j).rNext) →
    pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
    2 ≤ pB.modelOrder → collarAdmitsAllOrders_C11E.{u} pB.fixed.collarLength pB.fixed.collar_pos →
    CanonicalLateTimeCore_P6X F Γ.epsilon (C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ)
      (C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ) (p6CtimeHN_CH2.{u} Γ) := by
  have hmargin := @hmargin_slot_P6F5_CH2 P g εP6
  have hrecords := @hrecords_slot_P6NC_CH2 P g εP6
  have hderivL := @hderivLStar_slot_full_P6HS_CH2 P g εP6 Cgsel hCg4
  have hgradL := @hgradLStar_slot_full_P6HS_CH2 P g εP6 Cgsel hCg4
  have hscaleSep := @hscaleSep_slot_of_actualLate_S14CXW_CH2 P g εP6
  obtain ⟨_c₀w, -, Cbw, Rnw, ζw, δ₀w, m₀w, hCbw, hζw, hδ₀w, hRnw, hm₀w, hWr⟩ :=
    outerTwoLevelTime_KC_CH2.{u}
  obtain ⟨_c₀r, -, Cbr, Rnr, ζr, δ₀r, m₀r, hCbr, hζr, hδ₀r, hRnr, hm₀r, -, hB⟩ :=
    hrestP_of_jointPrefix_bad_coarse_gate_KC_KFP_HCT_CH2.{u}
  refine ⟨fun Γ Γf => min (εP6 Γ Γf) (min GC.LongTime.Ch11.εProf_C11E.{u}
        (GC.LongTime.Ch11.epsilon0_C11FR Γf.epsilon (GC.LongTime.Ch11.chainC1_C11KD Γf)
          (GC.LongTime.Ch11.chainC2_C11KD Γf) P)),
    fun Γ Γf => lt_min (hεP6 Γ Γf) (lt_min GC.LongTime.Ch11.εProf_pos_C11E.{u}
      (GC.LongTime.Ch11.epsilon0_pos_C11FR.{u} _ _ _ _)), ?_⟩
  intro pB Γ Γf hfine hs hW Cdist εReserve T hcert hS F _q hF _hq _hLate hcap hacc₂ hrad hord hcol
  have hacc' : pB.modelAccuracy ≤ min (εP6 Γ Γf) (min GC.LongTime.Ch11.εProf_C11E.{u}
      (GC.LongTime.Ch11.epsilon0_C11FR Γf.epsilon (GC.LongTime.Ch11.chainC1_C11KD Γf)
        (GC.LongTime.Ch11.chainC2_C11KD Γf) P)) := hacc₂
  have hacc : pB.modelAccuracy ≤ εP6 Γ Γf := hacc'.trans (min_le_left _ _)
  obtain ⟨-, hε11, -, hεX, hεN, hεc⟩ := GC.LongTime.Ch11.joint_gates_of_closedBirth_CXOU2.{u} hs hW
  obtain ⟨F₀, q, -, records, ⟨hF₀, hq, -⟩, -, -, ⟨-, -, hδ₀⟩, ⟨-, hrcs, -, hP5L₀⟩, -, hTD, -, -,
    hnom⟩ := id hS
  have hFF : F = F₀ := GC.LongTime.Ch11.rawSurgery_eq_of_tower_eq_C11KW (hF.trans hF₀.symm)
  subst F₀
  have hLate := hP5L₀
  have hOS := GC.LongTime.Ch11.outerSupply_twoLevel_C11G2 hS hfine F q hF hq
    (le_refl (GC.GeneralFlow.C1ceil_C11SC.{u} Γ)) (le_refl (GC.GeneralFlow.C2ceil_C11SC.{u} Γ))
    (le_refl Γ.Ctime)
  have hcan₁ := GC.LongTime.Ch11.historyCanonicalSupply_mono_all_C11G2
    (GC.LongTime.Ch11.hcan1_of_scrsPlus_fine_C11G2 hS hfine F q hF hq) le_rfl
    (GC.LongTime.Ch11.p6FineEta_lt_eleventh_C11G2 Γ)
    (GC.LongTime.Ch11.p6BadC_le_p6BadCH2_CH2.{u} Γ)
    (GC.LongTime.Ch11.p6BadC_le_p6BadCH2_CH2.{u} Γ)
  obtain ⟨hcb, hL1, hL2, -⟩ := hrestP_bad_numerics_CH2.{u} Γ
    (C1 := C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ) (C2 := C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ)
    (Ctime := p6CtimeHN_CH2.{u} Γ) le_rfl le_rfl le_rfl
  have hdom := GC.LongTime.Ch11.hdomL_badHN_CH2.{u} Γ
  have hc1 := GC.LongTime.Ch11.one_le_p6BadCH2_CH2.{u} Γ
  have hC1f : 1 ≤ max (p6BadCH2_CH2.{u} Γ) 9 + Real.sqrt (p6BadCH2_CH2.{u} Γ) :=
    le_add_of_le_of_nonneg (le_trans (by norm_num) (le_max_right _ _)) (Real.sqrt_nonneg _)
  have hC2f : 1 ≤ 1200 * p6BadCH2_CH2.{u} Γ := by linarith
  have hm1 : htransMBadHN_CH2.{u} Γ ≤ 1 / 2 := (min_le_left _ _).trans (by norm_num)
  have hE := htransE_of_P5L_P6HD (F := F) (qc := q) (ε := Γ.epsilon)
    (C1 := C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ) (C2 := C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ)
    (Ctime := p6CtimeHN_CH2.{u} Γ)
    (C1f := max (p6BadCH2_CH2.{u} Γ) 9 + Real.sqrt (p6BadCH2_CH2.{u} Γ))
    (C2f := 1200 * p6BadCH2_CH2.{u} Γ) (m := htransMBadHN_CH2.{u} Γ)
    (η₁ := p6FineEta_C11GT6 Γ.epsilon) (C1₁ := p6BadCH2_CH2.{u} Γ) (C2₁ := p6BadCH2_CH2.{u} Γ)
    (kk := max 2 ⌈Γ.epsilon⁻¹⌉₊) hP5L₀ hδ₀ Γ.epsilon_pos (p6FineEta_pos_C11GT6 Γ.epsilon_pos)
    (GC.LongTime.Ch11.thirteenK_mul_fineEta_le_C11CL3 Γ.epsilon)
    (GC.LongTime.Ch11.fineEta_le_bJS_C11CL3 Γ.epsilon)
    hc1 hc1 le_rfl le_rfl (min_le_left _ _) (min_le_right _ _) hdom.1 (by linarith [hdom.2])
  obtain ⟨a₀, ha₀, hHI⟩ := exists_initialHI_P6WR F
  have hP3 : CollarWindowSupply_C11E.{u} pB := ⟨hcol, hrad⟩
  have hprof : ModelConstraintsSupply_C11E pB εProf_C11E.{u} := by
    refine ⟨hacc'.trans ((min_le_right _ _).trans (min_le_left _ _)), hord, ?_⟩
    have hte := StandardCap.transitionEnd_pos
    have hrad' := hrad
    unfold capWindowRadius_C11E at hrad'
    linarith
  have hfresh := hfresh_of_certifiedTower_P6HA T hcert F hF q hq hP3 hprof
    (hacc'.trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨δ₀w', hδ₀w', hlew, hδCw⟩ := kernelDelta_shrink_all_V11 hCbw hδ₀w
  obtain ⟨δ₀r', hδ₀r', hler, hδCr⟩ := kernelDelta_shrink_all_V11 hCbr hδ₀r
  have hpc : SurgeryParamCompat_P6PC q 2 :=
    paramCompat_q_of_requestCap_P6SS hq (fun j => by
      have h0 := hcap j
      have hr := (T.block j).radius_pos
      have hc0 := (T.request j).accuracyCap
      have hcp : 0 < (T.request j).accuracyCap := (T.ready j).2.cap_pos
      nlinarith [pow_pos (show (0 : ℝ) < 3 by norm_num) j, mul_pos hcp hr])
  obtain ⟨Θw, hΘw0⟩ := hresJ Cbw Rnw ζw δ₀w' m₀w hCbw hζw hδ₀w' hRnw hm₀w hfine hs hW Cdist
    εReserve T hcert hS F q hF hq hacc hrad hord ha₀ hHI
  obtain ⟨Θr, hΘr0⟩ := hresJ8 Cbr Rnr ζr δ₀r' m₀r hCbr hζr hδ₀r' hRnr hm₀r hfine hs hW Cdist
    εReserve T hcert hS F q hF hq hacc hrad hord ha₀ hHI
  have hΘw : ∀ {ε C1 C2 : ℝ} {Ctime Ctime₀ : ℝ≥0} {T₀ : ℕ → ℝ}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ → C2 = C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ →
      Ctime = p6CtimeHN_CH2.{u} Γ → Ctime₀ = Γf.Ctime → (∀ n, Θw n ≤ T₀ n) →
      HgwResE8_CH2_MJ F q ε C1 C2 Ctime Ctime₀ T₀ (fun _ => (0 : ℝ)) Cbw Rnw ζw δ₀w' m₀w a₀ :=
    fun h1 h2 h3 h4 h5 h6 => hΘw0 h1 h2 h3 h4 h5 h6 hpc
  have hΘr : ∀ {ε C1 C2 : ℝ} {Ctime Ctime₀ : ℝ≥0} {T₀ : ℕ → ℝ}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ → C2 = C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ →
      Ctime = p6CtimeHN_CH2.{u} Γ → Ctime₀ = Γf.Ctime → (∀ n, Θr n ≤ T₀ n) →
      HgwResJ8H8_CH2_MJ F q ε C1 C2 Ctime Ctime₀ T₀ (fun _ => (0 : ℝ)) Cbr Rnr ζr δ₀r' m₀r a₀ :=
    fun h1 h2 h3 h4 h5 h6 => hΘr0 h1 h2 h3 h4 h5 h6 hpc
  obtain ⟨ΘF, hΘF⟩ := hresJF hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord ha₀ hHI
  obtain ⟨ΘF8, hΘF8⟩ := hresJF8 hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord
    ha₀ hHI
  have hanti := hOS.1
  obtain ⟨Tδ, hTδ⟩ : ∃ Tδ : ℕ → ℝ, ∀ (n : ℕ) (s : ℝ), Tδ n ≤ s →
      q.delta s ≤ 1 / ((n : ℝ) + 1) := by
    have h : ∀ n : ℕ, ∃ T : ℝ, ∀ s, T ≤ s → q.delta s ≤ 1 / ((n : ℝ) + 1) := fun n =>
      Filter.eventually_atTop.mp (hδ₀.eventually (ge_mem_nhds (by positivity)))
    choose Tδ h using h
    exact ⟨Tδ, h⟩
  obtain ⟨T₀, hT₀m, hbw, hbr, hbF, hbF8, hbδ⟩ : ∃ T₀ : ℕ → ℝ, Monotone T₀ ∧
      (∀ n, max (Θw n) (max (lateThrJ8_P6WR2 (fun n => Cbw Γf.Ctime n)
        (fun n => Rnw Γf.Ctime n) (fun n => ζw Γf.Ctime n) (fun n => δ₀w' Γf.Ctime n)
        (fun n => m₀w Γf.Ctime n) a₀ records hnom hδ₀ hanti n)
        (max (lateLambdaThr_P6HA q hδ₀) (recentThr_P6HGW hrcs n))) ≤ T₀ n) ∧
      (∀ n, max (Θr n) (max (lateThrJ8_P6WR2 (fun n => Cbr Γf.Ctime n)
        (fun n => Rnr Γf.Ctime n) (fun n => ζr Γf.Ctime n) (fun n => δ₀r' Γf.Ctime n)
        (fun n => m₀r Γf.Ctime n) a₀ records hnom hδ₀ hanti n)
        (max (lateLambdaThr_P6HA q hδ₀) (recentThr_P6HGW hrcs n))) ≤ T₀ n) ∧
      (∀ n, max (ΘF n) (lateThrJF_P6WR2 a₀ records hnom hδ₀ hanti n) ≤ T₀ n) ∧
      (∀ n, max (ΘF8 n) (lateThrJF_P6WR2 a₀ records hnom hδ₀ hanti n) ≤ T₀ n) ∧
      ∀ n, Tδ n ≤ T₀ n := by
    have key := common_T₀_W9S
      (fun n => max (Θw n) (max (lateThrJ8_P6WR2 (fun n => Cbw Γf.Ctime n)
        (fun n => Rnw Γf.Ctime n) (fun n => ζw Γf.Ctime n) (fun n => δ₀w' Γf.Ctime n)
        (fun n => m₀w Γf.Ctime n) a₀ records hnom hδ₀ hanti n)
        (max (lateLambdaThr_P6HA q hδ₀) (recentThr_P6HGW hrcs n))))
      (fun n => max (Θr n) (max (lateThrJ8_P6WR2 (fun n => Cbr Γf.Ctime n)
        (fun n => Rnr Γf.Ctime n) (fun n => ζr Γf.Ctime n) (fun n => δ₀r' Γf.Ctime n)
        (fun n => m₀r Γf.Ctime n) a₀ records hnom hδ₀ hanti n)
        (max (lateLambdaThr_P6HA q hδ₀) (recentThr_P6HGW hrcs n))))
      (fun n => max (ΘF n) (lateThrJF_P6WR2 a₀ records hnom hδ₀ hanti n))
      (fun n => max (max (ΘF8 n) (lateThrJF_P6WR2 a₀ records hnom hδ₀ hanti n)) (Tδ n))
    exact ⟨_, key.1, key.2.1, key.2.2.1, key.2.2.2.1,
      fun n => (le_max_left _ _).trans (key.2.2.2.2 n),
      fun n => (le_max_right _ _).trans (key.2.2.2.2 n)⟩
  have hT₀δ : ∀ (n : ℕ) (s : ℝ), T₀ n ≤ s → q.delta s ≤ 1 / ((n : ℝ) + 1) :=
    fun n s hs => hTδ n s ((hbδ n).trans hs)
  have hbwΘ : ∀ n, Θw n ≤ T₀ n := fun n => (le_max_left _ _).trans (hbw n)
  have hbwThr : ∀ n, lateThrJ8_P6WR2 (fun n => Cbw Γf.Ctime n) (fun n => Rnw Γf.Ctime n)
      (fun n => ζw Γf.Ctime n) (fun n => δ₀w' Γf.Ctime n) (fun n => m₀w Γf.Ctime n) a₀ records
      hnom hδ₀ hanti n ≤ T₀ n :=
    fun n => (le_max_left _ _).trans ((le_max_right _ _).trans (hbw n))
  have hbwLam : ∀ n, lateLambdaThr_P6HA q hδ₀ ≤ T₀ n :=
    fun n => (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (hbw n)))
  have hbwRec : ∀ n, recentThr_P6HGW hrcs n ≤ T₀ n :=
    fun n => (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (hbw n)))
  have hCtt : Γf.Ctime ≤ p6CtimeHN_CH2.{u} Γ :=
    (GC.LongTime.Ch11.ctime_le_p6Ctime_of_fine_V11 hfine).trans
      (GC.LongTime.Ch11.p6Ctime_le_p6CtimeHN_CH2.{u} Γ)
  have hC2pos : (0 : ℝ) ≤ C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ := by
    have h1 := GC.LongTime.Ch11.one_le_p6BadCH2_CH2.{u} Γ
    have h2 : 1200000 * p6BadCH2_CH2.{u} Γ ≤ p6X2HN_CH2.{u} Γ :=
      (le_max_left _ _).trans (le_max_right _ _)
    have h3 := GC.LongTime.Ch11.X_le_C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ
    linarith
  have hfineR :
      ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T₀ : ℝ, ∀ n, ∃ p : CutoffParameters,
        D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
        ∃ records' : ∀ i : Fin (F.tower.history n).eventCount,
            T₀ ≤ (F.tower.history n).time i.succ →
            GeometricCutoffRecord (F.tower.history n).toHistory i p,
          (∀ i hi b, ((records' i hi).static b).hasCanonicalWindow) ∧
          ∀ i hi b, ((records' i hi).static b).neck.scale = ((records n i).static b).neck.scale
      := by
    intro D ζ m hζ
    obtain ⟨T₀', hT⟩ := hnom D ζ m hζ
    refine ⟨T₀', fun n => ?_⟩
    obtain ⟨p, -, -, -, -, hD, hζ', hm, rec', hlink, hrel⟩ := hT n
    exact ⟨p, hD, hζ', hm, rec', fun i hi b =>
      GC.LongTime.Ch11.linkedCanonicalWindow_hasCanonicalWindow_C11E _ (hlink i hi b),
      fun i hi b => (hrel i hi).2.2.2.2.1 b⟩
  have hderC := GC.LongTime.Ch11.timeDerivativeSupply_congr_mono_CXOU hTD (fun _ _ => rfl) hCtt
  have hΘw4 := fun {T₀' : ℕ → ℝ} (h : ∀ n, Θw n ≤ T₀' n)
      (hδ' : ∀ (n : ℕ) (s : ℝ), T₀' n ≤ s → q.delta s ≤ 1 / ((n : ℝ) + 1)) =>
    hgwResE4_of_E8_CH2_MJ Γ.epsilon_pos hεX hεN hεc hC2pos hanti hderC hfresh records hfineR ha₀ hHI
      hδ' (hΘw rfl rfl rfl rfl rfl h)
  have hΘr4 := fun {T₀' : ℕ → ℝ} (h : ∀ n, Θr n ≤ T₀' n)
      (hδ' : ∀ (n : ℕ) (s : ℝ), T₀' n ≤ s → q.delta s ≤ 1 / ((n : ℝ) + 1)) =>
    hgwResJ8H_CH2_of_J8H8_CH2_MJ Γ.epsilon_pos hεX hεN hεc hC2pos hanti hderC hfresh records
      hfineR ha₀ hHI hδ' (hΘr rfl rfl rfl rfl rfl h)
  have sJ := hgapJ_loc_of_producers_q0kTD_fresh_Q_V11 Cbw Rnw ζw δ₀w' m₀w hCbw
    (fun C n => (hζw C n).1) (fun C n => (hδ₀w' C n).1) hanti hδ₀ records hnom hrcs hTD ha₀ hHI
    hbwThr
    (hΘw4 hbwΘ hT₀δ).1
    hδCw
    hbwLam
    (hJ11_loc_of_drv_J11S (T₀ := T₀) (Qt := fun _ => (0 : ℝ)) (a₀ := a₀) Cbw Rnw ζw δ₀w' m₀w hanti
      hfresh hC2pos records (hΘw4 hbwΘ hT₀δ).2.1) hfresh
    (by
      intro A hA ind Ho Tno pTo r hr h1 h2 h3 h4 c hc K Kh Tn pT aSeed haT h5 h6 h7 hT0k
        seedTrace σ y R hsT has L hRdef hRpos hR1 hQtk a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
      refine ⟨?_, (hΘw4 hbwΘ hT₀δ).2.2 A hA ind Tno pTo r hr h1 h2 h3 h4
        aSeed haT h5 h6 h7 hT0k seedTrace σ y R hsT has L hRdef hRpos hR1 hQtk
        a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13⟩
      intro p recordsK hcan hδW hacc' hrad' hord' hJ7b hJ8 hwit n i hi b
      have hTno : ∀ k, (Tno k : ℝ) = c k * (Tn k : ℝ) := fun k => by
        have : (Tn k : ℝ) = (Tno k : ℝ) / c k := rfl
        rw [this]; field_simp [(hc k).ne']
      exact j6_of_recent_seq_P6HGW records hrcs hanti hδ₀ ind (T₀ := T₀) (c := c)
        (σ := fun k => (σ k : ℝ)) (L := L) (R := R) (Tn := fun k => (Tn k : ℝ))
        (Tno := fun k => (Tno k : ℝ)) hbwRec (fun k => hbwLam k)
        (fun k => by
          have h5k := h5 k
          have := hT0k k
          have hk := hc k
          have hT := hTno k
          nlinarith)
        hc hTno (fun k => (Tno k).2.1) (fun k => h2 k) a9 hR1
        (fun k => by
          have := sel_orig_of_rescale_P6KT2c q (hc k) (Tno := (Tno k : ℝ)) (a8 k)
          rw [div_eq_mul_inv] at this
          exact this)
        recordsK hwit n i hi b)
  have hbrΘ : ∀ n, Θr n ≤ T₀ n := fun n => (le_max_left _ _).trans (hbr n)
  have hbrThr : ∀ n, lateThrJ8_P6WR2 (fun n => Cbr Γf.Ctime n) (fun n => Rnr Γf.Ctime n)
      (fun n => ζr Γf.Ctime n) (fun n => δ₀r' Γf.Ctime n) (fun n => m₀r Γf.Ctime n) a₀ records
      hnom hδ₀ hanti n ≤ T₀ n :=
    fun n => (le_max_left _ _).trans ((le_max_right _ _).trans (hbr n))
  have hbrLam : ∀ n, lateLambdaThr_P6HA q hδ₀ ≤ T₀ n :=
    fun n => (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (hbr n)))
  have hbrRec : ∀ n, recentThr_P6HGW hrcs n ≤ T₀ n :=
    fun n => (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (hbr n)))
  have sJ8 := hgapJ8_loc_of_producers_q0kTD_fresh_Q_V11_CH2 Cbr Rnr ζr δ₀r' m₀r hCbr
    (fun C n => (hζr C n).1) (fun C n => (hδ₀r' C n).1) hanti hδ₀ records hnom hrcs hTD ha₀ hHI
    hbrThr
    (hΘr4 hbrΘ hT₀δ).1
    hδCr
    hbrLam
    (hJ11_8_loc_of_drv_J11S_CH2 (T₀ := T₀) (Qt := fun _ => (0 : ℝ)) (a₀ := a₀) Cbr Rnr ζr δ₀r' m₀r
      hanti
      hfresh hC2pos records (hΘr4 hbrΘ hT₀δ).2.1) hfresh
    (by
      intro A hA ind Ho Tno pTo r hr h1 h2 h3 h4 c hc K Kh Tn pT aSeed haT h5 h6 h7 hT0k
        seedTrace σ y R hsT has L hRdef hRpos hR1 hQtk a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
      refine ⟨?_, (hΘr4 hbrΘ hT₀δ).2.2 A hA ind Tno pTo r hr h1 h2 h3 h4
        aSeed haT h5 h6 h7 hT0k seedTrace σ y R hsT has L hRdef hRpos hR1 hQtk
        a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13⟩
      intro p recordsK hcan hδW hacc' hrad' hord' hJ7b hJ8 hwit n i hi b
      have hTno : ∀ k, (Tno k : ℝ) = c k * (Tn k : ℝ) := fun k => by
        have : (Tn k : ℝ) = (Tno k : ℝ) / c k := rfl
        rw [this]; field_simp [(hc k).ne']
      exact j6_of_recent_seq_P6HGW records hrcs hanti hδ₀ ind (T₀ := T₀) (c := c)
        (σ := fun k => (σ k : ℝ)) (L := L) (R := R) (Tn := fun k => (Tn k : ℝ))
        (Tno := fun k => (Tno k : ℝ)) hbrRec (fun k => hbrLam k)
        (fun k => by
          have h5k := h5 k
          have := hT0k k
          have hk := hc k
          have hT := hTno k
          nlinarith)
        hc hTno (fun k => (Tno k).2.1) (fun k => h2 k) a9 hR1
        (fun k => by
          have := sel_orig_of_rescale_P6KT2c q (hc k) (Tno := (Tno k : ℝ)) (a8 k)
          rw [div_eq_mul_inv] at this
          exact this)
        recordsK hwit n i hi b)
  have sF := hgapJF_locCR_of_producers_J16_V11 hanti hδ₀ records hnom hTD hCtt ha₀ hHI
    (fun n => (le_max_right _ _).trans (hbF n))
    (hJ11F_loc_of_depthExt_J11S (T₀ := T₀) (Qt := fun _ => (0 : ℝ)) (a₀ := a₀) hanti hfresh hC2pos
      records (hΘF rfl rfl rfl rfl rfl (fun n => (le_max_left _ _).trans (hbF n))).1)
    (hJ15F_loc_of_fresh_P6HA hanti hfresh)
    (hΘF rfl rfl rfl rfl rfl (fun n => (le_max_left _ _).trans (hbF n))).2
  have sF8 := hgapJF8_locCR_of_producers_J16_V11_CH2 hanti hδ₀ records hnom hTD hCtt ha₀ hHI
    (fun n => (le_max_right _ _).trans (hbF8 n))
    (hJ11F8_loc_of_depthExt_J11S_CH2 (T₀ := T₀) (Qt := fun _ => (0 : ℝ)) (a₀ := a₀) hanti hfresh
      hC2pos
      records (hΘF8 rfl rfl rfl rfl rfl (fun n => (le_max_left _ _).trans (hbF8 n))).1)
    (hJ15F8_loc_of_fresh_P6HA_CH2 hanti hfresh)
    (hΘF8 rfl rfl rfl rfl rfl (fun n => (le_max_left _ _).trans (hbF8 n))).2
  have hder := hderivL hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord rfl
      rfl rfl rfl rfl
  obtain ⟨Cgrad, hgrad⟩ := hgradL hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord
      rfl rfl rfl rfl rfl
  have hfoot := hfootE_of_fresh_hP6bEnv_HIProp_guarded_HCT (P := P) (g := g) (F := F)
    (ε := Γ.epsilon)
    (C1 := C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ) (C2 := C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ)
    (Ctime := p6CtimeHN_CH2.{u} Γ) (q := q)
    (C1f := max (p6BadCH2_CH2.{u} Γ) 9 + Real.sqrt (p6BadCH2_CH2.{u} Γ))
    (C2f := 1200 * p6BadCH2_CH2.{u} Γ) (m := htransMBadHN_CH2.{u} Γ) (kk := max 2 ⌈Γ.epsilon⁻¹⌉₊)
    (Cg := Cgsel Γ Γf) (Cder := p6CtimeHN_CH2.{u} Γ) (Cgrad := Cgrad) hεc
    (hinit hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord)
    (hrecT hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord)
    (hmargin hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord rfl rfl rfl rfl)
    (hrecords hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord rfl rfl rfl rfl)
    hder hgrad (min_le_right _ _) hcol
    T hcert hF hq hacc' hrad hord
    (hdistLA hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord hcol rfl rfl rfl rfl)
    (hscaleSep hfine hs hW Cdist εReserve T hcert hS F q hF hq hLate hacc hrad hord rfl rfl rfl rfl)
    Γ.epsilon_pos hε11 hC1f hC2f (GC.LongTime.Ch11.htransMBadHN_pos_CH2.{u} Γ) hm1 le_rfl
  have hrest := (hB Γ.epsilon Γ.epsilon_pos hε11 hW hW hεX hεN hεc).2
    (C1 := C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ) (C2 := C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ)
    (Ctime := p6CtimeHN_CH2.{u} Γ)
    (GC.LongTime.Ch11.coarse_le_C1P6HN_CH2.{u} Γ)
    (GC.LongTime.Ch11.coarse_le_C2P6HN_CH2.{u} Γ)
    (GC.LongTime.Ch11.coarseTime_le_p6CtimeHN_CH2.{u} Γ)
    (P := P) (g := g) (F := F) (q := q)
    (C1f := max (p6BadCH2_CH2.{u} Γ) 9 + Real.sqrt (p6BadCH2_CH2.{u} Γ))
    (C2f := 1200 * p6BadCH2_CH2.{u} Γ) (m := htransMBadHN_CH2.{u} Γ) (kk := max 2 ⌈Γ.epsilon⁻¹⌉₊)
    Γf.Ctime T₀ (fun _ => (0 : ℝ)) (cb := p6BadCH2_CH2.{u} Γ) hcb hL1 hL2
    hOS.1 hT₀m monotone_const hCtt
    (hgapJ8Q_loc_mono_V11_CH2 hler sJ8)
    sF
    sF8
    (hcapWL_std_of_P5L_P6HPB_CH2 Γ hP5L₀)
    (hcenE_bad_P6HC_CH2 P g (max 2 ⌈Γ.epsilon⁻¹⌉₊) εP6 hfine hs hW Cdist εReserve T hcert hS F q hF
      hq
        hacc hrad hord
      rfl rfl rfl rfl rfl rfl rfl)
    hfoot hE hcan₁ (GC.LongTime.Ch11.hdomF_twoLevel_CH2.{u} Γ).2.2
  exact hWr Γ.epsilon T hS hfine rfl hs hW (F := F) (q := q) hF hq
    (Ctime := p6CtimeHN_CH2.{u} Γ) rfl rfl
    (GC.LongTime.Ch11.p6CtimeHN_bounds_CH2.{u} Γ).1
    (GC.LongTime.Ch11.p6CtimeHN_bounds_CH2.{u} Γ).2
    Γf.Ctime T₀ (fun _ => (0 : ℝ)) hT₀m monotone_const hCtt
    (hgapJQ_loc_mono_V11 hlew sJ)
    hrest

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DistLADriverBridgeGateHCTD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6A12SlotsV10S14Hgw5P6HGW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DistLargeWinDLW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DistLADriverBridgeDLW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilHnDefsCH2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6A12TopV8FnActualCH2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HP6bAssemblyV7LocDTFullCH2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DistLargeWinGateHCTDCH2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DistLADriverBridgeGateHCTDCH2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeHSpineRecentCH2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HgwResJ11CH2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HgwResD0CH2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HinitRecTSlotP6HI
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HgwResDTV11
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HP6bAssemblyV7LocFinASM
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DistLADriverBridgeGateTJ
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DistLargeWinGateMTR
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6A12TopV8FnActualHcap_C2_HPC

/-!
# O-CH11-ASM：A12′ 终形顶层 `a12EnhancedFull_v11fin_ASM`（5 binder；MTRS + MJF + MJ）

自 `P6A12V11mHcolCH2_HPC_MTR.lean`（CH2_HPC 顶层 + hTRs 槽换 J10 槽〔R_c 形〕）起，叠加：
- `_hresJF` / `_hresJF8` binder 类型 = MJF 顶层的 `HgwResJFE_DT_J6W_MJF` /
  `HgwResJF8E_DT_J6W_CH2_MJF` 形（逐字）；
- `_hresJ` / `_hresJ8` binder 类型 = MJ2 顶层的 `HgwResE8_Th_MJ` / `HgwResJ8H8_Th_MJ` 形（逐字）；
  旧⇒新（J 槽）`hresJ_new_of_old_ASM`（自 MJ2 并入）；
- `_hTRs` binder：环境 = MTRS 顶层逐字，结论槽 = TRSJ10 的 `R4HnotC_TJ F ε C1 C2 Ctime`
  （桥 `hTRs_of_res_gate_TJ`，`P6DistLADriverBridgeGateTJ`；R4 帧 J10 槽前提改由 T0K 供给 + J10 链
  producer 提供，残余为 `R4HnotC_TJ`）；
- 引擎换 `hP6bTwoLevelTimeCollar_of_slots_v7_loc_v11fin_hcap_hcol_ASM`
  （`P6HP6bAssemblyV7LocFinASM`）。结论 `A12EnhancedFullConclusion_C11F P g` 逐字，binder 数 5，无新 binder。
生成器 `build-logs/scratch/O-CH11-ASM/gen/gen_top.py`；
binder 逐字比对 `build-logs/scratch/O-CH11-ASM/binderdiff.txt`。
本文件由 ASM 车道 owner 就地维护（COMMON-CH8-TAKEBACK 15:43 / 15:46）。下段为 CH2_HPC 底座前版说明。

[CEILHN2：自 `P6A12V11mHcolCHN_HPC.lean` 机械克隆]
# HPCCAP：A12′ v11m（CHN）顶层的 hcap 透传孪生（后缀 `_HPC`）

自 `P6A12V11mCHN.lean` 机械克隆（生成器 `build-logs/scratch/HPCCAP/gen/gen.py`）：hres / hres8 两槽核前加
`SurgeryParamCompat_P6PC q 2 →`；引擎换 `_HPC` 孪生（hcap 在实际构造点的 tower 上付 hpc）。顶层 binder 数不变（5）。
-/

set_option autoImplicit false

/-!
# W10 V11 CHN：A12′ 顶层 v11m（HN ceiling，5 binder）

CEIL-HN 孪生（O-CH11-CEILHN，后缀 `_CHN`）：自 `P6A12V11mV11.lean` 机械克隆
（生成器 `build-logs/scratch/CEILHN/gen/clone.py`），ceiling 常数换 HN 扩展。
-/

noncomputable section
universe u
open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow (ClosedBirthConstants)
open GC.LongTime.Ch11 (p6CoarseC_C11GT6 p6FineEta_C11GT6 p6FineEta_pos_C11GT6 epsW_CXOU2)
open GC.LongTime.Ch11 (BlockTower_C11W capWindowRadius_C11E FineOf_C11G2 BudgetCertificate_C11GT2
  SameConstructionRetentionSupplyPlus_C11GT6 chainDiagonal_C11A C1P6_C11GT6 C2P6_C11GT6
  p6X1HN_CH2 p6X2HN_CH2 p6CtimeHN_CH2 p6BadCH2_CH2 htransMBadHN_CH2)
namespace ObservedHistory
open GC.GeneralFlow (PreparedSpatialChain)
open GC.LongTime.Ch11 (p6CoarseCH2_CH2 one_le_p6CoarseCH2_CH2 p6CoarseC_le_p6CoarseCH2_CH2)

/-- **A12′ v11m（HPCCAP）**：`a12EnhancedFull_v11m_V11_CHN` 的 hcap 透传孪生——hres 两核不再带 hpc 合取（改为核前
假设 `SurgeryParamCompat_P6PC q 2 →`，由引擎在实际 tower 上用 hcap 付），顶层仍 5 binder。 -/
theorem a12EnhancedFull_v11fin_ASM
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∀ (_hresJ :
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
      pB.modelAccuracy ≤ εSel_W9S.{u} Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
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
      HgwResE8_Th_MJ F q ε C1 C2 Ctime Ctime₀ T₀ (fun _ => (0 : ℝ)) Cb Rn ζ δ₀ m₀
        a₀)
    (_hresJ8 :
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
      pB.modelAccuracy ≤ εSel_W9S.{u} Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
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
      HgwResJ8H8_Th_MJ F q ε C1 C2 Ctime Ctime₀ T₀ (fun _ => (0 : ℝ)) Cb Rn ζ δ₀
        m₀ a₀)
    (_hresJF :
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
      pB.modelAccuracy ≤ εSel_W9S.{u} Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∀ {a₀ : ℝ}, 0 < a₀ →
      (∀ n x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x) →
      ∃ Θ : ℕ → ℝ,
      ∀ {ε C1 C2 : ℝ} {Ctime Ctime₀ : ℝ≥0} {T₀ : ℕ → ℝ}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ →
      Ctime = p6CtimeHN_CH2.{u} Γ → Ctime₀ = Γf.Ctime → (∀ n, Θ n ≤ T₀ n) →
      HgwResJFE_DT_J6W_MJF F q ε C1 C2 Ctime T₀ (fun _ => (0 : ℝ)) a₀)
    (_hresJF8 :
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
      pB.modelAccuracy ≤ εSel_W9S.{u} Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∀ {a₀ : ℝ}, 0 < a₀ →
      (∀ n x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x) →
      ∃ Θ : ℕ → ℝ,
      ∀ {ε C1 C2 : ℝ} {Ctime Ctime₀ : ℝ≥0} {T₀ : ℕ → ℝ}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ →
      Ctime = p6CtimeHN_CH2.{u} Γ → Ctime₀ = Γf.Ctime → (∀ n, Θ n ≤ T₀ n) →
      HgwResJF8E_DT_J6W_CH2_MJF F q ε C1 C2 Ctime T₀ (fun _ => (0 : ℝ)) a₀)
    (_hTRs :
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
      pB.modelAccuracy ≤
        (min (min (εSel_W9S.{u} Γ Γf) (Classical.choose hTRs_of_res_gate_TJ.{u}))
        (min GC.LongTime.Ch11.εProf_C11E.{u} (GC.LongTime.Ch11.epsilon0_C11FR Γf.epsilon
          (GC.LongTime.Ch11.chainC1_C11KD Γf) (GC.LongTime.Ch11.chainC2_C11KD Γf) P))) →
       capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      GC.LongTime.Ch11.collarAdmitsAllOrders_C11E.{u} pB.fixed.collarLength pB.fixed.collar_pos →
      ∀ {ε C1 C2 : ℝ} {Ctime : ℝ≥0}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ →
      Ctime = p6CtimeHN_CH2.{u} Γ →
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
      R4HnotC_TJ F ε C1 C2 Ctime),
    GC.LongTime.Ch11.A12EnhancedFullConclusion_C11F P g := by
  intro hresJ hresJ8 hresJF hresJF8 hTRs
  obtain ⟨ε₁, hε₁, hDL⟩ := hdistLA_win_of_TRs_gate_MTR.{u}
  have hε₀G := (Classical.choose_spec hTRs_of_res_gate_TJ.{u}).1
  have hGate := (Classical.choose_spec hTRs_of_res_gate_TJ.{u}).2
  let e' : ClosedBirthConstants → ClosedBirthConstants → ℝ := fun Γ Γf =>
    min (min (min (εSel_W9S.{u} Γ Γf)
      (Classical.choose hTRs_of_res_gate_TJ.{u})) ε₁)
      (min GC.LongTime.Ch11.εProf_C11E.{u}
      (GC.LongTime.Ch11.epsilon0_C11FR Γf.epsilon (GC.LongTime.Ch11.chainC1_C11KD Γf)
        (GC.LongTime.Ch11.chainC2_C11KD Γf) P))
  have hm : ∀ Γ Γf, e' Γ Γf ≤ εSel_W9S.{u} Γ Γf := fun _ _ =>
    (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hpos : ∀ Γ Γf, 0 < e' Γ Γf := fun Γ Γf =>
    lt_min (lt_min (lt_min (εSel_pos_W9S.{u} Γ Γf) hε₀G) hε₁)
      (lt_min GC.LongTime.Ch11.εProf_pos_C11E.{u} (GC.LongTime.Ch11.epsilon0_pos_C11FR.{u} _ _ _ _))
  obtain ⟨Rn, mn, hslot⟩ := GC.LongTime.Ch11.hspineTwoLevelTime_of_recent_PB_CXW_CH2.{u} P g
  refine GC.LongTime.Ch11.a12EnhancedFull_of_v8_collar_actual_hcap_CH2_HPC P g Rn mn hslot
    (hP6bTwoLevelTimeCollar_of_slots_v7_loc_v11fin_hcap_hcol_ASM P g e' hpos
      (fun _ _ => 4) (fun _ _ => le_rfl)
      ?_ ?_ ?_ ?_ (hinit_slot_P6HI P g e') (hrecT_slot_P6HI P g e')
      (hDL P g e' (fun _ _ => (min_le_left _ _).trans (min_le_right _ _))
        (hGate P g e'
          (fun _ _ => (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
          (fun _ _ => min_le_right _ _) ?_)))
  · intro Cb Rn ζ δ₀ m₀ hCb hζ hδ₀ hRn hm₀ pB Γ Γf hfine he1 he2 Cdist εR T hbud hS F q hFT hq hacc
    exact hresJ Cb Rn ζ δ₀ m₀ hCb hζ hδ₀ hRn hm₀
      hfine he1 he2 Cdist εR T hbud hS F q hFT hq (hacc.trans (hm Γ Γf))
  · intro Cb Rn ζ δ₀ m₀ hCb hζ hδ₀ hRn hm₀ pB Γ Γf hfine he1 he2 Cdist εR T hbud hS F q hFT hq hacc
    exact hresJ8 Cb Rn ζ δ₀ m₀ hCb hζ hδ₀ hRn hm₀
      hfine he1 he2 Cdist εR T hbud hS F q hFT hq (hacc.trans (hm Γ Γf))
  · intro pB Γ Γf hfine he1 he2 Cdist εR T hbud hS F q hFT hq hacc
    exact hresJF hfine he1 he2 Cdist εR T hbud hS F q hFT hq (hacc.trans (hm Γ Γf))
  · intro pB Γ Γf hfine he1 he2 Cdist εR T hbud hS F q hFT hq hacc
    exact hresJF8 hfine he1 he2 Cdist εR T hbud hS F q hFT hq (hacc.trans (hm Γ Γf))
  · intro pB Γ Γf hfine he1 he2 Cdist εR T hbud hS F q hFT hq hacc
    exact hTRs hfine he1 he2 Cdist εR T hbud hS F q hFT hq
      (hacc.trans (min_le_min (min_le_left _ _) le_rfl))

/-- consumer：任意 9 binder 实参 ⇒ A12′ 结论（`_hTRs ⇒ _hdistLA`：`hdistLA_win_of_TRs_DLW_CH2`）。 -/
theorem a12_v11fin_apply_ASM (P : OrientedThreeStage.{u}) (g : P.Metric) :
    type_of% (a12EnhancedFull_v11fin_ASM P g) :=
  a12EnhancedFull_v11fin_ASM P g

/-- **旧核 ⇒ 新核（J 槽，自 MJ2 并入，PROVED）**：CH2_HPC 底座 `_hresJ`（核 `HgwResE6_V11`）⇒ 终形 `_hresJ`
（核 `HgwResE8_Th_MJ`）。 -/
theorem hresJ_new_of_old_ASM (P : OrientedThreeStage.{u}) (g : P.Metric) :
    (∀ (Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ) (m₀ : ℝ≥0 → ℕ → ℕ),
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
      pB.modelAccuracy ≤ εSel_W9S.{u} Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
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
      HgwResE6_V11 F q ε C1 C2 Ctime Ctime₀ T₀ (fun _ => (0 : ℝ)) Cb Rn ζ δ₀ m₀
        a₀) →
    (∀ (Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ) (m₀ : ℝ≥0 → ℕ → ℕ),
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
      pB.modelAccuracy ≤ εSel_W9S.{u} Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
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
      HgwResE8_Th_MJ F q ε C1 C2 Ctime Ctime₀ T₀ (fun _ => (0 : ℝ)) Cb Rn ζ δ₀ m₀
        a₀) := by
  intro hold Cb Rn ζ δ₀ m₀ hCb hζ hδ hRn hm pB Γ Γf hfine he1 he2 Cdist εR T hbud hS F q hFT hq
    hacc hrad hord a₀ ha₀ hHI
  obtain ⟨Θ, hΘ⟩ := hold Cb Rn ζ δ₀ m₀ hCb hζ hδ hRn hm hfine he1 he2 Cdist εR T hbud hS F q hFT hq
    hacc hrad hord ha₀ hHI
  exact ⟨Θ, fun e1 e2 e3 e4 e5 hT hpc => hgwResE8Th_of_E6_MJ (hΘ e1 e2 e3 e4 e5 hT hpc)⟩

end ObservedHistory
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

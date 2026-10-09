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
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DistLADriverBridgeGateTH
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DistLargeWinGateMTR
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6A12TopV8FnActualHcap_C2_HPC
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6A12V11FinASM

/-!
# O-CH11-ASM：候选 A′ `a12EnhancedFull_v11fin4_ASM`（4 binder；去 `_hTRs`）

自 `P6A12V11FinASM.lean`（终形 5 binder，`_hTRs` = `R4HnotC_TJ` 形）按 TRSHNOT `asm_edit_th.py` 改：
- import `P6DistLADriverBridgeGateTJ` → `…GateTH`；
  `hTRs_of_res_gate_TJ` → `hTRs_of_res_gate_TH`（3 处）；
- 删 `_hTRs` binder、`intro` 的 `hTRs`、`hGate` 末参 `?_`、末个 `?_` 分支；
  引擎 `P6HP6bAssemblyV7LocFinASM` 不改；
- 4 个 binder `_hresJ · _hresJ8 · _hresJF · _hresJF8` 与 `a12EnhancedFull_v11fin_ASM` 同名 binder 逐字相同；
  结论 `A12EnhancedFullConclusion_C11F P g` 逐字。hTRs 行不再是 binder：`hdistLA` 由 TH 桥在引擎环境内
  供出（依赖环境数据 `hanti / hδq / recQ / hrecent / hfine / hTD / hphi / hpinK`，皆在桥 / 驱动环境内）。
- `fin_of_fin4_ASM`：4-binder 定理 ⇒ 5-binder 终形（PROVED）。
生成器 `build-logs/scratch/O-CH11-ASM/gen/gen_fin4.py`。本文件为候选 A′，终形 5-binder 形不动，
待 R-C11-26 回复处置（lead 裁定）。下段为 CH2_HPC 底座前版说明。

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
theorem a12EnhancedFull_v11fin4_ASM
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
      HgwResJF8E_DT_J6W_CH2_MJF F q ε C1 C2 Ctime T₀ (fun _ => (0 : ℝ)) a₀),
    GC.LongTime.Ch11.A12EnhancedFullConclusion_C11F P g := by
  intro hresJ hresJ8 hresJF hresJF8
  obtain ⟨ε₁, hε₁, hDL⟩ := hdistLA_win_of_TRs_gate_MTR.{u}
  have hε₀G := (Classical.choose_spec hTRs_of_res_gate_TH.{u}).1
  have hGate := (Classical.choose_spec hTRs_of_res_gate_TH.{u}).2
  let e' : ClosedBirthConstants → ClosedBirthConstants → ℝ := fun Γ Γf =>
    min (min (min (εSel_W9S.{u} Γ Γf)
      (Classical.choose hTRs_of_res_gate_TH.{u})) ε₁)
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
          (fun _ _ => min_le_right _ _))))
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

/-- consumer：任意 4 binder 实参 ⇒ A12′ 结论（`hdistLA` 经 TH 桥 `hTRs_of_res_gate_TH`，无 `_hTRs`）。 -/
theorem a12_v11fin4_apply_ASM (P : OrientedThreeStage.{u}) (g : P.Metric) :
    type_of% (a12EnhancedFull_v11fin4_ASM P g) :=
  a12EnhancedFull_v11fin4_ASM P g

/-- **5 ⇐ 4（PROVED）**：4-binder 候选 A′ ⇒ 5-binder 终形（`a12EnhancedFull_v11fin_ASM`，其 `_hTRs`
= `R4HnotC_TJ` 形在此不被使用）。反向（5 ⇒ 4）不可得：需由 TH 桥供出 `R4HnotC_TJ` 形的 `_hTRs`，
而该形缺 `recordsF`（TRSHNOT G0），不能由引擎数据证出；4-binder 定理的证明＝5-binder 证明体把 TJ 桥换成
TH 桥、删去 `_hTRs` 的 intro / 末参 / 末分支（生成器 `gen_fin4.py`）。 -/
theorem fin_of_fin4_ASM (P : OrientedThreeStage.{u}) (g : P.Metric) :
    type_of% (a12EnhancedFull_v11fin4_ASM P g) → type_of% (a12EnhancedFull_v11fin_ASM P g) :=
  fun h h1 h2 h3 h4 _ => h h1 h2 h3 h4

end ObservedHistory
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

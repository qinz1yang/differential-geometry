import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6A12SlotsV10S14Hgw5P6HGW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HgapWireRes2P6HGW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HgapWireRes3P6HGW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HgwResJ11V11
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HgwResD0V11

/-!
# F-24-1 GAP-WITNESS + δ₀ 收缩可行性 + F-24-5 同见证推论（O-CH11-F241，后缀 `_F241`）

* **GAP-WITNESS（F-24-1）**：kernel 元组 `δ₀ = ζ = 1/(n+1)`、`Cb = 1/(n+1)²`、`Rn = n+1`、`m₀ = n+2`
  满足 hres 槽前全部数值前提（`cexTuple_premises_F241`），但 `2·δ₀(C,0)² = 2 > 1 = Cb(C,0)`。
  故含无条件 `hδ₀Cb` 合取的开放核
  `HgwResE2 / J8F / J8E / J8D_P6HGW`、`HgwResE3 / J8G_V11` 在该元组处为假；HGW5 顶层的 `_hresJ` / `_hresJ8` 槽类型
  （逐字复制）在任一满足环境前提的实例中取 `T₀ := Θ` 即推出 `False`（`hgw5_hresJ_refuted_F241` 等）。
* **修正线（W10 G8 v11j / v11）不受此反例影响**：`HgwResE4_V11` / `HgwResJ8H_V11` 对 kernel 元组定义上无关
  （`Iff.rfl`），且反例元组经 `kernelDelta_shrink_all_V11` 得 `δ₀′` 满足 `2δ₀′² ≤ Cb`、`δ₀′ ≤ δ₀`。
* **F-24-5 同见证**：`hgapJ{,8}Q_loc_V11` 的同一 ∃ 元组 `(p, Qs, recordsK)` 上 J6
  （`(n+1)·max((n+1)/c, Qs) ≤ scale`）与 `hQsρ` 同时成立，合得 `(n+1)·ρ(Tno)⁻² ≤ scale`
  （同 records、同 cutoff `max(T₀, c(σ−L/R))`）。
生成器 `build-logs/scratch/F241/gen/gen.py`（逐字复制 Hgw5 槽类型与 hgapJQ 前缀并断言）。
-/

set_option autoImplicit false

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
  p6X1std_C11GT6 p6X2std_C11GT6 p6Ctime_C11G7B p6BadC_C11G2 htransMBad_C11G7B)

namespace ObservedHistory

/-- 反例 `Cb`：`1/(n+1)²`。 -/
def cexCb_F241 : ℝ≥0 → ℕ → ℝ := fun _ n => 1 / ((n : ℝ) + 1) ^ (2 : ℕ)

/-- 反例 `δ₀ = ζ`：`1/(n+1)`。 -/
def cexDelta_F241 : ℝ≥0 → ℕ → ℝ := fun _ n => 1 / ((n : ℝ) + 1)

/-- 反例 `Rn`：`n+1`。 -/
def cexRn_F241 : ℝ≥0 → ℕ → ℝ := fun _ n => (n : ℝ) + 1

/-- 反例 `m₀`：`n+2`。 -/
def cexM0_F241 : ℝ≥0 → ℕ → ℕ := fun _ n => n + 2

/-- 反例元组满足 hres 槽前全部数值前提（`Cb, ζ, δ₀, Rn, m₀` 五行）。 -/
theorem cexTuple_premises_F241 :
    (∀ (C : ℝ≥0) (n : ℕ), 0 < cexCb_F241 C n ∧ cexCb_F241 C n ≤ 1 / ((n : ℝ) + 1) ^ (2 : ℕ)) ∧
    (∀ (C : ℝ≥0) (n : ℕ), 0 < cexDelta_F241 C n ∧ cexDelta_F241 C n ≤ 1 / ((n : ℝ) + 1)) ∧
    (∀ (C : ℝ≥0) (n : ℕ), (n : ℝ) + 1 ≤ cexRn_F241 C n) ∧
    (∀ (C : ℝ≥0) (n : ℕ), n + 2 ≤ cexM0_F241 C n) := by
  refine ⟨fun C n => ⟨by unfold cexCb_F241; positivity, le_rfl⟩,
    fun C n => ⟨by unfold cexDelta_F241; positivity, le_rfl⟩, fun C n => le_rfl, fun C n => le_rfl⟩

/-- **GAP-WITNESS 核心**：反例元组下 `hδ₀Cb` 为假（`n = 0`：`2 ≤ 1`）。 -/
theorem not_hδ₀Cb_cex_F241 :
    ¬ ∀ (C : ℝ≥0) (n : ℕ), 2 * cexDelta_F241 C n ^ 2 ≤ cexCb_F241 C n := by
  intro h
  have h0 := h 0 0
  simp only [cexDelta_F241, cexCb_F241, Nat.cast_zero, zero_add] at h0
  norm_num at h0

/-- GAP-WITNESS：`HgwResE2_P6HGW` 在反例元组处为假（第二合取 = 无条件 `hδ₀Cb`）。 -/
theorem hgwResE2_cex_false_F241 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
    (ε C1 C2 : ℝ) (Ctime Ctime₀ : ℝ≥0) (T₀ Qt : ℕ → ℝ) (a₀ : ℝ) :
    ¬ HgwResE2_P6HGW F q ε C1 C2 Ctime Ctime₀ T₀ Qt cexCb_F241 cexRn_F241
      cexDelta_F241 cexDelta_F241 cexM0_F241 a₀ :=
  fun h => not_hδ₀Cb_cex_F241 h.2.1

/-- GAP-WITNESS：`HgwResJ8F_P6HGW` 在反例元组处为假（第二合取 = 无条件 `hδ₀Cb`）。 -/
theorem hgwResJ8F_cex_false_F241 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
    (ε C1 C2 : ℝ) (Ctime Ctime₀ : ℝ≥0) (T₀ Qt : ℕ → ℝ) (a₀ : ℝ) :
    ¬ HgwResJ8F_P6HGW F q ε C1 C2 Ctime Ctime₀ T₀ Qt cexCb_F241 cexRn_F241
      cexDelta_F241 cexDelta_F241 cexM0_F241 a₀ :=
  fun h => not_hδ₀Cb_cex_F241 h.2.1

/-- GAP-WITNESS：`HgwResJ8E_P6HGW` 在反例元组处为假（第二合取 = 无条件 `hδ₀Cb`）。 -/
theorem hgwResJ8E_cex_false_F241 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
    (ε C1 C2 : ℝ) (Ctime Ctime₀ : ℝ≥0) (T₀ Qt : ℕ → ℝ) (a₀ : ℝ) :
    ¬ HgwResJ8E_P6HGW F q ε C1 C2 Ctime Ctime₀ T₀ Qt cexCb_F241 cexRn_F241
      cexDelta_F241 cexDelta_F241 cexM0_F241 a₀ :=
  fun h => not_hδ₀Cb_cex_F241 h.2.1

/-- GAP-WITNESS：`HgwResJ8D_P6HGW` 在反例元组处为假（第二合取 = 无条件 `hδ₀Cb`）。 -/
theorem hgwResJ8D_cex_false_F241 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
    (records : GC.LongTime.Ch11.CutoffRecords_C11S F q)
    (ε C1 C2 : ℝ) (Ctime Ctime₀ : ℝ≥0) (T₀ Qt : ℕ → ℝ) (a₀ : ℝ) :
    ¬ HgwResJ8D_P6HGW F q records ε C1 C2 Ctime Ctime₀ T₀ Qt cexCb_F241 cexRn_F241
      cexDelta_F241 cexDelta_F241 cexM0_F241 a₀ :=
  fun h => not_hδ₀Cb_cex_F241 h.2.1

/-- GAP-WITNESS：`HgwResE3_V11` 在反例元组处为假（第二合取 = 无条件 `hδ₀Cb`）。 -/
theorem hgwResE3_cex_false_F241 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
    (ε C1 C2 : ℝ) (Ctime Ctime₀ : ℝ≥0) (T₀ Qt : ℕ → ℝ) (a₀ : ℝ) :
    ¬ HgwResE3_V11 F q ε C1 C2 Ctime Ctime₀ T₀ Qt cexCb_F241 cexRn_F241
      cexDelta_F241 cexDelta_F241 cexM0_F241 a₀ :=
  fun h => not_hδ₀Cb_cex_F241 h.2.1

/-- GAP-WITNESS：`HgwResJ8G_V11` 在反例元组处为假（第二合取 = 无条件 `hδ₀Cb`）。 -/
theorem hgwResJ8G_cex_false_F241 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
    (ε C1 C2 : ℝ) (Ctime Ctime₀ : ℝ≥0) (T₀ Qt : ℕ → ℝ) (a₀ : ℝ) :
    ¬ HgwResJ8G_V11 F q ε C1 C2 Ctime Ctime₀ T₀ Qt cexCb_F241 cexRn_F241
      cexDelta_F241 cexDelta_F241 cexM0_F241 a₀ :=
  fun h => not_hδ₀Cb_cex_F241 h.2.1

/-- **GAP-WITNESS（F-24-1，binder 级）**：HGW5 顶层 `_hresJ` 槽类型（逐字）+ 任一环境实例 ⇒ `False`
（反例元组、`T₀ := Θ`）。故 `a12EnhancedFull_of_slots_v10_loc_s14_hgw5_P6HGW` 在可实例化环境下空真。 -/
theorem hgw5_hresJ_refuted_F241 (P : OrientedThreeStage.{u}) (g : P.Metric)
    (_hresJ :
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
        C1 = C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ →
        C2 = C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ →
        Ctime = p6Ctime_C11G7B.{u} Γ → Ctime₀ = Γf.Ctime → (∀ n, Θ n ≤ T₀ n) →
        HgwResE2_P6HGW F q ε C1 C2 Ctime Ctime₀ T₀ (fun _ => (0 : ℝ)) Cb Rn ζ δ₀ m₀ a₀)
    {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants} (hfine : FineOf_C11G2.{u} Γf Γ)
    (hs : Γ.epsilon ≤ εStrong_C12X.{u}) (hW : Γ.epsilon ≤ epsW_CXOU2.{u})
    (Cdist : ℝ≥0) (εReserve : ℝ)
    (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve)
    (hcert : ∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
      (T.block j) (T.lookahead j) (T.request j))
    (hS : SameConstructionRetentionSupplyPlus_C11GT6 T)
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (hF : F.tower = T.toChain.tower)
    (hq : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t)
    (hacc : pB.modelAccuracy ≤ εSel_W9S.{u} Γ Γf) (hrad : capWindowRadius_C11E + 1 ≤ pB.modelRadius)
    (hord : 2 ≤ pB.modelOrder) {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
      -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x) :
    False := by
  obtain ⟨hCb, hδ, hRn, hm⟩ := cexTuple_premises_F241
  obtain ⟨Θ, hΘ⟩ := _hresJ cexCb_F241 cexRn_F241 cexDelta_F241 cexDelta_F241 cexM0_F241 hCb hδ hδ
    hRn hm hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord ha₀ hHI
  exact hgwResE2_cex_false_F241 F q _ _ _ _ _ Θ _ a₀
    (hΘ rfl rfl rfl rfl rfl (fun n => le_refl (Θ n)))

/-- **GAP-WITNESS（F-24-1，binder 级）**：HGW5 顶层 `_hresJ8` 槽类型（逐字）+ 任一环境实例 ⇒ `False`
（反例元组、`T₀ := Θ`）。故 `a12EnhancedFull_of_slots_v10_loc_s14_hgw5_P6HGW` 在可实例化环境下空真。 -/
theorem hgw5_hresJ8_refuted_F241 (P : OrientedThreeStage.{u}) (g : P.Metric)
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
        C1 = C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ →
        C2 = C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ →
        Ctime = p6Ctime_C11G7B.{u} Γ → Ctime₀ = Γf.Ctime → (∀ n, Θ n ≤ T₀ n) →
        HgwResJ8F_P6HGW F q ε C1 C2 Ctime Ctime₀ T₀ (fun _ => (0 : ℝ)) Cb Rn ζ δ₀ m₀ a₀)
    {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants} (hfine : FineOf_C11G2.{u} Γf Γ)
    (hs : Γ.epsilon ≤ εStrong_C12X.{u}) (hW : Γ.epsilon ≤ epsW_CXOU2.{u})
    (Cdist : ℝ≥0) (εReserve : ℝ)
    (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve)
    (hcert : ∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
      (T.block j) (T.lookahead j) (T.request j))
    (hS : SameConstructionRetentionSupplyPlus_C11GT6 T)
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (hF : F.tower = T.toChain.tower)
    (hq : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t)
    (hacc : pB.modelAccuracy ≤ εSel_W9S.{u} Γ Γf) (hrad : capWindowRadius_C11E + 1 ≤ pB.modelRadius)
    (hord : 2 ≤ pB.modelOrder) {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
      -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x) :
    False := by
  obtain ⟨hCb, hδ, hRn, hm⟩ := cexTuple_premises_F241
  obtain ⟨Θ, hΘ⟩ := _hresJ8 cexCb_F241 cexRn_F241 cexDelta_F241 cexDelta_F241 cexM0_F241 hCb hδ hδ
    hRn hm hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord ha₀ hHI
  exact hgwResJ8F_cex_false_F241 F q _ _ _ _ _ Θ _ a₀
    (hΘ rfl rfl rfl rfl rfl (fun n => le_refl (Θ n)))

/-- 修正核 `HgwResE4_V11` 与 kernel 元组无关（`Iff.rfl`）：反例元组不能作用于它。 -/
theorem hgwResE4_tuple_indep_F241 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime Ctime₀ : ℝ≥0}
    {T₀ Qt : ℕ → ℝ} (Cb Rn ζ δ₀ Cb' Rn' ζ' δ₀' : ℝ≥0 → ℕ → ℝ) (m₀ m₀' : ℝ≥0 → ℕ → ℕ) (a₀ a₀' : ℝ) :
    HgwResE4_V11 F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀ a₀ ↔
      HgwResE4_V11 F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb' Rn' ζ' δ₀' m₀' a₀' := Iff.rfl

/-- 修正核 `HgwResJ8H_V11` 与 kernel 元组无关（`Iff.rfl`）。 -/
theorem hgwResJ8H_tuple_indep_F241 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime Ctime₀ : ℝ≥0}
    {T₀ Qt : ℕ → ℝ} (Cb Rn ζ δ₀ Cb' Rn' ζ' δ₀' : ℝ≥0 → ℕ → ℝ) (m₀ m₀' : ℝ≥0 → ℕ → ℕ) (a₀ a₀' : ℝ) :
    HgwResJ8H_V11 F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀ a₀ ↔
      HgwResJ8H_V11 F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb' Rn' ζ' δ₀' m₀' a₀' := Iff.rfl

/-- 反例元组下 v11j 引擎的 δ₀ 收缩可行：`δ₀′ ≤ δ₀`、`2δ₀′² ≤ Cb`、`0 < δ₀′ ≤ 1/(n+1)`。 -/
theorem cexTuple_shrink_F241 :
    ∃ d : ℝ≥0 → ℕ → ℝ, (∀ (C : ℝ≥0) (n : ℕ), 0 < d C n ∧ d C n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ C n, d C n ≤ cexDelta_F241 C n) ∧ (∀ (C : ℝ≥0) (n : ℕ), 2 * d C n ^ 2 ≤ cexCb_F241 C n) :=
  kernelDelta_shrink_all_V11 cexTuple_premises_F241.1 cexTuple_premises_F241.2.1

/-- **F-24-5 同见证（`hgapJQ_loc_V11`）**：同一 ∃ 元组 `(p, Qs, recordsK)` 上 J6 与 `hQsρ` 同时成立，合得
`(n+1)·ρ(Tno)⁻² ≤ scale`（同 records、同 cutoff `max(T₀, c(σ−L/R))`）。 -/
theorem hgapJQ_sameWitness_Qsρ_F241 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime Ctime₀ : ℝ≥0}
    {T₀ Qt : ℕ → ℝ} {Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ} {m₀ : ℝ≥0 → ℕ → ℕ}
    (h : hgapJQ_loc_V11 F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀) :
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
      ∀ (_hRpos : ∀ k, 0 < R k), (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
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
    ∃ (p : ℕ → CutoffParameters) (Qs : ℕ → ℝ)
      (recordsK : ∀ n (i : Fin (Ho n).eventCount),
        max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time i.succ →
          GeometricCutoffRecord (Ho n).toHistory i (p n)),
      (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qs n) ≤
        ((recordsK n i hi).static b).neck.scale) ∧
      (∀ n, (q.neckRadius (Tno n : ℝ) ^ 2)⁻¹ ≤ Qs n) ∧
      (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * (q.neckRadius (Tno n : ℝ) ^ 2)⁻¹ ≤
        ((recordsK n i hi).static b).neck.scale) := by
  intro A _h0 ind Ho Tno pTo r hr _h1 _h2 _h3 _h4 c hc K Kh Tn pT aSeed haT _h5 _h6 _h7 _h8
    seedTrace σ y R hsT has L _h9 hRpos _h10 _h11 _h12 _h13 _h14 _h15 _h16 _h17 _h18 _h19 _h20 _h21
    _h22 _h23 _h24
  obtain ⟨p, -, Qs, recordsK, -, -, -, -, -, -, -, -, -, hJ6, -, -, -, -, -, -, -, -, -, hQs⟩ :=
    h A _h0 ind Tno pTo r hr _h1 _h2 _h3 _h4 aSeed haT _h5 _h6 _h7 _h8 seedTrace σ y R hsT has L _h9
      hRpos _h10 _h11 _h12 _h13 _h14 _h15 _h16 _h17 _h18 _h19 _h20 _h21 _h22 _h23 _h24
  exact ⟨p, Qs, recordsK, hJ6, hQs, fun n i hi b =>
    le_trans (mul_le_mul_of_nonneg_left ((hQs n).trans (le_max_right _ _))
      (Nat.cast_add_one_pos n).le) (hJ6 n i hi b)⟩

/-- **F-24-5 同见证（`hgapJ8Q_loc_V11`）**：同一 ∃ 元组 `(p, Qs, recordsK)` 上 J6 与 `hQsρ` 同时成立，合得
`(n+1)·ρ(Tno)⁻² ≤ scale`（同 records、同 cutoff `max(T₀, c(σ−L/R))`）。 -/
theorem hgapJ8Q_sameWitness_Qsρ_F241 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {η₁ C1₁ C2₁ : ℝ} {Ctime₁ : ℝ≥0}
    {ε C1 C2 : ℝ} {Ctime Ctime₀ : ℝ≥0}
    {T₀ Qt : ℕ → ℝ} {Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ} {m₀ : ℝ≥0 → ℕ → ℕ}
    (h : hgapJ8Q_loc_V11 F q η₁ C1₁ C2₁ Ctime₁ ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀) :
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
      ∀ (_hRpos : ∀ k, 0 < R k), (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
      Tendsto L atTop atTop →
      (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl η₁ C1₁ C2₁ Ctime₁ (σ k) (y k)) →
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
          8 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
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
    ∃ (p : ℕ → CutoffParameters) (Qs : ℕ → ℝ)
      (recordsK : ∀ n (i : Fin (Ho n).eventCount),
        max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time i.succ →
          GeometricCutoffRecord (Ho n).toHistory i (p n)),
      (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qs n) ≤
        ((recordsK n i hi).static b).neck.scale) ∧
      (∀ n, (q.neckRadius (Tno n : ℝ) ^ 2)⁻¹ ≤ Qs n) ∧
      (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * (q.neckRadius (Tno n : ℝ) ^ 2)⁻¹ ≤
        ((recordsK n i hi).static b).neck.scale) := by
  intro A _h0 ind Ho Tno pTo r hr _h1 _h2 _h3 _h4 c hc K Kh Tn pT aSeed haT _h5 _h6 _h7 _h8
    seedTrace σ y R hsT has L _h9 hRpos _h10 _h11 _h12 _h13 _h14 _h15 _h16 _h17 _h18 _h19 _h20 _h21
    _h22 _h23 _h24
  obtain ⟨p, -, Qs, recordsK, -, -, -, -, -, -, -, -, -, hJ6, -, -, -, -, -, -, -, -, -, hQs⟩ :=
    h A _h0 ind Tno pTo r hr _h1 _h2 _h3 _h4 aSeed haT _h5 _h6 _h7 _h8 seedTrace σ y R hsT has L _h9
      hRpos _h10 _h11 _h12 _h13 _h14 _h15 _h16 _h17 _h18 _h19 _h20 _h21 _h22 _h23 _h24
  exact ⟨p, Qs, recordsK, hJ6, hQs, fun n i hi b =>
    le_trans (mul_le_mul_of_nonneg_left ((hQs n).trans (le_max_right _ _))
      (Nat.cast_add_one_pos n).le) (hJ6 n i hi b)⟩

/-- consumer：GAP-WITNESS 投影（E2 在反例元组任一实例为假）与修正线收缩同时可用。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (q : CutoffParameters) :
    (¬ HgwResE2_P6HGW F q 0 0 0 0 0 (fun _ => 0) (fun _ => 0) cexCb_F241 cexRn_F241
        cexDelta_F241 cexDelta_F241 cexM0_F241 1) ∧
      ∃ d : ℝ≥0 → ℕ → ℝ, ∀ (C : ℝ≥0) (n : ℕ), 2 * d C n ^ 2 ≤ cexCb_F241 C n :=
  ⟨hgwResE2_cex_false_F241 F q 0 0 0 0 0 _ _ 1,
    let ⟨d, _, _, hd⟩ := cexTuple_shrink_F241; ⟨d, hd⟩⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

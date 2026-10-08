import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6A12V11V11
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HgwResDTV11
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ParamCompatTwoP6SS

set_option autoImplicit false

/-!
# VACUITY 审计见证（O-CH11-VACUITY，后缀 `_VAC`）：F-24-1 同类 hpc 条件反例 + 正例

* **GAP-WITNESS（hpc，条件形）**：开放核 `HgwResE4_V11 / HgwResE5_DW / HgwResE6_V11 / HgwResJ8H_V11 /
  HgwResJ8H_V11_CHN` 的第一合取 `SurgeryParamCompat_P6PC q 2` 位于全部反证假设之外，只依赖槽外层
  全称量化的 tower `T`（经 `hq`，q 在 `[0, ∞)` 上 = 链对角）。顶层 env 的 `BudgetCertificate_C11GT2`
  只给 cap 上界，`LookaheadReady_C11W` 只给 `0 < rNext ≤ radius`，不含 `cap·r_j ≤ rNext`（hcap）。
  故：任一可实例化 env 中若 tower 链对角违反 θ=2 合同，v11 最终顶层的 `_hresJ` / `_hresJ8` 槽类型
  （逐字）推出 `False`（`v11_hresJ_refuted_of_badTower_VAC` / `v11_hresJ8_refuted_of_badTower_VAC`）。
* **非重言**：`not_paramCompat_step_VAC`：δ ≡ 1/2、ρ 在 1 处由 1 跳到 1/4 的参数违反合同。
* **正例**：常值 ρ 满足合同（`paramCompat_const_VAC`）；ratio tower（hcap）上合同成立
  （`hpc_of_hcap_VAC`）；五行 kernel 元组前提可同时满足（`tuple_premises_VAC`）。
* 修法建议：把 `SurgeryParamCompat_P6PC q 2 ∧ K` 改为槽前提（`hcap →` 或
  `SurgeryParamCompat_P6PC q 2 → K`），由引擎在其实际构造的 ratio tower 上供给；不对任意 tower 无条件要求。
生成器 `build-logs/scratch/VACUITY/gen.py`（逐字复制 v11 槽类型并断言）。
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
  p6X1HN_CHN p6X2HN_CHN p6CtimeHN_CHN p6BadCHN_CHN htransMBadHN_CHN)
namespace ObservedHistory
open GC.GeneralFlow (PreparedSpatialChain)


/-- 五行元组 `Cb`。 -/
def tupCb_VAC : ℝ≥0 → ℕ → ℝ := fun _ n => 1 / ((n : ℝ) + 1) ^ (2 : ℕ)

/-- 五行元组 `δ₀ = ζ`。 -/
def tupDelta_VAC : ℝ≥0 → ℕ → ℝ := fun _ n => 1 / ((n : ℝ) + 1)

/-- 五行元组 `Rn`。 -/
def tupRn_VAC : ℝ≥0 → ℕ → ℝ := fun _ n => (n : ℝ) + 1

/-- 五行元组 `m₀`。 -/
def tupM0_VAC : ℝ≥0 → ℕ → ℕ := fun _ n => n + 2

/-- **正例**：hres 槽前五行 kernel 元组前提可同时满足。 -/
theorem tuple_premises_VAC :
    (∀ (C : ℝ≥0) (n : ℕ), 0 < tupCb_VAC C n ∧ tupCb_VAC C n ≤ 1 / ((n : ℝ) + 1) ^ (2 : ℕ)) ∧
    (∀ (C : ℝ≥0) (n : ℕ), 0 < tupDelta_VAC C n ∧ tupDelta_VAC C n ≤ 1 / ((n : ℝ) + 1)) ∧
    (∀ (C : ℝ≥0) (n : ℕ), (n : ℝ) + 1 ≤ tupRn_VAC C n) ∧
    (∀ (C : ℝ≥0) (n : ℕ), n + 2 ≤ tupM0_VAC C n) :=
  ⟨fun _ _ => ⟨by unfold tupCb_VAC; positivity, le_rfl⟩,
    fun _ _ => ⟨by unfold tupDelta_VAC; positivity, le_rfl⟩, fun _ _ => le_rfl, fun _ _ => le_rfl⟩

/-- 步函数 `ρ`：`t < 1` 取 1，否则 1/4。 -/
def stepRho_VAC : ℝ → ℝ := fun t => if t < 1 then 1 else 1 / 4

/-- 常值 `δ ≡ 1/2`。 -/
def halfDelta_VAC : ℝ → ℝ := fun _ => 1 / 2

/-- `0 < δ`。 -/
theorem halfDelta_pos_VAC : ∀ t, 0 < halfDelta_VAC t := fun _ => by
  unfold halfDelta_VAC; norm_num

/-- `δ < 1`。 -/
theorem halfDelta_lt_one_VAC : ∀ t, halfDelta_VAC t < 1 := fun _ => by
  unfold halfDelta_VAC; norm_num

/-- `0 < ρ`。 -/
theorem stepRho_pos_VAC : ∀ t, 0 < stepRho_VAC t := fun t => by
  unfold stepRho_VAC; split_ifs <;> norm_num

/-- **非重言**：`δ ≡ 1/2`、`ρ` 在 1 处跳到 1/4 违反 θ=2 合同（`x = 9/10, y = 1`：`1/2 > 1/4`）。 -/
theorem not_paramCompat_step_VAC (p₀ : CutoffParameters) :
    ¬ SurgeryParamCompat_P6PC (withRadii_P6PC p₀ halfDelta_VAC stepRho_VAC halfDelta_pos_VAC
      halfDelta_lt_one_VAC stepRho_pos_VAC) 2 := by
  rintro ⟨-, h⟩
  have h0 := h (9 / 10) 1 (by norm_num) (by norm_num) (by norm_num)
  norm_num [withRadii_P6PC, halfDelta_VAC, stepRho_VAC] at h0

/-- **正例**：常值 `ρ ≡ 1` 满足合同。 -/
theorem paramCompat_const_VAC (p₀ : CutoffParameters) :
    SurgeryParamCompat_P6PC (withRadii_P6PC p₀ halfDelta_VAC (fun _ => 1) halfDelta_pos_VAC
      halfDelta_lt_one_VAC (fun _ => one_pos)) 2 :=
  paramCompat_of_const_P6PC _ 2 (fun _ _ => rfl)

/-- **正例（ratio tower）**：env 的 `hq` + tower `hcap` ⇒ 槽第一合取（修法下引擎可供给）。 -/
theorem hpc_of_hcap_VAC {P : OrientedThreeStage.{u}} {g : P.Metric} {pB : CutoffParameters}
    {Γf : ClosedBirthConstants} {Cdist : ℝ≥0} {εR : ℝ}
    {T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εR} {q : CutoffParameters}
    (hq : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t)
    (hcap : ∀ j, (T.request j).accuracyCap * (T.block j).radius ≤ (T.lookahead j).rNext) :
    SurgeryParamCompat_P6PC q 2 :=
  paramCompat_q_of_requestCap_P6SS hq hcap

/-- GAP-WITNESS（核级）：`¬ SurgeryParamCompat_P6PC q 2` ⇒ `¬ HgwResE4_V11`。 -/
theorem not_E4_of_not_pc_VAC {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ}
    {Ctime Ctime₀ : ℝ≥0} {T₀ Qt : ℕ → ℝ} {Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ} {m₀ : ℝ≥0 → ℕ → ℕ}
    {a₀ : ℝ} (hbad : ¬ SurgeryParamCompat_P6PC q 2) :
    ¬ HgwResE4_V11 F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀ a₀ :=
  fun h => hbad h.1

/-- GAP-WITNESS（核级）：`¬ SurgeryParamCompat_P6PC q 2` ⇒ `¬ HgwResE5_DW`。 -/
theorem not_E5_of_not_pc_VAC {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ}
    {Ctime Ctime₀ : ℝ≥0} {T₀ Qt : ℕ → ℝ} {Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ} {m₀ : ℝ≥0 → ℕ → ℕ}
    {a₀ : ℝ} (hbad : ¬ SurgeryParamCompat_P6PC q 2) :
    ¬ HgwResE5_DW F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀ a₀ :=
  fun h => hbad h.1

/-- GAP-WITNESS（核级）：`¬ SurgeryParamCompat_P6PC q 2` ⇒ `¬ HgwResE6_V11`。 -/
theorem not_E6_of_not_pc_VAC {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ}
    {Ctime Ctime₀ : ℝ≥0} {T₀ Qt : ℕ → ℝ} {Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ} {m₀ : ℝ≥0 → ℕ → ℕ}
    {a₀ : ℝ} (hbad : ¬ SurgeryParamCompat_P6PC q 2) :
    ¬ HgwResE6_V11 F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀ a₀ :=
  fun h => hbad h.1

/-- GAP-WITNESS（核级）：`¬ SurgeryParamCompat_P6PC q 2` ⇒ `¬ HgwResJ8H_V11`。 -/
theorem not_J8H_of_not_pc_VAC {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ}
    {Ctime Ctime₀ : ℝ≥0} {T₀ Qt : ℕ → ℝ} {Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ} {m₀ : ℝ≥0 → ℕ → ℕ}
    {a₀ : ℝ} (hbad : ¬ SurgeryParamCompat_P6PC q 2) :
    ¬ HgwResJ8H_V11 F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀ a₀ :=
  fun h => hbad h.1

/-- GAP-WITNESS（核级）：`¬ SurgeryParamCompat_P6PC q 2` ⇒ `¬ HgwResJ8H_V11_CHN`。 -/
theorem not_J8HCHN_of_not_pc_VAC {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ}
    {Ctime Ctime₀ : ℝ≥0} {T₀ Qt : ℕ → ℝ} {Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ} {m₀ : ℝ≥0 → ℕ → ℕ}
    {a₀ : ℝ} (hbad : ¬ SurgeryParamCompat_P6PC q 2) :
    ¬ HgwResJ8H_V11_CHN F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀ a₀ :=
  fun h => hbad h.1

/-- **GAP-WITNESS（binder 级，条件形）**：v11 最终顶层 `_hresJ` 槽类型（逐字）+ env 实例 +
链对角违反 θ=2 合同 ⇒ `False`（五行元组 `tuple_premises_VAC`，`T₀ := Θ`）。 -/
theorem v11_hresJ_refuted_of_badTower_VAC (P : OrientedThreeStage.{u}) (g : P.Metric)
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
      C1 = C1P6_C11GT6.{u} p6X1HN_CHN.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2HN_CHN.{u} Γ →
      Ctime = p6CtimeHN_CHN.{u} Γ → Ctime₀ = Γf.Ctime → (∀ n, Θ n ≤ T₀ n) →
      HgwResE6_V11 F q ε C1 C2 Ctime Ctime₀ T₀ (fun _ => (0 : ℝ)) Cb Rn ζ δ₀ m₀ a₀)
    {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants} (hfine : FineOf_C11G2.{u} Γf Γ)
    (he1 : Γ.epsilon ≤ εStrong_C12X.{u}) (he2 : Γ.epsilon ≤ epsW_CXOU2.{u})
    (Cdist : ℝ≥0) (εR : ℝ)
    (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εR)
    (hbud : ∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
      (T.block j) (T.lookahead j) (T.request j))
    (hS : SameConstructionRetentionSupplyPlus_C11GT6 T)
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (hFT : F.tower = T.toChain.tower)
    (hq : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t)
    (hacc : pB.modelAccuracy ≤ εSel_W9S.{u} Γ Γf)
    (hrad : capWindowRadius_C11E + 1 ≤ pB.modelRadius)
    (hord : 2 ≤ pB.modelOrder) {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
      -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x)
    (hbad : ¬ SurgeryParamCompat_P6PC (chainDiagonal_C11A T.toChain) 2) : False := by
  obtain ⟨h1, h2, h3, h4⟩ := tuple_premises_VAC
  obtain ⟨Θ, hΘ⟩ := _hresJ tupCb_VAC tupRn_VAC tupDelta_VAC tupDelta_VAC tupM0_VAC h1 h2 h2 h3 h4
    hfine he1 he2 Cdist εR T hbud hS F q hFT hq hacc hrad hord ha₀ hHI
  have hpc := (hΘ (T₀ := Θ) rfl rfl rfl rfl rfl (fun _ => le_rfl)).1
  exact hbad (paramCompat_of_eqOn_P6SS hpc fun t ht => ⟨(hq t ht).1.symm, (hq t ht).2.symm⟩)

/-- **GAP-WITNESS（binder 级，条件形）**：v11 最终顶层 `_hresJ8` 槽类型（逐字）+ env 实例 +
链对角违反 θ=2 合同 ⇒ `False`（五行元组 `tuple_premises_VAC`，`T₀ := Θ`）。 -/
theorem v11_hresJ8_refuted_of_badTower_VAC (P : OrientedThreeStage.{u}) (g : P.Metric)
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
      C1 = C1P6_C11GT6.{u} p6X1HN_CHN.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2HN_CHN.{u} Γ →
      Ctime = p6CtimeHN_CHN.{u} Γ → Ctime₀ = Γf.Ctime → (∀ n, Θ n ≤ T₀ n) →
      HgwResJ8H_V11_CHN F q ε C1 C2 Ctime Ctime₀ T₀ (fun _ => (0 : ℝ)) Cb Rn ζ δ₀ m₀ a₀)
    {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants} (hfine : FineOf_C11G2.{u} Γf Γ)
    (he1 : Γ.epsilon ≤ εStrong_C12X.{u}) (he2 : Γ.epsilon ≤ epsW_CXOU2.{u})
    (Cdist : ℝ≥0) (εR : ℝ)
    (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εR)
    (hbud : ∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
      (T.block j) (T.lookahead j) (T.request j))
    (hS : SameConstructionRetentionSupplyPlus_C11GT6 T)
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (hFT : F.tower = T.toChain.tower)
    (hq : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t)
    (hacc : pB.modelAccuracy ≤ εSel_W9S.{u} Γ Γf)
    (hrad : capWindowRadius_C11E + 1 ≤ pB.modelRadius)
    (hord : 2 ≤ pB.modelOrder) {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
      -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x)
    (hbad : ¬ SurgeryParamCompat_P6PC (chainDiagonal_C11A T.toChain) 2) : False := by
  obtain ⟨h1, h2, h3, h4⟩ := tuple_premises_VAC
  obtain ⟨Θ, hΘ⟩ := _hresJ8 tupCb_VAC tupRn_VAC tupDelta_VAC tupDelta_VAC tupM0_VAC h1 h2 h2 h3 h4
    hfine he1 he2 Cdist εR T hbud hS F q hFT hq hacc hrad hord ha₀ hHI
  have hpc := (hΘ (T₀ := Θ) rfl rfl rfl rfl rfl (fun _ => le_rfl)).1
  exact hbad (paramCompat_of_eqOn_P6SS hpc fun t ht => ⟨(hq t ht).1.symm, (hq t ht).2.symm⟩)

/-- consumer：同一 `p₀` 上合同的正例与反例并存。 -/
example (p₀ : CutoffParameters) :
    SurgeryParamCompat_P6PC (withRadii_P6PC p₀ halfDelta_VAC (fun _ => 1) halfDelta_pos_VAC
      halfDelta_lt_one_VAC (fun _ => one_pos)) 2 ∧
    ¬ SurgeryParamCompat_P6PC (withRadii_P6PC p₀ halfDelta_VAC stepRho_VAC halfDelta_pos_VAC
      halfDelta_lt_one_VAC stepRho_pos_VAC) 2 :=
  ⟨paramCompat_const_VAC p₀, not_paramCompat_step_VAC p₀⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Outer.BlockStepOfAstraC11W5

set_option autoImplicit false

/-!
# S-CH11-W1L5 (G2)：A12 ⇐ astra step（BlockStep 路线）+ S8，生产者全部被消费

(F) 路线的 A12 consumer。与 ASM 的 `A12OfExistenceC11A`（`∃ S` 路线，经 `PreparedSpatialExistence`）
**并列、互不引用**：那条给 `∃ S : PreparedSpatialChain`，这条给
`∀ j, BlockStep_C11W j`（`∀ X, Inv X → ∃ ℓ … ∀ req … ∃ Y d`）再经 OUTER 的 W5 装配
`tower_of_blockSteps_C11W` 得到 `PreparedSpatialChain`。

* `exists_blockTower_of_astra_C11W5`：Providers + Step ⇒ 对每个 `P g`，存在 `pBase`、seed `X₀`
  （`Inv_C11W`、`history = atZero`、`radius ≤ 1`）与以 `X₀` 起头的 `BlockTower_C11W`（其 `toChain`
  是 `PreparedSpatialChain`）。量词顺序 `∃ Cdist C, ∀ P g, ∃ pBase …`。
* `a12_of_astra_blockSteps_C11W5`：A12 的结论逐字；**唯一**前提是 S8（P6 车道）的 of_chain 绑定形
  （D-R-C11-3-9：同一 tower / 同一对角 δ；D-R-C11-3-10：只对以 seed 起头的、带证书的输出 tower
  陈述，不是全称 chain）。`Dstar εReserve cMax` 只带正性，是 Step / Providers 自己的自由参数。
* consumer：同一产出（不要 S8）给 W1 的十项；produced chain 的 `state 0` 就是 seed。

## 三条验收（R-C11-3 D-8 / rev2 §6）各自落在哪个声明
1. **核完整类型**：`BlockStepOfAstraC11W5.hshape_of_astra_C11W5`（Step 结论 `makeCap` 支的逐字投影）；
   本文件 `a12_of_astra_blockSteps_C11W5` 的前提列表 = `{P g, Dstar εReserve cMax}` 的三个正性 + S8，
   没有 `BlockStep` / `BudgetChoice` / provider / class callback 前提（`#print` 可核）。
2. **∀ X 形 step，不是 `∃ S`**：`blockStep_of_astra_C11W5` / `blockSteps_of_astra_C11W5` 的结论就是
   `BlockStep_C11W …`（`∀ X, Inv X → ∃ ℓ … ∀ req …`）；它们的证明经 Step 的 `∀ L, L.DistanceData → …`。
   本文件与 G1 的声明都不引用 `PreparedSpatialExistence` / `PreparedSpatialRecursion` 的任何
   `∃ S` 定理（依赖闭包检查，见 audit）。
3. **消费生产者**：`a12_of_astra_blockSteps_C11W5` 的依赖闭包含 Step
   （`exists_prepared_spatial_step_…_small_test_margin_with_reserve_quality`）、
   Providers（`exists_prepared_spatial_initial_state_with_distance_scalars_with_reserve_quality`）、
   PCBC（`exists_prepared_closed_birth_class_before_quality_…_with_reserve_quality`）、
   DistanceBase（`exists_prepared_spatial_base_with_distance_scalars_and_small_test_margin`）。
   闭包检查在 `build-logs/audit/S-CH11-W1L5G2Audit.lean`（`run_cmd` 递归收集常量，断言这些在、
   且 `exists_prepared_spatial_chains_from_initial*` 不在）。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped NNReal

namespace GC.LongTime.Ch11

universe u

/-- **produced tower**：Providers + Step ⇒ 每个 `P g` 上存在 seed 与以 seed 起头的 block tower。 -/
theorem exists_blockTower_of_astra_C11W5 (Dstar εReserve : ℝ) (hDstar : 0 < Dstar)
    (hεReserve : 0 < εReserve) (cMax : ℝ) (hcMax : 0 < cMax) :
    ∃ Cdist : ℝ≥0, 1 ≤ Cdist ∧ ∃ C : ClosedBirthConstants,
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric),
    ∃ (pBase : CutoffParameters) (X₀ : BlockState_C11W pBase C P g 0),
      Inv_C11W Cdist cMax Dstar εReserve X₀ ∧ X₀.history = RetainedCoreHistory.atZero P g ∧
      X₀.radius ≤ 1 ∧
      ∃ T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve,
        T.block 0 = X₀ ∧ T.toChain.state 0 = X₀ := by
  obtain ⟨Cdist, hCdist, C, -, hC⟩ :=
    exists_blockSteps_of_astra_C11W5.{u} Dstar εReserve hDstar hεReserve cMax hcMax
  refine ⟨Cdist, hCdist, C, fun P g => ?_⟩
  obtain ⟨pBase, prepared, hbase, hdist, hres, hstep⟩ := hC P g
  obtain ⟨X₀, hX₀, hhist, hrad⟩ :=
    exists_inv_base_C11W Cdist cMax Dstar εReserve hcMax prepared hbase hdist hres
  exact ⟨pBase, X₀, hX₀, hhist, hrad,
    exists_chain_of_blockSteps_C11W hstep X₀ hX₀ hhist hrad⟩

/-- **A12 ⇐ astra step（BlockStep 路线）+ S8**（G2 主定理）：结论与 A12 逐字相同。唯一的数学前提是
S8 的 of_chain 绑定形：对以 seed 起头的 block tower 的 `toChain`，S8 在它自己的 tower 与对角 δ 上
成立（`Γ = (Cdist, C, pBase)` 是 Providers 的产出，在结论里不可命名，故 S8 对 Γ 全称，再限制到
SeedOK 的 `X₀` 与以它起头的 tower；这是 D-R-C11-3-10 的"合法但略强"形）。 -/
theorem a12_of_astra_blockSteps_C11W5 (P : OrientedThreeStage.{u}) (g : P.Metric)
    (Dstar εReserve : ℝ) (hDstar : 0 < Dstar) (hεReserve : 0 < εReserve)
    (cMax : ℝ) (hcMax : 0 < cMax)
    (hS8 : ∀ (Cdist : ℝ≥0) (C : ClosedBirthConstants) (pBase : CutoffParameters)
      (X₀ : BlockState_C11W pBase C P g 0),
      Inv_C11W Cdist cMax Dstar εReserve X₀ → X₀.history = RetainedCoreHistory.atZero P g →
      X₀.radius ≤ 1 →
      ∀ T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve, T.block 0 = X₀ →
        ∀ F : GC.Interface.RawSurgery P g, F.tower = T.toChain.tower →
          LargerBallScalarLargeSupply_C11S F (chainDiagonal_C11A T.toChain).delta
            (diagonalAccuracy_C11S (chainDiagonal_C11A T.toChain).delta)) :
    (∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Set.Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ) := by
  obtain ⟨Cdist, -, C, -, hC⟩ :=
    exists_blockSteps_of_astra_C11W5.{u} Dstar εReserve hDstar hεReserve cMax hcMax
  obtain ⟨pBase, prepared, hbase, hdist, hres, hstep⟩ := hC P g
  obtain ⟨X₀, hX₀, hhist, hrad⟩ :=
    exists_inv_base_C11W Cdist cMax Dstar εReserve hcMax prepared hbase hdist hres
  exact a12_of_blockSteps_C11W P g pBase C Cdist cMax Dstar εReserve X₀ hX₀ hhist hrad hstep
    fun T hT => hS8 Cdist C pBase X₀ hX₀ hhist hrad T hT

/-- consumer（不要 S8）：astra step 路线的产出 chain 给 W1 的十项（S1–S7、S9 的原料），且 chain 的
第 0 块就是 seed。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ (C : ClosedBirthConstants) (pBase : CutoffParameters)
      (S : PreparedSpatialChain pBase C P g) (F : GC.Interface.RawSurgery P g)
      (q : CutoffParameters) (κ : ℝ → ℝ) (records : CutoffRecords_C11S F q) (ε C1 C2 : ℝ),
      (S.state 0).history = RetainedCoreHistory.atZero P g ∧
      F.tower = S.tower ∧ CanonicalConstantsSupply_C11S ε C1 C2 ∧ (∀ t : ℝ, 0 < κ t) ∧
      Antitone κ ∧ AntitoneOn q.delta (Set.Ici 0) ∧ AntitoneOn q.neckRadius (Set.Ici 0) ∧
      HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 ∧
      (∀ (n : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) (n : ℝ) →
        (F.tower.history n).NoncollapsedBefore (κ t) ε t) ∧
      Filter.Tendsto q.delta Filter.atTop (nhds 0) ∧ RecentCutoffSupply_C11S records := by
  obtain ⟨_, -, C, hC⟩ :=
    exists_blockTower_of_astra_C11W5.{u} 1 1 one_pos one_pos 1 one_pos
  obtain ⟨pBase, X₀, -, hhist, -, T, -, h0⟩ := hC P g
  obtain ⟨F, q, κ, records, ε, C1, C2, hTower, -, hconst, hκ, hκanti, hδanti, hρanti, hcan,
    -, hnc, hδlim, hrecent⟩ := w1_of_preparedSpatialChain_C11A T.toChain
  have h00 : (T.toChain.state 0).history = RetainedCoreHistory.atZero P g := by
    rw [h0]
    exact hhist
  exact ⟨C, pBase, T.toChain, F, q, κ, records, ε, C1, C2, h00,
    hTower, hconst, hκ, hκanti, hδanti, hρanti, hcan, hnc, hδlim, hrecent⟩

/-- consumer：S8 取全称强形（对所有 `Γ`、所有 block tower）也走同一主定理——便利入口。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hS8 : ∀ (Cdist : ℝ≥0) (C : ClosedBirthConstants) (pBase : CutoffParameters)
      (T : BlockTower_C11W pBase C P g Cdist 1 1 1),
        ∀ F : GC.Interface.RawSurgery P g, F.tower = T.toChain.tower →
          LargerBallScalarLargeSupply_C11S F (chainDiagonal_C11A T.toChain).delta
            (diagonalAccuracy_C11S (chainDiagonal_C11A T.toChain).delta)) :
    (∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Set.Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ) :=
  a12_of_astra_blockSteps_C11W5 P g 1 1 one_pos one_pos 1 one_pos
    fun Cdist C pBase _ _ _ _ T _ => hS8 Cdist C pBase T

end GC.LongTime.Ch11

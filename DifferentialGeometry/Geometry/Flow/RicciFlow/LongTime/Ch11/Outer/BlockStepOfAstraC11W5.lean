import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Outer.TimeDerivativeMaintenanceC11W3
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialStep
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialProviders
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.ClosedBirthConstantsStrongC12X

set_option autoImplicit false

/-!
# S-CH11-W1L5 (G1)：astra step 主定理 ⇒ `hshape` ⇒ `∀ j, BlockStep_C11W j`（(F) 路线，`_C11W5`）

E1 闭包已落地：`SH/PreparedSpatialStep`（patched-at-path）与 `SH/PreparedSpatialProviders`
（shim → `PortC11P`）在树内。本文件用 astra 生产者实例化 OUTER 的 `blockStep_of_astraStepShape_C11W3`
的 `hshape` 前提（R-C11-3 D-8 三条验收，对照见下）。

* `hshape_of_astra_C11W5`：astra
  `exists_prepared_spatial_step_…_small_test_margin_with_reserve_quality`
  （`SH/PreparedSpatialStep` 末尾定理，下称 Step）在 `L := X`、`E = b_j = preparedSpatialHorizon j`、
  `B = 3^j`、`Bnext = 3^(j+1)`、`activation = (5/6)·3^j`、`η = 1/(j+2)` 处的 `makeCap` 支，
  逐字就是 `blockStep_of_astraStepShape_C11W3` 的 `hshape`（第二支 `∀ accuracyCap` 取出，
  `makeExact` 支不用）。`BlockLookahead_C11W` 打包 Step 的 `(nextClass, rNext)`。
* `blockStep_of_astra_C11W5`：`hshape_of_astra_C11W5` + `blockStep_of_astraStepShape_C11W3`
  ⇒ 第 `j` 块的 `BlockStep_C11W`；**不再有** `hshape` / `hderiv` 前提。前提只剩 Step 自己的
  provider 假设（`prepareClass` 与 `analytic`，类型与 Step / Providers 逐字同）。
* `blockSteps_of_astra_C11W5`：`∀ j` 版。
* `exists_blockSteps_of_astra_C11W5`（producer-closed）：`prepareClass` / `analytic` / `C` / `Cdist` /
  capacity 1 的 prepared class 全部由 Providers 的
  `exists_prepared_spatial_initial_state_with_distance_scalars_with_reserve_quality` 给出，量词顺序
  `∃ Cdist C, ∀ P g, ∃ pBase prepared, …（∀ j, BlockStep_C11W …）`（"uniform constants precede
  all data"，同 `exists_prepared_spatial_chains_from_initial_with_distance_scalars`）。
  `Dstar εReserve cMax` 只带正性，是 Step / Providers 自己的自由参数。

## 三条验收（R-C11-3 D-8 / rev2 §6）各自落在哪
1. **核完整类型**：`hshape_of_astra_C11W5` 的证明是 Step 结论的直接投影——`BlockState_C11W` 是
   `PreparedSpatialState pBase C P g (b_j) (3^j)` 的 abbrev（不是新结构），`Inv_C11W.distance`
   就是 Step 的 `hL : L.DistanceData Cdist`，`BlockLookahead_C11W` 的两字段类型就是 Step 的
   `ClosedBirthPreparedClass pBase C Pnext gnext (Bnext - b)` 与 `rNext : ℝ`，
   `Y : BlockState_C11W (j+1)` 与 Step 的 `R : PreparedSpatialState pBase C P g B Bnext` defeq
   （`preparedSpatialHorizon (j+1) = 3^j` 按定义展开）。类型对不上的话 `exact` 不会通过；
   没有用占位证明、`cast` 或 `Classical` 兜底。
2. **`∀ X, Inv → ∃ ℓ … ∀ req … ∃ Y d` 落在一般的 step theorem 而非 `∃ S`**：Step 本身是
   `∀ L (hL : L.DistanceData Cdist) …`，对**任意** `L`（不是 astra 自己选出来的某个 chain）；
   `blockStep_of_astra_C11W5` 的结论 `BlockStep_C11W … j` 是 `∀ X, Inv X → ∃ ℓ …` 的全称形。
   本文件**不**引用 `PreparedSpatialExistence` / `PreparedSpatialRecursion` 的任何 `∃ S` 结论。
3. **消费生产者**：`exists_blockSteps_of_astra_C11W5` 从 Providers 取 `prepareClass`、`analytic`、
   `C`、`Cdist`、prepared class，从 Step 取每块的 step，`BlockStep` / provider / class callback 都
   不是未支付前提。A12 consumer 见 `A12OfAstraBlockStepsC11W5`。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped NNReal

namespace GC.LongTime.Ch11

universe u

/-- **Step ⇒ `hshape`**：astra step 主定理在第 `j` 块的实例，结论逐字是
`blockStep_of_astraStepShape_C11W3` 的 `hshape`。`prepareClass` / `analytic` 是 Step 自己的
provider 假设（类型逐字同）。 -/
theorem hshape_of_astra_C11W5 (Dstar εReserve : ℝ) (hDstar : 0 < Dstar)
    (hεReserve : 0 < εReserve) (Cdist : ℝ≥0) {pBase : CutoffParameters}
    {C : ClosedBirthConstants} (cMax : ℝ) (hcMax : 0 < cMax)
    (prepareClass : PreparedDistanceClassProvider.{u} pBase.fixed pBase.recenterConstant Cdist)
    (analytic :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
      ∃ (qcan qs Qbirth δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
        0 < qcan ∧ qcan ≤ qs ∧ qs ≤ C.Cs * qcan ∧
        max 1 (max qcan qs) ≤ Qbirth ∧
        0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
        δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
      ∀ (K : RetainedCoreHistory.{u}) (_I : InitialIdentification P g K.toHistory)
        (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord K.toHistory i p),
        K.horizon ≤ B → K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
        K.NoncollapsedBefore κ C.epsilon K.horizon →
        NativeEstimates K C.epsilon C.C1 C.C2 C.C1s C.C2s qcan qs C.tauMin C.Ctime C.Cgrad ∧
        ∀ t : Icc (0 : ℝ) K.toHistory.horizon,
          (t : ℝ) < K.horizon → K.time (K.toHistory.activeStage t) = (t : ℝ) →
          K.toHistory.activeStage t ≠ 0 →
          ∀ y : (K.toHistory.stageAt t).Carrier,
            Qbirth < metricScalarAt (K.initialMetric (K.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (K.initialMetric (K.toHistory.activeStage t))
              C.epsilon C.Cbirth (max C.Cbirth (C.Cgrad : ℝ)) y, W.capTubeHasNeckChart C.epsilon)
    {P : OrientedThreeStage.{u}} {g : P.Metric} (j : ℕ) :
    ∀ X : BlockState_C11W pBase C P g j, X.DistanceData Cdist →
      ∃ ℓ : BlockLookahead_C11W X,
        ℓ.nextClass.HasReserveQuality Dstar εReserve ∧ ℓ.nextClass.HasDistanceExtension Cdist ∧
        0 < ℓ.rNext ∧ ℓ.rNext ≤ X.radius ∧ ℓ.nextClass.Qall ≤ (ℓ.rNext ^ 2)⁻¹ ∧
        ℓ.rNext * Real.sqrt ℓ.nextClass.Qall ≤ 100 * cMax ∧
        ∀ (εcut Dcut : ℝ) (mcut : ℕ), 0 < εcut → 0 < Dcut →
        ∀ accuracyCap : ℝ, 0 < accuracyCap →
          ∃ d : ℝ, 0 < d ∧ d < 1 ∧ d ≤ X.parameters.delta (preparedSpatialHorizon j) ∧
            d ≤ accuracyCap ∧
          ∃ Y : BlockState_C11W pBase C P g (j + 1),
            Y.radius = ℓ.rNext ∧ Y.shift = X.history.time (Fin.last X.history.eventCount) ∧
            Y.offset = X.history.eventCount ∧
            Y.nativeStage = X.native.stage (Fin.last X.native.eventCount) ∧
            HEq Y.nativeMetric (X.native.initialMetric (Fin.last X.native.eventCount)) ∧
            HEq Y.prepared ℓ.nextClass ∧ Y.DistanceData Cdist ∧
            PreparedSpatialSuccessor X Y ((5 / 6 : ℝ) * 3 ^ j) (1 / ((j : ℝ) + 2)) d ∧
            Nonempty (PreparedSpatialStepRetention X Y d (1 / ((j : ℝ) + 2)) εcut Dcut mcut) := by
  intro X hX
  obtain ⟨-, hEact, hact⟩ := blockActivation_mem_C11W j
  have hBB : (3 : ℝ) ^ j < (3 : ℝ) ^ (j + 1) := by
    have hp : (0 : ℝ) < 3 ^ j := pow_pos (by norm_num) j
    rw [pow_succ]
    linarith
  have hstep :=
    exists_prepared_spatial_step_with_quality_and_distance_scalars_and_small_test_margin_with_reserve_quality
      Dstar εReserve hDstar hεReserve Cdist pBase C cMax hcMax prepareClass analytic X hX
      (Bnext := (3 : ℝ) ^ (j + 1)) (activation := (5 / 6 : ℝ) * 3 ^ j)
      (eta := 1 / ((j : ℝ) + 2)) hBB hEact hact (by positivity)
  obtain ⟨nextClass, rNext, hres, hdist, hr, hrle, hQ, hfit, make⟩ := hstep
  refine ⟨⟨nextClass, rNext⟩, hres, hdist, hr, hrle, hQ, hfit, ?_⟩
  intro εcut Dcut mcut hε hD accuracyCap hcap
  exact (make εcut Dcut mcut hε hD).2 accuracyCap hcap

/-- **G1 主定理（条件形：astra 自己的 provider 假设）**：第 `j` 块的 `BlockStep_C11W`，由 Step 与
OUTER 的导数界维护（`blockStep_of_astraStepShape_C11W3`）给出，不再有 `hshape` / `hderiv`。 -/
theorem blockStep_of_astra_C11W5 (Dstar εReserve : ℝ) (hDstar : 0 < Dstar)
    (hεReserve : 0 < εReserve) (Cdist : ℝ≥0) {pBase : CutoffParameters}
    {C : ClosedBirthConstants} (cMax : ℝ) (hcMax : 0 < cMax)
    (prepareClass : PreparedDistanceClassProvider.{u} pBase.fixed pBase.recenterConstant Cdist)
    (analytic :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
      ∃ (qcan qs Qbirth δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
        0 < qcan ∧ qcan ≤ qs ∧ qs ≤ C.Cs * qcan ∧
        max 1 (max qcan qs) ≤ Qbirth ∧
        0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
        δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
      ∀ (K : RetainedCoreHistory.{u}) (_I : InitialIdentification P g K.toHistory)
        (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord K.toHistory i p),
        K.horizon ≤ B → K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
        K.NoncollapsedBefore κ C.epsilon K.horizon →
        NativeEstimates K C.epsilon C.C1 C.C2 C.C1s C.C2s qcan qs C.tauMin C.Ctime C.Cgrad ∧
        ∀ t : Icc (0 : ℝ) K.toHistory.horizon,
          (t : ℝ) < K.horizon → K.time (K.toHistory.activeStage t) = (t : ℝ) →
          K.toHistory.activeStage t ≠ 0 →
          ∀ y : (K.toHistory.stageAt t).Carrier,
            Qbirth < metricScalarAt (K.initialMetric (K.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (K.initialMetric (K.toHistory.activeStage t))
              C.epsilon C.Cbirth (max C.Cbirth (C.Cgrad : ℝ)) y, W.capTubeHasNeckChart C.epsilon)
    {P : OrientedThreeStage.{u}} {g : P.Metric} (j : ℕ) :
    BlockStep_C11W pBase C P g Cdist cMax Dstar εReserve j :=
  blockStep_of_astraStepShape_C11W3 j
    (hshape_of_astra_C11W5 Dstar εReserve hDstar hεReserve Cdist cMax hcMax prepareClass analytic j)

/-- `∀ j` 版（brief 的 `blockStep_of_astra_C11W5 : ∀ j, BlockStep_C11W j`）。 -/
theorem blockSteps_of_astra_C11W5 (Dstar εReserve : ℝ) (hDstar : 0 < Dstar)
    (hεReserve : 0 < εReserve) (Cdist : ℝ≥0) {pBase : CutoffParameters}
    {C : ClosedBirthConstants} (cMax : ℝ) (hcMax : 0 < cMax)
    (prepareClass : PreparedDistanceClassProvider.{u} pBase.fixed pBase.recenterConstant Cdist)
    (analytic :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
      ∃ (qcan qs Qbirth δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
        0 < qcan ∧ qcan ≤ qs ∧ qs ≤ C.Cs * qcan ∧
        max 1 (max qcan qs) ≤ Qbirth ∧
        0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
        δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
      ∀ (K : RetainedCoreHistory.{u}) (_I : InitialIdentification P g K.toHistory)
        (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord K.toHistory i p),
        K.horizon ≤ B → K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
        K.NoncollapsedBefore κ C.epsilon K.horizon →
        NativeEstimates K C.epsilon C.C1 C.C2 C.C1s C.C2s qcan qs C.tauMin C.Ctime C.Cgrad ∧
        ∀ t : Icc (0 : ℝ) K.toHistory.horizon,
          (t : ℝ) < K.horizon → K.time (K.toHistory.activeStage t) = (t : ℝ) →
          K.toHistory.activeStage t ≠ 0 →
          ∀ y : (K.toHistory.stageAt t).Carrier,
            Qbirth < metricScalarAt (K.initialMetric (K.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (K.initialMetric (K.toHistory.activeStage t))
              C.epsilon C.Cbirth (max C.Cbirth (C.Cgrad : ℝ)) y, W.capTubeHasNeckChart C.epsilon)
    {P : OrientedThreeStage.{u}} {g : P.Metric} :
    ∀ j : ℕ, BlockStep_C11W pBase C P g Cdist cMax Dstar εReserve j :=
  fun j => blockStep_of_astra_C11W5 Dstar εReserve hDstar hεReserve Cdist cMax hcMax prepareClass
    analytic j

/-- **G1 producer-closed 形**：Providers 先给统一常数 `Cdist`、`C`（在任何 `P g` 之前），再对每个
`P g` 给 `pBase` 与 capacity 1 的 prepared class（`prepared.parameters = pBase`、distance rule、
reserve quality），并且对该 `pBase` **每一块**的 `BlockStep_C11W` 成立。`prepareClass` / `analytic`
是 Providers 的产出，不是前提（`pBase.fixed = fixed`、`pBase.recenterConstant = recenter` 把
`PreparedDistanceClassProvider fixed recenter` 改写成 `pBase` 版）。 -/
theorem exists_blockSteps_of_astra_C11W5 (Dstar εReserve : ℝ) (hDstar : 0 < Dstar)
    (hεReserve : 0 < εReserve) (cMax : ℝ) (hcMax : 0 < cMax) :
    ∃ Cdist : ℝ≥0, 1 ≤ Cdist ∧ ∃ C : ClosedBirthConstants,
    C.epsilon ≤ DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.εStrong_C12X.{u} ∧
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric),
    ∃ (pBase : CutoffParameters) (prepared : ClosedBirthPreparedClass pBase C P g 1),
      prepared.parameters = pBase ∧ prepared.HasDistanceExtension Cdist ∧
      prepared.HasReserveQuality Dstar εReserve ∧
      ∀ j : ℕ, BlockStep_C11W pBase C P g Cdist cMax Dstar εReserve j := by
  obtain ⟨Cdist, hCdist, fixed, recenter, C, hεs, -, prepareClass, analytic, initial⟩ :=
    exists_closedBirthConstants_strong_C12X.{u} Dstar εReserve hDstar hεReserve
  refine ⟨Cdist, hCdist, C, hεs, fun P g => ?_⟩
  obtain ⟨pBase, prepared, -, hres, -, hfixed, hrc, hbase, hdist, -⟩ := initial P g
  have hprep : PreparedDistanceClassProvider.{u} pBase.fixed pBase.recenterConstant Cdist := by
    rw [hfixed, hrc]
    exact prepareClass
  exact ⟨pBase, prepared, hbase, hdist, hres,
    blockSteps_of_astra_C11W5 Dstar εReserve hDstar hεReserve Cdist cMax hcMax hprep analytic⟩

end GC.LongTime.Ch11

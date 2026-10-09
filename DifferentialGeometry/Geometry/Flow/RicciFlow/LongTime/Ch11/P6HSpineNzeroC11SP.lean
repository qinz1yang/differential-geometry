import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HSpineNativeOnlyC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeOnlyNzeroC11SP

set_option autoImplicit false

/-!
# hspine‴ 换槽 hnreg → hnzero（O-CH11-SPINE-C2 G1，后缀 `_C11SP`；R-C11-19 主对象）

结论 = 合同 def `HSpineTwoLevelTime_C11G7B P g` 本身：
`hspineTwoLevelTime_of_hnzero_C11SP P g hnzero :=
  hspineTwoLevelTime_of_hnreg_C11SP P g (native_hnreg_of_hnzero_C11SP P g hnzero)`。
* SPINE-C G5 `hspineTwoLevelTime_of_hnreg_C11SP`（guard 支 = A2 G4 PROVED；glue = C0；常数 / 量词序 /
  TimeCore 实例化 = SPINE-C G1）原样调用，不改；
* SPINE-B G8 `native_hnreg_of_hnzero_C11SP`（无额外参数；`hguardΛ` 在其体内由 SPINE-A1 G6
  `guard_regime_false_final_bdd_C11SP` 付，`∃ Λ, ∃ᶠ i, nr ≤ Λ r` / `r / nr → 0` 二分）付 `hnreg` 槽。
**sha 断言（生成器 gen_c2.py 机械核对，不是目测）**：
* G5 的 `hnreg` binder 体（`P6HSpineNativeOnlyC11SP.lean` l.41–69，去 4 格缩进、去末尾 `) :`）与
  G8 `native_hnreg_of_hnzero_C11SP` 的结论（`P6NativeOnlyNzeroC11SP.lean` l.67–95，去 ` := by`）
  逐字相同，sha256 = `7c14a2e7c7b5ec56…`；
* 下面 `hnzero` binder 逐字切自 G8 l.36–66（G8a / G8b 同文），
  sha256 = `888045562c9716f9…`；
  源文件 sha256：G8 = `5d2c85de6e352add…`，G5 = `771d97f4769e8a58…`。
**唯一剩余 binder** `hnzero`（owner SPINE-B；OPEN）：regular 时刻、`r / nr → 0` 的 native 子情形；
repair target（SPINE-B state G4b / HANDOVER v2）= (D4′) buffer no-shortcut 余 binder
`hdisj` + `hshort`、窗内大 cap crossing 计数 `≤ n₀`、NJ 装配（SL2 = SPINE-B G3 / G6 / G7 已 PROVED）。
块标 **PROVISIONAL[hnzero]**。
consumer：`a12EnhancedFull_of_hnzero_C11SP`（CODEX-C §2.3 验收形，`hp` 作 binder）。
生成：build-logs/scratch/O-CH11-SPINE-C2/gen_c2.py。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

/-- **G1 `hspineTwoLevelTime_of_hnzero_C11SP`（PROVISIONAL[hnzero]）**：见文件头。 -/
theorem hspineTwoLevelTime_of_hnzero_C11SP (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hnzero :
        ∃ ε₀ : ℝ, 0 < ε₀ ∧
          ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
            {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
            (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
            (q : CutoffParameters), F.tower = S.tower →
            (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
              q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
            pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
            2 ≤ pBase.modelOrder → CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
            ε ≤ coneAccuracy →
            C1ceil_C11SC.{u} Γf ≤ C1 → C2ceil_C11SC.{u} Γf ≤ C2 →
          ∀ A : ℝ, 0 < A →
          ∀ idx : ℕ → ℕ,
          let H : ℕ → ObservedHistory.{u} := fun i => (F.tower.history (idx i)).toHistory
          ∀ (t : ∀ i, Icc (0 : ℝ) (H i).horizon) (s : ℕ → RegularSlice F.observation),
            (∀ i, (s i).time = (t i : ℝ)) →
          ∀ (p x : ∀ i, ((H i).stageAt (t i)).Carrier) (r : ℕ → ℝ),
            (∀ i, 2 * r i ^ 2 < (t i : ℝ)) →
            (∀ i, hasSmallParabolicCurvature (H i) (t i) (p i) (r i)) →
            (∀ i, ENNReal.ofReal (A⁻¹ * r i ^ 3) ≤
              ballVolume ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (r i)) →
            (∀ i, x i ∈ riemannianBallOf
              ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (A * r i)) →
            Tendsto (fun i => (t i : ℝ)) atTop atTop →
            Tendsto (fun i => metricScalarAt
              ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (x i) * r i ^ 2) atTop atTop →
            (∀ i, r i < q.neckRadius (t i)) →
            Tendsto (fun i => r i / q.neckRadius (t i)) atTop (𝓝 0) →
            Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0) →
          False) :
    HSpineTwoLevelTime_C11G7B.{u} P g :=
  hspineTwoLevelTime_of_hnreg_C11SP P g (native_hnreg_of_hnzero_C11SP P g hnzero)

/-- **consumer（CODEX-C §2.3 验收形）**：`hp : HP6bTwoLevelTime_C11G7B` 作 binder；spine 侧只剩 `hnzero`。 -/
theorem a12EnhancedFull_of_hnzero_C11SP (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hnzero :
        ∃ ε₀ : ℝ, 0 < ε₀ ∧
          ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
            {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
            (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
            (q : CutoffParameters), F.tower = S.tower →
            (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
              q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
            pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
            2 ≤ pBase.modelOrder → CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
            ε ≤ coneAccuracy →
            C1ceil_C11SC.{u} Γf ≤ C1 → C2ceil_C11SC.{u} Γf ≤ C2 →
          ∀ A : ℝ, 0 < A →
          ∀ idx : ℕ → ℕ,
          let H : ℕ → ObservedHistory.{u} := fun i => (F.tower.history (idx i)).toHistory
          ∀ (t : ∀ i, Icc (0 : ℝ) (H i).horizon) (s : ℕ → RegularSlice F.observation),
            (∀ i, (s i).time = (t i : ℝ)) →
          ∀ (p x : ∀ i, ((H i).stageAt (t i)).Carrier) (r : ℕ → ℝ),
            (∀ i, 2 * r i ^ 2 < (t i : ℝ)) →
            (∀ i, hasSmallParabolicCurvature (H i) (t i) (p i) (r i)) →
            (∀ i, ENNReal.ofReal (A⁻¹ * r i ^ 3) ≤
              ballVolume ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (r i)) →
            (∀ i, x i ∈ riemannianBallOf
              ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (A * r i)) →
            Tendsto (fun i => (t i : ℝ)) atTop atTop →
            Tendsto (fun i => metricScalarAt
              ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (x i) * r i ^ 2) atTop atTop →
            (∀ i, r i < q.neckRadius (t i)) →
            Tendsto (fun i => r i / q.neckRadius (t i)) atTop (𝓝 0) →
            Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0) →
          False)
    (hp : HP6bTwoLevelTime_C11G7B.{u} P g) :
    A12EnhancedFullConclusion_C11F P g :=
  a12EnhancedFull_of_v7two_contracts_C11G7B P g (hspineTwoLevelTime_of_hnzero_C11SP P g hnzero) hp

end GC.LongTime.Ch11

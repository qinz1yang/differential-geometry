import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HSpineTwoLevelTimeGlueC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GuardRegimeFalseC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeExcludeC11SP

set_option autoImplicit false

/-!
# hspine‴ 只剩 native（O-CH11-SPINE-C G5，后缀 `_C11SP`；R-C11-19 主对象）

结论 = 合同 def `HSpineTwoLevelTime_C11G7B P g` 本身。相对 G4 `hspineTwoLevelTime_final_C11SP`：
* `hguard` ⇐ SPINE-A2 G4 `guard_regime_false_final_C11SP P g`（**PROVED，无 binder**；陈述逐字 =
  CODEX-C §3.3；链 = G55 → G54 / G56 / G58（G60 体）→ A1 G4 二次 blow-up 反向极限 → A2 exclusion）
  ⇒ G4 的 `hflowA1` 消去；
* `hnative` ⇐ SPINE-B G2 `native_regime_false_C11SP P g hguardT1 hnreg`，`hguardT1` 用同一个
  `guard_regime_false_final_C11SP P g` 付清；
* glue ⇐ C0 `regime_glue_C11SP`（经 G3 `hspineTwoLevelTime_of_regimes_C11SP`）。
**唯一剩余 binder** `hnreg`（owner SPINE-B 路线 B；状态 OPEN）：CODEX-C §3.4 陈述体在 regular 时刻
（`s : ℕ → RegularSlice F.observation`，`(s i).time = t i`）的形，文本逐字切自 `P6NativeExcludeC11SP.lean`；
无 producer 的一环 = NJ（native 第一层整内球 jets）+ SL1（native surgery distance control）+ SL2（trace
坐标 product domain），见 build-logs/scratch/O-CH11-SPINE-B/native-route.md。块标 **PROVISIONAL[hnreg]**。
consumer：`a12EnhancedFull_of_hnreg_C11SP`（CODEX-C §2.3 验收形，`hp` 作 binder）。
生成：build-logs/scratch/O-CH11-SPINE-C/gen_g5.py。
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

/-- **G5 `hspineTwoLevelTime_of_hnreg_C11SP`（PROVISIONAL[hnreg]）**：见文件头。 -/
theorem hspineTwoLevelTime_of_hnreg_C11SP (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hnreg :
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
            Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0) →
          False) :
    HSpineTwoLevelTime_C11G7B.{u} P g :=
  hspineTwoLevelTime_of_regimes_C11SP P g (guard_regime_false_final_C11SP P g)
    (native_regime_false_C11SP P g (guard_regime_false_final_C11SP P g) hnreg)

/-- **consumer（CODEX-C §2.3 验收形）**：`hp : HP6bTwoLevelTime_C11G7B` 作 binder；spine 侧只剩 `hnreg`。 -/
theorem a12EnhancedFull_of_hnreg_C11SP (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hnreg :
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
            Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0) →
          False)
    (hp : HP6bTwoLevelTime_C11G7B.{u} P g) :
    A12EnhancedFullConclusion_C11F P g :=
  a12EnhancedFull_of_v7two_contracts_C11G7B P g (hspineTwoLevelTime_of_hnreg_C11SP P g hnreg) hp

end GC.LongTime.Ch11

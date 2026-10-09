import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12GapTopV7TwoC11G7B

set_option autoImplicit false

/-!
# hspine‴ 装配（O-CH11-SPINE-C G1，后缀 `_C11SP`；CODEX-C §3.5 任务 3）

**G1 `hspineTwoLevelTime_C11SP`**：结论类型 = 合同 def `HSpineTwoLevelTime_C11G7B P g` 本身（F1：不是裸
`TimeCore → LargerBallScalarAt`）。装配 = by_contra + regime 二分 + 两侧矛盾，binder **逐字**：
* `hglue`（C0 `P6RegimeGlueC11SP` 未交付时的显式 binder）：对 `¬ LargerBallScalarAt_C11S` 给重索引坏序列，
  字段 = T1 / T2 的序列前提（CODEX-C §3.2(a)），并带 guard / native 二分
  `(∀ i, nr(t i) ≤ r i) ∨ (∀ i, r i < nr(t i))`；
* `hguard` = CODEX-C §3.3 `guard_regime_false_CXSP` 的陈述体逐字（SPINE-A1/A2 的目标）；
* `hnative` = CODEX-C §3.4 `native_regime_false_CXSP` 的陈述体逐字（SPINE-B 的目标）。
量词序（核对表 C1–C12）：
* C1 / F7：`εsp := fun _ _ => min ε₀g ε₀n` 取自两个 `∃ ε₀`，在 `∀ pB Γ Γf` 与 `∀ A` 之前；
* C2：`FineOf` 只用于 native 侧 `C1ceil Γf ≤ C1P6 std Γ`、`C2ceil Γf ≤ C2P6 std Γ`；
* C3：TimeCore 原样在粗 `Γ` 的 `(Γ.epsilon, C1P6 std, C2P6 std, p6Ctime Γ)`，链仍 over 细 `Γf`；
* C4：hdiag / `F.tower = S.tower` 原样转交；C5：accuracy 经 `min_le_left/right`；
* C6 / F6：`hw` 保留 binder、不消费；C7：无 `Awork`；C8 / F4：无 Budget / SCRS⁺ / hTD / BlockTower；
* C9 / F11：不 unfold 常数；C10：`.{u}` 同合同；C11：装配层不排除任何 `t`（含 surgery 时刻、horizon）；
* C12：`∃ rbar K` 只来自 `by_contra`，装配层不另造常数。
块标 **PROVISIONAL[hglue (C0), hguard (A), hnative (B)]**。
生成：build-logs/scratch/O-CH11-SPINE-C/gen_g1.py。
-/

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped NNReal Topology ContDiff Manifold ENNReal

namespace GC.LongTime.Ch11

universe u

/-- **G1 `hspineTwoLevelTime_C11SP`（PROVISIONAL[hglue, hguard, hnative]）**：三 binder 逐字（见文件头）⇒
合同 `HSpineTwoLevelTime_C11G7B P g`。`εsp` 是常值 `min ε₀g ε₀n`（只依赖 `P g`，不依赖 `Γ Γf A`）。 -/
theorem hspineTwoLevelTime_C11SP (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hglue : ∀ {pB : CutoffParameters} {Γf : ClosedBirthConstants}
      (S : PreparedSpatialChain pB Γf P g) (F : GC.Interface.RawSurgery P g)
      (q : CutoffParameters), F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      ∀ A : ℝ, 0 < A →
      ¬ LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A →
      ∃ idx : ℕ → ℕ,
      let H : ℕ → ObservedHistory.{u} := fun i => (F.tower.history (idx i)).toHistory
      ∃ (t : ∀ i, Icc (0 : ℝ) (H i).horizon)
        (p x : ∀ i, ((H i).stageAt (t i)).Carrier) (r : ℕ → ℝ),
        (∀ i, 2 * r i ^ 2 < (t i : ℝ)) ∧
        (∀ i, hasSmallParabolicCurvature (H i) (t i) (p i) (r i)) ∧
        (∀ i, ENNReal.ofReal (A⁻¹ * r i ^ 3) ≤
          ballVolume ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (r i)) ∧
        (∀ i, x i ∈ riemannianBallOf
          ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (A * r i)) ∧
        Tendsto (fun i => (t i : ℝ)) atTop atTop ∧
        Tendsto (fun i => metricScalarAt
          ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (x i) * r i ^ 2) atTop atTop ∧
        ((∀ i, q.neckRadius (t i) ≤ r i) ∨ (∀ i, r i < q.neckRadius (t i))) ∧
        Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0))
    (hguard :
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
        ∀ A : ℝ, 0 < A →
        ∀ idx : ℕ → ℕ,
        let H : ℕ → ObservedHistory.{u} := fun i => (F.tower.history (idx i)).toHistory
        ∀ (t : ∀ i, Icc (0 : ℝ) (H i).horizon)
          (p x : ∀ i, ((H i).stageAt (t i)).Carrier) (r : ℕ → ℝ),
          (∀ i, 2 * r i ^ 2 < (t i : ℝ)) →
          (∀ i, hasSmallParabolicCurvature (H i) (t i) (p i) (r i)) →
          (∀ i, ENNReal.ofReal (A⁻¹ * r i ^ 3) ≤
            ballVolume ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (r i)) →
          (∀ i, x i ∈ riemannianBallOf
            ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (A * r i)) →
          Tendsto (fun i => (t i : ℝ)) atTop atTop →
          Tendsto (fun i => metricScalarAt
            ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (x i) * r i ^ 2) atTop atTop →
          (∀ i, q.neckRadius (t i) ≤ r i) →
          Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0) →
        False)
    (hnative :
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
        ∀ (t : ∀ i, Icc (0 : ℝ) (H i).horizon)
          (p x : ∀ i, ((H i).stageAt (t i)).Carrier) (r : ℕ → ℝ),
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
    HSpineTwoLevelTime_C11G7B.{u} P g := by
  obtain ⟨ε₀g, hε₀g, hg⟩ := hguard
  obtain ⟨ε₀n, hε₀n, hn⟩ := hnative
  refine ⟨fun _ _ => min ε₀g ε₀n, fun _ _ => lt_min hε₀g hε₀n, ?_⟩
  intro pB Γ Γf hFine S F q hTower hdiag hacc hrad hord A hA _hw hcore
  have hA0 : 0 < A := zero_lt_one.trans hA
  have haccg : pB.modelAccuracy ≤ ε₀g := hacc.trans (min_le_left _ _)
  have haccn : pB.modelAccuracy ≤ ε₀n := hacc.trans (min_le_right _ _)
  have hC1 : C1ceil_C11SC.{u} Γf ≤ C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ :=
    hFine.2.1.trans (C1ceil_le_C1P6_C11GT6 _ Γ)
  have hC2 : C2ceil_C11SC.{u} Γf ≤ C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ :=
    hFine.2.2.1.trans (C2ceil_le_C2P6_C11GT6 _ Γ)
  by_contra hnot
  obtain ⟨idx, t, p, x, r, h2r, hsmall, hvol, hx, htime, hesc, hreg, hratio⟩ :=
    hglue S F q hTower hdiag A hA0 hnot
  rcases hreg with hgd | hnat
  · exact hg S F q hTower hdiag haccg hrad hord hcore Γ.epsilon_cone A hA0 idx t p x r
      h2r hsmall hvol hx htime hesc hgd hratio
  · exact hn S F q hTower hdiag haccn hrad hord hcore Γ.epsilon_cone hC1 hC2 A hA0 idx t p x r
      h2r hsmall hvol hx htime hesc hnat hratio

/-- **consumer（CODEX-C §2.3 验收形）**：G1 喂合同形 consumer `a12EnhancedFull_of_v7two_contracts_C11G7B`；
`hp : HP6bTwoLevelTime_C11G7B` 作 binder（ch8 的 OPEN 输入），G1 的三个 binder 原样上提。 -/
theorem a12EnhancedFull_of_regimes_C11SP (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hglue : ∀ {pB : CutoffParameters} {Γf : ClosedBirthConstants}
      (S : PreparedSpatialChain pB Γf P g) (F : GC.Interface.RawSurgery P g)
      (q : CutoffParameters), F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      ∀ A : ℝ, 0 < A →
      ¬ LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A →
      ∃ idx : ℕ → ℕ,
      let H : ℕ → ObservedHistory.{u} := fun i => (F.tower.history (idx i)).toHistory
      ∃ (t : ∀ i, Icc (0 : ℝ) (H i).horizon)
        (p x : ∀ i, ((H i).stageAt (t i)).Carrier) (r : ℕ → ℝ),
        (∀ i, 2 * r i ^ 2 < (t i : ℝ)) ∧
        (∀ i, hasSmallParabolicCurvature (H i) (t i) (p i) (r i)) ∧
        (∀ i, ENNReal.ofReal (A⁻¹ * r i ^ 3) ≤
          ballVolume ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (r i)) ∧
        (∀ i, x i ∈ riemannianBallOf
          ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (A * r i)) ∧
        Tendsto (fun i => (t i : ℝ)) atTop atTop ∧
        Tendsto (fun i => metricScalarAt
          ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (x i) * r i ^ 2) atTop atTop ∧
        ((∀ i, q.neckRadius (t i) ≤ r i) ∨ (∀ i, r i < q.neckRadius (t i))) ∧
        Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0))
    (hguard :
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
        ∀ A : ℝ, 0 < A →
        ∀ idx : ℕ → ℕ,
        let H : ℕ → ObservedHistory.{u} := fun i => (F.tower.history (idx i)).toHistory
        ∀ (t : ∀ i, Icc (0 : ℝ) (H i).horizon)
          (p x : ∀ i, ((H i).stageAt (t i)).Carrier) (r : ℕ → ℝ),
          (∀ i, 2 * r i ^ 2 < (t i : ℝ)) →
          (∀ i, hasSmallParabolicCurvature (H i) (t i) (p i) (r i)) →
          (∀ i, ENNReal.ofReal (A⁻¹ * r i ^ 3) ≤
            ballVolume ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (r i)) →
          (∀ i, x i ∈ riemannianBallOf
            ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (A * r i)) →
          Tendsto (fun i => (t i : ℝ)) atTop atTop →
          Tendsto (fun i => metricScalarAt
            ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (x i) * r i ^ 2) atTop atTop →
          (∀ i, q.neckRadius (t i) ≤ r i) →
          Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0) →
        False)
    (hnative :
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
        ∀ (t : ∀ i, Icc (0 : ℝ) (H i).horizon)
          (p x : ∀ i, ((H i).stageAt (t i)).Carrier) (r : ℕ → ℝ),
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
  a12EnhancedFull_of_v7two_contracts_C11G7B P g
    (hspineTwoLevelTime_C11SP P g hglue hguard hnative) hp

end GC.LongTime.Ch11

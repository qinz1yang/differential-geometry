import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeForwardC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LateTimeCoreDefP6TC
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12OfNarrowTupleC11A
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.EnhancedProfileDefsC11E
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongCeilingStarC11SC

set_option autoImplicit false

/-!
# native 分支到 `False`（O-CH11-SPINE-B G2，后缀 `_C11SP`；CODEX-C §3.4 任务 2）

**`native_regime_false_C11SP`**：结论（`:` 之后）逐字 = CODEX-C §3.4 `native_regime_false_CXSP`
的陈述体（脚本从 `CH8-HANDOVER-TO-CODEX-20261007-C.md` 切出，只改后缀）。
块标 **PROVISIONAL[hguardT1, hnreg]**：
* `hguardT1` = CODEX-C §3.3 `guard_regime_false_CXSP` 陈述体逐字（SPINE-A1/A2 目标
  `guard_regime_false_C11SP`）；
* `hnreg` = §3.4 陈述体，仅在 `t` 之后插入 RegularSlice 两行
  `(s : ℕ → RegularSlice F.observation)`、`(∀ i, (s i).time = (t i : ℝ))`——即 **native 坏序列
  只需在 regular 时刻处理**；repair target = Codex 交接的路线 B（局部 Shi + newborn jets reset），
  其合同形（native 第一层整内球 jets）与两条新子引理见
  `build-logs/scratch/O-CH11-SPINE-B/native-route.md` §N1。
证明 = G1 `native_forward_split_C11SP`（G65 + 无穷鸽巢）：guard 支喂 `hguardT1`
（`A := 32768·e³·A`，任意时刻含 birth / horizon），native 支喂 `hnreg`。
`ε₀ := min ε₁ ε₂`，在 `∀ A` 之前。T2 的 native 前提 `r < nr(t)` **不被消费**（归约对任意坏序列成立）。
不新增具名 Prop；无 Budget / SCRS⁺ / hTD / κ 窗 / δ 窗（F4/F9）；不 unfold 常数（F11）。
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

/-- **G2（PROVISIONAL[hguardT1, hnreg]）**：native 分支到 `False`；结论逐字 = CODEX-C §3.4。 -/
theorem native_regime_false_C11SP
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hguardT1 :
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
      False := by
  obtain ⟨ε₁, hε₁, hg⟩ := hguardT1
  obtain ⟨ε₂, hε₂, hn⟩ := hnreg
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hcore hε hC1 hC2 A hA idx H
    t p x r htime hsmall hvol hx hlate hescape _hnative hratio
  obtain ⟨N, τ, s, p', x', ρ, hs, htime', hsmall', hvol', hx', hτ, hR, hρ, hsplit⟩ :=
    native_forward_split_C11SP F q A hA idx t p x r htime hsmall hvol hx hlate hescape hratio
  have hA' : 0 < 32768 * Real.exp 3 * A := by positivity
  rcases hsplit with hgd | hnt
  · exact hg S F q hTower hdiag (hacc.trans (min_le_left _ _)) hrad hord hcore hε _ hA' N τ
      p' x' ρ htime' hsmall' hvol' hx' hτ hR hgd hρ
  · exact hn S F q hTower hdiag (hacc.trans (min_le_right _ _)) hrad hord hcore hε hC1 hC2 _
      hA' N τ s hs p' x' ρ htime' hsmall' hvol' hx' hτ hR hnt hρ

end GC.LongTime.Ch11

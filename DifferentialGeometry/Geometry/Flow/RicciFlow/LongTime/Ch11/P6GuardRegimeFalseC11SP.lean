import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GuardFlowAssembleC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GuardSecondFlowC11SP

/-!
# O-CH11-SPINE-A2 G4：guard 分支到 `False`，无 binder（CODEX-C §3.3 任务 1 收口，`_C11SP`）

链：G55 → G54 / G56 / G58（G60 证明体，A2 G3a 内联扩输出）→ SPINE-A1 G4
`guard_secondBlowupFlow_C11SP`（cone 端点点列处二次 blow-up 反向极限，PROVED）→ A2 G3a
`guard_flowAtConePoints_C11SP`（= `hflowA1`）→ SPINE-A1 G1 `guard_puncturedConeEnd_v2_C11SP`
（= `hconeA1`）→ A2 G1a `guard_cone_flow_exclusion_C11SP`（树内 `solution_not_rescaled_cone_limit`）。
结论（`:` 之后）逐字 = CODEX-C §3.3 `guard_regime_false_CXSP`，只改名（后缀 `_C11SP`；
`guard_regime_false_C11SP` 已是 G1 的带 binder 版，故此处加 `final`）。
-/

set_option autoImplicit false
noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

/-- **G4（PROVED）**：guard 分支（`nr(t) ≤ r`）的坏序列不存在。陈述体逐字 = CODEX-C §3.3。 -/
theorem guard_regime_false_final_C11SP
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
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
      False :=
  guard_regime_false_of_secondFlow_C11SP P g (guard_secondBlowupFlow_C11SP P g)

end GC.LongTime.Ch11

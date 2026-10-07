import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.AttainedPhysicalSupport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.C1Attainment
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowActionRegularCrossingRecenter
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryPartition

/-!
# S-CH11-FIX9 port of astra `ControlledPolePhysicalSupport`（`PortC11P`）

来源：donor `ControlledPolePhysicalSupport.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败。本 port 只有 elaboration 层面修补（no statement / definition /
proof idea altered；不加 `set_option`）：
* `/-- docstring -/ attribute [-instance] … in theorem` 的顺序对调（docstring 不能放在
  `attribute … in` 前面）；
* 陈述里的 `ℝ≥0` 需要 `open scoped NNReal`（donor 漏开，`LE Type / OfNat Type 0`）→ 在已有的
  `open scoped` 行补上 `NNReal`；
* 陈述里未被引用的 binder `identification` → `_identification`（unusedVariables）。

原路径 `ControlledPolePhysicalSupport` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open Set Filter _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators NNReal

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- Uniform cap-action thresholds on a fixed query box produce one actual
fixed-endpoint minimizing curve and physical cost supports for that same curve.
The original initial-metric parameter and its preservation callback precede all
query choices. No free-endpoint minimum or vanishing-velocity condition is used. -/
theorem exists_uniform_physical_cost_support_on_action_sublevel
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    ∃ a₀ : ℝ, 0 < a₀ ∧
    (∀ (H : ObservedHistory.{u}) (_ : InitialIdentification P₀ g₀ H),
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) ∧
        ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) ∧
    ∀ (Aact E rTerm qDeriv ρ : ℝ) (Cderiv : ℝ≥0),
      0 ≤ E → 0 < rTerm → 0 < qDeriv → 0 < ρ →
    ∃ (m₀ : ℕ) (R₀ ε₀ δ₀ : ℝ), 0 < R₀ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters),
      m₀ ≤ parameters.modelOrder → R₀ ≤ parameters.modelRadius →
      parameters.modelAccuracy ≤ ε₀ →
      (∀ i : Fin H.eventCount,
        parameters.recenterConstant * parameters.delta (H.time i.succ) ≤ 1 / 2) →
      (∀ i : Fin H.eventCount, parameters.delta (H.time i.succ) ≤ δ₀) →
      (∀ i : Fin H.eventCount, parameters.neckRadius (H.time i.succ) ≤ ρ) →
    ∀ (records : ∀ i, GeometricCutoffRecord H i parameters)
      (_identification : InitialIdentification P₀ g₀ H)
      (t : Icc (0 : ℝ) H.horizon),
      (∀ (j : Fin (H.eventCount + 1)) (y : (H.stage j).Carrier),
        ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s < t.val →
          qDeriv < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun z => metricScalarAt (H.stageMetric j z) y) (Iic s) s| ≤
              Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) →
    ∀ (p : (H.stageAt t).Carrier), H.isParabolicallyRmControlledBall t p rTerm →
    ∀ (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t) (v : ℝ),
      0 < v → v ≤ E → H.time (H.activeStage t) < t.val →
      t.val - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first) →
      (∀ (i : Fin H.eventCount), first ≤ i.castSucc → i.succ ≤ H.activeStage t →
        ∀ b : (H.event i).RetainedBoundaryIndex, ((records i).static b).hasCanonicalWindow) →
    ∀ q : (H.stage first).Carrier,
      H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0 v p q <
        (Aact : WithTop ℝ) →
    ∃ gamma : (j : H.StageInterval first (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) ∧
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ∧
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j)) volume
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ∧
      gamma ⟨H.activeStage t, hle, le_rfl⟩ 0 = p ∧
      gamma ⟨first, le_rfl, hle⟩ v = q ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t),
        ∃ z : (H.event i).old,
          z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)) ∧
          (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time i.succ))) ∧
      H.regularizedExtendedAction first (H.activeStage t) t.val (3 / a₀) 0 v gamma =
        H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0 v p q ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t),
        (H.event i).RegularCrossing
          (gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)))
          (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time i.succ)))) ∧
    ∀ etaError : ℝ, 0 < etaError →
    let jf : H.StageInterval first (H.activeStage t) := ⟨first, le_rfl, hle⟩;
    let jl : H.StageInterval first (H.activeStage t) := ⟨H.activeStage t, hle, le_rfl⟩;
    let q := gamma jf v;
    let Loriginal := ∑ x : H.StageInterval first (H.activeStage t),
      H.stageRegularizedAction x.val t.val (gamma x)
        (H.regularizedStageStart t.val 0 x.val) (H.regularizedStageEnd t.val v x.val);
    let gOriginal := H.stageMetric first (t.val - v ^ 2);
    let Vorig : TangentSpace ThreeModel q := lVelocity (I := ThreeModel) (gamma jf) v;
    let Roriginal := metricScalarAt gOriginal q;
    ∃ (U : Set ((H.stage first).Carrier × ℝ)) (F : (H.stage first).Carrier × ℝ → ℝ),
      IsOpen U ∧ (q, v) ∈ U ∧
      ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 F U ∧
      F (q, v) = Loriginal ∧
      H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0 v (gamma jl 0) q = (F (q, v) : WithTop ℝ) ∧
      (∀ z ∈ U, H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0 z.2 (gamma jl 0) z.1 ≤
        (F z : WithTop ℝ)) ∧
      gradientFun gOriginal (fun y => F (y, v)) q = Vorig ∧
      HasDerivAt (fun w => F (q, w))
        (2 * v ^ 2 * Roriginal - (1 / 2 : ℝ) * gOriginal.inner q Vorig Vorig) v ∧
      laplacian (LeviCivita gOriginal) gOriginal (fun y => F (y, v)) q <
        3 / v - v * Roriginal - Loriginal / (2 * v ^ 2) +
          gOriginal.inner q Vorig Vorig / (4 * v) + etaError / (2 * v) ∧
    let Omega : Set ((H.stage first).Carrier × ℝ) :=
      {z | z.2 < t.val ∧ z.2 ∈ Ioo (H.time first) (H.stageEndTime first) ∧
        (z.1, Real.sqrt (t.val - z.2)) ∈ U};
    let Aphys : (H.stage first).Carrier × ℝ → ℝ :=
      fun z => 2 * Real.sqrt (t.val - z.2) * F (z.1, Real.sqrt (t.val - z.2));
    IsOpen Omega ∧ (q, t.val - v ^ 2) ∈ Omega ∧
      ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 Aphys Omega ∧
      Aphys (q, t.val - v ^ 2) = 2 * v * Loriginal ∧
      (∀ z ∈ Omega, ∃ cost : ℝ,
        H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0 (Real.sqrt (t.val - z.2))
          (gamma jl 0) z.1 = (cost : WithTop ℝ) ∧
        2 * Real.sqrt (t.val - z.2) * cost ≤ Aphys z) ∧
      H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0
        (Real.sqrt (t.val - (t.val - v ^ 2))) (gamma jl 0) q = (Loriginal : WithTop ℝ) ∧
      gradientFun gOriginal (fun y => Aphys (y, t.val - v ^ 2)) q = (2 * v) • Vorig ∧
      HasDerivAt (fun t => Aphys (q, t))
        (-Loriginal / v - 2 * v ^ 2 * Roriginal + gOriginal.inner q Vorig Vorig / 2)
        (t.val - v ^ 2) ∧
      laplacian (LeviCivita gOriginal) gOriginal (fun y => Aphys (y, t.val - v ^ 2)) q =
        2 * v * laplacian (LeviCivita gOriginal) gOriginal (fun y => F (y, v)) q ∧
      -6 - etaError < deriv (fun t => Aphys (q, t)) (t.val - v ^ 2) -
        laplacian (LeviCivita gOriginal) gOriginal (fun y => Aphys (y, t.val - v ^ 2)) q := by
  classical
  obtain ⟨a₀, ha₀, hInitial⟩ :=
    exists_pos_fixedHamiltonIveyRegion_for_identified_histories P₀ g₀
  refine ⟨a₀, ha₀, hInitial, ?_⟩
  intro Aact E rTerm qDeriv ρ Cderiv hE hrTerm hqDeriv hρ
  obtain ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, hbarrier⟩ :=
    exists_uniform_regularCrossing_of_sum_stageRegularizedAction_lt_of_recenter_budget
      Aact (3 / a₀) E rTerm qDeriv a₀ ρ Cderiv
      (by positivity) hE hrTerm hqDeriv ha₀ hρ
  refine ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, ?_⟩
  intro H parameters hm hmodelRadius herror hbudget hdelta hneck records identification
    t hderiv p hball first hle v hv hvE hpole hpast hwindows q hsmall
  obtain ⟨hfixed, hscalarInitial⟩ := hInitial H identification
  have hpreserve :=
    H.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ hfixed hscalarInitial
  have hscalar : ∀ j (s : ℝ), s ∈ H.stageDomain j →
      ∀ x : (H.stage j).Carrier,
        -(3 / a₀) ≤ metricScalarAt (H.stageMetric j s) x := by
    intro j s hs x
    have htime := (H.stageDomain_subset j hs).1
    have hratio : 3 / (a₀ + s) ≤ 3 / a₀ :=
      div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3) ha₀
        (le_add_of_nonneg_right htime)
    have hneg : -(3 / a₀) ≤ -3 / (a₀ + s) := by
      simpa only [neg_div] using neg_le_neg hratio
    exact hneg.trans (hpreserve.1 j s hs x).2
  have hupper : t.val - (0 : ℝ) ^ 2 ∈ H.stageDomain (H.activeStage t) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero] using H.activeStage_mem t
  have hupperIcc : t.val - (0 : ℝ) ^ 2 ∈
      Icc (H.time (H.activeStage t)) (H.stageEndTime (H.activeStage t)) :=
    ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
  have hupperSupport : t.val ∈
      Ioc (H.time (H.activeStage t)) (H.stageEndTime (H.activeStage t)) :=
    ⟨hpole, by simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero] using hupperIcc.2⟩
  have hpastDomain : t.val - v ^ 2 ∈ H.stageDomain first :=
    H.mem_stageDomain_of_mem_Ioo hpast
  have hscalarClock (j : H.StageInterval first (H.activeStage t))
      (r : ℝ) (hr : r ∈ Ioo (H.regularizedStageStart t.val 0 j.val)
        (H.regularizedStageEnd t.val v j.val)) (x : (H.stage j.val).Carrier) :
      -(3 / a₀) ≤ metricScalarAt (H.stageMetric j.val (t.val - r ^ 2)) x :=
    hscalar j.val _ (H.mapsTo_regularizedStage_Ioo t.val 0 v j.val hr) x
  have hcost := H.regularizedCost_eq_regularizedC1Cost first (H.activeStage t) hle
    t.val (3 / a₀) 0 v hupper hscalarClock p q
  have hfinite : H.regularizedCost first (H.activeStage t) hle
      t.val (3 / a₀) 0 v p q ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top hsmall.le
  have hfiniteC1 : H.regularizedC1Cost first (H.activeStage t) hle
      t.val 0 v p q ≠ ⊤ := by
    rw [← hcost]
    exact hfinite
  obtain ⟨gamma, hC1, hInt, hp, hq, hNodes, hSumC1⟩ :=
    H.exists_regularizedC1Cost_minimizer_of_ne_top first (H.activeStage t) hle
      t.val (3 / a₀) 0 v hupper hscalarClock p q hfiniteC1
  have hAC (j : H.StageInterval first (H.activeStage t)) :
      Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val) :=
    Manifold.absolutelyContinuousOnInterval_of_contMDiffOn (hC1 j).contMDiffOn
  have hSumCost : (((∑ j : H.StageInterval first (H.activeStage t),
      H.stageRegularizedAction j.val t.val (gamma j)
        (H.regularizedStageStart t.val 0 j.val)
        (H.regularizedStageEnd t.val v j.val)) : ℝ) : WithTop ℝ) =
      H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0 v p q :=
    hSumC1.trans hcost.symm
  have hmin : H.regularizedExtendedAction first (H.activeStage t)
      t.val (3 / a₀) 0 v gamma =
      H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0 v p q := by
    have hext := H.regularizedExtendedAction_eq_sum_action first (H.activeStage t)
      (le_refl 0) hv.le hupperIcc hpastDomain gamma hInt (fun j => by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        exact hscalarClock j r hr (gamma j r))
    exact hext.trans hSumCost
  have hsmallAction : (∑ j : H.StageInterval first (H.activeStage t),
      H.stageRegularizedAction j.val t.val (gamma j)
        (H.regularizedStageStart t.val 0 j.val)
        (H.regularizedStageEnd t.val v j.val)) < Aact := by
    have hh := hsmall
    rw [← hSumCost] at hh
    exact WithTop.coe_lt_coe.mp hh
  have hcross := hbarrier H parameters hm hmodelRadius herror hbudget hdelta hneck
    records hfixed hscalarInitial t hderiv p hball first hle v hv.le hvE hpastDomain
    hscalarClock gamma hAC hInt hp hNodes hsmallAction
  have hcrossAll (i : Fin H.eventCount) (hf : first ≤ i.castSucc)
      (hl : i.succ ≤ H.activeStage t) :
      (H.event i).RegularCrossing
        (gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
          (Real.sqrt (t.val - H.time i.succ)))
        (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
          (Real.sqrt (t.val - H.time i.succ))) :=
    hcross i hf hl (hwindows i hf hl)
  refine ⟨gamma, hC1, hAC, hInt, hp, hq, hNodes, hmin, hcrossAll, ?_⟩
  intro etaError hetaError
  exact H.exists_physical_cost_upper_support_of_attained_action first (H.activeStage t) hle
    hv hupperSupport hpast hscalar gamma hAC hInt hNodes
    (by simpa only [hp, hq] using hmin)
    (hC1 ⟨first, le_rfl, hle⟩).contMDiffAt hcrossAll hetaError

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

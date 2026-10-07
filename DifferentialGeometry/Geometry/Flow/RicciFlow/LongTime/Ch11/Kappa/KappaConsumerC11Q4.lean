import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaEndToEndC11Q4

/-!
# κ 线 consumer（O-CH11-KAPPA3 G4，后缀 `_C11Q4`）

* 显式合成 `hW` 的全称形：无 event 半窗口种子走 KAPPA2 Q3-G1（`weightedMinBoundEnd_of_noEvent_C11Q3`，
  DPWSP:859），有 event 种子（`hEvent`）走本车道 G1 的逐种子跨 event 归纳
  `tracedMin_le_of_eventContact_C11Q4` + G2 的逐种子 contact
  `ObservedHistory.eventLowSublevelContact_of_nodeData_C11Q4`（seed trace Rm 控制由
  `seedTrace_isRmControlled_C11Q4`），再经 `weightedMinBound_of_traced_C11Q2` 与
  `cutoffMin_halfClock_eq_C11Q3`（`A' = max A 1`）；
* 接 G3：native + 两类 node 数据 + FINECAP `hact/hfine` ⇒ `LocalKappaWideSupply_C11Q`
  （`localKappaWideSupply_of_native_nodes_C11Q4`）⇒ P6B `LocalKappaSupply_P6B`（`hKappaLocal` 形）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal NNReal Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
  (eventLowSublevelContact_of_nodeData_C11Q4)

namespace GC.LongTime.Ch11

universe u

/-- **native + 两类 node 数据 ⇒ 局部 κ（wide supply）**（G3 链的 κ 段）：`hW` ⇐ event node 数据，
`hB` ⇐ URE node 数据，K3 ⇐ FINECAP `hact` + `hfine`。 -/
theorem localKappaWideSupply_of_native_nodes_C11Q4 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ}
    (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory))
    (Cderiv : ℝ≥0)
    (hnode : ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        ∀ ϱ₀ : ℝ, N.params.neckRadius t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
        (t : ℝ) - r ^ 2 / 2 ≤ H.time (H.activeStage t) →
        ∃ nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ,
          EventNodeData_C11Q4 P g Cderiv H N.params (N.records n) t x r (max A 1)
            nodeA nodeE nodeR nodeQ nodeRho)
    (hure : ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        ∀ ϱ₀ : ℝ, N.params.neckRadius t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
        ∀ a : Icc (0 : ℝ) H.horizon, (a : ℝ) = (t : ℝ) - (Real.sqrt 3 * r / 2) ^ 2 →
        ∃ nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ,
          UREBlockNodeData_C11Q4 P g Cderiv H N.params (N.records n) t x r A a
            nodeA nodeE nodeR nodeQ nodeRho)
    (hδ : ∀ s, 0 ≤ s → N.params.delta s ≤ δ s)
    (hact : ∀ n i b, ActualCanonicalInsertion_C11Q5 ((N.records n i).static b))
    (hfine : KappaFineScale_C11Q5 P g N.params α
      (weightedMinLevel_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1))) N.Ctime) :
    LocalKappaWideSupply_C11Q F δ α N.params.neckRadius :=
  localKappaWideSupply_of_native_end_C11Q4 N
    (weightedMinBoundEnd_of_nodeData_C11Q4 N.params N.records Cderiv hnode)
    (seedRegularBlock_of_URE_C11Q4 N.params N.records Cderiv hure)
    (fun A _ => ureBlockKappa_pos_C11Q3 A) hδ hact hfine

/-- **consumer 1（显式合成 `hW`）**：无 event 种子（KAPPA2 Q3-G1）+ 有 event 种子（G1 逐种子归纳 + G2
逐种子 contact）⇒ `WeightedMinBoundEnd_C11Q3` 的全称形（与 `weightedMinBoundEnd_of_nodeData_C11Q4` 同结论）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr : ℝ → ℝ}
    (params : CutoffParameters)
    (records : ∀ n i, GeometricCutoffRecord (F.tower.history n).toHistory i params)
    (Cderiv : ℝ≥0)
    (hnode : ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        ∀ ϱ₀ : ℝ, nr t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
        (t : ℝ) - r ^ 2 / 2 ≤ H.time (H.activeStage t) →
        ∃ nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ,
          EventNodeData_C11Q4 P g Cderiv H params (records n) t x r (max A 1)
            nodeA nodeE nodeR nodeQ nodeRho)
 :
    WeightedMinBoundEnd_C11Q3 F δ α nr (fun A => cutoffBarrierConst_C11Q3 (max A 1)) := by
  refine weightedMinBoundEnd_of_noEvent_C11Q3 params records ?_
  intro A hA n R H t p r hr hacc hsmall hvol b hbt hb seedTrace x hx ϱ₀ hϱ₀ hball Bf hBf hev
  have hr0 : 0 < r := hsmall.1
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hA1 : 1 ≤ max A 1 := le_max_right _ _
  have hx' : riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x <
      ENNReal.ofReal (max A 1 * r) :=
    lt_of_lt_of_le hx (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hr0.le))
  have hN := hnode A hA n t p r hr hacc hsmall hvol x hx ϱ₀ hϱ₀ hball hev
  obtain ⟨nodeA, nodeE, nodeR, nodeQ, nodeRho, hN'⟩ := hN
  have hseedBall := isParabolicallyRmControlledBall_of_seed_C11Q hsmall
  have hcon := eventLowSublevelContact_of_nodeData_C11Q4 Cderiv H (F.tower.initial n) params
    (records n) t p x hA1 hseedBall b hbt hb seedTrace
    (seedTrace_isRmControlled_C11Q4 hsmall hbt hb seedTrace) hN'
  have hbound := tracedMin_le_of_eventContact_C11Q4 Cderiv H (F.tower.initial n) params
    (records n) t p x hA1 hr hseedBall hx' hball b hbt hb seedTrace hN' hcon
  have hspec := windowBarrierA₀_spec_C11Q2 P g
  have h := weightedMinBound_of_traced_C11Q2 R (F.tower.initial n) (records n) hspec.1 hspec.2.1
    hBf hbt seedTrace hb x hr hbound (r / Real.sqrt 2) ⟨div_pos hr0 hs2, le_rfl⟩
  rw [cutoffMin_halfClock_eq_C11Q3 R hr0 A (max A 1) hbt seedTrace x]
  exact h

/-- **consumer 2（接 G3 ⇒ P6B）**：native + 两类 node 数据 + `hact/hfine` ⇒ P6B `LocalKappaSupply_P6B`
（`hKappaLocal` 形，`nr = neckRadius`）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ}
    (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory))
    (Cderiv : ℝ≥0)
    (hnode : ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        ∀ ϱ₀ : ℝ, N.params.neckRadius t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
        (t : ℝ) - r ^ 2 / 2 ≤ H.time (H.activeStage t) →
        ∃ nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ,
          EventNodeData_C11Q4 P g Cderiv H N.params (N.records n) t x r (max A 1)
            nodeA nodeE nodeR nodeQ nodeRho)
    (hure : ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        ∀ ϱ₀ : ℝ, N.params.neckRadius t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
        ∀ a : Icc (0 : ℝ) H.horizon, (a : ℝ) = (t : ℝ) - (Real.sqrt 3 * r / 2) ^ 2 →
        ∃ nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ,
          UREBlockNodeData_C11Q4 P g Cderiv H N.params (N.records n) t x r A a
            nodeA nodeE nodeR nodeQ nodeRho)
    (hδ : ∀ s, 0 ≤ s → N.params.delta s ≤ δ s)
    (hact : ∀ n i b, ActualCanonicalInsertion_C11Q5 ((N.records n i).static b))
    (hfine : KappaFineScale_C11Q5 P g N.params α
      (weightedMinLevel_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1))) N.Ctime) :
    LocalKappaSupply_P6B F δ α N.params.neckRadius :=
  (localKappaWideSupply_of_native_nodes_C11Q4 N Cderiv hnode hure hδ hact hfine).toP6B

end GC.LongTime.Ch11

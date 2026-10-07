import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaEventContactC11Q4
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaUREBlockC11Q3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaFineEndToEndC11Q5

/-!
# 端点形端到端 wrapper（O-CH11-KAPPA3 G3 = GAP-3，后缀 `_C11Q4`）

* `localKappa_of_weightedMinBoundEnd_block_C11Q4`：端点形 `WeightedMinBoundEnd_C11Q3` + K3 + block ⇒
  `LocalKappaWideSupply_C11Q`（`localKappa_of_weightedMinBound_block_C11Q2` 的端点形，K4 经
  `boundedReducedLength_of_weightedMinBoundEnd_C11Q3`）；
* `nonempty_pre841Data_of_native_end_C11Q4`：FINECAP `nonempty_pre841Data_of_native_fineCap_C11Q5` 的
  binder **逐字**，只把积分形 `hW : WeightedMinBound_C11Q2` 换成端点形 `hW : WeightedMinBoundEnd_C11Q3`；
* **SeedRegularBlock 全称版** `seedRegularBlock_of_URE_C11Q4`：逐种子 URE 实例
  `seedRegularBlock_at_of_URE_C11Q3`（KAPPA2 Q3-G3）对所有种子量化，node 数据 =
  `UREBlockNodeData_C11Q4`（URE 的 `hdata ∧ hbud` 逐字，request = `ureRequest_C11Q3`）显式 binder；
* **只差清单落到一个定理** `nonempty_pre841Data_of_native_nodes_C11Q4`：`hW` ⇐ event node 数据
  （G1 + G2），`hB` ⇐ URE node 数据，`C = cutoffBarrierConst_C11Q3 ∘ max · 1`、`D = ureBlockD_C11Q3`、
  `κ = ureBlockKappa_C11Q3`。剩余前提：`hnode`、`hure`（两类 request 形 node 数据，cap 子句的 producer 路线 =
  astra retention 的 `fineRecords`，FINECAP gap 文档）、`hδ`、`hact` + `hfine`（FINECAP）、`hacc`（S7）、
  `hsmallScale`（Q3）与 PRE841 种子数据。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.Ch11

universe u

/-! ## 1. 端点形链 -/

/-- **链（端点形 + block）**：`WeightedMinBoundEnd_C11Q3` + K3（`Λ ≥ e^{C/2+32/√2} + 1`）+ block ⇒
`LocalKappaWideSupply_C11Q`。 -/
theorem localKappa_of_weightedMinBoundEnd_block_C11Q4 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr C Λ D κ : ℝ → ℝ}
    (hW : WeightedMinBoundEnd_C11Q3 F δ α nr C) (hK3 : SurgeryActionBarrier_C11Q F δ α nr Λ)
    (hΛ : ∀ A, 0 < A → weightedMinLevel_C11Q2 C A ≤ Λ A)
    (hB : SeedRegularBlock_C11Q2 F δ α nr (weightedMinLengthConst_C11Q2 C) D κ)
    (hκ : ∀ A, 0 < A → 0 < κ A) :
    LocalKappaWideSupply_C11Q F δ α nr :=
  localKappaWide_of_seedReducedVolume_C11Q
    (seedReducedVolumeLower_of_block_C11Q2 hκ
      (boundedReducedLength_of_weightedMinBoundEnd_C11Q3 hW hK3 hΛ) hB)

/-- **局部 κ 由 native 数据 + fine-cap（端点形）**：`localKappaWideSupply_of_native_fineCap_C11Q5` 的
`hW` 换成端点形。 -/
theorem localKappaWideSupply_of_native_end_C11Q4 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {C D κ : ℝ → ℝ}
    (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory))
    (hW : WeightedMinBoundEnd_C11Q3 F δ α N.params.neckRadius C)
    (hB : SeedRegularBlock_C11Q2 F δ α N.params.neckRadius (weightedMinLengthConst_C11Q2 C) D κ)
    (hκ : ∀ A, 0 < A → 0 < κ A)
    (hδ : ∀ s, 0 ≤ s → N.params.delta s ≤ δ s)
    (hact : ∀ n i b, ActualCanonicalInsertion_C11Q5 ((N.records n i).static b))
    (hfine : KappaFineScale_C11Q5 P g N.params α (weightedMinLevel_C11Q2 C) N.Ctime) :
    LocalKappaWideSupply_C11Q F δ α N.params.neckRadius :=
  localKappa_of_weightedMinBoundEnd_block_C11Q4 hW
    (surgeryActionBarrier_of_native_fineCap_C11Q5 N hact hδ
      (fun A _ => weightedMinLevel_pos_C11Q2 C A) hfine)
    (fun _ _ => le_rfl) hB hκ

/-- **端到端 ⇒ `Pre841Data_C11K`（端点形，GAP-3）**：binder 与 FINECAP
`nonempty_pre841Data_of_native_fineCap_C11Q5` 逐字相同，只把积分形 `hW : WeightedMinBound_C11Q2` 换成端点形
`hW : WeightedMinBoundEnd_C11Q3`（K4 只消费 `v₁ = r/√2`）。 -/
theorem nonempty_pre841Data_of_native_end_C11Q4 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {C D κ : ℝ → ℝ}
    (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory))
    (hW : WeightedMinBoundEnd_C11Q3 F δ α N.params.neckRadius C)
    (hB : SeedRegularBlock_C11Q2 F δ α N.params.neckRadius (weightedMinLengthConst_C11Q2 C) D κ)
    (hκ : ∀ A, 0 < A → 0 < κ A)
    (hδ : ∀ s, 0 ≤ s → N.params.delta s ≤ δ s)
    (hact : ∀ n i b, ActualCanonicalInsertion_C11Q5 ((N.records n i).static b))
    (hfine : KappaFineScale_C11Q5 P g N.params α (weightedMinLevel_C11Q2 C) N.Ctime)
    (hacc : LargerBallAccuracySupply_C11S δ α) {A κ' : ℝ} (hA : 0 < A) (hκ' : 0 < κ')
    (hsmallScale : ∃ T : ℝ, 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) →
        2 * r ^ 2 < (t : ℝ) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
          (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (A * r),
        ∀ ρ' : ℝ, 0 < ρ' → ρ' < N.params.neckRadius v / 100 → ρ' < r / 100 →
          H.isParabolicallyRmControlledBall v x ρ' →
          ENNReal.ofReal (κ' * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage v) v) x ρ')
    (ind : ℕ → ℕ)
    (t : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (p : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (t n)).Carrier) (r : ℕ → ℝ)
    (hlate : Tendsto (fun n => (t n : ℝ)) atTop atTop)
    (htime : ∀ n, 2 * r n ^ 2 < (t n : ℝ))
    (hsmall : ∀ n, hasSmallParabolicCurvature (F.tower.history (ind n)).toHistory (t n) (p n)
      (r n))
    (hvol : ∀ n, ENNReal.ofReal (A⁻¹ * r n ^ 3) ≤
      ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
        ((F.tower.history (ind n)).toHistory.activeStage (t n)) (t n)) (p n) (r n))
    (aSeed : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (haT : ∀ n, aSeed n ≤ t n) (hclock : ∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (F.tower.history (ind n)).toHistory
      ((F.tower.history (ind n)).toHistory.activeStage (aSeed n))
      ((F.tower.history (ind n)).toHistory.activeStage (t n))
      ((F.tower.history (ind n)).toHistory.activeStage_mono (haT n)) (p n))
    (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (hst : ∀ n, s n ≤ t n)
    (y : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier) (R : ℕ → ℝ)
    (hR : ∀ n, 0 < R n)
    (hradii : Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (t n : ℝ) - r n ^ 2 / 2 ≤ (s n : ℝ) - T / R n)
    (hdist : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (w : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hws : w ≤ s n),
        (s n : ℝ) - T / R n ≤ w →
      ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage w)
        ((F.tower.history (ind n)).toHistory.activeStage (s n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono hws) x,
      ∀ haw : aSeed n ≤ w,
        riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage w) w)
          ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage w)
            ((F.tower.history (ind n)).toHistory.activeStage_mono haw)
            ((F.tower.history (ind n)).toHistory.activeStage_mono (hws.trans (hst n))))
          (tr.point ((F.tower.history (ind n)).toHistory.activeStage w) le_rfl
            ((F.tower.history (ind n)).toHistory.activeStage_mono hws)) <
          ENNReal.ofReal (A * r n)) :
    Nonempty (Pre841Data_C11K (fun n => (F.tower.history (ind n)).toHistory) s y R hR) := by
  have hloc : LocalKappaSupply_P6B F δ α N.params.neckRadius :=
    (localKappaWideSupply_of_native_end_C11Q4 N hW hB hκ hδ hact hfine).toP6B
  obtain ⟨κ₁, hκ₁, hW₁⟩ :=
    localKappaWindow_of_late_P6B (localKappaLateSupply_of_envelope_P6B hacc hloc) A hA
  have hW0 := localKappaWindow_zero_of_window_and_small_C11V hW₁ hsmallScale
  exact ⟨pre841Data_of_window_C11K (lt_min hκ₁ hκ') hW0 ind (N.comp ind) t p r hlate htime hsmall
    hvol aSeed haT hclock seedTrace s hst y R hR hradii hwin hdist⟩

/-- **consumer（G3，型对齐）**：FINECAP 积分形端到端的 binder 逐字 ⇒ 经 `.toEnd` 由端点形端到端得出
（端点形严格弱于积分形）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {C D κ : ℝ → ℝ}
    (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory))
    (hW : WeightedMinBound_C11Q2 F δ α N.params.neckRadius C)
    (hB : SeedRegularBlock_C11Q2 F δ α N.params.neckRadius (weightedMinLengthConst_C11Q2 C) D κ)
    (hκ : ∀ A, 0 < A → 0 < κ A)
    (hδ : ∀ s, 0 ≤ s → N.params.delta s ≤ δ s)
    (hact : ∀ n i b, ActualCanonicalInsertion_C11Q5 ((N.records n i).static b))
    (hfine : KappaFineScale_C11Q5 P g N.params α (weightedMinLevel_C11Q2 C) N.Ctime)
    (hacc : LargerBallAccuracySupply_C11S δ α) {A κ' : ℝ} (hA : 0 < A) (hκ' : 0 < κ')
    (hsmallScale : ∃ T : ℝ, 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) →
        2 * r ^ 2 < (t : ℝ) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
          (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (A * r),
        ∀ ρ' : ℝ, 0 < ρ' → ρ' < N.params.neckRadius v / 100 → ρ' < r / 100 →
          H.isParabolicallyRmControlledBall v x ρ' →
          ENNReal.ofReal (κ' * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage v) v) x ρ')
    (ind : ℕ → ℕ)
    (t : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (p : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (t n)).Carrier) (r : ℕ → ℝ)
    (hlate : Tendsto (fun n => (t n : ℝ)) atTop atTop)
    (htime : ∀ n, 2 * r n ^ 2 < (t n : ℝ))
    (hsmall : ∀ n, hasSmallParabolicCurvature (F.tower.history (ind n)).toHistory (t n) (p n)
      (r n))
    (hvol : ∀ n, ENNReal.ofReal (A⁻¹ * r n ^ 3) ≤
      ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
        ((F.tower.history (ind n)).toHistory.activeStage (t n)) (t n)) (p n) (r n))
    (aSeed : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (haT : ∀ n, aSeed n ≤ t n) (hclock : ∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (F.tower.history (ind n)).toHistory
      ((F.tower.history (ind n)).toHistory.activeStage (aSeed n))
      ((F.tower.history (ind n)).toHistory.activeStage (t n))
      ((F.tower.history (ind n)).toHistory.activeStage_mono (haT n)) (p n))
    (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (hst : ∀ n, s n ≤ t n)
    (y : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier) (R : ℕ → ℝ)
    (hR : ∀ n, 0 < R n)
    (hradii : Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (t n : ℝ) - r n ^ 2 / 2 ≤ (s n : ℝ) - T / R n)
    (hdist : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (w : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hws : w ≤ s n),
        (s n : ℝ) - T / R n ≤ w →
      ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage w)
        ((F.tower.history (ind n)).toHistory.activeStage (s n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono hws) x,
      ∀ haw : aSeed n ≤ w,
        riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage w) w)
          ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage w)
            ((F.tower.history (ind n)).toHistory.activeStage_mono haw)
            ((F.tower.history (ind n)).toHistory.activeStage_mono (hws.trans (hst n))))
          (tr.point ((F.tower.history (ind n)).toHistory.activeStage w) le_rfl
            ((F.tower.history (ind n)).toHistory.activeStage_mono hws)) <
          ENNReal.ofReal (A * r n)) :
    Nonempty (Pre841Data_C11K (fun n => (F.tower.history (ind n)).toHistory) s y R hR) := by
  exact nonempty_pre841Data_of_native_end_C11Q4 N hW.toEnd hB hκ hδ hact hfine hacc hA hκ'
    hsmallScale ind t p r hlate htime hsmall hvol aSeed haT hclock seedTrace s hst y R hR hradii
    hwin hdist

/-! ## 2. SeedRegularBlock 全称版 -/

/-- **URE node 数据**（逐种子；`seedRegularBlock_at_of_URE_C11Q3` 的 `hdata ∧ hbud` 逐字，request =
`ureRequest_C11Q3`，`a` = 时钟 `√3 r/2` 的切片）。 -/
def UREBlockNodeData_C11Q4 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (Cderiv : ℝ≥0)
    (H : ObservedHistory.{u}) (parameters : CutoffParameters)
    (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters)
    (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier) (r A : ℝ)
    (a : Icc (0 : ℝ) H.horizon) (nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ) :
    Prop :=
  (∀ (i : Fin H.eventCount) (_hf : H.activeStage a ≤ i.castSucc)
      (_hl : i.succ ≤ H.activeStage t),
    0 ≤ nodeE i ∧ 0 < nodeR i ∧ 0 < nodeQ i ∧ 0 < nodeRho i ∧
    Real.sqrt 3 * r / 2 ≤ nodeE i ∧
    H.isParabolicallyRmControlledBall t x (nodeR i) ∧
    parameters.delta (H.time i.succ) ≤
      (ureRequest_C11Q3 P₀ g₀ parameters.recenterConstant Cderiv
        (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)).2.2.2 ∧
    parameters.neckRadius (H.time i.succ) ≤ nodeRho i ∧
    (∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ H.activeStage t →
      ∀ b, (records j).delta b ≤
        (ureRequest_C11Q3 P₀ g₀ parameters.recenterConstant Cderiv
          (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)).2.2.2) ∧
    (∀ j : Fin (H.eventCount + 1), i.succ ≤ j → j ≤ H.activeStage t →
      ∀ y : (H.stage j).Carrier, ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s ≤ t.val →
        nodeQ i < metricScalarAt (H.stageMetric j s) y →
        |derivWithin (fun z => metricScalarAt (H.stageMetric j z) y) (Iic s) s| ≤
          Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) ∧
    (∀ b : (H.event i).RetainedBoundaryIndex,
      ∃ (Dbig ζ : ℝ) (m : ℕ) (S : (H.event i).PresentedStaticCap parameters.fixed Dbig m ζ b),
        (ureRequest_C11Q3 P₀ g₀ parameters.recenterConstant Cderiv
          (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)).2.1 ≤ Dbig ∧
        (ureRequest_C11Q3 P₀ g₀ parameters.recenterConstant Cderiv
          (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)).2.2.1 ≤ m ∧
        ζ ≤ (ureRequest_C11Q3 P₀ g₀ parameters.recenterConstant Cderiv
          (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)).1 ∧
        S.hasCanonicalWindow ∧ S.neck.scale = ((records i).static b).neck.scale)) ∧
  ∀ (i : Fin H.eventCount), H.activeStage a ≤ i.castSucc → i.succ ≤ H.activeStage t →
    ureBlockD_C11Q3 A * r ≤ nodeA i

/-- **SeedRegularBlock 全称版（URE）**：records + 每个种子的 URE node 数据 ⇒
`SeedRegularBlock_C11Q2 F δ α nr (weightedMinLengthConst_C11Q2 C) ureBlockD_C11Q3
ureBlockKappa_C11Q3`，`C = cutoffBarrierConst_C11Q3 ∘ max · 1`。 -/
theorem seedRegularBlock_of_URE_C11Q4 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr : ℝ → ℝ}
    (params : CutoffParameters)
    (records : ∀ n i, GeometricCutoffRecord (F.tower.history n).toHistory i params)
    (Cderiv : ℝ≥0)
    (hure : ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        ∀ ϱ₀ : ℝ, nr t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
        ∀ a : Icc (0 : ℝ) H.horizon, (a : ℝ) = (t : ℝ) - (Real.sqrt 3 * r / 2) ^ 2 →
        ∃ nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ,
          UREBlockNodeData_C11Q4 P g Cderiv H params (records n) t x r A a
            nodeA nodeE nodeR nodeQ nodeRho) :
    SeedRegularBlock_C11Q2 F δ α nr
      (weightedMinLengthConst_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1)))
      ureBlockD_C11Q3 ureBlockKappa_C11Q3 := by
  intro A hA n R H t p r hr hacc hsmall hvol b hbt hb seedTrace x hx ϱ₀ hϱ₀ hball Bf hBf s₁ hbs₁
    hs₁t hs₁ hq
  obtain ⟨q₁, hq₁, hlow⟩ := hq
  have hr0 : 0 < r := hsmall.1
  have hw2 : (Real.sqrt 3 * r / 2) ^ 2 = 3 / 4 * r ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    ring
  have hmem : (t : ℝ) - (Real.sqrt 3 * r / 2) ^ 2 ∈ Icc (0 : ℝ) H.horizon := by
    rw [hw2]
    have := t.2.2
    constructor <;> nlinarith [sq_nonneg r]
  have hval : ((projIcc 0 H.horizon H.horizon_nonneg ((t : ℝ) - (Real.sqrt 3 * r / 2) ^ 2) :
      Icc (0 : ℝ) H.horizon) : ℝ) = (t : ℝ) - (Real.sqrt 3 * r / 2) ^ 2 := by
    rw [projIcc_of_mem _ hmem]
  have has : b ≤ projIcc 0 H.horizon H.horizon_nonneg ((t : ℝ) - (Real.sqrt 3 * r / 2) ^ 2) := by
    change (b : ℝ) ≤ _
    rw [hval, hb, hw2]
    nlinarith [sq_nonneg r]
  have hat : projIcc 0 H.horizon H.horizon_nonneg ((t : ℝ) - (Real.sqrt 3 * r / 2) ^ 2) ≤ t := by
    change _ ≤ (t : ℝ)
    rw [hval]
    nlinarith [sq_nonneg (Real.sqrt 3 * r / 2)]
  have hN := hure A hA n t p r hr hacc hsmall hvol x hx ϱ₀ hϱ₀ hball _ hval
  obtain ⟨nodeA, nodeE, nodeR, nodeQ, nodeRho, hdata, hbud⟩ := hN
  exact seedRegularBlock_at_of_URE_C11Q3 R (F.tower.initial n) params (records n) hBf Cderiv t p x
    hA hr hsmall hvol hbt hb seedTrace s₁ hbs₁ hs₁t hs₁ q₁ hq₁ hlow _ rfl has hat
    nodeA nodeE nodeR nodeQ nodeRho hdata hbud

/-! ## 3. 只差清单落到一个定理 -/

/-- **端到端（只差清单）**：`nonempty_pre841Data_of_native_end_C11Q4` 的 `hW` ⇐ event node 数据（G1 + G2：
`weightedMinBoundEnd_of_nodeData_C11Q4`），`hB` ⇐ URE node 数据（`seedRegularBlock_of_URE_C11Q4`），
`hκ` ⇐ `ureBlockKappa_pos_C11Q3`。其余 binder 与 FINECAP `_fineCap_C11Q5` 逐字相同。 -/
theorem nonempty_pre841Data_of_native_nodes_C11Q4 {P : OrientedThreeStage.{u}} {g : P.Metric}
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
      (weightedMinLevel_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1))) N.Ctime)
    (hacc : LargerBallAccuracySupply_C11S δ α) {A κ' : ℝ} (hA : 0 < A) (hκ' : 0 < κ')
    (hsmallScale : ∃ T : ℝ, 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) →
        2 * r ^ 2 < (t : ℝ) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
          (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (A * r),
        ∀ ρ' : ℝ, 0 < ρ' → ρ' < N.params.neckRadius v / 100 → ρ' < r / 100 →
          H.isParabolicallyRmControlledBall v x ρ' →
          ENNReal.ofReal (κ' * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage v) v) x ρ')
    (ind : ℕ → ℕ)
    (t : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (p : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (t n)).Carrier) (r : ℕ → ℝ)
    (hlate : Tendsto (fun n => (t n : ℝ)) atTop atTop)
    (htime : ∀ n, 2 * r n ^ 2 < (t n : ℝ))
    (hsmall : ∀ n, hasSmallParabolicCurvature (F.tower.history (ind n)).toHistory (t n) (p n)
      (r n))
    (hvol : ∀ n, ENNReal.ofReal (A⁻¹ * r n ^ 3) ≤
      ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
        ((F.tower.history (ind n)).toHistory.activeStage (t n)) (t n)) (p n) (r n))
    (aSeed : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (haT : ∀ n, aSeed n ≤ t n) (hclock : ∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (F.tower.history (ind n)).toHistory
      ((F.tower.history (ind n)).toHistory.activeStage (aSeed n))
      ((F.tower.history (ind n)).toHistory.activeStage (t n))
      ((F.tower.history (ind n)).toHistory.activeStage_mono (haT n)) (p n))
    (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (hst : ∀ n, s n ≤ t n)
    (y : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier) (R : ℕ → ℝ)
    (hR : ∀ n, 0 < R n)
    (hradii : Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (t n : ℝ) - r n ^ 2 / 2 ≤ (s n : ℝ) - T / R n)
    (hdist : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (w : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hws : w ≤ s n),
        (s n : ℝ) - T / R n ≤ w →
      ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage w)
        ((F.tower.history (ind n)).toHistory.activeStage (s n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono hws) x,
      ∀ haw : aSeed n ≤ w,
        riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage w) w)
          ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage w)
            ((F.tower.history (ind n)).toHistory.activeStage_mono haw)
            ((F.tower.history (ind n)).toHistory.activeStage_mono (hws.trans (hst n))))
          (tr.point ((F.tower.history (ind n)).toHistory.activeStage w) le_rfl
            ((F.tower.history (ind n)).toHistory.activeStage_mono hws)) <
          ENNReal.ofReal (A * r n)) :
    Nonempty (Pre841Data_C11K (fun n => (F.tower.history (ind n)).toHistory) s y R hR) := by
  exact nonempty_pre841Data_of_native_end_C11Q4 N
    (weightedMinBoundEnd_of_nodeData_C11Q4 N.params N.records Cderiv hnode)
    (seedRegularBlock_of_URE_C11Q4 N.params N.records Cderiv hure)
    (fun A _ => ureBlockKappa_pos_C11Q3 A) hδ hact hfine hacc hA hκ' hsmallScale ind t p r hlate
    htime hsmall hvol aSeed haT hclock seedTrace s hst y R hR hradii hwin hdist

end GC.LongTime.Ch11

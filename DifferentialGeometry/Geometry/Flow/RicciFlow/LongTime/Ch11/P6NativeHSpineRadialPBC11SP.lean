import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CCPrimeOfXC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeWindowRadialPBC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeNJSlotV3RadialPBC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeRayNeckChainPBC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeFlowRayPBC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeOnlyNzeroPBC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeExcludePBC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HSpineTwoLevelTimePBC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HSpineTwoLevelTimeGlueC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GuardRegimeFalseC11SP

set_option autoImplicit false

/-!
# hspine‴（PB 形槽）⇐ X ∧ PB，CE 由 v3 radial records 付（O-CH11-NRPRIME-WIRE G4 = CE-WIRE，后缀 `_C11SP`）

**依赖 TRACKED-RADIAL root（C12-12 patch：`PreparedSpatialState.radial` + Base/Step）；INT 在该 root 之后登记。**
G3 `hspineTwoLevelTime_of_X_PB_CE_C11SP` 去掉 `hCE` binder：native 链底三层换 radial-aware PB-twin
（生成器 `gen/gen_twin.py` 层 R1/R2/R3）——R1 window：删 `hCE`，hSL1 结论在 canonical
前提后加 `(∀ n e b, ((records n e).static b).witness.HasRadialCoordinates) →`，
原唯一用点改由树内 `window_ne_of_regularCrossing_of_radial_C11SP` 逐点付；
R2 bounded ball：透传 radial 前提；R3 NJslot：records 来源由
`exists_linked_records_of_prepared_chain_C11SP` 换成 C12-12 v3
`exists_records_of_prepared_chain_v3_C12R`（同一批 records、
同一 witness，第 7 合取 = radial）并把它传给 R2。NJslot 输出不含 records 量化 ⇒ L4a–L9 的 PB-twin 原样复用。
结论 = HPBASE-V8 PB 形 hspine 槽逐字（同 G3）。**PROVISIONAL[X, PB]**：X = 已登记局部 Dt 合同（Xtower 逐字实例），
PB = 槽内前提（HpbaseTwoLevel v8 provider，HPBASE-V8 G1 已交）；CE 已付（v3 radial）。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Metric
open GC.GeneralFlow
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

/-- **G4（PROVISIONAL[X, PB]）**：PB 形 hspine 槽 ⇐ Xtower（CE 由 v3 radial records 付，PB 在槽内）。 -/
theorem hspineTwoLevelTime_of_X_PB_C11SP (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ Cbirth : ℝ, 0 < Cbirth ∧ ∀ C : ℝ≥0, ∃ (Rmod : ℝ) (mmod : ℕ) (εX : ℝ), 0 < εX ∧
    ((
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g),
        F.tower = S.tower → ∀ q : CutoffParameters,
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ εX → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
        Rmod ≤ pBase.modelRadius → mmod ≤ pBase.modelOrder →
      ∀ (params : CutoffParameters)
        (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
          GeometricCutoffRecord (F.tower.history n).toHistory e params),
        params.modelRadius = pBase.modelRadius → params.modelOrder = pBase.modelOrder →
        params.modelAccuracy = pBase.modelAccuracy →
        (∀ t : ℝ, 0 ≤ t → params.delta t = q.delta t ∧
          params.neckRadius t = q.neckRadius t) →
        (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
        (∀ n e, ((F.tower.history n).toHistory.event e).old =
          ((F.tower.history n).toHistory.event e).transition.trace.retainedCore) →
        Tendsto params.delta atTop (𝓝 0) →
        (∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
          ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
            (F.tower.history n).time e.succ ∈ Icc (t / 2) t →
            ∀ h, (records n e).nominalRadius h ≤ η * params.neckRadius t) →
      ∀ B : ℝ, 0 < B → ∃ T₀ : ℝ, 0 < T₀ ∧
      ∀ (n : ℕ) (θ : ℝ), 0 < θ → θ * B ≤ 1 / 16 →
      let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon), T₀ ≤ (t : ℝ) →
      ∀ Q : ℝ, (q.neckRadius t ^ 2)⁻¹ < Q →
      ∀ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t),
        (t : ℝ) - a ≤ θ / Q →
      ∀ (y : (H.stageAt t).Carrier)
        (A : BackwardPointTrace H
          (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) y),
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
          metricScalarAt (H.stageMetric (H.activeStage v) v)
            (A.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono hvt)) ≤ 2 * B * Q) →
      ∀ (e₁ e₂ : Fin H.eventCount) (hf₁ : H.activeStage a ≤ e₁.castSucc)
        (hl₁ : e₁.succ ≤ H.activeStage t) (_hf₂ : H.activeStage a ≤ e₂.castSucc)
        (_hl₂ : e₂.succ ≤ H.activeStage t), e₁ < e₂ →
      ∀ (b : (H.event e₁).RetainedBoundaryIndex) (z : standardCapWindow params.modelRadius),
        StandardCap.transitionEnd < ‖z.val‖ → ‖z.val‖ ≤ StandardCap.transitionEnd + 10 →
        ((records n e₁).static b).window z =
          A.point e₁.succ (hf₁.trans e₁.castSucc_lt_succ.le) hl₁ →
        ((records n e₁).static b).neck.scale ≤ 4 * (B * Q) →
      ∃ W : ∀ i : Fin (H.eventCount + 1), Set (H.stage i).Carrier, (∀ i, IsOpen (W i)) ∧
        (∀ (i : Fin (H.eventCount + 1)) (hf : e₁.succ ≤ i), i ≤ e₂.castSucc →
          ∀ (x' : (H.stage i).Carrier) (A' : BackwardPointTrace H e₁.succ i hf x'),
            A'.point e₁.succ le_rfl hf ∈
              ((records n e₁).static b).window '' {z | ‖z.val‖ < Rmod + 1} →
              x' ∈ W i) ∧
        (∀ i : Fin H.eventCount, e₁.succ ≤ i.castSucc → i.succ ≤ e₂.castSucc →
          ∀ x' : (H.stage i.castSucc).Carrier, x' ∈ W i.castSucc →
          ∀ τ ∈ Ioo (H.time i.castSucc) (H.time i.succ),
            Cbirth * ((records n e₁).static b).neck.scale < (H.event i).incoming.flow.scalar τ x' →
            |derivWithin (fun v => (H.event i).incoming.flow.scalar v x') (Iic τ) τ| ≤
              C * (H.event i).incoming.flow.scalar τ x' ^ 2) ∧
        (∀ x' : (H.stage e₂.castSucc).Carrier, x' ∈ W e₂.castSucc →
          ∀ τ ∈ Ioo (H.time e₂.castSucc) (H.time e₂.succ),
          Cbirth * ((records n e₁).static b).neck.scale < (H.event e₂).incoming.flow.scalar τ x' →
          |derivWithin (fun v => (H.event e₂).incoming.flow.scalar v x') (Iic τ) τ| ≤
            C * (H.event e₂).incoming.flow.scalar τ x' ^ 2)) →
    ∃ εsp : ClosedBirthConstants → ClosedBirthConstants → ℝ,
      (∀ Γ Γf, 0 < εsp Γ Γf) ∧
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ → ∀
      (S : PreparedSpatialChain pB Γf P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      pB.modelAccuracy ≤ εsp Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder → (Rmod ≤ pB.modelRadius ∧ mmod ≤ pB.modelOrder) →
      ∀ A : ℝ, 1 < A →
      (∃ κ'' : ℝ, 0 < κ'' ∧ ∃ T : ℝ, 0 < T ∧
        ∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
          T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
          ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
          q.neckRadius t ≤ r →
          ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
            (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
          ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
            (H.activeStage_mono haT) p,
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
            (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
          ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
            (A * r),
          ∀ ρ' : ℝ, 0 ≤ ρ' → ρ' < r / 100 → H.isParabolicallyRmControlledBall v x ρ' →
            ENNReal.ofReal (κ'' * ρ' ^ 3) ≤
              ballVolume (H.stageMetric (H.activeStage v) v) x ρ') →
        CanonicalLateTimeCore_P6X F Γ.epsilon (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ)
          (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ) (p6Ctime_C11G7B.{u} Γ) →
        LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A) := by
  obtain ⟨Cbirth, hCbirth, h⟩ := CCprime_of_X_C11SP.{u} P g
  refine ⟨Cbirth, hCbirth, fun C => ?_⟩
  obtain ⟨Rmod, mmod, εX, hεX, hXC⟩ := h C
  refine ⟨Rmod, mmod, εX, hεX, fun hX => ?_⟩
  exact hspineTwoLevelTime_PB_C11SP P g Rmod mmod
    (fun S F q hTower hdiag A hA hnot => regime_glue_C11SP S F q hTower hdiag A hA hnot)
    (guard_regime_false_final_C11SP P g)
    (native_regime_false_PB_C11SP P g Rmod mmod (guard_regime_false_final_C11SP P g)
      (native_hnreg_of_hnzero_PB_C11SP P g Rmod mmod
        (native_hnzero_of_flowRay_PB_C11SP P g Rmod mmod
          (hflowNRay_of_NJseg_PB_C11SP P g Rmod mmod
            (native_NJslot_of_SL1_v3_radial_PB_C11SP P g Rmod mmod
              (native_trace_window_of_CC_radial_PB_C11SP P g Rmod mmod (hXC hX)))))))

/-- **consumer（§2.3 验收形，PB 平凡时）**：G4 取到的 `(Rmod, mmod)` 若落在冻结门槛内
（`Rmod ≤ capWindowRadius_C11E + 1`、`mmod ≤ 2`），PB 形槽即冻结 `HSpineTwoLevelTime_C11G7B`，
直接喂冻结顶层 `a12EnhancedFull_of_gaps_v7two_C11G7B`——此时 spine 侧只剩 X。
一般 `(Rmod, mmod)` 走 HPBASE-V8 v8 引擎。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) (hp : HP6bTwoLevelTime_C11G7B.{u} P g) :
    ∃ Cbirth : ℝ, 0 < Cbirth ∧ ∀ C : ℝ≥0, ∃ (Rmod : ℝ) (mmod : ℕ) (εX : ℝ), 0 < εX ∧
    ((
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g),
        F.tower = S.tower → ∀ q : CutoffParameters,
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ εX → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
        Rmod ≤ pBase.modelRadius → mmod ≤ pBase.modelOrder →
      ∀ (params : CutoffParameters)
        (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
          GeometricCutoffRecord (F.tower.history n).toHistory e params),
        params.modelRadius = pBase.modelRadius → params.modelOrder = pBase.modelOrder →
        params.modelAccuracy = pBase.modelAccuracy →
        (∀ t : ℝ, 0 ≤ t → params.delta t = q.delta t ∧
          params.neckRadius t = q.neckRadius t) →
        (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
        (∀ n e, ((F.tower.history n).toHistory.event e).old =
          ((F.tower.history n).toHistory.event e).transition.trace.retainedCore) →
        Tendsto params.delta atTop (𝓝 0) →
        (∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
          ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
            (F.tower.history n).time e.succ ∈ Icc (t / 2) t →
            ∀ h, (records n e).nominalRadius h ≤ η * params.neckRadius t) →
      ∀ B : ℝ, 0 < B → ∃ T₀ : ℝ, 0 < T₀ ∧
      ∀ (n : ℕ) (θ : ℝ), 0 < θ → θ * B ≤ 1 / 16 →
      let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon), T₀ ≤ (t : ℝ) →
      ∀ Q : ℝ, (q.neckRadius t ^ 2)⁻¹ < Q →
      ∀ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t),
        (t : ℝ) - a ≤ θ / Q →
      ∀ (y : (H.stageAt t).Carrier)
        (A : BackwardPointTrace H
          (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) y),
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
          metricScalarAt (H.stageMetric (H.activeStage v) v)
            (A.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono hvt)) ≤ 2 * B * Q) →
      ∀ (e₁ e₂ : Fin H.eventCount) (hf₁ : H.activeStage a ≤ e₁.castSucc)
        (hl₁ : e₁.succ ≤ H.activeStage t) (_hf₂ : H.activeStage a ≤ e₂.castSucc)
        (_hl₂ : e₂.succ ≤ H.activeStage t), e₁ < e₂ →
      ∀ (b : (H.event e₁).RetainedBoundaryIndex) (z : standardCapWindow params.modelRadius),
        StandardCap.transitionEnd < ‖z.val‖ → ‖z.val‖ ≤ StandardCap.transitionEnd + 10 →
        ((records n e₁).static b).window z =
          A.point e₁.succ (hf₁.trans e₁.castSucc_lt_succ.le) hl₁ →
        ((records n e₁).static b).neck.scale ≤ 4 * (B * Q) →
      ∃ W : ∀ i : Fin (H.eventCount + 1), Set (H.stage i).Carrier, (∀ i, IsOpen (W i)) ∧
        (∀ (i : Fin (H.eventCount + 1)) (hf : e₁.succ ≤ i), i ≤ e₂.castSucc →
          ∀ (x' : (H.stage i).Carrier) (A' : BackwardPointTrace H e₁.succ i hf x'),
            A'.point e₁.succ le_rfl hf ∈
              ((records n e₁).static b).window '' {z | ‖z.val‖ < Rmod + 1} →
              x' ∈ W i) ∧
        (∀ i : Fin H.eventCount, e₁.succ ≤ i.castSucc → i.succ ≤ e₂.castSucc →
          ∀ x' : (H.stage i.castSucc).Carrier, x' ∈ W i.castSucc →
          ∀ τ ∈ Ioo (H.time i.castSucc) (H.time i.succ),
            Cbirth * ((records n e₁).static b).neck.scale < (H.event i).incoming.flow.scalar τ x' →
            |derivWithin (fun v => (H.event i).incoming.flow.scalar v x') (Iic τ) τ| ≤
              C * (H.event i).incoming.flow.scalar τ x' ^ 2) ∧
        (∀ x' : (H.stage e₂.castSucc).Carrier, x' ∈ W e₂.castSucc →
          ∀ τ ∈ Ioo (H.time e₂.castSucc) (H.time e₂.succ),
          Cbirth * ((records n e₁).static b).neck.scale < (H.event e₂).incoming.flow.scalar τ x' →
          |derivWithin (fun v => (H.event e₂).incoming.flow.scalar v x') (Iic τ) τ| ≤
            C * (H.event e₂).incoming.flow.scalar τ x' ^ 2)) →
    Rmod ≤ capWindowRadius_C11E + 1 → mmod ≤ 2 →
    A12EnhancedFullConclusion_C11F P g) := by
  obtain ⟨Cbirth, hCbirth, h⟩ := hspineTwoLevelTime_of_X_PB_C11SP.{u} P g
  refine ⟨Cbirth, hCbirth, fun C => ?_⟩
  obtain ⟨Rmod, mmod, εX, hεX, hXS⟩ := h C
  refine ⟨Rmod, mmod, εX, hεX, fun hX hR hm => ?_⟩
  obtain ⟨εsp, hεsp, hsl⟩ := hXS hX
  exact a12EnhancedFull_of_gaps_v7two_C11G7B P g
    ⟨εsp, hεsp, fun hFine S F q hT hdiag hacc hrad hord =>
      hsl hFine S F q hT hdiag hacc hrad hord ⟨hR.trans hrad, hm.trans hord⟩⟩ hp

end GC.LongTime.Ch11

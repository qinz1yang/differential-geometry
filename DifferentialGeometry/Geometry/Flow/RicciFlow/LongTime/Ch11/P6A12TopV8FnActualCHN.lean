import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6A12SlotsV8P6HV7
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6A12TopV8FnActualS14CXW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilHnDefsCHN

set_option autoImplicit false

/-!
# CHN G5b：v8 collar wrapper（HN ceiling）

CEIL-HN 孪生（O-CH11-CEILHN，后缀 `_CHN`）：自 `P6A12TopV8FnActualS14CXW.lean` 机械克隆
（生成器 `build-logs/scratch/CEILHN/gen/clone.py`），ceiling 常数换 HN 扩展。
-/

noncomputable section
universe u
section V8Engine
open Set Filter DifferentialGeometry MeasureTheory DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped NNReal Topology ContDiff Manifold ENNReal
namespace GC.LongTime.Ch11
open GC.LongTime.Ch11 (p6CoarseCHN_CHN one_le_p6CoarseCHN_CHN p6CoarseC_le_p6CoarseCHN_CHN)

/-- **`a12EnhancedFull_of_v8_collar_actual_S14CXW_CHN`**（collar 版 v8 合同形）：`X1 X2 := p6X1std /
    p6X2std`、`Ct := p6CtimeHN_CHN`。 -/
theorem a12EnhancedFull_of_v8_collar_actual_S14CXW_CHN (P : OrientedThreeStage.{u})
    (g : P.Metric)
    (Rn : ClosedBirthConstants → ℝ) (mn : ClosedBirthConstants → ℕ)
    (hspine : ∃ εsp : ClosedBirthConstants → ClosedBirthConstants → ℝ,
      (∀ Γ Γf, 0 < εsp Γ Γf) ∧
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ → ∀
      (S : PreparedSpatialChain pB Γf P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      TimeDerivativeSupply_C11E F q.neckRadius Γf.Ctime →
      pB.modelAccuracy ≤ εsp Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder → (Rn Γf ≤ pB.modelRadius ∧ mn Γf ≤ pB.modelOrder) →
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
        CanonicalLateTimeCore_P6X F Γ.epsilon (C1P6_C11GT6.{u} p6X1HN_CHN.{u} Γ)
          (C2P6_C11GT6.{u} p6X2HN_CHN.{u} Γ) (p6CtimeHN_CHN.{u} Γ) →
        LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A)
    (hp :
      ∃ εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ,
        (∀ Γ Γf, 0 < εP6 Γ Γf) ∧
        ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
        Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} → ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
          (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
        (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j (T.block j) (T.lookahead j)
          (T.request j)) →
        SameConstructionRetentionSupplyPlus_C11GT6 T →
        ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
        GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q →
        pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
        2 ≤ pB.modelOrder → collarAdmitsAllOrders_C11E.{u} pB.fixed.collarLength
          pB.fixed.collar_pos →
        CanonicalLateTimeCore_P6X F Γ.epsilon (C1P6_C11GT6.{u} p6X1HN_CHN.{u} Γ)
          (C2P6_C11GT6.{u} p6X2HN_CHN.{u} Γ) (p6CtimeHN_CHN.{u} Γ)) :
    A12EnhancedFullConclusion_C11F P g :=
  a12EnhancedFull_of_gaps_v8Collar_actual_S14CXW P g p6X1HN_CHN.{u} p6X2HN_CHN.{u}
    p6CtimeHN_CHN.{u} Rn mn hspine hp
end GC.LongTime.Ch11
end V8Engine

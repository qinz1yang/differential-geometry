import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NRPrimeRecentFnCXW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeWindowRadialSupFnP6XS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeNJSlotV3RadialSupFnP6XS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeRayNeckChainSupFnP6XS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeFlowRaySupFnP6XS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeOnlyNzeroSupFnP6XS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeExcludeSupFnP6XS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HSpineTwoLevelTimeSupFnP6XS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HSpineTwoLevelTimeGlueC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GuardRegimeFalseC11SP

set_option autoImplicit false

/-!
# Recent producer 接通完整 native spine / Complete native spine from actual recent data

新 X0 在实际 params/records 处生产 SEPseq，故此综合 consumer 无全球 SEPseq 前提。
复用 X1–X11 的已选请求函数与全部几何输出；epsilon_sp(Γ,Γf) 仍先于 A 选择。
公开结论保留原 hspine 的 TimeDerivativeSupply、same-tower 与 seed footprint 合同。
这是 spine 接线，不宣称其余 A12 slots 或 S14 的任意-q 旧槽已经关闭。
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

/-- 复用十一层并实际消去 SEPseq / Eleven-layer consumer with actual SEPseq producer. -/
theorem hspineTwoLevelTime_of_recent_PB_CXW (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ (Rn : ClosedBirthConstants → ℝ) (mn : ClosedBirthConstants → ℕ),
    ∃ εsp : ClosedBirthConstants → ClosedBirthConstants → ℝ,
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
        CanonicalLateTimeCore_P6X F Γ.epsilon (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ)
          (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ) (p6Ctime_C11G7B.{u} Γ) →
        LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A := by
  obtain ⟨Rn, mn, hN⟩ := hNRprime_of_recent_supply_CXW.{u} P g
  refine ⟨Rn, mn, ?_⟩
  exact hspineTwoLevelTime_SupFn_P6XS P g Rn mn
    (fun S F q hTower hdiag A hA hnot => regime_glue_C11SP S F q hTower hdiag A hA hnot)
    (guard_regime_false_final_C11SP P g)
    (native_regime_false_SupFn_P6XS P g Rn mn (guard_regime_false_final_C11SP P g)
      (native_hnreg_of_hnzero_SupFn_P6XS P g Rn mn
        (native_hnzero_of_flowRay_SupFn_P6XS P g Rn mn
          (hflowNRay_of_NJseg_SupFn_P6XS P g Rn mn
            (native_NJslot_of_SL1_v3_radial_SupFn_P6XS P g Rn mn
              (native_trace_window_of_CC_radial_SupFn_P6XS P g Rn mn
                (largeCap_crossing_count_of_nonResurgery_SupFn_P6XS P g Rn mn hN)))))))

end GC.LongTime.Ch11

import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NRPrimeSupFnP6XS
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
# 链顶：hspine（PB-fn + 供给形槽）⇐ (SEP-ρ⁺) 序列形（O-CH11-XSUP2 XT）

生成器 `build-logs/scratch/O-CH11-XSUP2/gen/gen_xt.py`。
NRPRIME G4 `hspineTwoLevelTime_of_X_PB_C11SP` 的孪生：
X0 `hNRprime_of_sepRho_supply_P6XS`（SEPseq → hNR′fn）∘ X1 CC′fn ∘
X2–X11 supply-threaded fn twin。
结论 = X11 `hspineTwoLevelTime_SupFn_P6XS` 结论逐字（= v8 collar 引擎 fn+SUP 孪生的 hspine 槽）：
PB 前提 `(Rn Γf ≤ pB.modelRadius ∧ mn Γf ≤ pB.modelOrder)`，`hdiag` 后供给前提
`TimeDerivativeSupply_C11E F q.neckRadius Γf.Ctime`（引擎在同一 `T.toChain / F / q` 处以 `hTD` 付）。
**PROVISIONAL[(SEP-ρ⁺)]**：SEPseq（`gen/sepseq.txt`，sha256 `b300b9e0…`）为唯一前提；
CE 已付（v3 radial）。
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

/-- **XT（PROVISIONAL[(SEP-ρ⁺)]）**：PB-fn + 供给形 hspine 槽 ⇐ SEPseq。 -/
theorem hspineTwoLevelTime_of_sepRho_PB_C11SP (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ (Rn : ClosedBirthConstants → ℝ) (mn : ClosedBirthConstants → ℕ),
    ((
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g),
        F.tower = S.tower → ∀ q : CutoffParameters,
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
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
      ∀ (ν : ℕ → ℕ) (t : ℕ → ℝ), Tendsto t atTop atTop → ∀ m : ℕ,
      ∀ᶠ k in atTop, ∀ (i : Fin (F.tower.history (ν k)).eventCount)
          (b : ((F.tower.history (ν k)).toHistory.event i).RetainedBoundaryIndex),
        (F.tower.history (ν k)).time i.succ ≤ t k →
        t k - (F.tower.history (ν k)).time i.succ ≤
          1 / 4 * (((records (ν k) i).static b).neck.scale)⁻¹ →
        ((m : ℝ) + 1) * max ((m : ℝ) + 1) (q.neckRadius (t k) ^ 2)⁻¹ ≤
          ((records (ν k) i).static b).neck.scale) →
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
        LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A) := by
  obtain ⟨Rn, mn, hN⟩ := hNRprime_of_sepRho_supply_P6XS.{u} P g
  refine ⟨Rn, mn, fun hSEP => ?_⟩
  exact hspineTwoLevelTime_SupFn_P6XS P g Rn mn
    (fun S F q hTower hdiag A hA hnot => regime_glue_C11SP S F q hTower hdiag A hA hnot)
    (guard_regime_false_final_C11SP P g)
    (native_regime_false_SupFn_P6XS P g Rn mn (guard_regime_false_final_C11SP P g)
      (native_hnreg_of_hnzero_SupFn_P6XS P g Rn mn
        (native_hnzero_of_flowRay_SupFn_P6XS P g Rn mn
          (hflowNRay_of_NJseg_SupFn_P6XS P g Rn mn
            (native_NJslot_of_SL1_v3_radial_SupFn_P6XS P g Rn mn
              (native_trace_window_of_CC_radial_SupFn_P6XS P g Rn mn
                (largeCap_crossing_count_of_nonResurgery_SupFn_P6XS P g Rn mn (hN hSEP))))))))

end GC.LongTime.Ch11

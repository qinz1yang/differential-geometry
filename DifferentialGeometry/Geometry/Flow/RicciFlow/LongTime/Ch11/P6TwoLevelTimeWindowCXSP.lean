import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PreparedTimeWindowCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilingC11GT6

set_option autoImplicit false

/-!
# CX-SPINE P-TIME：标准两级常数处的 actual window consumer

C_t* 的闭项体逐字取 max Γ.Ctime (C1P6 std Γ).toNNReal；它在选择 history/query 前固定。
G7B 文件尚未进入此批次 SNAP root66，故这里用闭项体，不自行编译 peer 文件。
Γf 用于真实 chain，Γ 用于 canonical/time ceiling；εsp 为双参数函数（本叶可取常值）。
此局部窗口无需 FineOf，因此可直接在新版合同已有的 FineOf Γf Γ 环境内应用。
不声称此 consumer 的输出已是 LargerBallScalarAt，亦不声称上游 selected closure 已付。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

/-- 新版两级合同的标准 ceiling 实例；双参数 εsp 在两级参数之前选择。 -/
theorem exists_twoLevel_time_trace_window_CXSP
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ εsp : ClosedBirthConstants → ClosedBirthConstants → ℝ,
      (∀ Γ Γf, 0 < εsp Γ Γf) ∧
      ∀ {pBase : CutoffParameters} {Γ Γf : ClosedBirthConstants}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ εsp Γ Γf → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
        CanonicalLateTimeCore_P6X F Γ.epsilon
          (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ)
          (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ)
          (max Γ.Ctime (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ).toNNReal) →
      ∀ Afac : ℝ, 1 < Afac → ∃ H0 : ℝ, 4 ≤ H0 ∧
        ∀ d0 Δ γ : ℝ, 0 ≤ d0 → 0 < Δ → 0 < γ → d0 + Δ + γ ≤ Afac →
        ∃ lam0 β0 : ℝ, 0 < lam0 ∧ 0 < β0 ∧
        ∀ m : ℝ, 1 / 2 ≤ m → ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        let Q := H0 * (r ^ 2)⁻¹
        let ell := (lam0 / (m + 1)) / Real.sqrt Q
        let β := β0 / (m + 1)
        T₀ ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (Afac⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        q.neckRadius t ≤ r →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ x : (H.stageAt t).Carrier,
          metricScalarAt (H.stageMetric (H.activeStage t) t) x ≤ m * Q →
          riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x ≤ ENNReal.ofReal (d0 * r) →
        ∃ (a : Icc (0 : ℝ) H.horizon) (haa : aSeed ≤ a) (hat : a ≤ t),
          (a : ℝ) = (t : ℝ) - β / Q ∧ Q * ((t : ℝ) - a) = β ∧
          ∃ B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
            (H.activeStage_mono hat) x,
          let A := seedTrace.restrictFirst (H.activeStage_mono haa) (H.activeStage_mono hat)
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
            A.pairEDist_CXSP (hat := hat) B v hav hvt < ENNReal.ofReal ((d0 + Δ) * r) ∧
              A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
                A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
                  ENNReal.ofReal ((8 / ell) * ((t : ℝ) - v)) := by
  obtain ⟨ε₀, hε₀, hwindow⟩ := exists_prepared_time_trace_window_CXSP P g
  refine ⟨fun _ _ => ε₀, fun _ _ => hε₀, ?_⟩
  intro pBase Γ Γf S F q hTower hdiag hacc hrad hord hb
  exact hwindow S F q hTower hdiag hacc hrad hord hb

end GC.LongTime.Ch11

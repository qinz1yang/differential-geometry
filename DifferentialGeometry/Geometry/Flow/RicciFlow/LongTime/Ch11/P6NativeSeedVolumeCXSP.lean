import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalScalarGapVolumeCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SurgerySuppliesC11S

set_option autoImplicit false

/-!
# CX-SPINE G10：native canonical 供给给实际高中心测试球 κ

同一 history / time / metric 上，native S5 供给中心 witness，低曲率同分支点排除 round。
受控球的实际 terminal curvature bound 支付 static volume theorem 的中心 Rm 条件。
κ 在 F/q/history/time/points/radius 之前选定；未声称覆盖低于 native threshold 的中心。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

/-- native S5 和同分支 scalar gap 给实际受控球的统一 κ 下界。 -/
theorem native_tested_kappa_of_scalar_gap_CXSP (ε C1 C2 : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ {P : OrientedThreeStage.{u}} {g : P.Metric}
      {F : GC.Interface.RawSurgery P g} {q : CutoffParameters},
      HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 →
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (v : Icc (0 : ℝ) H.horizon) (x p : (H.stageAt v).Carrier),
      p ∈ connectedComponent x →
      (q.neckRadius v ^ 2)⁻¹ < metricScalarAt (H.stageMetric (H.activeStage v) v) x →
      C2 * metricScalarAt (H.stageMetric (H.activeStage v) v) p <
        metricScalarAt (H.stageMetric (H.activeStage v) v) x →
      ∀ b : ℝ, H.isParabolicallyRmControlledBall v x b →
        ENNReal.ofReal (κ * b ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage v) v) x b := by
  obtain ⟨κ, hκ, hvol⟩ :=
    exists_ball_volume_of_spatialCanonicalWitness_of_scalar_gap_CXSP.{u} ε C1 C2
  refine ⟨κ, hκ, ?_⟩
  intro P g F q hcan n H v x p hp hR hgap b hball
  obtain ⟨W, hchart⟩ := hcan n v x hR
  have hx : x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v) x b := by
    change riemannianEDistOf _ x x < ENNReal.ofReal b
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hball.1
  exact hvol W hchart p hp hgap b hball.1
    (ObservedHistory.isParabolicallyRmControlledBall.terminal_curvature_bound H hball x hx)

/-- 实际 native 小种子支付 scalar gap，故同分支全部高中心都有 κ-tested volume。 -/
theorem native_small_seed_tested_kappa_CXSP (ε C1 C2 : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ {P : OrientedThreeStage.{u}} {g : P.Metric}
      {F : GC.Interface.RawSurgery P g} {q : CutoffParameters},
      HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 →
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
      hasSmallParabolicCurvature H t p r → r ≤ q.neckRadius t →
      ∀ x ∈ connectedComponent p,
      4 * max C2 1 * (r ^ 2)⁻¹ ≤ metricScalarAt (H.stageMetric (H.activeStage t) t) x →
      ∀ b : ℝ, H.isParabolicallyRmControlledBall t x b →
        ENNReal.ofReal (κ * b ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) x b := by
  obtain ⟨κ, hκ, hvol⟩ := native_tested_kappa_of_scalar_gap_CXSP.{u} ε C1 C2
  refine ⟨κ, hκ, ?_⟩
  intro P g F q hcan n H t p r hsmall hradius x hx hR b hball
  have hr : 0 < r := hsmall.1
  have hi : 0 < (r ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_pos hr)
  have hm : 1 ≤ max C2 1 := le_max_right _ _
  have hnative : (q.neckRadius t ^ 2)⁻¹ <
      metricScalarAt (H.stageMetric (H.activeStage t) t) x := by
    have hle := (inv_le_inv₀ (sq_pos_of_pos (q.neckRadius_pos t t.2.1))
      (sq_pos_of_pos hr)).mpr (pow_le_pow_left₀ hr.le hradius 2)
    exact hle.trans_lt (lt_of_lt_of_le (by nlinarith) hR)
  obtain ⟨W, -⟩ := hcan n t x hnative
  have hC2 : 0 < C2 := zero_lt_one.trans_le W.one_le_comparison_constant
  have hpball : p ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r := by
    change riemannianEDistOf _ p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  have hpR := (le_abs_self _).trans
    (hasSmallParabolicCurvature_scalar_abs_le_C11S hsmall hpball)
  have hgap : C2 * metricScalarAt (H.stageMetric (H.activeStage t) t) p <
      metricScalarAt (H.stageMetric (H.activeStage t) t) x := by
    calc
      _ ≤ C2 * (3 * (r ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hpR hC2.le
      _ ≤ 3 * max C2 1 * (r ^ 2)⁻¹ := by
        nlinarith [mul_le_mul_of_nonneg_right (le_max_left C2 1) hi.le]
      _ < 4 * max C2 1 * (r ^ 2)⁻¹ := by
        nlinarith [mul_pos (zero_lt_one.trans_le hm) hi]
      _ ≤ _ := hR
  have hp : p ∈ connectedComponent x := by
    rw [← connectedComponent_eq hx]
    exact mem_connectedComponent
  exact hvol hcan n t x p hp hnative hgap b hball

end GC.LongTime.Ch11

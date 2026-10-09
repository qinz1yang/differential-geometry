import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedScaleP6A
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedComponentCXSP

set_option autoImplicit false

/-!
# CX-SPINE G12：同一 seed 球实际支付 canonical-base scalar gap

仅用小 seed 的中心 scalar 界、同一球的 canonical supply 和固定 ceiling。
球成员关系支付同一 connectedComponent；不使用 P6(b) 的 non-Good 反证序列。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

/-- 同一 seed 的低点和 canonical supply 生产 volume consumer 所需的全部 base 数据。 -/
theorem exists_seed_volume_base_CXSP
    {H : ObservedHistory.{u}} {t : Icc (0 : ℝ) H.horizon}
    {p x : (H.stageAt t).Carrier} {r A Kb ε C1 C2 : ℝ}
    (hsmall : hasSmallParabolicCurvature H t p r)
    (hx : x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r))
    (hhigh : max Kb (4 * max C2 1) * (r ^ 2)⁻¹ ≤
      metricScalarAt (H.stageMetric (H.activeStage t) t) x)
    (hcan : ∀ y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
      Kb * (r ^ 2)⁻¹ ≤ metricScalarAt (H.stageMetric (H.activeStage t) t) y →
      ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage t) t) ε C1 C2 y,
        W.capTubeHasNeckChart ε) :
    ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage t) t) ε C1 C2 x,
      W.capTubeHasNeckChart ε ∧ p ∈ connectedComponent x ∧
        C2 * metricScalarAt (H.stageMetric (H.activeStage t) t) p <
          metricScalarAt (H.stageMetric (H.activeStage t) t) x := by
  have hr : 0 < r := hsmall.1
  have hi : 0 < (r ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_pos hr)
  have hKb : Kb * (r ^ 2)⁻¹ ≤ metricScalarAt (H.stageMetric (H.activeStage t) t) x :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hi.le).trans hhigh
  obtain ⟨W, hchart⟩ := hcan x hx hKb
  have hC2 : 0 < C2 := zero_lt_one.trans_le W.one_le_comparison_constant
  have hxcomp : x ∈ connectedComponent p :=
    Geometry.Metric.edistOf_ball_subset_connCompOpen
      (H.stageMetric (H.activeStage t) t) p (A * r) hx
  have hpcomp : p ∈ connectedComponent x := by
    rw [← connectedComponent_eq hxcomp]
    exact mem_connectedComponent
  refine ⟨W, hchart, hpcomp, ?_⟩
  have hpball : p ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r := by
    change riemannianEDistOf _ p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  have hpR := (le_abs_self _).trans
    (hasSmallParabolicCurvature_scalar_abs_le_C11S hsmall hpball)
  have hmax : 0 < max C2 1 := zero_lt_one.trans_le (le_max_right _ _)
  calc
    _ ≤ C2 * (3 * (r ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hpR hC2.le
    _ ≤ 3 * max C2 1 * (r ^ 2)⁻¹ := by
      nlinarith [mul_le_mul_of_nonneg_right (le_max_left C2 1) hi.le]
    _ < 4 * max C2 1 * (r ^ 2)⁻¹ := by nlinarith [mul_pos hmax hi]
    _ ≤ max Kb (4 * max C2 1) * (r ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hi.le
    _ ≤ _ := hhigh

/-- 原 seed 中心作为 volume consumer 的同分支低点，无额外 scalar-gap binder。 -/
example {H : ObservedHistory.{u}} {t : Icc (0 : ℝ) H.horizon}
    {p x : (H.stageAt t).Carrier} {r A Kb ε C1 C2 : ℝ}
    (hsmall : hasSmallParabolicCurvature H t p r)
    (hx : x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r))
    (hhigh : max Kb (4 * max C2 1) * (r ^ 2)⁻¹ ≤
      metricScalarAt (H.stageMetric (H.activeStage t) t) x)
    (hcan : ∀ y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
      Kb * (r ^ 2)⁻¹ ≤ metricScalarAt (H.stageMetric (H.activeStage t) t) y →
      ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage t) t) ε C1 C2 y,
        W.capTubeHasNeckChart ε) :
    ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage t) t) ε C1 C2 x,
      W.capTubeHasNeckChart ε ∧ ∃ y ∈ connectedComponent x,
        C2 * metricScalarAt (H.stageMetric (H.activeStage t) t) y <
          metricScalarAt (H.stageMetric (H.activeStage t) t) x := by
  obtain ⟨W, hchart, hpcomp, hgap⟩ := exists_seed_volume_base_CXSP hsmall hx hhigh hcan
  exact ⟨W, hchart, p, hpcomp, hgap⟩

end GC.LongTime.Ch11

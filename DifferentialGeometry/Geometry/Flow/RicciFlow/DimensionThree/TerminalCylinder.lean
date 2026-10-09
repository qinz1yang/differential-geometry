import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.TerminalRigidity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderModelEvolution
import DifferentialGeometry.Geometry.Curvature.RoundCylinder
import DifferentialGeometry.Topology.Covering.CylindricalModel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ShrinkingCylinder

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set
open Perelman.KappaSolutions
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold ContDiff

private local instance sphereTwoDimensionRigidity :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

theorem metric_eq_scalarOneShrinkingCylinderMetric_of_terminal_roundCylinderMetric
    {D : RealTimeInterval}
    (S : SolutionOn (I := SpatialNeckCylinderModel) (M := SpatialNeckCylinder) D)
    (hS : IsSolutionOn S) {a : ℝ} (ha : a < 0)
    (hcar : Icc a 0 ⊆ D.carrier) (hreg : Ioo a 0 ⊆ D.regular)
    (hR : ∀ t ∈ Icc a 0, ∀ x,
      metricAlgebraicCurvatureTensorAt (S.family.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone)
    (hbound : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc a 0, ∀ x,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K)
    (hzero : S.family.metric 0 = Geometry.Metric.roundCylinderMetric
      (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) :
    ∀ t, ∀ ht : t ∈ Icc a 0, S.family.metric t =
      scalarOneShrinkingCylinderMetric t (ht.2.trans_lt zero_lt_one) := by
  let _ : SimplyConnectedSpace SpatialNeckCylinder :=
    DifferentialGeometry.Topology.simplyConnectedSpace_sphereTwo_prod_real
  have hcomplete : RiemannianMetricComplete (S.base.metric 0) := by
    change RiemannianMetricComplete (S.family.metric 0)
    rw [hzero, ← doubleSphereCylinderMetric_eq_roundCylinderMetric,
      doubleSphereCylinderMetric_eq_roundThreeCylinderShrinkerMetric]
    exact roundThreeCylinderShrinkerMetric_complete
  let x₀ : SpatialNeckCylinder := Classical.choice inferInstance
  have hrank : Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric 0) x₀
      (metricAlgebraicCurvatureTensorAt (S.family.metric 0) x₀)) = 1 := by
    rw [hzero]
    exact DimensionThree.curvatureOperatorImageAt_finrank_roundCylinder x₀
  have hscalar (x : SpatialNeckCylinder) : S.scalar 0 x = 1 := by
    change metricScalarAt (S.family.metric 0) x = 1
    rw [hzero, metricScalarAt_roundCylinder]
    norm_num
  have haffine := metric_inner_eq_affine_ricci_of_terminal_rank_one_and_scalar_constant_of_simplyConnected
    S hS (by simp [Module.finrank_prod]) ha hcar hreg hR
    hcomplete hbound x₀ hrank hscalar
  intro t ht
  apply eq_shrinkingCylinderMetric_of_inner_eq_sub_two_mul_ricci_of_roundCylinderMetric
  intro x v w
  have hh := haffine t ht x v w
  rw [hzero] at hh
  convert hh using 1
  ring

theorem metric_eq_shrinkingCylinderMetric_of_terminal_roundCylinderMetric
    {D : RealTimeInterval}
    (S : SolutionOn (I := SpatialNeckCylinderModel) (M := SpatialNeckCylinder) D)
    (hS : IsSolutionOn S) {a : ℝ} (ha : a < 0)
    (hcar : Icc a 0 ⊆ D.carrier) (hreg : Ioo a 0 ⊆ D.regular)
    (hR : ∀ t ∈ Icc a 0, ∀ x,
      metricAlgebraicCurvatureTensorAt (S.family.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone)
    (hbound : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc a 0, ∀ x,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K)
    (hzero : S.family.metric 0 = Geometry.Metric.roundCylinderMetric
      (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) :
    ∀ t ∈ Icc a 0, S.family.metric t =
      DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric
        (E := EuclideanSpace ℝ (Fin 3)) t := by
  intro t ht
  rw [metric_eq_scalarOneShrinkingCylinderMetric_of_terminal_roundCylinderMetric
    S hS ha hcar hreg hR hbound hzero t ht]
  apply SmoothRiemannianMetric.ext_inner
  rintro ⟨y,z⟩ ⟨v,c⟩ ⟨w,d⟩
  erw [scalarOneShrinkingCylinderMetric_inner,
    DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_inner
      (ht.2.trans_lt zero_lt_one)]

end DifferentialGeometry.PDE.RicciFlow

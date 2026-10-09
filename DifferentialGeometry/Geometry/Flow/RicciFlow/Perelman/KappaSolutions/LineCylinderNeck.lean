import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SeparatedRayCylinderBranch
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderNecks

set_option autoImplicit false

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem exists_trivial_shrinkingCylinderCover_of_line
    (P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hP : IsAncientKappaSolution kappa P) (hbase : PointedFlowScalarAtBase P 1)
    (o : TangentOrientationSection P.M) (γ : ℝ → P.M)
    (hγ : ∀ a b, metricDistance (P.S.base.metric 0) (γ a) (γ b) = |a - b|)
    (hγ0 : γ 0 = P.basepoint) :
    ∃ C : ShrinkingCylinderCover P, C.TrivialModel := by
  refine exists_trivial_shrinkingCylinderCover_of_rays_comparisonAngle_lower P hP hbase o
    (fun r => γ r) (fun r => γ (-(r : ℝ))) ?_ ?_ (by simpa using hγ0) (by simpa using hγ0)
    Real.pi_pos ?_
  · intro a b
    rw [hγ, NNReal.dist_eq]
  · intro a b
    rw [hγ, NNReal.dist_eq, neg_sub_neg, abs_sub_comm]
  · filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with r hr
    have hr' : (0 : ℝ) < r := hr
    rw [hγ, sub_neg_eq_add, abs_of_pos (add_pos hr' hr'), comparisonAngle_add hr' hr']

theorem exists_strongNeck_of_line
    (P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hP : IsAncientKappaSolution kappa P) (hbase : PointedFlowScalarAtBase P 1)
    (o : TangentOrientationSection P.M) (γ : ℝ → P.M)
    (hγ : ∀ a b, metricDistance (P.S.base.metric 0) (γ a) (γ b) = |a - b|)
    (hγ0 : γ 0 = P.basepoint) {eps : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11) :
    Nonempty (StrongNeck P.S eps P.basepoint 0) := by
  obtain ⟨C, hC⟩ := exists_trivial_shrinkingCylinderCover_of_line P hP hbase o γ hγ hγ0
  obtain ⟨_p, _e, _, _, hnecks⟩ :=
    exists_strongNeck_of_shrinkingCylinderCover_trivialModel P C hC hbase
  obtain ⟨N, _⟩ := hnecks eps heps hsmall
  exact ⟨N⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

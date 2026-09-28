import DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotients
import DifferentialGeometry.Geometry.Metric.Pullback.LocalComposition
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderCoverScalarNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderMetric

section

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

private local instance diagonalCoverSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

theorem ShrinkingCylinderCover.exists_diagonal_shrinking_model
    (P : PointedFlowData.{u, 0, 0} ThreeModel ancientTimeInterval)
    (C : ShrinkingCylinderCover P) (hdiagonal : C.DiagonalModel)
    (hbase : PointedFlowScalarAtBase P 1) :
    ∃ d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮SpatialNeckCylinderModel, ThreeModel⟯ P.M,
      (∀ p : SpatialNeckCylinder, d (cylinderDiagonalQuotientMap p) = C.projection p) ∧
      ∀ t : ℝ, ∀ ht : t ≤ 0,
        localPullMetric (Diffeomorph.pullbackMetricCross (P.S.base.metric t) d)
          cylinderDiagonalQuotientMap cylinderDiagonalQuotientMap_isLocalDiffeomorph =
            scalarOneShrinkingCylinderMetric t (ht.trans_lt (by norm_num)) := by
  obtain ⟨d, hd⟩ := hdiagonal.1
  have hprojection (p : SpatialNeckCylinder) :
      d (cylinderDiagonalQuotientMap p) = C.projection p := hd p
  have hcomp : (d : Geometry.CylinderDiagonalQuotient → P.M) ∘
      cylinderDiagonalQuotientMap = C.projection := funext hprojection
  refine ⟨d, hprojection, ?_⟩
  intro t ht
  have hmetric : localPullMetric (P.S.base.metric t) C.projection C.projection_local =
      scalarOneShrinkingCylinderMetric t (ht.trans_lt (by norm_num)) := by
    apply SmoothRiemannianMetric.ext_inner
    intro z V W
    have hpull := localPullMetric_inner (P.S.base.metric t) C.projection C.projection_local z V W
    have hh := C.projection_metric t ht z.1 z.2 V.1 W.1 V.2 W.2
    rw [C.extinctionTime_eq_one_of_scalar_at_base_one hbase] at hh
    exact hpull.trans (hh.trans (scalarOneShrinkingCylinderMetric_inner t _ z.1 z.2 V.1 W.1 V.2 W.2).symm)
  rw [Diffeomorph.pullbackMetricCross_eq_localPullMetric]
  have hcompose := localPullMetric_comp (P.S.base.metric t) d cylinderDiagonalQuotientMap
    d.isLocalDiffeomorph cylinderDiagonalQuotientMap_isLocalDiffeomorph
    (isLocalDiffeomorph_comp d.isLocalDiffeomorph cylinderDiagonalQuotientMap_isLocalDiffeomorph)
  rw [hcompose]
  simpa only [hcomp] using hmetric

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end

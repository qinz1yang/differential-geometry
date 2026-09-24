import DifferentialGeometry.Topology.ProjectiveSpace.CylinderQuotientSmoothModels
import DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotients

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient

theorem exists_homeomorph_orbitQuotient :
    ∃ e : CylinderDiagonalQuotient ≃ₜ DifferentialGeometry.Geometry.CylinderDiagonalQuotient,
      ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ,
        e (proj p) = DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap p := by
  apply exists_homeomorph DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap
    DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_isLocalDiffeomorph.contMDiff.continuous
    DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_isLocalDiffeomorph.isOpenMap
    DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_surjective
  intro p q
  rw [eq_comm, DifferentialGeometry.Geometry.cylinderDiagonalQuotientMap_eq_iff]
  rfl

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient

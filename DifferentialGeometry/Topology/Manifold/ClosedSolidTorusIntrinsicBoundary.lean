import DifferentialGeometry.Topology.Manifold.ClosedSolidTorusBoundary
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

theorem closedSolidTorus_boundary :
    ((𝓡∂ 2).prod (𝓡 1)).boundary (ClosedCell 2 × Circle) =
      {x | ‖x.1.val‖ = 1} := by
  rw [ModelWithCorners.boundary_of_boundaryless_right, closedCell_boundary_eq_sphere 1]
  ext x
  change (‖x.1.val‖ = 1 ∧ True) ↔ ‖x.1.val‖ = 1
  simp only [and_true]

theorem range_closedSolidTorusBoundary_eq_boundary :
    Set.range closedSolidTorusBoundary =
      ((𝓡∂ 2).prod (𝓡 1)).boundary (ClosedCell 2 × Circle) := by
  rw [closedSolidTorus_boundary, range_closedSolidTorusBoundary]

theorem closedSolidTorus_interior :
    ((𝓡∂ 2).prod (𝓡 1)).interior (ClosedCell 2 × Circle) =
      {x | ‖x.1.val‖ < 1} := by
  rw [← ModelWithCorners.compl_boundary, closedSolidTorus_boundary]
  ext x
  change ¬‖x.1.val‖ = 1 ↔ ‖x.1.val‖ < 1
  exact (lt_iff_le_and_ne.trans (and_iff_right x.1.property)).symm

end DifferentialGeometry.Topology.Manifold

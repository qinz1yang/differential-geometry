import DifferentialGeometry.Topology.ThreeManifold.Geometrization.SolidTorusCarrier
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Presentation

set_option autoImplicit false
noncomputable section
open DifferentialGeometry.Topology.Manifold GC.Endpoint
open scoped Manifold ContDiff

namespace GC.GraphManifold

def closedSolidTorusBoundaryTori : BoundaryTori closedSolidTorusCarrier 1 where
  collar _ := closedSolidTorusCarrierCollar
  source_eq _ := closedSolidTorusCarrierCollar_source
  boundary_zero _ z := by
    change closedSolidTorusCarrierCollar (z, halfZero) ∈
      closedSolidTorusCarrier.model.boundary closedSolidTorusCarrier.Carrier
    rw [closedSolidTorusCarrierCollar_zero, closedSolidTorusCarrier_boundary]
    exact closedDiskBoundary_norm z.1
  disjoint i j hij := (hij (Subsingleton.elim i j)).elim

theorem closedSolidTorusBoundaryTori_torusMap (i : Fin 1) (z : Torus) :
    closedSolidTorusBoundaryTori.torusMap i z = closedSolidTorusBoundary z :=
  closedSolidTorusCarrierCollar_zero z

theorem closedSolidTorusBoundaryTori_image :
    closedSolidTorusBoundaryTori.image = Set.range closedSolidTorusBoundary := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨i, z, hz⟩ := Set.mem_iUnion.mp hx
    exact ⟨z, (closedSolidTorusBoundaryTori_torusMap i z).symm.trans hz⟩
  · rintro x ⟨z, rfl⟩
    exact Set.mem_iUnion.mpr ⟨0, z, closedSolidTorusBoundaryTori_torusMap 0 z⟩

theorem closedSolidTorusBoundaryTori_exhausted :
    closedSolidTorusCarrier.model.boundary closedSolidTorusCarrier.Carrier =
      closedSolidTorusBoundaryTori.image :=
  closedSolidTorusCarrier_boundary.trans
    (range_closedSolidTorusBoundary.symm.trans closedSolidTorusBoundaryTori_image.symm)

end GC.GraphManifold

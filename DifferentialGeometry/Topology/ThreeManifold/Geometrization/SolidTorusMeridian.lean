import DifferentialGeometry.Topology.ThreeManifold.Geometrization.SolidTorusCarrier
import DifferentialGeometry.Topology.Manifold.ProductSectionEmbedding
import DifferentialGeometry.Topology.Manifold.SmoothModelTransportTarget

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff

namespace GC.Endpoint

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

def closedSolidTorusMeridianDisk (w : Circle) (x : ClosedCell 2) :
    closedSolidTorusCarrier.Carrier := closedSolidTorusCarrierDiffeomorph (x, w)

theorem closedSolidTorusMeridianDisk_apply (w : Circle) (x : ClosedCell 2) :
    closedSolidTorusMeridianDisk w x = (x, w) := rfl

theorem closedSolidTorusMeridianDisk_contMDiff (w : Circle) :
    ContMDiff (𝓡∂ 2) closedSolidTorusCarrier.model ∞ (closedSolidTorusMeridianDisk w) :=
  closedSolidTorusCarrierDiffeomorph.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)

theorem closedSolidTorusMeridianDisk_isSmoothEmbedding (w : Circle) :
    Manifold.IsSmoothEmbedding (𝓡∂ 2) closedSolidTorusCarrier.model ∞
      (closedSolidTorusMeridianDisk w) :=
  DifferentialGeometry.Manifold.isSmoothEmbedding_chartedSpaceTransHomeomorph_target
    (M := ClosedCell 2) (N := ClosedCell 2 × Circle)
    ((𝓡∂ 2).prod (𝓡 1)) (𝓡∂ 3)
    (DifferentialGeometry.Manifold.euclideanHalfSpaceProdLeftHomeomorph 1 1)
    (DifferentialGeometry.Manifold.euclideanHalfSpaceProdLeftCoordinates 1 1)
    (DifferentialGeometry.Manifold.euclideanHalfSpaceProdLeftHomeomorph_model 1 1) (𝓡∂ 2)
    (Manifold.isSmoothEmbedding_prodMk_const (M := ClosedCell 2) (I := 𝓡∂ 2) (n := ∞) w)

theorem closedSolidTorusMeridianDisk_boundary (w z : Circle) :
    closedSolidTorusMeridianDisk w (closedDiskBoundary z) =
      closedSolidTorusBoundary (z, w) := rfl

theorem closedSolidTorusMeridianDisk_boundary_slope (w z : Circle) :
    closedSolidTorusMeridianDisk w (closedDiskBoundary z) =
      closedSolidTorusBoundary (Circle.slopeMap ![1, 0] z * (1, w)) := by
  rw [closedSolidTorusMeridianDisk_boundary]
  congr 1
  apply Prod.ext <;> simp [Circle.slopeMap]

theorem closedSolidTorusMeridianDisk_preimage_boundary (w : Circle) :
    closedSolidTorusMeridianDisk w ⁻¹'
      closedSolidTorusCarrier.model.boundary closedSolidTorusCarrier.Carrier =
        (𝓡∂ 2).boundary (ClosedCell 2) := by
  rw [closedSolidTorusCarrier_boundary, closedCell_boundary_eq_sphere 1]
  rfl

theorem range_closedSolidTorusMeridianDisk (w : Circle) :
    Set.range (closedSolidTorusMeridianDisk w) = {x | x.2 = w} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro hx
    exact ⟨x.1, Prod.ext rfl hx.symm⟩

end GC.Endpoint

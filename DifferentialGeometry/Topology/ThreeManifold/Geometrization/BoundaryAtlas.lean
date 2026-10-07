import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Orientation
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Inclusion
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.Carrier

noncomputable section

namespace GC.Endpoint.CompactCarrier

open DifferentialGeometry DifferentialGeometry.Topology
open Manifold
open scoped Manifold ContDiff

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] {K : Set M}
  (A : SmoothBoundaryAtlas (𝓡 3) 3 K)
  (O : ManifoldOrientation (𝓡 3) M 3) (hK : IsCompact K)

abbrev ofBoundaryAtlas : CompactCarrier where
  kind := .withBoundary
  Carrier := K
  charts := A.toChartedSpace
  smooth := A.isManifold
  compact := isCompact_iff_compactSpace.mp hK
  secondCountable := by
    let _ := A.toChartedSpace
    let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
    let _ : SecondCountableTopology (EuclideanHalfSpace 3) :=
      inferInstanceAs (SecondCountableTopology {x : EuclideanSpace ℝ (Fin 3) // 0 ≤ x 0})
    exact ChartedSpace.secondCountable_of_sigmaCompact (EuclideanHalfSpace 3) K
  orientation := A.orientation O

theorem ofBoundaryAtlas_isSmoothEmbedding :
    let _ := (ofBoundaryAtlas A O hK).charts
    IsSmoothEmbedding (ofBoundaryAtlas A O hK).model (𝓡 3) ∞
      (Subtype.val : (ofBoundaryAtlas A O hK).Carrier → M) := by
  let _ := (ofBoundaryAtlas A O hK).charts
  exact A.isSmoothEmbedding_subtype_val

theorem ofBoundaryAtlas_orientation_map (x : K) :
    let _ := (ofBoundaryAtlas A O hK).charts
    let _ := (ofBoundaryAtlas A O hK).smooth
    Orientation.map (Fin 3) (A.inclusionDifferentialEquiv x).toLinearEquiv
      ((ofBoundaryAtlas A O hK).orientation.orientation x) = O.orientation x.val := by
  let _ := (ofBoundaryAtlas A O hK).charts
  let _ := (ofBoundaryAtlas A O hK).smooth
  exact A.orientation_map_inclusion O x

end GC.Endpoint.CompactCarrier

import DifferentialGeometry.Topology.Manifold.ImmersionInterior
import DifferentialGeometry.Topology.ThreeManifold.CutCap

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

theorem exists_coreInterior_partialDiffeomorph (x : T.core) :
    letI := C.coreCharts
    (𝓡∂ 3).IsInteriorPoint x →
    ∃ (G : _root_.PartialDiffeomorph (𝓡 3) (𝓡 3) N.Carrier M.Carrier ∞) (U : Set T.core),
      IsOpen U ∧ x ∈ U ∧ C.coreInclusion x ∈ G.source ∧
      ∀ y ∈ U, C.coreInclusion y ∈ G.source ∧ G (C.coreInclusion y) = y.val := by
  let _ := C.coreCharts
  let _ := C.coreSmooth
  intro hx
  exact Manifold.exists_partialDiffeomorph_comp_eq_of_isInteriorPoint
    C.core_embedding.isImmersion C.core_induced.isImmersion hx rfl rfl

end DifferentialGeometry.Topology.SphericalCapping

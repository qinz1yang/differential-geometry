import DifferentialGeometry.Topology.PiecewiseLinear.Atlas.Compact
import DifferentialGeometry.Topology.PiecewiseLinear.Smoothing.Compact

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem exists_isManifold_three {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] :
    ∃ C : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
      letI := C
      IsManifold (𝓡 3) ∞ M := by
  obtain ⟨C, hC⟩ := exists_chartedSpace_hasGroupoid_plGroupoid_three (X := M)
  let := C
  let : HasGroupoid M (plGroupoid 3) := hC
  exact exists_isManifold_of_hasGroupoid_plGroupoid_three (X := M)

end DifferentialGeometry.Topology.PiecewiseLinear

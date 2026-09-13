import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TransverseCrossingSide

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Topology.SphereSeparation (SphereSides)

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M]

omit [IsManifold I3 ∞ M] in
theorem not_isPreconnected_compl_and_not_mem_connectedComponentIn_of_sphereSides
    {sphere : Set M} (d : SphereSides sphere) :
    ¬ IsPreconnected sphereᶜ ∧
      ∀ {p z : M}, p ∉ sphere → z ∉ sphere → (c : TransversePath p z sphere) →
        (c.intersection = 1 ∨ c.intersection = -1) →
          z ∉ connectedComponentIn sphereᶜ p :=
  ⟨d.not_isPreconnected_compl, fun hp hz c hint =>
    c.not_mem_connectedComponentIn_of_intersection d hp hz hint⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

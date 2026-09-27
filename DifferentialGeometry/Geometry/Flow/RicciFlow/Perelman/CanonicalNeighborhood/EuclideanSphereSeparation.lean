import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TransverseCrossingSeparation
import DifferentialGeometry.Topology.SphereSeparation.SourceTheorems

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Topology.SphereSeparation

universe u

variable {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
  [IsManifold I3 ∞ N]

theorem not_isPreconnected_compl_and_not_mem_connectedComponentIn_of_diffeomorph_euclidean
    (e : Sphere 2 → N) (he : Manifold.IsSmoothEmbedding I2 I3 ∞ e)
    (ψ : Diffeomorph I3 I3 N ThreeSpace ∞) :
    ¬ IsPreconnected (Set.range e)ᶜ ∧
      ∀ {p z : N}, p ∉ Set.range e → z ∉ Set.range e →
        (c : TransversePath p z (Set.range e)) →
        (c.intersection = 1 ∨ c.intersection = -1) →
          z ∉ connectedComponentIn (Set.range e)ᶜ p :=
  not_isPreconnected_compl_and_not_mem_connectedComponentIn_of_sphereSides
    (jordanBrouwer_openThreeSpace e he ψ).toSphereSides

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

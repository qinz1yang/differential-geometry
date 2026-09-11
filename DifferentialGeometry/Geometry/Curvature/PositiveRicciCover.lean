import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.PositiveRicci.Hamilton
import DifferentialGeometry.Geometry.Curvature.SphericalCover

open Manifold
open scoped ContDiff

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Topology.ThreeManifold
open DifferentialGeometry.Topology

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [SigmaCompactSpace M]

theorem exists_spherical_cover_of_admits_positive_ricci
    (hM : isClosedThreeManifold (I := 𝓡 3) (M := M))
    (hpos : admitsPositiveRicci (I := 𝓡 3) (M := M)) :
    (∃ p : SphereThree → M, IsCoveringMap p ∧ Function.Surjective p ∧
      IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p) ∧
      ∀ x : M, Finite (FundamentalGroup M x) := by
  exact exists_spherical_cover_of_admits_constant_positive_sectional_curvature hM
    (DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamilton_positive_ricci
      (I := 𝓡 3) (M := M) hM hpos).1

end DifferentialGeometry.Geometry

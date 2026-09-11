import DifferentialGeometry.Topology.Homology.BoundaryEulerIndex
import DifferentialGeometry.Topology.Homology.BoundaryEulerIndexOne
import DifferentialGeometry.Topology.Homology.ManifoldBoundary
import DifferentialGeometry.Topology.Homology.Relative
import DifferentialGeometry.Topology.Homology.Manifold

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
namespace DifferentialGeometry.Homology

theorem eulerChar_intrinsicBoundary
    {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space M] [CompactSpace M]
    (K : Type) [Field K] :
    eulerChar K (TopCat.of ((𝓡∂ (n + 1)).boundary M)) =
      (1 - (-1 : ℤ) ^ (n + 1)) * eulerChar K (TopCat.of M) := by
  cases n with
  | zero => exact eulerChar_intrinsicBoundary_eq_of_dimension_one K
  | succ d => exact eulerChar_intrinsicBoundary_eq_of_dimension_ge_two K

theorem relativeEulerChar_intrinsicBoundary
    {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space M] [CompactSpace M]
    (K : Type) [Field K] :
    relativeEulerChar (TopCat.of M) ((𝓡∂ (n + 1)).boundary M) K =
      (-1 : ℤ) ^ (n + 1) * eulerChar K (TopCat.of M) := by
  rw [relativeEulerChar_eq_sub _ _ K
    (finiteHomologyType_intrinsicBoundary (𝓡∂ (n + 1)) K)
    (finiteHomologyType_of_compact_manifold_withBoundary (n := n + 1) K),
    eulerChar_intrinsicBoundary K]
  ring

end DifferentialGeometry.Homology

import DifferentialGeometry.Topology.Homology.ManifoldBoundary
import DifferentialGeometry.Topology.Homology.Manifold
import DifferentialGeometry.Topology.Homology.Relative
import DifferentialGeometry.Geometry.Boundary.Model.EuclideanHalfSpace

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
namespace DifferentialGeometry.Homology
variable {n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]
  [T2Space M] [CompactSpace M]
  (B : Set M) (hB : B ⊆ (𝓡∂ n).boundary M)
  (hclopen : IsClopen (((↑) : BoundaryManifold (𝓡∂ n) M → M) ⁻¹' B))

include hB hclopen

theorem finiteHomologyType_relative_boundary_subset (K : Type) [Field K] :
    DifferentialGeometry.HomologicalComplex.finiteHomologyType
      (relativeChainComplex (TopCat.of M) B (ModuleCat.of K K)) :=
  finiteHomologyType_relativeChainComplex (TopCat.of M) B K
    (finiteHomologyType_of_isClopen_boundary_subset (𝓡∂ n) K B hB hclopen)
    (finiteHomologyType_of_compact_manifold_withBoundary (n := n) K)

theorem relativeEulerChar_boundary_subset_eq_sub (K : Type) [Field K] :
    relativeEulerChar (TopCat.of M) B K =
      eulerChar K (TopCat.of M) - eulerChar K (TopCat.of B) :=
  relativeEulerChar_eq_sub (TopCat.of M) B K
    (finiteHomologyType_of_isClopen_boundary_subset (𝓡∂ n) K B hB hclopen)
    (finiteHomologyType_of_compact_manifold_withBoundary (n := n) K)

theorem relativeEulerChar_boundary_subset_eq (K L : Type) [Field K] [Field L] :
    relativeEulerChar (TopCat.of M) B K = relativeEulerChar (TopCat.of M) B L := by
  rw [relativeEulerChar_boundary_subset_eq_sub B hB hclopen K,
    relativeEulerChar_boundary_subset_eq_sub B hB hclopen L,
    eulerChar_eq_of_compact_manifold_withBoundary (n := n) K L,
    eulerChar_eq_of_isClopen_boundary_subset (𝓡∂ n) K L B hB hclopen]

end DifferentialGeometry.Homology

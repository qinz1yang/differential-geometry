import DifferentialGeometry.Topology.Homology.ClosedManifold
import DifferentialGeometry.Geometry.Boundary.Manifold.Basic

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
namespace DifferentialGeometry.Homology
variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]

theorem finiteHomologyType_intrinsicBoundary (K : Type) [Field K] :
    finiteHomologyType K (TopCat.of (I.boundary M)) := by
  let _ : CompactSpace (BoundaryManifold I M) :=
    isCompact_iff_compactSpace.mp
      (show IsCompact (I.boundary M) from (I.isClosed_boundary (n := ∞) (by simp)).isCompact)
  exact finiteHomologyType_of_compact_boundaryless_manifold hI.boundaryI K
    (M := BoundaryManifold I M)

theorem finiteHomologyType_of_isClopen_boundary (K : Type) [Field K]
    (B : Set (BoundaryManifold I M)) (hB : IsClopen B) :
    finiteHomologyType K (TopCat.of B) := by
  let _ : CompactSpace (BoundaryManifold I M) :=
    isCompact_iff_compactSpace.mp
      (show IsCompact (I.boundary M) from (I.isClosed_boundary (n := ∞) (by simp)).isCompact)
  let U : TopologicalSpace.Opens (BoundaryManifold I M) := ⟨B,hB.isOpen⟩
  let _ : CompactSpace U := isCompact_iff_compactSpace.mp hB.isClosed.isCompact
  exact finiteHomologyType_of_compact_boundaryless_manifold hI.boundaryI K (M := U)

theorem finiteHomologyType_of_isClopen_boundary_subset (K : Type) [Field K]
    (B : Set M) (hB : B ⊆ I.boundary M)
    (hclopen : IsClopen (((↑) : BoundaryManifold I M → M) ⁻¹' B)) :
    finiteHomologyType K (TopCat.of B) := by
  have hrange : B ⊆ range ((↑) : BoundaryManifold I M → M) :=
    (BoundaryManifold.range_coe_eq_boundary (I := I) (M := M)).symm ▸ hB
  let e := (show Topology.IsEmbedding ((↑) : BoundaryManifold I M → M) from
    Topology.IsEmbedding.subtypeVal).homeomorphOfSubsetRange hrange
  exact (finiteHomologyType_iff_of_homeomorph K e).mp
    (finiteHomologyType_of_isClopen_boundary I K _ hclopen)

theorem eulerChar_eq_of_isClopen_boundary_subset (K L : Type) [Field K] [Field L]
    (B : Set M) (hB : B ⊆ I.boundary M)
    (hclopen : IsClopen (((↑) : BoundaryManifold I M → M) ⁻¹' B)) :
    eulerChar K (TopCat.of B) = eulerChar L (TopCat.of B) := by
  let _ : CompactSpace (BoundaryManifold I M) :=
    isCompact_iff_compactSpace.mp
      (show IsCompact (I.boundary M) from (I.isClosed_boundary (n := ∞) (by simp)).isCompact)
  let U : TopologicalSpace.Opens (BoundaryManifold I M) := ⟨_,hclopen.isOpen⟩
  have hclosed : IsClosed (U : Set (BoundaryManifold I M)) := hclopen.isClosed
  let _ : CompactSpace U := isCompact_iff_compactSpace.mp hclosed.isCompact
  have hrange : B ⊆ range ((↑) : BoundaryManifold I M → M) :=
    (BoundaryManifold.range_coe_eq_boundary (I := I) (M := M)).symm ▸ hB
  let e := (show Topology.IsEmbedding ((↑) : BoundaryManifold I M → M) from
    Topology.IsEmbedding.subtypeVal).homeomorphOfSubsetRange hrange
  exact (eulerChar_eq_of_homeomorph K e).symm.trans
    ((eulerChar_eq_of_compact_boundaryless_manifold hI.boundaryI K L (M := U)).trans
      (eulerChar_eq_of_homeomorph L e))

end DifferentialGeometry.Homology

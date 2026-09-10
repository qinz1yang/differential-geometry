import DifferentialGeometry.Topology.Homology.ManifoldBoundary
import DifferentialGeometry.Topology.Homology.ManifoldEulerParity
import DifferentialGeometry.Topology.Homology.OpenCover
import DifferentialGeometry.Geometry.Boundary.Model.EuclideanHalfSpace

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
namespace Poincare.Homology
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space M] [CompactSpace M]

theorem eulerChar_boundary_partition (K : Type) [Field K]
    (A : Set (BoundaryManifold (𝓡∂ (n + 1)) M)) (hA : IsClopen A) :
    eulerChar K (TopCat.of ((𝓡∂ (n + 1)).boundary M)) =
      eulerChar K (TopCat.of A) + eulerChar K (TopCat.of (Aᶜ : Set _)) := by
  have hi : IsEmpty (A ∩ Aᶜ : Set (BoundaryManifold (𝓡∂ (n + 1)) M)) := by
    rw [inter_compl_self]
    infer_instance
  have h := eulerChar_openCover (TopCat.of (BoundaryManifold (𝓡∂ (n + 1)) M)) A Aᶜ K
    hA.isOpen hA.isClosed.isOpen_compl (union_compl_self A)
    (finiteHomologyType_of_isClopen_boundary (𝓡∂ (n + 1)) K A hA)
    (finiteHomologyType_of_isClopen_boundary (𝓡∂ (n + 1)) K Aᶜ hA.compl)
    (finiteHomologyType_of_finite_totallyDisconnected K)
  simpa only [eulerChar_of_isEmpty, sub_zero] using! h

theorem eulerChar_boundary_component_parity (K : Type) [Field K]
    (A : Set (BoundaryManifold (𝓡∂ (n + 1)) M)) (hA : IsClopen A) :
    eulerChar K (TopCat.of A) = (-1 : ℤ) ^ n * eulerChar K (TopCat.of A) := by
  let I := 𝓡∂ (n + 1)
  let B := BoundaryManifold I M
  let J := HasSmoothBoundary.boundaryModel I
  let _ : CompactSpace B := isCompact_iff_compactSpace.mp
    (show IsCompact (I.boundary M) from (I.isClosed_boundary (n := ∞) (by simp)).isCompact)
  let U : TopologicalSpace.Opens B := ⟨A, hA.isOpen⟩
  let _ : CompactSpace U := isCompact_iff_compactSpace.mp hA.isClosed.isCompact
  have hdim : Module.finrank ℝ (HasSmoothBoundary.boundaryE I) = n := by
    have h := (inferInstance : HasSmoothBoundary (EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanHalfSpace (n + 1)) I).finrank_boundaryE_succ
    simp only [finrank_euclideanSpace, Fintype.card_fin] at h
    omega
  have h := eulerChar_eq_neg_one_pow_mul_of_compact_boundaryless_manifold J K (M := U)
  rw [hdim] at h
  exact h

end Poincare.Homology

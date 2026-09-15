import DifferentialGeometry.Topology.PiecewiseLinear.FrontierBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryExtension
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBoundaryImage

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphOn.image_stdSimplexBoundary {n : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {f : (Fin (n + 2) → ℝ) → EuclideanSpace ℝ (Fin (n + 1))}
    (hf : IsPLHomeomorphOn f (stdSimplex ℝ (Fin (n + 2))) P) :
    f '' stdSimplexBoundary (n + 1) = frontier P := by
  classical
  have hP : IsPLBall (n + 1) P := ⟨f, hf⟩
  obtain ⟨K, hKfin, hKP⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hfK : IsPLHomeomorphOn f (stdSimplex ℝ (Fin (n + 2))) K.space := hKP.symm ▸ hf
  have hK : IsPLBall (n + 1) K.space := ⟨f, hfK⟩
  rw [← hKP, frontier_space_eq_boundaryComplex_space (n := n) hK.isCombinatorialManifoldWithBoundary]
  have hboundary := boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex K hfK
  rw [simplexBoundary_stdVertices_space] at hboundary
  convert hboundary.symm using 1
  congr 2
  exact Subsingleton.elim _ _

theorem IsPLBall.isPLSphere_frontier {n : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hP : IsPLBall (n + 1) P) :
    IsPLSphere n (frontier P) := by
  classical
  let _ : DecidableEq (EuclideanSpace ℝ (Fin (n + 1))) := Classical.decEq _
  obtain ⟨K, hfin, rfl⟩ := hP.isPolyhedron.exists_simplicialComplex
  have := hfin.to_subtype
  rw [frontier_space_eq_boundaryComplex_space (n := n) (K := K)
    (IsPLBall.isCombinatorialManifoldWithBoundary (n := n) (K := K) hP)]
  exact isPLSphere_boundaryComplex_space_of_isPLBall (n := n) K hP

theorem IsPLBall.interior_nonempty {n : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hP : IsPLBall (n + 1) P) :
    (interior P).Nonempty := by
  obtain ⟨f, hf⟩ := hP
  exact ⟨f (stdCenter n),
    mem_interior_image_of_isPLHomeomorphOn_stdSimplex hf (stdCenter_mem_openSimplex n)⟩

theorem IsPLBall.closure_interior {n : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hP : IsPLBall (n + 1) P) :
    closure (interior P) = P := by
  apply Subset.antisymm (closure_minimal interior_subset hP.isPolyhedron.isCompact.isClosed)
  obtain ⟨f, hf⟩ := hP
  have hmap : MapsTo f (openSimplex (stdVertices n)) (interior P) :=
    fun _ hx => mem_interior_image_of_isPLHomeomorphOn_stdSimplex hf hx
  have hclsub : closure (openSimplex (stdVertices n)) ⊆ stdSimplex ℝ (Fin (n + 2)) :=
    closure_minimal openSimplex_stdVertices_subset_stdSimplex (isClosed_stdSimplex ℝ _)
  have hclmap := hmap.closure_of_continuousOn (hf.isPiecewiseAffineOn.continuousOn.mono hclsub)
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hf.bijOn.surjOn hy
  apply hclmap
  apply convexHull_subset_closure_openSimplex
    (Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) (two_le_card_stdVertices n)))
  rwa [convexHull_stdVertices]

theorem exists_isPLHomeomorphOn_of_frontier {n : ℕ}
    {P Q : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hP : IsPLBall (n + 1) P) (hQ : IsPLBall (n + 1) Q)
    {g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hg : IsPLHomeomorphOn g (frontier P) (frontier Q)) :
    ∃ G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)),
      IsPLHomeomorphOn G P Q ∧ EqOn G g (frontier P) := by
  classical
  let _ : DecidableEq (EuclideanSpace ℝ (Fin (n + 1))) := Classical.decEq _
  obtain ⟨K, hfinK, rfl⟩ := hP.isPolyhedron.exists_simplicialComplex
  obtain ⟨L, hfinL, rfl⟩ := hQ.isPolyhedron.exists_simplicialComplex
  have := hfinK.to_subtype
  have := hfinL.to_subtype
  rw [frontier_space_eq_boundaryComplex_space (n := n) (K := K)
    (IsPLBall.isCombinatorialManifoldWithBoundary (n := n) (K := K) hP),
    frontier_space_eq_boundaryComplex_space (n := n) (K := L)
      (IsPLBall.isCombinatorialManifoldWithBoundary (n := n) (K := L) hQ)] at hg
  rw [frontier_space_eq_boundaryComplex_space (n := n) (K := K)
    (IsPLBall.isCombinatorialManifoldWithBoundary (n := n) (K := K) hP)]
  exact exists_isPLHomeomorphOn_of_boundaryComplex (n := n) K L hP hQ hg

end DifferentialGeometry.Topology.PiecewiseLinear

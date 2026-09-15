import DifferentialGeometry.Topology.PiecewiseLinear.FrontierBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryExtension

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

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

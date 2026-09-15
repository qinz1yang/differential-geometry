import DifferentialGeometry.Topology.PiecewiseLinear.ChartComplexPiece
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralBallTopology

open Set
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) X] [HasGroupoid X (plGroupoid (n + 1))]

theorem frontier_chart_symm_image_of_isPLBall
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin (n + 1))))
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin (n + 1))) X)
    {C : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hC : IsPLBall (n + 1) C) (hCe : C ⊆ e.target) :
    frontier (e.symm '' C) = e.symm '' frontier C := by
  classical
  let _ : DecidableEq (EuclideanSpace ℝ (Fin (n + 1))) := Classical.decEq _
  obtain ⟨K, hfin, hKspace⟩ := hC.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hfin.to_subtype
  have hK : IsPLBall (n + 1) K.space := hKspace.symm ▸ hC
  let T := chartPieceOfComplex e he K (hKspace.symm ▸ hCe)
  have h := T.frontier_eq_image_boundaryComplex hK.isCombinatorialManifoldWithBoundary
  change frontier (e.symm '' K.space) = e.symm '' (boundaryComplex (n + 1) K).space at h
  rw [← frontier_space_eq_boundaryComplex_space hK.isCombinatorialManifoldWithBoundary, hKspace] at h
  exact h

end DifferentialGeometry.Topology.PiecewiseLinear

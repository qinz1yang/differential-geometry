import DifferentialGeometry.Topology.PiecewiseLinear.PlanarFreeFace
import DifferentialGeometry.Topology.PiecewiseLinear.FaceStarBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_isPLHomeomorphOn_eraseTriangleComplex_faceStarComplex
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) [Finite K.faces]
    (hK : IsPLBall 2 K.space) {t s : Finset (EuclideanSpace ℝ (Fin 2))}
    (ht : t ∈ K.faces) (htcard : t.card = 3) (hs : s ∈ K.faces)
    (hst : s ⊆ t) (hscard : s.card = 1 ∨ s.card = 2)
    (htrace : frontier K.space ∩ convexHull ℝ (t : Set _) =
      ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset _) : Set _))
    {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U)
    (htU : convexHull ℝ (t : Set _) ⊆ U) :
    ∃ g : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2),
      IsPLHomeomorphOn g univ univ ∧ EqOn g id Uᶜ ∧
      EqOn g id (frontier (faceStarComplex K s).space \ convexHull ℝ (t : Set _)) ∧
      g '' (faceStarComplex K s).space =
        (eraseTriangleComplex (faceStarComplex K s) t).space ∧
      IsPLBall 2 (eraseTriangleComplex (faceStarComplex K s) t).space := by
  let P := faceStarComplex K s
  let _ : Finite P.faces := (faceStarComplex_faces_finite K s).to_subtype
  have hP : IsPLBall 2 P.space :=
    hK.isCombinatorialManifoldWithBoundary.isPLBall_faceStarComplex K hs
  have htP : t ∈ P.faces := mem_faceStarComplex_faces_of_subset K ht hst
  have hPtrace : frontier P.space ∩ convexHull ℝ (t : Set _) =
      ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset _) : Set _) :=
    by
      change frontier (faceStarComplex K s).space ∩ convexHull ℝ (t : Set _) = _
      simpa only [Finset.coe_erase] using
        (frontier_faceStarComplex_inter_convexHull K ht hst
          (by simpa only [Finset.coe_erase] using htrace))
  have hne : P.space ≠ convexHull ℝ (t : Set _) := by
    intro heq
    let x := s.centroid ℝ id
    have hx : x ∈ openSimplex s := centroid_mem_openSimplex (K.nonempty_of_mem_faces hs)
    have hxint := openSimplex_subset_interior_of_frontier_inter_eq P htP hst
      (by simpa only [Finset.coe_erase] using hPtrace) hx
    have hxfront : x ∈ frontier (convexHull ℝ (t : Set _)) := by
      rw [frontier_convexHull_eq_simplexBoundary (K.indep ht) (by simpa using htcard)]
      apply (simplexBoundary t (K.indep ht)).convexHull_subset_space
        ⟨hst, K.nonempty_of_mem_faces hs, ?_⟩ (openSimplex_subset_convexHull s hx)
      intro hst'
      have hcard := congrArg Finset.card hst'
      rcases hscard with hscard | hscard <;> omega
    exact hxfront.2 (heq ▸ hxint)
  simpa only [P] using exists_isPLHomeomorphOn_eraseTriangleComplex_of_frontier_inter
    P hP htP htcard hst hscard hPtrace hne hU htU

end DifferentialGeometry.Topology.PiecewiseLinear

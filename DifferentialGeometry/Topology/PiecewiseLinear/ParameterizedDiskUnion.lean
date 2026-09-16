import DifferentialGeometry.Topology.PiecewiseLinear.CoveredHeightSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryInvariance

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_triangulation_parameterized_disk_union
    [dE : DecidableEq E] {P D J : Set E} {u v : (Fin 3 → ℝ) → E}
    (hu : IsPLHomeomorphOn u (stdSimplex ℝ (Fin 3)) P)
    (hv : IsPLHomeomorphOn v (stdSimplex ℝ (Fin 3)) D)
    (huJ : u '' stdSimplexBoundary 2 = J) (hvJ : v '' stdSimplexBoundary 2 = J)
    (a : E →ᵃ[ℝ] ℝ) (r : ℝ) :
    ∃ R : Geometry.SimplicialComplex ℝ E, R.faces.Finite ∧ R.space = P ∪ D ∧
      (restrict R P).space = P ∧ (restrict R D).space = D ∧
      IsPLBall 2 (restrict R P).space ∧ IsPLBall 2 (restrict R D).space ∧
      (boundaryComplex 2 (restrict R P)).space = J ∧
      (boundaryComplex 2 (restrict R D)).space = J ∧
      (∀ s ∈ R.faces, s ∈ (restrict R P).faces ∨ s ∈ (restrict R D).faces) ∧
      ∀ s ∈ R.faces, convexHull ℝ (s : Set E) ⊆ {x | a x ≤ r} ∨
        convexHull ℝ (s : Set E) ⊆ {x | r ≤ a x} := by
  classical
  cases Subsingleton.elim dE (Classical.decEq E)
  have hP : IsPLBall 2 P := ⟨u, hu⟩
  have hD : IsPLBall 2 D := ⟨v, hv⟩
  obtain ⟨K, hKfin, hKspace⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  obtain ⟨R, hRfin, hRspace, hsub, hRD, hcover, hside⟩ :=
    exists_triangulation_union_with_face_cover_and_halfSpace_faces
      K hD.isPolyhedron a r
  let _ : Finite R.faces := hRfin.to_subtype
  let _ : Finite (restrict R P).faces := (restrict_faces_finite R P).to_subtype
  let _ : Finite (restrict R D).faces := (restrict_faces_finite R D).to_subtype
  have hRP : (restrict R P).space = P := by
    simpa only [hKspace] using hsub.space_eq
  have huR : IsPLHomeomorphOn u (stdSimplex ℝ (Fin 3)) (restrict R P).space := by
    rwa [hRP]
  have hvR : IsPLHomeomorphOn v (stdSimplex ℝ (Fin 3)) (restrict R D).space := by
    rwa [hRD]
  have hboundaryP := boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex
    (restrict R P) huR
  have hboundaryD := boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex
    (restrict R D) hvR
  rw [simplexBoundary_stdVertices_space, huJ] at hboundaryP
  rw [simplexBoundary_stdVertices_space, hvJ] at hboundaryD
  refine ⟨R, hRfin, ?_, hRP, hRD, hRP.symm ▸ hP, hRD.symm ▸ hD,
    hboundaryP, hboundaryD, ?_, hside⟩
  · rwa [hKspace] at hRspace
  · intro s hs
    simpa only [hKspace] using hcover s hs

end DifferentialGeometry.Topology.PiecewiseLinear

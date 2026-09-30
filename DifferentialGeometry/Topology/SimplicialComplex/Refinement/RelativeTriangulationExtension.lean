import DifferentialGeometry.Topology.SimplicialComplex.Refinement.RelativeTriangulation
import DifferentialGeometry.Topology.SimplicialComplex.Refinement.RelativeTriangulationInduction

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry

noncomputable section

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem boundary_simplex_filling : boundarySimplexFilling (E := E) := by
  intro B V hB hVne hV hparents hBs
  exact exists_cone_triangulation_of_boundary B hB V hVne hV hparents hBs

omit [FiniteDimensional ℝ E] in
omit [DecidableEq E] in
theorem exists_relative_triangulation
    (K D J : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hDK : D.faces ⊆ K.faces) (hJ : J.faces.Finite)
    (hJD : simplicialRefines J D) (hJs : J.space = D.space)
    {d : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) :
    ∃ T : SimplicialComplex ℝ E, T.faces.Finite ∧ T.space = K.space ∧
      simplicialRefines T K ∧ J.faces ⊆ T.faces ∧
      ∀ s ∈ T.faces, s.card ≤ d + 1 := by
  classical
  exact exists_relative_refinement_of_boundary_filling boundary_simplex_filling
    K D J hK hDK hJ hJD hJs hd

omit [FiniteDimensional ℝ E] in
omit [DecidableEq E] in
theorem complexRestriction_eq_of_prescribed_refinement
    (T D J : SimplicialComplex ℝ E) (hJT : J.faces ⊆ T.faces)
    (hJD : simplicialRefines J D) (hJs : J.space = D.space) :
    complexRestriction T D = J := by
  classical
  apply SimplicialComplex.ext
  ext s
  constructor
  · intro hs
    obtain ⟨t, ht, hst⟩ := hs.2
    have hc : s.centroid ℝ id ∈ J.space := by
      rw [hJs]
      exact D.convexHull_subset_space ht
        ((convexHull_min hst (convex_convexHull ℝ _))
          (s.centroid_mem_convexHull (T.nonempty_of_mem_faces hs.1)))
    obtain ⟨u, hu, hcu⟩ := SimplicialComplex.mem_space_iff.mp hc
    exact J.down_closed hu (face_subset_of_centroid_mem T hs.1 (hJT hu) hcu)
      (T.nonempty_of_mem_faces hs.1)
  · intro hs
    obtain ⟨t, ht, hst⟩ := hJD s hs
    exact ⟨hJT hs, t, ht, fun x hx => hst (subset_convexHull ℝ _ hx)⟩

end

end DifferentialGeometry.Topology.Engulfing

import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalSchoenflies

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem convexHull_subset_closure_connectedComponentIn_sdiff
    (K L : Geometry.SimplicialComplex ℝ E) (hLK : L.faces ⊆ K.faces)
    {s : Finset E} (hs : s ∈ K.faces) {p x : E}
    (hxs : x ∈ openSimplex s) (hx : x ∈ connectedComponentIn (K.space \ L.space) p) :
    convexHull ℝ (s : Set E) ⊆ closure (connectedComponentIn (K.space \ L.space) p) := by
  have hsL : s ∉ L.faces := fun h =>
    (connectedComponentIn_subset (K.space \ L.space) p hx).2
      (L.convexHull_subset_space h (openSimplex_subset_convexHull s hxs))
  have hopen : openSimplex s ⊆ K.space \ L.space := fun y hy =>
    ⟨K.convexHull_subset_space hs (openSimplex_subset_convexHull s hy),
      notMem_space_of_notMem_faces hLK hs hsL hy⟩
  have hsub := (convex_openSimplex s).isPreconnected.subset_connectedComponentIn hxs hopen
  rw [← connectedComponentIn_eq hx] at hsub
  exact (convexHull_subset_closure_openSimplex (K.nonempty_of_mem_faces hs)).trans
    (closure_mono hsub)

theorem restrict_closure_connectedComponentIn_sdiff_space [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hLK : L.faces ⊆ K.faces)
    (p : E) :
    (restrict K (closure (connectedComponentIn (K.space \ L.space) p))).space =
      closure (connectedComponentIn (K.space \ L.space) p) := by
  let _ : Finite (restrict K (closure (connectedComponentIn (K.space \ L.space) p))).faces :=
    (restrict_faces_finite K _).to_subtype
  apply Subset.antisymm (restrict_space_subset K _)
  refine closure_minimal ?_ (isPolyhedron_space (restrict K _)).isClosed
  intro x hx
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex K
    (connectedComponentIn_subset (K.space \ L.space) p hx).1
  exact (restrict K _).convexHull_subset_space
    ⟨hs, convexHull_subset_closure_connectedComponentIn_sdiff K L hLK hs hxs hx⟩
    (openSimplex_subset_convexHull s hxs)

theorem isPolyhedron_closure_connectedComponentIn_sdiff_of_subset [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hLK : L.space ⊆ K.space) (p : E) :
    IsPolyhedron (closure (connectedComponentIn (K.space \ L.space) p)) := by
  obtain ⟨R, hR, hRfin, hRL⟩ := exists_isSubdivision_restrict_isSubdivision K L hLK
  let _ : Finite R.faces := hRfin.to_subtype
  let A := restrict R L.space
  let B := restrict R (closure (connectedComponentIn (R.space \ A.space) p))
  let _ : Finite B.faces := (restrict_faces_finite R _).to_subtype
  have hB : B.space = closure (connectedComponentIn (K.space \ L.space) p) := by
    rw [restrict_closure_connectedComponentIn_sdiff_space R A
      (restrict_faces_subset R L.space), hR.space_eq, hRL.space_eq]
  exact hB ▸ isPolyhedron_space B

end DifferentialGeometry.Topology.PiecewiseLinear

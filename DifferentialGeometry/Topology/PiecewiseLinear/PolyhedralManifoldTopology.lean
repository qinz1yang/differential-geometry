/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Connected.FiniteCover
import DifferentialGeometry.Topology.Connected.TwoSided
import DifferentialGeometry.Topology.PiecewiseLinear.PieceInclusion
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralBallTopology

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) X]

open Classical in
theorem IsPolyhedralBall.closure_interior {P : Set X}
    (hP : IsPolyhedralBall (n := n + 1) (n + 1) P) : closure (interior P) = P := by
  have hclosed := hP.isPolyhedralManifoldWithBoundary.isCompact.isClosed
  obtain ⟨T, hT⟩ := hP
  let _ : DecidableEq (EuclideanSpace ℝ (Fin T.ambientDim)) := Classical.decEq _
  obtain ⟨f, hf⟩ := hT
  have hint := T.piece.interior_eq_image_openSimplex
    (⟨f, hf⟩ : IsPLBall (n + 1) T.piece.complex.space) hf
  have hstdclosed : IsClosed (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2))) :=
    (isHPolytope_stdSimplex (Fin (n + 2))).isPolyhedron.isClosed
  have hclsub : closure (openSimplex (stdVertices n)) ⊆ Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2)) :=
    closure_minimal (openSimplex_stdVertices_subset_stdSimplex (n := n)) hstdclosed
  have hsubcl : Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2)) ⊆ closure (openSimplex (stdVertices n)) := by
    rw [← convexHull_stdVertices]
    exact convexHull_subset_closure_openSimplex (by simp [stdVertices])
  have hcont : ContinuousOn (T.piece.map ∘ f) (closure (openSimplex (stdVertices n))) :=
    (T.piece.continuousOn.comp hf.isPiecewiseAffineOn.continuousOn hf.bijOn.mapsTo).mono hclsub
  apply Subset.antisymm (closure_minimal interior_subset hclosed)
  intro y hy
  obtain ⟨x, hx, rfl⟩ := T.piece.bijOn.surjOn hy
  obtain ⟨z, hz, rfl⟩ := hf.bijOn.surjOn hx
  rw [hint]
  exact hcont.image_closure ⟨z, hsubcl hz, rfl⟩

open Classical in
theorem IsPolyhedralManifoldWithBoundary.closure_interior {P : Set X}
    (hP : IsPolyhedralManifoldWithBoundary (n := n + 1) (n + 1) P) :
    closure (interior P) = P := by
  have hclosed := hP.isCompact.isClosed
  obtain ⟨T, hT⟩ := hP
  let _ : DecidableEq (EuclideanSpace ℝ (Fin T.ambientDim)) := Classical.decEq _
  let _ : Finite T.piece.complex.faces := T.piece.finite_faces.to_subtype
  apply Subset.antisymm (closure_minimal interior_subset hclosed)
  intro y hy
  by_cases hyint : y ∈ interior P
  · exact subset_closure hyint
  obtain ⟨x, hx, rfl⟩ := T.piece.bijOn.surjOn hy
  have hxB : x ∈ (boundaryComplex (n + 1) T.piece.complex).space := by
    by_contra hxnot
    exact hyint ((T.piece.mem_interior_iff_not_mem_boundaryComplex_space hT hx).mpr hxnot)
  obtain ⟨C, hC, hCK, hCn, _⟩ := exists_isPLBall_subset_inter_boundary T.piece.complex hT x hxB
  have hQ := T.piece.isPolyhedralBall_image hC hCK
  have hQP : T.piece.map '' C ⊆ P := (image_mono hCK).trans T.piece.bijOn.image_eq.le
  have hxQ : T.piece.map x ∈ T.piece.map '' C := ⟨x, mem_of_mem_nhdsWithin hx hCn, rfl⟩
  exact closure_mono (interior_mono hQP) (hQ.closure_interior.symm ▸ hxQ)

open Classical in
theorem PLPieceIn.isClosed_image_sdiff_connectedComponentIn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Set X} (T : PLPieceIn E (n + 1) X P)
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hLK : L.faces ⊆ T.complex.faces) (x : X) :
    IsClosed (T.map '' L.space \ connectedComponentIn (T.map '' L.space) x) := by
  let C := fun s : Finset E => T.map '' convexHull ℝ (s : Set E)
  have hsub (s : Finset E) (hs : s ∈ L.faces) : convexHull ℝ (s : Set E) ⊆ T.complex.space :=
    T.complex.convexHull_subset_space (hLK hs)
  apply DifferentialGeometry.Topology.isClosed_sdiff_connectedComponentIn_of_finite_closed_cover
    (Set.toFinite L.faces) C
  · intro s hs
    exact ((s.finite_toSet.isCompact_convexHull ℝ).image_of_continuousOn
      (T.continuousOn.mono (hsub s hs))).isClosed
  · intro s hs
    exact (convex_convexHull ℝ (s : Set E)).isPreconnected.image T.map
      (T.continuousOn.mono (hsub s hs))
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨s, hs, hzs⟩ := L.mem_space_iff.mp hz
      exact mem_iUnion₂.mpr ⟨s, hs, z, hzs, rfl⟩
    · intro hy
      obtain ⟨s, hs, z, hzs, rfl⟩ := mem_iUnion₂.mp hy
      exact ⟨z, L.convexHull_subset_space hs hzs, rfl⟩

open Classical in
theorem IsPolyhedralManifoldWithBoundary.isTwoSided_frontier {P : Set X}
    (hP : IsPolyhedralManifoldWithBoundary (n := n + 1) (n + 1) P) :
    DifferentialGeometry.Topology.IsTwoSided (frontier P) := by
  apply DifferentialGeometry.Topology.isTwoSided_frontier_of_isClosed_sdiff_connectedComponentIn
    hP.closure_interior
  obtain ⟨T, hT⟩ := hP
  let _ : DecidableEq (EuclideanSpace ℝ (Fin T.ambientDim)) := Classical.decEq _
  let _ : Finite T.piece.complex.faces := T.piece.finite_faces.to_subtype
  let _ : Finite (boundaryComplex (n + 1) T.piece.complex).faces :=
    (boundaryComplex_faces_finite (n + 1) T.piece.complex).to_subtype
  intro x _
  rw [T.piece.frontier_eq_image_boundaryComplex hT]
  exact T.piece.isClosed_image_sdiff_connectedComponentIn _
    (boundaryComplex_faces_subset (n + 1) T.piece.complex) x

open Classical in
theorem IsPolyhedralManifoldWithBoundary.isTwoSided_of_union_boundary_components {P S : Set X}
    (hP : IsPolyhedralManifoldWithBoundary (n := n + 1) (n + 1) P)
    (hSP : S ⊆ polyhedralBoundary (n + 1) P hP)
    (hcomponents : ∀ x ∈ S, connectedComponentIn (polyhedralBoundary (n + 1) P hP) x ⊆ S) :
    DifferentialGeometry.Topology.IsTwoSided S := by
  obtain ⟨T, hT⟩ := hP
  let _ : DecidableEq (EuclideanSpace ℝ (Fin T.ambientDim)) := Classical.decEq _
  have hP : IsPolyhedralManifoldWithBoundary (n := n + 1) (n + 1) P := ⟨T, hT⟩
  have hbd : polyhedralBoundary (n + 1) P hP = frontier P :=
    (polyhedralBoundary_eq_of_piece hP T).trans (T.piece.frontier_eq_image_boundaryComplex hT).symm
  rw [hbd] at hSP hcomponents
  exact hP.isTwoSided_frontier.of_union_components hSP hcomponents

end DifferentialGeometry.Topology.PiecewiseLinear

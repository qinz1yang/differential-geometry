/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ArcDerivedNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.ArcCellBoundaryExample
import DifferentialGeometry.Topology.PiecewiseLinear.ChartComplexPiece
import DifferentialGeometry.Topology.PiecewiseLinear.FrontierBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralGraph

open Set Filter

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem arcComplexIn_space_subset_interior_of_interior_faces [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hn : Module.finrank ℝ E = 3) (hK : IsCombinatorialManifoldWithBoundary 3 K)
    {n : ℕ} {v : ℕ → E}
    (hinterior : ∀ j ≤ 2 * n, arcChainFace v j ∉ (boundaryComplex 3 K).faces) :
    (arcComplexIn K v n).space ⊆ interior K.space := by
  intro x hx
  have hxK : x ∈ K.space :=
    space_mono_of_faces_subset (arcComplexIn_faces_subset K v n) hx
  apply (mem_interior_iff_notMem_frontier hxK).mpr
  rw [frontier_space_eq_boundaryComplex_space_of_finrank (n := 2) hn K hK]
  intro hxB
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex (arcComplexIn K v n) hx
  obtain ⟨hsK, j, hj, rfl⟩ := hs
  exact notMem_space_of_notMem_faces (boundaryComplex_faces_subset 3 K) hsK
    (hinterior j hj) hxs hxB

open Classical in
theorem arcComplexIn_space_subset_interior_derivedNeighborhood_of_interior_faces
    [FiniteDimensional ℝ E] {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hn : Module.finrank ℝ E = 3) (hK : IsCombinatorialManifoldWithBoundary 3 K)
    {n : ℕ} {v : ℕ → E}
    (hinterior : ∀ j ≤ 2 * n, arcChainFace v j ∉ (boundaryComplex 3 K).faces) :
    (arcComplexIn K v n).space ⊆
      interior (PiecewiseLinear.derivedNeighborhood K (arcComplexIn K v n)).space := by
  intro x hx
  have hxint := arcComplexIn_space_subset_interior_of_interior_faces hn hK hinterior hx
  have hKn : K.space ∈ nhds x := mem_interior_iff_mem_nhds.mp hxint
  obtain ⟨U, hU, hUsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp
    (derivedNeighborhood_mem_nhdsWithin (arcComplexIn_faces_subset K v n) hx)
  apply mem_interior_iff_mem_nhds.mpr
  exact mem_of_superset (inter_mem hU hKn) hUsub

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isPLBall_neighborhood_arcComplexIn
    [FiniteDimensional ℝ E] {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hn : Module.finrank ℝ E = 3)
    {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    (hinj : ∀ i ≤ n, ∀ j ≤ n, v i = v j → i = j)
    (hinterior : ∀ j ≤ 2 * n, arcChainFace v j ∉ (boundaryComplex 3 K).faces) :
    ∃ C : Set E, IsPLBall 3 C ∧ (arcComplexIn K v n).space ⊆ interior C ∧ C ⊆ K.space := by
  refine ⟨(PiecewiseLinear.derivedNeighborhood K (arcComplexIn K v n)).space,
    hK.isPLBall_derivedNeighborhood_arcComplexIn hvert hedge hinj, ?_,
    derivedNeighborhood_space_subset K (arcComplexIn K v n)⟩
  exact arcComplexIn_space_subset_interior_derivedNeighborhood_of_interior_faces
    hn hK hinterior

open Classical in
theorem exists_isLocallyFiniteRegularNeighborhoodOf_nonempty_arc :
    ∃ (N K U : Set (EuclideanSpace ℝ (Fin 3))),
      N.Nonempty ∧ K.Nonempty ∧ U.Nonempty ∧
        IsLocallyFiniteRegularNeighborhoodOf (n := 3) N K U := by
  let E := EuclideanSpace ℝ (Fin 3)
  obtain ⟨A, v, hAfin, hA, hvert, hedge, hinj, hinterior⟩ :=
    exists_simplicialArc_one_with_all_faces_interior (E := E)
      (by simp only [E, finrank_euclideanSpace, Fintype.card_fin])
  let _ : Finite A.faces := hAfin.to_subtype
  let e := chartAt E (0 : E)
  have he : e ∈ atlas E E := chart_mem_atlas _ _
  have hAe : A.space ⊆ e.target := by
    simp only [e, chartAt_self_eq, OpenPartialHomeomorph.refl_target, subset_univ]
  let Q := chartPieceOfComplex e he A hAe
  let P : PLPiece 3 E (e.symm '' A.space) := ⟨3, Q⟩
  let _ : Finite P.piece.complex.faces := P.piece.finite_faces.to_subtype
  have hcomplex : P.piece.complex = A := rfl
  have hmap : P.piece.map = id := by
    simp only [P, Q, chartPieceOfComplex, e, chartAt_self_eq,
      OpenPartialHomeomorph.refl_symm]
    rfl
  let _ : DecidableEq E := Classical.decEq E
  let G := arcComplexIn A v 1
  have hGA : G.faces ⊆ A.faces := arcComplexIn_faces_subset A v 1
  have hGP : G.faces ⊆ P.piece.complex.faces := by
    simpa only [hcomplex] using hGA
  have hcard : ∀ s ∈ G.faces, s.card ≤ 2 := by
    rintro s ⟨-, j, -, rfl⟩
    exact arcChainFace_card_le_two v j
  have hP : IsCombinatorialManifoldWithBoundary 3 P.piece.complex := by
    simpa only [hcomplex] using hA
  have hD : IsCombinatorialManifoldWithBoundary 3
      (derivedNeighborhood P.piece.complex G) := by
    simpa only [Nat.reduceAdd] using hP.derivedNeighborhood G
  have hinner : G.space ⊆ interior (derivedNeighborhood P.piece.complex G).space := by
    simpa only [G, hcomplex] using
      (arcComplexIn_space_subset_interior_derivedNeighborhood_of_interior_faces
        (K := A) (n := 1) (v := v)
          (by simp only [E, finrank_euclideanSpace, Fintype.card_fin]) hA hinterior)
  have hnhds : P.piece.map '' (derivedNeighborhood P.piece.complex G).space ∈
      nhdsSet (P.piece.map '' G.space) := by
    rw [hmap, image_id, image_id]
    exact subset_interior_iff_mem_nhdsSet.mp hinner
  have hvface : arcChainFace v 0 ∈ G.faces := by
    exact arcChainFace_mem_arcComplexIn_faces hvert hedge (by omega)
  have hvG : v 0 ∈ G.space := by
    apply G.subset_space hvface
    simp [arcChainFace]
  have hvD : v 0 ∈ (derivedNeighborhood P.piece.complex G).space :=
    interior_subset (hinner hvG)
  have hvA : v 0 ∈ A.space := space_mono_of_faces_subset hGA hvG
  have hregular := PLPiece.isLocallyFiniteRegularNeighborhoodOf_derivedNeighborhood
    (n := 3) (X := E) (U := e.symm '' A.space) (P := P) (G := G)
      hGP hcard hP hD hnhds
  refine ⟨P.piece.map '' (derivedNeighborhood P.piece.complex G).space,
    P.piece.map '' G.space, e.symm '' A.space,
    ⟨P.piece.map (v 0), ⟨v 0, hvD, rfl⟩⟩,
    ⟨P.piece.map (v 0), ⟨v 0, hvG, rfl⟩⟩, ?_, hregular⟩
  · exact ⟨P.piece.map (v 0), P.piece.bijOn.mapsTo hvA⟩

end DifferentialGeometry.Topology.PiecewiseLinear

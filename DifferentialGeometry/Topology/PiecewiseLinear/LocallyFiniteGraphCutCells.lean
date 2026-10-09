/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteGraphDualCells
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePieceRestriction

open Set Function Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem splittingDisk_space_subset (K : Geometry.SimplicialComplex ℝ E)
    {e : Finset E} (he : e ∈ K.faces) : (splittingDisk K e he).space ⊆ K.space :=
  (space_mono_of_faces_subset (splittingDisk_faces_subset K he)).trans
    (secondDerived_isSubdivision K).space_eq.subset

open Classical in
theorem vertex_mem_of_graphDualCell_inter_splittingDisk_nonempty
    (K L : Geometry.SimplicialComplex ℝ E) (hL : L.faces ⊆ K.faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {v : E} (hv : {v} ∈ L.faces)
    {e : Finset E} (he : e ∈ K.faces) (hc : e.card = 2)
    (hne : ((graphDualCell K L v).space ∩ (splittingDisk K e he).space).Nonempty) :
    v ∈ e := by
  obtain ⟨x, hxC, hxD⟩ := hne
  obtain ⟨u, hu, hxu⟩ := exists_face_mem_openSimplex (splittingDisk K e he) hxD
  have huC := mem_faces_of_mem_openSimplex_of_mem_space
    ((graphDualCell_faces_subset K L v).trans (derivedNeighborhood_faces_subset K L))
    (splittingDisk_faces_subset K he hu) hxu hxC
  obtain ⟨D, hD, hDne, rfl⟩ := splittingDisk_faces_subset K he hu
  have hDe := ((mem_splittingDisk_faces_iff_of_flag he hD hDne).mp hu).1
  obtain ⟨hmeet, hDv⟩ := (mem_graphDualCell_faces_iff_of_flag L (hL hv) hD hDne).mp huC
  obtain ⟨s, hs⟩ := hDne
  obtain ⟨t, ht, hct⟩ := hmeet s hs
  have het := subset_of_mem_dualCell_of_mem_convexHull K he (hL ht)
    ((dualCell K e he).convexHull_subset_space (hDe s hs) (subset_convexHull ℝ _ hct))
    (t.centroid_mem_convexHull (L.nonempty_of_mem_faces ht))
  have hvt := subset_of_mem_dualCell_of_mem_convexHull K (hL hv) (hL ht)
    ((dualCell K {v} (hL hv)).convexHull_subset_space (hDv s hs)
      (subset_convexHull ℝ _ hct))
    (t.centroid_mem_convexHull (L.nonempty_of_mem_faces ht))
  have het' : e = t := Finset.eq_of_subset_of_card_le het (hc ▸ hcard t ht)
  rw [het']
  exact Finset.singleton_subset_iff.mp hvt

open Classical in
theorem LocallyFinitePLPieceIn.isPLCellOn_graphDualCell [FiniteDimensional ℝ E]
    {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    {Y : Set X} (T : LocallyFinitePLPieceIn E 3 X Y)
    (L : Geometry.SimplicialComplex ℝ E)
    (hK : IsCombinatorialManifoldWithBoundary 3 T.complex)
    (hL : L.faces ⊆ T.complex.faces) (hcard : ∀ s ∈ L.faces, s.card ≤ 2)
    {v : E} (hv : {v} ∈ L.faces) :
    IsPLCellOn 3 (T.map '' (graphDualCell T.complex L v).space)
      (T.map '' (boundaryComplex 3 (graphDualCell T.complex L v)).space) :=
  T.isPLCellOn_image_boundaryComplex _ (T.graphDualCell_faces_finite L (hL hv))
    ((graphDualCell_space_subset T.complex L v).trans
      (derivedNeighborhood_space_subset T.complex L)) (by omega)
    (T.isPLBall_graphDualCell L hK hL hcard hv)

open Classical in
theorem LocallyFinitePLPieceIn.isPLCellOn_splittingDisk [FiniteDimensional ℝ E]
    {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    {Y : Set X} (T : LocallyFinitePLPieceIn E 3 X Y)
    (hK : IsCombinatorialManifold 3 T.complex)
    (e : {s : Finset E // s ∈ T.complex.faces ∧ s.card = 2}) :
    IsPLCellOn 2 (T.map '' (splittingDisk T.complex e e.2.1).space)
      (T.map '' (boundaryComplex 2 (splittingDisk T.complex e e.2.1)).space) :=
  T.isPLCellOn_image_boundaryComplex _ (T.splittingDisk_faces_finite e)
    (splittingDisk_space_subset T.complex e.2.1) (by omega)
    (T.isPLBall_splittingDisk (n := 2) (k := 1) hK e.2.1 e.2.2 (by omega))

open Classical in
theorem LocallyFinitePLPieceIn.image_graphDualCell_inter
    {X : Type*} {n : ℕ} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] {Y : Set X}
    (T : LocallyFinitePLPieceIn E n X Y) (L : Geometry.SimplicialComplex ℝ E)
    (hL : L.faces ⊆ T.complex.faces) (hcard : ∀ s ∈ L.faces, s.card ≤ 2)
    {v w : E} (hvw : v ≠ w) (he : {v, w} ∈ L.faces) :
    (T.map '' (graphDualCell T.complex L v).space) ∩
      (T.map '' (graphDualCell T.complex L w).space) =
      T.map '' (splittingDisk T.complex {v, w} (hL he)).space := by
  rw [← T.bijOn.injOn.image_inter
    ((graphDualCell_space_subset T.complex L v).trans
      (derivedNeighborhood_space_subset T.complex L))
    ((graphDualCell_space_subset T.complex L w).trans
      (derivedNeighborhood_space_subset T.complex L)),
    graphDualCell_space_inter T.complex L hL hcard hvw he]

open Classical in
theorem LocallyFinitePLPieceIn.disjoint_image_graphDualCell
    {X : Type*} {n : ℕ} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] {Y : Set X}
    (T : LocallyFinitePLPieceIn E n X Y) (L : Geometry.SimplicialComplex ℝ E)
    (hL : L.faces ⊆ T.complex.faces) (hcard : ∀ s ∈ L.faces, s.card ≤ 2)
    {v w : E} (hv : {v} ∈ L.faces) (hw : {w} ∈ L.faces) (hvw : v ≠ w)
    (he : {v, w} ∉ L.faces) :
    Disjoint (T.map '' (graphDualCell T.complex L v).space)
      (T.map '' (graphDualCell T.complex L w).space) := by
  have hdis := disjoint_iff_inter_eq_empty.mpr
    (graphDualCell_space_inter_eq_empty T.complex L hL hcard hv hw hvw he)
  exact hdis.image T.bijOn.injOn
    ((graphDualCell_space_subset T.complex L v).trans
      (derivedNeighborhood_space_subset T.complex L))
    ((graphDualCell_space_subset T.complex L w).trans
      (derivedNeighborhood_space_subset T.complex L))

open Classical in
theorem LocallyFinitePLPieceIn.pairwise_disjoint_image_splittingDisk
    {X : Type*} {n : ℕ} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] {Y : Set X}
    (T : LocallyFinitePLPieceIn E n X Y) :
    Pairwise (Disjoint on fun e : {s : Finset E // s ∈ T.complex.faces ∧ s.card = 2} =>
      T.map '' (splittingDisk T.complex e e.2.1).space) := by
  intro e f hef
  exact (disjoint_splittingDisk_space T.complex e.2.1 f.2.1
    (fun h => hef (Subtype.ext h)) (e.2.2.trans f.2.2.symm)).image T.bijOn.injOn
    (splittingDisk_space_subset T.complex e.2.1)
    (splittingDisk_space_subset T.complex f.2.1)

open Classical in
theorem LocallyFinitePLPieceIn.locallyFinite_image_splittingDisk
    {X : Type*} {n : ℕ} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] {Y : Set X}
    (T : LocallyFinitePLPieceIn E n X Y) :
    ∀ x ∈ Y, ∃ V ∈ 𝓝 x,
      {e : {s : Finset E // s ∈ T.complex.faces ∧ s.card = 2} |
        (T.map '' (splittingDisk T.complex e e.2.1).space ∩ V).Nonempty}.Finite := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := T.bijOn.surjOn hx
  obtain ⟨W, hW, hfin⟩ := T.locallyFinite_splittingDisk ⟨p, hp⟩
  rw [T.isEmbedding.isInducing.nhds_eq_comap] at hW
  obtain ⟨V, hV, hVW⟩ := Filter.mem_comap.mp hW
  refine ⟨V, hV, hfin.subset ?_⟩
  rintro e ⟨y, ⟨z, hz, rfl⟩, hyV⟩
  exact ⟨⟨z, splittingDisk_space_subset T.complex e.2.1 hz⟩, hz, hVW hyV⟩

end DifferentialGeometry.Topology.PiecewiseLinear

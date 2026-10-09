/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldOfLocallyFinitePLPieceIn
import DifferentialGeometry.Topology.PiecewiseLinear.SplittingDiskRim

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem dualCell_starComplex_eq (K : Geometry.SimplicialComplex ℝ E) {v : E}
    (hv : {v} ∈ K.faces) :
    dualCell (starComplex K v) {v} (singleton_mem_starComplex K v hv) =
      dualCell K {v} hv := by
  ext u
  rw [mem_dualCell_faces_iff, mem_dualCell_faces_iff]
  constructor
  · rintro ⟨d, hd, hne, hsub, rfl⟩
    exact ⟨d, hd.of_le (starComplex_faces_subset K v), hne, hsub, rfl⟩
  · rintro ⟨d, hd, hne, hsub, rfl⟩
    refine ⟨d, ⟨?_, hd.2⟩, hne, hsub, rfl⟩
    intro s hs
    refine ⟨hd.mem_faces hs, ?_⟩
    rw [Finset.insert_eq_of_mem (Finset.singleton_subset_iff.mp (hsub s hs))]
    exact hd.mem_faces hs

open Classical in
theorem graphDualCell_starComplex_eq (K L : Geometry.SimplicialComplex ℝ E)
    (hL : L.faces ⊆ K.faces) {v : E} (hv : {v} ∈ K.faces) :
    graphDualCell (starComplex K v) (restrict L (starComplex K v).space) v =
      graphDualCell K L v := by
  let S := starComplex K v
  have hS : S.faces ⊆ K.faces := starComplex_faces_subset K v
  have hvS : {v} ∈ S.faces := singleton_mem_starComplex K v hv
  have hdual : dualCell S {v} hvS = dualCell K {v} hv := dualCell_starComplex_eq K hv
  ext u
  constructor
  · intro hu
    obtain ⟨d, hd, hne, rfl⟩ := derivedNeighborhood_faces_subset S _ hu.1
    obtain ⟨hmeet, hfaces⟩ := (mem_graphDualCell_faces_iff_of_flag _ hvS hd hne).mp hu
    refine (mem_graphDualCell_faces_iff_of_flag L hv
      (hd.of_le (barycentricSubdivision_faces_subset hS)) hne).mpr ⟨?_, ?_⟩
    · intro e he
      obtain ⟨s, hs, hse⟩ := hmeet e he
      exact ⟨s, hs.1, hse⟩
    · intro e he
      rw [← hdual]
      exact hfaces e he
  · intro hu
    obtain ⟨d, hd, hne, rfl⟩ := derivedNeighborhood_faces_subset K L hu.1
    obtain ⟨hmeet, hfaces⟩ := (mem_graphDualCell_faces_iff_of_flag L hv hd hne).mp hu
    have hfacesS : ∀ e ∈ d, e ∈ (dualCell S {v} hvS).faces := by
      intro e he
      rw [hdual]
      exact hfaces e he
    have hdS : IsFlag (barycentricSubdivision S) d :=
      ⟨fun e he => dualCell_faces_subset S hvS (hfacesS e he), hd.2⟩
    refine (mem_graphDualCell_faces_iff_of_flag _ hvS hdS hne).mpr ⟨?_, hfacesS⟩
    intro e he
    obtain ⟨s, hs, hse⟩ := hmeet e he
    have hcent : s.centroid ℝ id ∈ S.space := by
      rw [← (barycentricSubdivision_isSubdivision S).space_eq]
      exact (barycentricSubdivision S).convexHull_subset_space (hdS.mem_faces he)
        (subset_convexHull ℝ _ hse)
    have hsS := mem_faces_of_mem_openSimplex_of_mem_space hS (hL hs)
      (centroid_mem_openSimplex (L.nonempty_of_mem_faces hs)) hcent
    exact ⟨s, ⟨hs, S.convexHull_subset_space hsS⟩, hse⟩

open Classical in
theorem LocallyFinitePLPieceIn.isPLBall_closedStar [FiniteDimensional ℝ E]
    {X : Type*} {d n : ℕ} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) X] {Y : Set X}
    (T : LocallyFinitePLPieceIn E d X Y)
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) T.complex) {v : E}
    (hv : {v} ∈ T.complex.faces) : IsPLBall (n + 1) (closedStar T.complex v) := by
  let _ : Finite (SimplicialComplex.geometricLink T.complex {v}).faces :=
    (T.geometricLink_faces_finite hv).to_subtype
  rw [closedStar_eq_coneComplex_space T.complex hv]
  rcases hK v hv with hlink | hlink
  · exact (isConeBase_geometricLink T.complex).isPLBall_of_isPLSphere hlink
  · exact (isConeBase_geometricLink T.complex).isPLBall_of_isPLBall hlink

open Classical in
theorem LocallyFinitePLPieceIn.isPLBall_graphDualCell [FiniteDimensional ℝ E]
    {X : Type*} {d : ℕ} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) X] {Y : Set X}
    (T : LocallyFinitePLPieceIn E d X Y) (L : Geometry.SimplicialComplex ℝ E)
    (hK : IsCombinatorialManifoldWithBoundary 3 T.complex)
    (hL : L.faces ⊆ T.complex.faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {v : E} (hv : {v} ∈ L.faces) :
    IsPLBall 3 (graphDualCell T.complex L v).space := by
  let S := starComplex T.complex v
  let _ : Finite S.faces := (T.starComplex_faces_finite (hL hv)).to_subtype
  have hSball : IsPLBall 3 S.space := by
    rw [starComplex_space T.complex v (hL hv)]
    exact T.isPLBall_closedStar hK (hL hv)
  rw [← graphDualCell_starComplex_eq T.complex L hL (hL hv)]
  apply hSball.isCombinatorialManifoldWithBoundary.isPLBall_graphDualCell S _
  · intro s hs
    exact mem_faces_of_mem_openSimplex_of_mem_space (starComplex_faces_subset T.complex v)
      (hL hs.1) (centroid_mem_openSimplex (L.nonempty_of_mem_faces hs.1))
      (hs.2 (s.centroid_mem_convexHull (L.nonempty_of_mem_faces hs.1)))
  · exact fun s hs => hcard s hs.1
  · exact ⟨hv, S.convexHull_subset_space (singleton_mem_starComplex T.complex v (hL hv))⟩

open Classical in
theorem LocallyFinitePLPieceIn.graphDualCell_faces_finite
    {X : Type*} {d : ℕ} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) X] {Y : Set X}
    (T : LocallyFinitePLPieceIn E d X Y) (L : Geometry.SimplicialComplex ℝ E)
    {v : E} (hv : {v} ∈ T.complex.faces) :
    (graphDualCell T.complex L v).faces.Finite := by
  let A := dualCell T.complex {v} hv
  let _ : Finite A.faces := (T.dualCell_faces_finite hv).to_subtype
  apply (Set.toFinite (barycentricSubdivision A).faces).subset
  intro u hu
  obtain ⟨d, hd, hne, rfl⟩ := derivedNeighborhood_faces_subset T.complex L hu.1
  obtain ⟨-, hfaces⟩ := (mem_graphDualCell_faces_iff_of_flag L hv hd hne).mp hu
  exact ⟨d, ⟨hfaces, hd.2⟩, hne, rfl⟩

open Classical in
theorem LocallyFinitePLPieceIn.locallyFinite_graphDualCell
    {X : Type*} {d : ℕ} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) X] {Y : Set X}
    (T : LocallyFinitePLPieceIn E d X Y) (L : Geometry.SimplicialComplex ℝ E) :
    LocallyFinite fun v : T.complex.vertices =>
      (Subtype.val : T.complex.space → E) ⁻¹' (graphDualCell T.complex L v.1).space := by
  intro x
  obtain ⟨V, hV, hfin⟩ := T.locallyFinite x
  have hvertex (s : T.complex.faces) :
      {v : T.complex.vertices | v.1 ∈ s.1}.Finite :=
    s.1.finite_toSet.preimage Subtype.val_injective.injOn
  refine ⟨V, hV, (hfin.biUnion fun s _ => hvertex s).subset ?_⟩
  intro v hv
  obtain ⟨y, hyC, hyV⟩ := hv
  obtain ⟨s, hs, hys⟩ := T.complex.mem_space_iff.mp y.2
  have hstar := graphDualCell_space_subset_closedStar T.complex L v.1 hyC
  rw [closedStar_barycentricSubdivision_eq_dualCell T.complex v.2] at hstar
  have hvs := subset_of_mem_dualCell_of_mem_convexHull T.complex v.2 hs hstar hys
  exact mem_biUnion (x := (⟨s, hs⟩ : T.complex.faces)) ⟨y, hys, hyV⟩
    (Finset.singleton_subset_iff.mp hvs)

open Classical in
theorem LocallyFinitePLPieceIn.locallyFinite_image_graphDualCell
    {X : Type*} {d : ℕ} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) X] {Y : Set X}
    (T : LocallyFinitePLPieceIn E d X Y) (L : Geometry.SimplicialComplex ℝ E) :
    ∀ x ∈ Y, ∃ V ∈ 𝓝 x, {v : T.complex.vertices |
      (T.map '' (graphDualCell T.complex L v.1).space ∩ V).Nonempty}.Finite := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := T.bijOn.surjOn hx
  obtain ⟨W, hW, hfin⟩ := T.locallyFinite_graphDualCell L ⟨p, hp⟩
  rw [T.isEmbedding.isInducing.nhds_eq_comap] at hW
  obtain ⟨V, hV, hVW⟩ := Filter.mem_comap.mp hW
  refine ⟨V, hV, hfin.subset ?_⟩
  rintro v ⟨y, ⟨z, hz, rfl⟩, hyV⟩
  have hzK := derivedNeighborhood_space_subset T.complex L
    (graphDualCell_space_subset T.complex L v.1 hz)
  exact ⟨⟨z, hzK⟩, hz, hVW hyV⟩

end DifferentialGeometry.Topology.PiecewiseLinear

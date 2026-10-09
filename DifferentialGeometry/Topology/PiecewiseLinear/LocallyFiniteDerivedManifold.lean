/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteDerivedNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexNhdsWithin

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] {U : Set X}

open Classical in
theorem LocallyFinitePLPieceIn.exists_finite_manifold_subcomplex_neighborhood
    [FiniteDimensional ℝ E] (T : LocallyFinitePLPieceIn E 3 X U) {n : ℕ}
    (hT : IsCombinatorialManifoldWithBoundary (n + 1) T.complex)
    {x : E} (hx : x ∈ T.complex.space) :
    ∃ S : Geometry.SimplicialComplex ℝ E, S.faces.Finite ∧ S.faces ⊆ T.complex.faces ∧
      S.space ∈ 𝓝[T.complex.space] x ∧ IsCombinatorialManifoldWithBoundary (n + 1) S := by
  obtain ⟨v, hv, hxv⟩ := exists_vertex_mem_openStar T.complex hx
  let S := starComplex T.complex v
  let _ : Finite S.faces := (T.starComplex_faces_finite hv).to_subtype
  have hball : IsPLBall (n + 1) S.space := by
    rw [starComplex_space T.complex v hv]
    exact T.isPLBall_closedStar hT hv
  refine ⟨S, T.starComplex_faces_finite hv, starComplex_faces_subset T.complex v,
    ?_, hball.isCombinatorialManifoldWithBoundary⟩
  rw [starComplex_space T.complex v hv]
  have hpre : (Subtype.val : T.complex.space → E) ⁻¹' closedStar T.complex v ∈
      𝓝 (⟨x, hx⟩ : T.complex.space) :=
    Filter.mem_of_superset ((T.isOpen_preimage_openStar v).mem_nhds hxv)
      (preimage_mono (openStar_subset_closedStar T.complex hv))
  exact preimage_coe_mem_nhds_subtype.mp hpre

open Classical in
theorem LocallyFinitePLPieceIn.isCombinatorialManifoldWithBoundary_derivedNeighborhood
    [FiniteDimensional ℝ E] (T : LocallyFinitePLPieceIn E 3 X U) {n : ℕ}
    (hT : IsCombinatorialManifoldWithBoundary (n + 1) T.complex)
    (L : Geometry.SimplicialComplex ℝ E) (hL : L.faces ⊆ T.complex.faces) :
    IsCombinatorialManifoldWithBoundary (n + 1) (derivedNeighborhood T.complex L) := by
  intro x hx
  have hxT : x ∈ T.complex.space := derivedNeighborhood_space_subset T.complex L
    ((derivedNeighborhood T.complex L).convexHull_subset_space hx (by simp))
  obtain ⟨S, hfin, hS, hnbhd, hman⟩ :=
    T.exists_finite_manifold_subcomplex_neighborhood hT hxT
  let _ : Finite S.faces := hfin.to_subtype
  let R := derivedNeighborhood S (restrict L S.space)
  have hR : R.faces ⊆ (derivedNeighborhood T.complex L).faces :=
    derivedNeighborhood_faces_mono hS (restrict_faces_subset L S.space)
  have hRnhds : R.space ∈ 𝓝[(derivedNeighborhood T.complex L).space] x :=
    derivedNeighborhood_restrict_space_mem_nhdsWithin T.complex S L hS hL hnbhd
  have hxR : {x} ∈ R.faces :=
    mem_faces_of_mem_nhdsWithin_space hR hx (by simp) hRnhds
  have hlink := hman.derivedNeighborhood (restrict L S.space) x hxR
  rwa [geometricLink_eq_of_space_mem_nhdsWithin hR hRnhds] at hlink

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] in
open Classical in
theorem LocallyFinitePLPieceIn.derivedNeighborhood_faces_finite_of_finite_core
    {d : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin d)) X]
    (T : LocallyFinitePLPieceIn E d X U) (L : Geometry.SimplicialComplex ℝ E)
    (hL : L.faces ⊆ T.complex.faces) (hfin : L.faces.Finite) :
    (derivedNeighborhood T.complex L).faces.Finite := by
  have hvertices : L.vertices.Finite := hfin.preimage Finset.singleton_injective.injOn
  apply (hvertices.biUnion fun v hv => T.graphDualCell_faces_finite L (hL hv)).subset
  intro s hs
  obtain ⟨v, hv, hsv⟩ := exists_mem_graphDualCell_faces T.complex L hL hs
  exact mem_biUnion hv hsv

end DifferentialGeometry.Topology.PiecewiseLinear

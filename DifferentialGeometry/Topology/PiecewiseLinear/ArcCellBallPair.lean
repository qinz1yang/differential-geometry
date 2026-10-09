/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ArcChainCells
import DifferentialGeometry.Topology.PiecewiseLinear.BallPairArc

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem IsCombinatorialManifold.isPLBallPair_derivedNeighborhoodCell_arcChainFace
    [FiniteDimensional ℝ E] {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifold 3 K) {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    (hinj : ∀ i ≤ n, ∀ k ≤ n, v i = v k → i = k) {j : ℕ}
    (hj0 : 1 ≤ j) (hjn : j + 1 ≤ 2 * n) :
    IsPLBallPair 2 1 (derivedNeighborhoodCell K (arcChainFace v j)).space
      ((derivedNeighborhoodCell K (arcChainFace v j)).space ∩ (arcComplexIn K v n).space) := by
  let s := arcChainFace v j
  let sPrev := arcChainFace v (j - 1)
  let sNext := arcChainFace v (j + 1)
  let p := s.centroid ℝ id
  let zPrev := ({p, sPrev.centroid ℝ id} : Finset E).centroid ℝ id
  let zNext := ({p, sNext.centroid ℝ id} : Finset E).centroid ℝ id
  let L := upperLink (PiecewiseLinear.barycentricSubdivision K) {p}
  let _ : Finite L.faces :=
    (upperLink_faces_finite (PiecewiseLinear.barycentricSubdivision K) {p}).to_subtype
  have hs : s ∈ K.faces := by
    exact arcChainFace_mem_faces hvert hedge (by omega)
  have hsPrev : sPrev ∈ K.faces := by
    exact arcChainFace_mem_faces hvert hedge (by omega)
  have hsNext : sNext ∈ K.faces := by
    exact arcChainFace_mem_faces hvert hedge (by omega)
  have hssPrev : s ≠ sPrev := by
    intro h
    have := arcChainFace_injective hinj (by omega) (by omega) h
    omega
  have hssNext : s ≠ sNext := by
    intro h
    have := arcChainFace_injective hinj (by omega) (by omega) h
    omega
  have hsPrevNext : sPrev ≠ sNext := by
    intro h
    have := arcChainFace_injective hinj (by omega) (by omega) h
    omega
  have hcompPrev : s ⊆ sPrev ∨ sPrev ⊆ s := by
    exact (arcChainFace_comparable_iff hinj (by omega) (by omega)).mpr (by omega)
  have hcompNext : s ⊆ sNext ∨ sNext ⊆ s := by
    exact (arcChainFace_comparable_iff hinj (by omega) (by omega)).mpr (by omega)
  have hL : IsConeBase p L := by
    exact isConeBase_centroid_upperLink K hs
  have hS : IsPLSphere 2 L.space := by
    exact hK.isPLSphere_upperLink_centroid hs
  have hzPrevL : zPrev ∈ L.space := by
    apply coneSet_pair_centroid_subset_upperLink K hs hsPrev hssPrev hcompPrev
    exact apex_mem_coneSet zPrev
      (upperLink (PiecewiseLinear.barycentricSubdivision K) {p, sPrev.centroid ℝ id}).space
  have hzNextL : zNext ∈ L.space := by
    apply coneSet_pair_centroid_subset_upperLink K hs hsNext hssNext hcompNext
    exact apex_mem_coneSet zNext
      (upperLink (PiecewiseLinear.barycentricSubdivision K) {p, sNext.centroid ℝ id}).space
  have hpair : ({zPrev, zNext} : Set E) ⊆ L.space := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact hzPrevL
    · rw [Set.mem_singleton_iff.mp hx]
      exact hzNextL
  have hePrev : ({p, sPrev.centroid ℝ id} : Finset E) ∈
      (PiecewiseLinear.barycentricSubdivision K).faces := by
    exact pair_centroid_mem_barycentricSubdivision_of_subset_or_subset K hs hsPrev hcompPrev
  have heNext : ({p, sNext.centroid ℝ id} : Finset E) ∈
      (PiecewiseLinear.barycentricSubdivision K).faces := by
    exact pair_centroid_mem_barycentricSubdivision_of_subset_or_subset K hs hsNext hcompNext
  have hsPrevCentroidNe : sPrev.centroid ℝ id ≠ s.centroid ℝ id :=
    centroid_ne_centroid_of_ne K hsPrev hs hssPrev.symm
  have hsPrevNextCentroidNe : sPrev.centroid ℝ id ≠ sNext.centroid ℝ id :=
    centroid_ne_centroid_of_ne K hsPrev hsNext hsPrevNext
  have he : ({p, sPrev.centroid ℝ id} : Finset E) ≠ {p, sNext.centroid ℝ id} := by
    intro h
    have hmem : sPrev.centroid ℝ id ∈ ({p, sNext.centroid ℝ id} : Finset E) := by
      rw [← h]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    exact hmem.elim hsPrevCentroidNe hsPrevNextCentroidNe
  have hzne : zPrev ≠ zNext :=
    centroid_ne_centroid_of_ne (PiecewiseLinear.barycentricSubdivision K) hePrev heNext he
  have hpzPrev : p ≠ zPrev := by
    intro h
    exact hL.notMem_space (by rw [h]; exact hzPrevL)
  have hpzNext : p ≠ zNext := by
    intro h
    exact hL.notMem_space (by rw [h]; exact hzNextL)
  have hrad : IsRadiallyInjective p ({zPrev, zNext} : Set E) := by
    intro x hx y hy t ht hxy
    exact hL.radial x (hpair hx) y (hpair hy) t ht hxy
  have hballPair :=
    isPLBallPair_coneSet_arc_of_radial hL hS hpair hzne hpzPrev hpzNext hrad
  rw [derivedNeighborhoodCell_inter_arcComplexIn_space hvert hedge hinj hj0 hjn,
    derivedNeighborhoodCell_space_eq_coneSet K hs, coneSet_pair_eq_union_segment]
  exact hballPair

end DifferentialGeometry.Topology.PiecewiseLinear

/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ArcCellBallPair

/-!
# Gluing data for adjacent cells of a simplicial arc
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
noncomputable def arcCellApex (v : ℕ → E) (j : ℕ) : E :=
  (arcChainFace v j).centroid ℝ id

open Classical in
noncomputable def arcCellCrossing (v : ℕ → E) (j : ℕ) : E :=
  ({arcCellApex v j, arcCellApex v (j + 1)} : Finset E).centroid ℝ id

open Classical in
noncomputable def arcCellBase (K : Geometry.SimplicialComplex ℝ E) (v : ℕ → E) (j : ℕ) :=
  upperLink (PiecewiseLinear.barycentricSubdivision K) {arcCellApex v j}

open Classical in
noncomputable def arcCellInterfaceBase
    (K : Geometry.SimplicialComplex ℝ E) (v : ℕ → E) (j : ℕ) :=
  upperLink (PiecewiseLinear.barycentricSubdivision K)
    {arcCellApex v j, arcCellApex v (j + 1)}

open Classical in
theorem derivedNeighborhoodCell_arcChainFace_space_eq_coneSet
    {K : Geometry.SimplicialComplex ℝ E} {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    {j : ℕ} (hj : j ≤ 2 * n) :
    (derivedNeighborhoodCell K (arcChainFace v j)).space =
      coneSet (arcCellApex v j) (arcCellBase K v j).space := by
  simpa only [arcCellApex, arcCellBase] using
    derivedNeighborhoodCell_space_eq_coneSet K (arcChainFace_mem_faces hvert hedge hj)

open Classical in
theorem adjacent_derivedNeighborhoodCell_arcChainFace_inter_eq_coneSet
    {K : Geometry.SimplicialComplex ℝ E} {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    (hinj : ∀ i ≤ n, ∀ k ≤ n, v i = v k → i = k)
    {j : ℕ} (hj : j + 1 ≤ 2 * n) :
    (derivedNeighborhoodCell K (arcChainFace v j)).space ∩
        (derivedNeighborhoodCell K (arcChainFace v (j + 1))).space =
      coneSet (arcCellCrossing v j) (arcCellInterfaceBase K v j).space := by
  have hs := arcChainFace_mem_faces hvert hedge (j := j) (by omega)
  have ht := arcChainFace_mem_faces hvert hedge (j := j + 1) (by omega)
  have hcomp : arcChainFace v j ⊆ arcChainFace v (j + 1) ∨
      arcChainFace v (j + 1) ⊆ arcChainFace v j :=
    (arcChainFace_comparable_iff hinj (by omega) (by omega)).mpr (by omega)
  simpa only [arcCellApex, arcCellCrossing, arcCellInterfaceBase] using
    derivedNeighborhoodCell_inter_eq_coneSet K hs ht hcomp

open Classical in
theorem arcCellBase_faces_finite {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (v : ℕ → E) (j : ℕ) : (arcCellBase K v j).faces.Finite := by
  exact upperLink_faces_finite (PiecewiseLinear.barycentricSubdivision K) {arcCellApex v j}

open Classical in
theorem arcCellInterfaceBase_faces_finite
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces] (v : ℕ → E) (j : ℕ) :
    (arcCellInterfaceBase K v j).faces.Finite := by
  exact upperLink_faces_finite (PiecewiseLinear.barycentricSubdivision K)
    {arcCellApex v j, arcCellApex v (j + 1)}

open Classical in
theorem isConeBase_arcCellBase {K : Geometry.SimplicialComplex ℝ E}
    {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    {j : ℕ} (hj : j ≤ 2 * n) : IsConeBase (arcCellApex v j) (arcCellBase K v j) := by
  simpa only [arcCellApex, arcCellBase] using
    isConeBase_centroid_upperLink K (arcChainFace_mem_faces hvert hedge hj)

open Classical in
theorem IsCombinatorialManifold.isPLSphere_arcCellBase [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifold 3 K) {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    {j : ℕ} (hj : j ≤ 2 * n) : IsPLSphere 2 (arcCellBase K v j).space := by
  simpa only [arcCellApex, arcCellBase] using
    hK.isPLSphere_upperLink_centroid (arcChainFace_mem_faces hvert hedge hj)

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLSphere_arcCellBase_of_interior
    [FiniteDimensional ℝ E] {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    {j : ℕ} (hj : j ≤ 2 * n) (hjB : arcChainFace v j ∉ (boundaryComplex 3 K).faces) :
    IsPLSphere 2 (arcCellBase K v j).space := by
  simpa only [arcCellApex, arcCellBase] using
    hK.isPLSphere_upperLink_centroid_of_not_mem_boundaryComplex
      (arcChainFace_mem_faces hvert hedge hj) hjB

open Classical in
theorem isConeBase_arcCellInterfaceBase {K : Geometry.SimplicialComplex ℝ E}
    {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    (hinj : ∀ i ≤ n, ∀ k ≤ n, v i = v k → i = k)
    {j : ℕ} (hj : j + 1 ≤ 2 * n) :
    IsConeBase (arcCellCrossing v j) (arcCellInterfaceBase K v j) := by
  have hs := arcChainFace_mem_faces hvert hedge (j := j) (by omega)
  have ht := arcChainFace_mem_faces hvert hedge (j := j + 1) (by omega)
  have hcomp : arcChainFace v j ⊆ arcChainFace v (j + 1) ∨
      arcChainFace v (j + 1) ⊆ arcChainFace v j :=
    (arcChainFace_comparable_iff hinj (by omega) (by omega)).mpr (by omega)
  have hface := pair_centroid_mem_barycentricSubdivision_of_subset_or_subset K hs ht hcomp
  simpa only [arcCellApex, arcCellCrossing, arcCellInterfaceBase] using
    isConeBase_upperLink (PiecewiseLinear.barycentricSubdivision K) hface

open Classical in
theorem IsCombinatorialManifold.isPLSphere_arcCellInterfaceBase [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifold 3 K) {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    (hinj : ∀ i ≤ n, ∀ k ≤ n, v i = v k → i = k)
    {j : ℕ} (hj : j + 1 ≤ 2 * n) : IsPLSphere 1 (arcCellInterfaceBase K v j).space := by
  have hs := arcChainFace_mem_faces hvert hedge (j := j) (by omega)
  have ht := arcChainFace_mem_faces hvert hedge (j := j + 1) (by omega)
  have hne : arcChainFace v j ≠ arcChainFace v (j + 1) := by
    intro h
    have := arcChainFace_injective hinj (by omega) (by omega) h
    omega
  have hcomp : arcChainFace v j ⊆ arcChainFace v (j + 1) ∨
      arcChainFace v (j + 1) ⊆ arcChainFace v j :=
    (arcChainFace_comparable_iff hinj (by omega) (by omega)).mpr (by omega)
  simpa only [arcCellApex, arcCellInterfaceBase] using
    hK.isPLSphere_upperLink_pair_centroid hs ht hne hcomp

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLSphere_arcCellInterfaceBase_of_interior_left
    [FiniteDimensional ℝ E] {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    (hinj : ∀ i ≤ n, ∀ k ≤ n, v i = v k → i = k)
    {j : ℕ} (hj : j + 1 ≤ 2 * n)
    (hjB : arcChainFace v j ∉ (boundaryComplex 3 K).faces) :
    IsPLSphere 1 (arcCellInterfaceBase K v j).space := by
  have hs := arcChainFace_mem_faces hvert hedge (j := j) (by omega)
  have ht := arcChainFace_mem_faces hvert hedge (j := j + 1) (by omega)
  have hne : arcChainFace v j ≠ arcChainFace v (j + 1) := by
    intro h
    have := arcChainFace_injective hinj (by omega) (by omega) h
    omega
  have hcomp : arcChainFace v j ⊆ arcChainFace v (j + 1) ∨
      arcChainFace v (j + 1) ⊆ arcChainFace v j :=
    (arcChainFace_comparable_iff hinj (by omega) (by omega)).mpr (by omega)
  simpa only [arcCellApex, arcCellInterfaceBase] using
    hK.isPLSphere_upperLink_pair_centroid_of_interior_face hs ht hjB hne hcomp

open Classical in
theorem arcCellInterface_subset_arcCellBase_left {K : Geometry.SimplicialComplex ℝ E}
    {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    (hinj : ∀ i ≤ n, ∀ k ≤ n, v i = v k → i = k)
    {j : ℕ} (hj : j + 1 ≤ 2 * n) :
    coneSet (arcCellCrossing v j) (arcCellInterfaceBase K v j).space ⊆
      (arcCellBase K v j).space := by
  have hs := arcChainFace_mem_faces hvert hedge (j := j) (by omega)
  have ht := arcChainFace_mem_faces hvert hedge (j := j + 1) (by omega)
  have hne : arcChainFace v j ≠ arcChainFace v (j + 1) := by
    intro h
    have := arcChainFace_injective hinj (by omega) (by omega) h
    omega
  have hcomp : arcChainFace v j ⊆ arcChainFace v (j + 1) ∨
      arcChainFace v (j + 1) ⊆ arcChainFace v j :=
    (arcChainFace_comparable_iff hinj (by omega) (by omega)).mpr (by omega)
  simpa only [arcCellApex, arcCellCrossing, arcCellBase, arcCellInterfaceBase] using
    coneSet_pair_centroid_subset_upperLink K hs ht hne hcomp

open Classical in
theorem arcCellInterface_subset_arcCellBase_right {K : Geometry.SimplicialComplex ℝ E}
    {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    (hinj : ∀ i ≤ n, ∀ k ≤ n, v i = v k → i = k)
    {j : ℕ} (hj : j + 1 ≤ 2 * n) :
    coneSet (arcCellCrossing v j) (arcCellInterfaceBase K v j).space ⊆
      (arcCellBase K v (j + 1)).space := by
  have hs := arcChainFace_mem_faces hvert hedge (j := j) (by omega)
  have ht := arcChainFace_mem_faces hvert hedge (j := j + 1) (by omega)
  have hne : arcChainFace v j ≠ arcChainFace v (j + 1) := by
    intro h
    have := arcChainFace_injective hinj (by omega) (by omega) h
    omega
  have hcomp : arcChainFace v j ⊆ arcChainFace v (j + 1) ∨
      arcChainFace v (j + 1) ⊆ arcChainFace v j :=
    (arcChainFace_comparable_iff hinj (by omega) (by omega)).mpr (by omega)
  simpa only [arcCellApex, arcCellCrossing, arcCellBase, arcCellInterfaceBase] using
    coneSet_pair_centroid_subset_upperLink_right K hs ht hne hcomp

open Classical in
theorem arcCellCrossing_mem_adjacent_derivedNeighborhoodCells
    {K : Geometry.SimplicialComplex ℝ E} {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    (hinj : ∀ i ≤ n, ∀ k ≤ n, v i = v k → i = k)
    {j : ℕ} (hj : j + 1 ≤ 2 * n) :
    arcCellCrossing v j ∈ (derivedNeighborhoodCell K (arcChainFace v j)).space ∩
      (derivedNeighborhoodCell K (arcChainFace v (j + 1))).space := by
  rw [adjacent_derivedNeighborhoodCell_arcChainFace_inter_eq_coneSet hvert hedge hinj hj]
  exact apex_mem_coneSet _ _

open Classical in
theorem previous_arcCellCrossing_not_mem_interface
    {K : Geometry.SimplicialComplex ℝ E} {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    (hinj : ∀ i ≤ n, ∀ k ≤ n, v i = v k → i = k)
    {j : ℕ} (hj0 : 1 ≤ j) (hjn : j + 1 ≤ 2 * n) :
    arcCellCrossing v (j - 1) ∉
      coneSet (arcCellCrossing v j) (arcCellInterfaceBase K v j).space := by
  intro hmem
  have hprev := arcCellCrossing_mem_adjacent_derivedNeighborhoodCells
    hvert hedge hinj (j := j - 1) (by omega)
  have hnext : arcCellCrossing v (j - 1) ∈
      (derivedNeighborhoodCell K (arcChainFace v (j + 1))).space := by
    rw [← adjacent_derivedNeighborhoodCell_arcChainFace_inter_eq_coneSet
      hvert hedge hinj (j := j) (by omega)] at hmem
    exact hmem.2
  have hdis := disjoint_derivedNeighborhoodCell_arcChainFace hvert hedge hinj
    (i := j - 1) (j := j + 1) (by omega) (by omega) (by omega)
  exact Set.disjoint_left.mp hdis hprev.1 hnext

open Classical in
theorem next_arcCellCrossing_not_mem_interface
    {K : Geometry.SimplicialComplex ℝ E} {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    (hinj : ∀ i ≤ n, ∀ k ≤ n, v i = v k → i = k)
    {j : ℕ} (hjn : j + 2 ≤ 2 * n) :
    arcCellCrossing v (j + 1) ∉
      coneSet (arcCellCrossing v j) (arcCellInterfaceBase K v j).space := by
  intro hmem
  have hnext := arcCellCrossing_mem_adjacent_derivedNeighborhoodCells
    hvert hedge hinj (j := j + 1) (by omega)
  have hprev : arcCellCrossing v (j + 1) ∈
      (derivedNeighborhoodCell K (arcChainFace v j)).space := by
    rw [← adjacent_derivedNeighborhoodCell_arcChainFace_inter_eq_coneSet
      hvert hedge hinj (j := j) (by omega)] at hmem
    exact hmem.1
  have hdis := disjoint_derivedNeighborhoodCell_arcChainFace hvert hedge hinj
    (i := j) (j := j + 2) (by omega) (by omega) (by omega)
  exact Set.disjoint_left.mp hdis hprev hnext.2

open Classical in
theorem previous_arcCellCrossing_mem_closure_diff_interface
    {K : Geometry.SimplicialComplex ℝ E} {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    (hinj : ∀ i ≤ n, ∀ k ≤ n, v i = v k → i = k)
    {j : ℕ} (hj0 : 1 ≤ j) (hjn : j + 1 ≤ 2 * n) :
    arcCellCrossing v (j - 1) ∈ closure
        ((arcCellBase K v j).space \
          coneSet (arcCellCrossing v j) (arcCellInterfaceBase K v j).space) \
      coneSet (arcCellCrossing v j) (arcCellInterfaceBase K v j).space := by
  have hbase' : arcCellCrossing v (j - 1) ∈ (arcCellBase K v ((j - 1) + 1)).space := by
    exact arcCellInterface_subset_arcCellBase_right (K := K) (n := n) (v := v)
      hvert hedge hinj (j := j - 1) (by omega) (apex_mem_coneSet _ _)
  have hbase : arcCellCrossing v (j - 1) ∈ (arcCellBase K v j).space := by
    simpa only [Nat.sub_add_cancel hj0] using hbase'
  have hnot := previous_arcCellCrossing_not_mem_interface hvert hedge hinj hj0 hjn
  exact ⟨subset_closure ⟨hbase, hnot⟩, hnot⟩

open Classical in
theorem next_arcCellCrossing_mem_closure_diff_interface
    {K : Geometry.SimplicialComplex ℝ E} {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    (hinj : ∀ i ≤ n, ∀ k ≤ n, v i = v k → i = k)
    {j : ℕ} (hjn : j + 2 ≤ 2 * n) :
    arcCellCrossing v (j + 1) ∈ closure
        ((arcCellBase K v (j + 1)).space \
          coneSet (arcCellCrossing v j) (arcCellInterfaceBase K v j).space) \
      coneSet (arcCellCrossing v j) (arcCellInterfaceBase K v j).space := by
  have hbase : arcCellCrossing v (j + 1) ∈ (arcCellBase K v (j + 1)).space :=
    arcCellInterface_subset_arcCellBase_left hvert hedge hinj (j := j + 1) (by omega)
      (apex_mem_coneSet _ _)
  have hnot := next_arcCellCrossing_not_mem_interface hvert hedge hinj hjn
  exact ⟨subset_closure ⟨hbase, hnot⟩, hnot⟩

open Classical in
theorem derivedNeighborhoodCell_arcChainFace_inter_arcComplexIn_space_eq
    {K : Geometry.SimplicialComplex ℝ E} {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    (hinj : ∀ i ≤ n, ∀ k ≤ n, v i = v k → i = k)
    {j : ℕ} (hj0 : 1 ≤ j) (hjn : j + 1 ≤ 2 * n) :
    (derivedNeighborhoodCell K (arcChainFace v j)).space ∩ (arcComplexIn K v n).space =
      coneSet (arcCellApex v j) {arcCellCrossing v (j - 1), arcCellCrossing v j} := by
  rw [derivedNeighborhoodCell_inter_arcComplexIn_space hvert hedge hinj hj0 hjn]
  change coneSet (arcCellApex v j)
    {({arcCellApex v j, arcCellApex v (j - 1)} : Finset E).centroid ℝ id,
      arcCellCrossing v j} = _
  rw [Finset.pair_comm (arcCellApex v j) (arcCellApex v (j - 1))]
  have hcross :
      ({arcCellApex v (j - 1), arcCellApex v j} : Finset E).centroid ℝ id =
        arcCellCrossing v (j - 1) := by
    rw [arcCellCrossing, Nat.sub_add_cancel hj0]
  rw [hcross]

end DifferentialGeometry.Topology.PiecewiseLinear

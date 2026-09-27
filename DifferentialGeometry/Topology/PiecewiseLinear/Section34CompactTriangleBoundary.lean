/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConeSphereBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedCellCone
import DifferentialGeometry.Topology.PiecewiseLinear.DualCellVertexInterface
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTriangleTraces

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem derivedNeighborhoodCell_inter_derivedNeighborhood_eq_upperLink
    (K L : Geometry.SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces)
    (hL : ∀ r, r ∈ L.faces ↔ r ∈ K.faces ∧ r ≠ s) :
    (derivedNeighborhoodCell K s).space ∩ (derivedNeighborhood K L).space =
      (upperLink (barycentricSubdivision K) {s.centroid ℝ id}).space := by
  have hLK : L.faces ⊆ K.faces := fun r hr => ((hL r).mp hr).1
  have hU : (derivedNeighborhood K L).space =
      ⋃ q ∈ (barycentricSubdivision K).vertices \ ({s.centroid ℝ id} : Set E),
        closedStar (secondDerived K) q := by
    rw [← iUnion_derivedNeighborhoodCell_space K L hLK]
    apply Subset.antisymm
    · intro x hx
      obtain ⟨r, hr, hxr⟩ := mem_iUnion₂.mp hx
      have hrK := hLK hr
      have hne : r.centroid ℝ id ≠ s.centroid ℝ id := fun h =>
        ((hL r).mp hr).2 (injOn_faces_of_mem_openSimplex K
          (centroid_mem_openSimplex_of_mem_faces K) hrK hs h)
      refine mem_iUnion₂.mpr ⟨r.centroid ℝ id,
        ⟨singleton_centroid_mem_barycentricSubdivision K hrK, hne⟩, ?_⟩
      rwa [← derivedNeighborhoodCell_space_eq_closedStar K hrK]
    · intro x hx
      obtain ⟨q, ⟨hq, hqs⟩, hxq⟩ := mem_iUnion₂.mp hx
      obtain ⟨r, hr, hcr⟩ := exists_mem_image_centroid_of_mem_barycentricSubdivision hq
      have hcrq : r.centroid ℝ id = q := Finset.mem_singleton.mp hcr
      have hrs : r ≠ s := by
        intro h
        exact hqs (by simp only [mem_singleton_iff, ← hcrq, h])
      refine mem_iUnion₂.mpr ⟨r, (hL r).mpr ⟨hr, hrs⟩, ?_⟩
      rw [derivedNeighborhoodCell_space_eq_closedStar K hr, hcrq]
      exact hxq
  rw [derivedNeighborhoodCell_eq_dualCell K hs, hU]
  simpa only [Finset.coe_singleton, secondDerived] using
    dualCell_space_inter_iUnion_closedStar_eq_upperLink (barycentricSubdivision K)
      (singleton_centroid_mem_barycentricSubdivision K hs)

open Classical in
theorem boundaryComplex_derivedNeighborhoodCell_space_of_not_mem_boundaryComplex
    [FiniteDimensional ℝ E] {n : ℕ} (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    {s : Finset E} (hs : s ∈ K.faces) (hsB : s ∉ (boundaryComplex (n + 1) K).faces) :
    (boundaryComplex (n + 1) (derivedNeighborhoodCell K s)).space =
      (upperLink (barycentricSubdivision K) {s.centroid ℝ id}).space := by
  have hc := singleton_centroid_mem_barycentricSubdivision K hs
  have hcB : {s.centroid ℝ id} ∉
      (boundaryComplex (n + 1) (barycentricSubdivision K)).faces := by
    intro h
    have hx : s.centroid ℝ id ∈
        (boundaryComplex (n + 1) (barycentricSubdivision K)).space :=
      (boundaryComplex (n + 1) (barycentricSubdivision K)).subset_space h
        (Finset.mem_singleton_self _)
    rw [boundaryComplex_space_of_isSubdivision K _ hK
      (barycentricSubdivision_isSubdivision K)] at hx
    exact notMem_space_of_notMem_faces (boundaryComplex_faces_subset (n + 1) K) hs hsB
      (centroid_mem_openSimplex_of_mem_faces K s hs) hx
  have hbase : IsPLSphere n
      (upperLink (barycentricSubdivision K) {s.centroid ℝ id}).space := by
    simpa only [Nat.sub_zero] using
      hK.barycentricSubdivision.isPLSphere_upperLink_of_not_mem_boundaryComplex
        (barycentricSubdivision K) hc hcB (k := 0) (Finset.card_singleton _) (Nat.zero_le n)
  let _ : Finite (upperLink (barycentricSubdivision K) {s.centroid ℝ id}).faces :=
    (upperLink_faces_finite _ _).to_subtype
  rw [derivedNeighborhoodCell_eq_dualCell K hs, dualCell]
  have hcone := isConeBase_upperLink (barycentricSubdivision K) hc
  exact hcone.boundaryComplex_space_of_isPLSphere hbase

open Classical in
theorem boundaryComplex_derivedNeighborhoodCell_eq_iUnion_graphDualCell
    [FiniteDimensional ℝ E] {n : ℕ} (K L : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    {s : Finset E} (hs : s ∈ K.faces) (hsB : s ∉ (boundaryComplex (n + 1) K).faces)
    (hL : ∀ r, r ∈ L.faces ↔ r ∈ K.faces ∧ r ≠ s) :
    (boundaryComplex (n + 1) (derivedNeighborhoodCell K s)).space =
      ⋃ v ∈ {v : E | {v} ∈ L.faces},
        (graphDualCell K L v).space ∩ (derivedNeighborhoodCell K s).space := by
  rw [boundaryComplex_derivedNeighborhoodCell_space_of_not_mem_boundaryComplex K hK hs hsB,
    ← derivedNeighborhoodCell_inter_derivedNeighborhood_eq_upperLink K L hs hL,
    ← iUnion_graphDualCell_space K L (fun r hr => ((hL r).mp hr).1),
    inter_iUnion]
  simp only [inter_iUnion, inter_comm]

open Classical in
theorem boundaryComplex_triangleCell_eq_iUnion_graphDualCell [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {s : Finset E} (hs : s ∈ K.faces) (hcard : s.card = 3)
    (hmax : ∀ r ∈ K.faces, r ⊆ s)
    (hL : ∀ r, r ∈ L.faces ↔ r ∈ K.faces ∧ r ≠ s) :
    (boundaryComplex 2 (derivedNeighborhoodCell K s)).space =
      ⋃ v ∈ s, (graphDualCell K L v).space ∩ (derivedNeighborhoodCell K s).space := by
  have hKsp : K.space = convexHull ℝ (s : Set E) := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨r, hr, hxr⟩ := K.mem_space_iff.mp hx
      exact convexHull_mono (Finset.coe_subset.mpr (hmax r hr)) hxr
    · exact K.convexHull_subset_space hs
  have hKball : IsPLBall 2 K.space := by
    rw [hKsp]
    exact isPLBall_convexHull_of_affineIndependent s (K.indep hs) hcard
  have hK := hKball.isCombinatorialManifoldWithBoundary
  have hsB : s ∉ (boundaryComplex 2 K).faces := by
    intro h
    have hc := ((hK.mem_boundaryComplex_faces_iff K).mp h).2.1
    omega
  have hvertices : {v : E | {v} ∈ L.faces} = (s : Set E) := by
    ext v
    constructor
    · intro hv
      exact hmax {v} ((hL {v}).mp hv).1 (Finset.mem_singleton_self _)
    · intro hv
      refine (hL {v}).mpr ⟨K.down_closed hs (Finset.singleton_subset_iff.mpr hv)
        (Finset.singleton_nonempty _), ?_⟩
      intro heq
      have hc := congrArg Finset.card heq
      rw [Finset.card_singleton, hcard] at hc
      omega
  simpa only [hvertices, Finset.mem_coe] using
    boundaryComplex_derivedNeighborhoodCell_eq_iUnion_graphDualCell K L hK hs hsB hL

end DifferentialGeometry.Topology.PiecewiseLinear

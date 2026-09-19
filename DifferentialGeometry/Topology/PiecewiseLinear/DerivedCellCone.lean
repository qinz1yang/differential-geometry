import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodCells
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryDerivedNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.ConePairExtension

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem derivedNeighborhoodCell_space_eq_coneSet (K : Geometry.SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) :
    (derivedNeighborhoodCell K s).space =
      coneSet (s.centroid ℝ id)
        (upperLink (barycentricSubdivision K) {s.centroid ℝ id}).space := by
  rw [derivedNeighborhoodCell_eq_dualCell K hs, dualCell, coneComplex_space_eq_coneSet,
    Finset.centroid_singleton]
  rfl

open Classical in
theorem isConeBase_centroid_upperLink (K : Geometry.SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) :
    IsConeBase (s.centroid ℝ id) (upperLink (barycentricSubdivision K) {s.centroid ℝ id}) := by
  have h := isConeBase_upperLink (barycentricSubdivision K)
    (singleton_centroid_mem_barycentricSubdivision K hs)
  rwa [Finset.centroid_singleton] at h

open Classical in
theorem IsCombinatorialManifold.isPLSphere_upperLink_centroid [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces] (hK : IsCombinatorialManifold 3 K)
    {s : Finset E} (hs : s ∈ K.faces) :
    IsPLSphere 2 (upperLink (PiecewiseLinear.barycentricSubdivision K) {s.centroid ℝ id}).space :=
  hK.barycentricSubdivision.isPLSphere_upperLink _
    (singleton_centroid_mem_barycentricSubdivision K hs) (k := 0) (Finset.card_singleton _)
    (Nat.zero_le 2)

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLSphere_upperLink_of_not_mem_boundaryComplex
    [FiniteDimensional ℝ E] {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) {s : Finset E}
    (hs : s ∈ K.faces) (hsB : s ∉ (boundaryComplex (n + 1) K).faces) {k : ℕ}
    (hcard : s.card = k + 1) (hk : k ≤ n) : IsPLSphere (n - k) (upperLink K s).space := by
  obtain ⟨f, hf⟩ := exists_isPLHomeomorphOn_upperLink K hs
  exact
    (hK.isPLSphere_geometricLink_of_not_mem_boundaryComplex K hs hsB hcard hk).of_isPLHomeomorphOn
      hf.symm

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLSphere_upperLink_centroid_of_not_mem_boundaryComplex
    [FiniteDimensional ℝ E] {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {s : Finset E} (hs : s ∈ K.faces)
    (hsB : s ∉ (boundaryComplex 3 K).faces) :
    IsPLSphere 2
      (upperLink (PiecewiseLinear.barycentricSubdivision K) {s.centroid ℝ id}).space := by
  let c := s.centroid ℝ id
  have hc : ({c} : Finset E) ∈ (PiecewiseLinear.barycentricSubdivision K).faces :=
    singleton_centroid_mem_barycentricSubdivision K hs
  have hcB : ({c} : Finset E) ∉
      (boundaryComplex 3 (PiecewiseLinear.barycentricSubdivision K)).faces := by
    intro hcB
    have hcspace : c ∈
        (boundaryComplex 3 (PiecewiseLinear.barycentricSubdivision K)).space :=
      (boundaryComplex 3 (PiecewiseLinear.barycentricSubdivision K)).subset_space hcB
        (Finset.mem_singleton_self c)
    rw [boundaryComplex_space_of_isSubdivision K _ hK
      (barycentricSubdivision_isSubdivision K)] at hcspace
    exact notMem_space_of_notMem_faces (boundaryComplex_faces_subset 3 K) hs hsB
      (centroid_mem_openSimplex_of_mem_faces K s hs) hcspace
  simpa only [c] using hK.barycentricSubdivision.isPLSphere_upperLink_of_not_mem_boundaryComplex
    (PiecewiseLinear.barycentricSubdivision K) hc hcB (k := 0) (Finset.card_singleton c)
      (Nat.zero_le 2)

open Classical in
theorem centroid_ne_centroid_of_ne (K : Geometry.SimplicialComplex ℝ E) {s t : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hne : s ≠ t) :
    s.centroid ℝ id ≠ t.centroid ℝ id := fun h =>
  hne (injOn_faces_of_mem_openSimplex K (centroid_mem_openSimplex_of_mem_faces K) hs ht h)

open Classical in
theorem derivedNeighborhoodCell_inter_eq_coneSet (K : Geometry.SimplicialComplex ℝ E)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hst : s ⊆ t ∨ t ⊆ s) :
    (derivedNeighborhoodCell K s).space ∩ (derivedNeighborhoodCell K t).space =
      coneSet (({s.centroid ℝ id, t.centroid ℝ id} : Finset E).centroid ℝ id)
        (upperLink (barycentricSubdivision K) {s.centroid ℝ id, t.centroid ℝ id}).space := by
  rw [derivedNeighborhoodCell_space_inter K hs ht hst, dualCell, coneComplex_space_eq_coneSet]

open Classical in
theorem IsCombinatorialManifold.isPLSphere_upperLink_pair_centroid [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces] (hK : IsCombinatorialManifold 3 K)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hne : s ≠ t)
    (hst : s ⊆ t ∨ t ⊆ s) :
    IsPLSphere 1
      (upperLink (PiecewiseLinear.barycentricSubdivision K)
        {s.centroid ℝ id, t.centroid ℝ id}).space :=
  hK.barycentricSubdivision.isPLSphere_upperLink _
    (pair_centroid_mem_barycentricSubdivision_of_subset_or_subset K hs ht hst) (k := 1)
    (Finset.card_pair (centroid_ne_centroid_of_ne K hs ht hne)) (by norm_num)

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLSphere_upperLink_pair_centroid_of_interior_face
    [FiniteDimensional ℝ E] {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {s t : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hsB : s ∉ (boundaryComplex 3 K).faces)
    (hne : s ≠ t) (hst : s ⊆ t ∨ t ⊆ s) :
    IsPLSphere 1
      (upperLink (PiecewiseLinear.barycentricSubdivision K)
        {s.centroid ℝ id, t.centroid ℝ id}).space := by
  have hp := pair_centroid_mem_barycentricSubdivision_of_subset_or_subset K hs ht hst
  have hcent := centroid_ne_centroid_of_ne K hs ht hne
  have hsB' : ({s.centroid ℝ id} : Finset E) ∉
      (boundaryComplex 3 (PiecewiseLinear.barycentricSubdivision K)).faces := by
    intro h
    have hspace : s.centroid ℝ id ∈
        (boundaryComplex 3 (PiecewiseLinear.barycentricSubdivision K)).space :=
      (boundaryComplex 3 (PiecewiseLinear.barycentricSubdivision K)).subset_space h
        (Finset.mem_singleton_self _)
    rw [boundaryComplex_space_of_isSubdivision K _ hK
      (barycentricSubdivision_isSubdivision K)] at hspace
    exact notMem_space_of_notMem_faces (boundaryComplex_faces_subset 3 K) hs hsB
      (centroid_mem_openSimplex_of_mem_faces K s hs) hspace
  have hpB : ({s.centroid ℝ id, t.centroid ℝ id} : Finset E) ∉
      (boundaryComplex 3 (PiecewiseLinear.barycentricSubdivision K)).faces := by
    intro h
    exact hsB' ((boundaryComplex 3 (PiecewiseLinear.barycentricSubdivision K)).down_closed h
      (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))
      (Finset.singleton_nonempty _))
  exact hK.barycentricSubdivision.isPLSphere_upperLink_of_not_mem_boundaryComplex
    (PiecewiseLinear.barycentricSubdivision K) hp hpB (k := 1) (Finset.card_pair hcent)
      (by norm_num)

open Classical in
theorem coneSet_pair_centroid_subset_upperLink (K : Geometry.SimplicialComplex ℝ E)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hne : s ≠ t)
    (hst : s ⊆ t ∨ t ⊆ s) :
    coneSet (({s.centroid ℝ id, t.centroid ℝ id} : Finset E).centroid ℝ id)
        (upperLink (barycentricSubdivision K) {s.centroid ℝ id, t.centroid ℝ id}).space ⊆
      (upperLink (barycentricSubdivision K) {s.centroid ℝ id}).space := by
  have hcent := centroid_ne_centroid_of_ne K hs ht hne
  have hpair := pair_centroid_mem_barycentricSubdivision_of_subset_or_subset K hs ht hst
  have hss : ({s.centroid ℝ id} : Finset E) ⊂ {s.centroid ℝ id, t.centroid ℝ id} := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _), fun h => hcent ?_⟩
    have hmem : t.centroid ℝ id ∈ ({s.centroid ℝ id} : Finset E) := by
      rw [h]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    exact (Finset.mem_singleton.mp hmem).symm
  have h := space_mono_of_faces_subset
    (dualCell_faces_subset_upperLink (barycentricSubdivision K) hpair hss)
  rwa [dualCell, coneComplex_space_eq_coneSet] at h

open Classical in
theorem coneSet_pair_centroid_subset_upperLink_right (K : Geometry.SimplicialComplex ℝ E)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hne : s ≠ t)
    (hst : s ⊆ t ∨ t ⊆ s) :
    coneSet (({s.centroid ℝ id, t.centroid ℝ id} : Finset E).centroid ℝ id)
        (upperLink (barycentricSubdivision K) {s.centroid ℝ id, t.centroid ℝ id}).space ⊆
      (upperLink (barycentricSubdivision K) {t.centroid ℝ id}).space := by
  rw [Finset.pair_comm]
  exact coneSet_pair_centroid_subset_upperLink K ht hs hne.symm hst.symm

end DifferentialGeometry.Topology.PiecewiseLinear

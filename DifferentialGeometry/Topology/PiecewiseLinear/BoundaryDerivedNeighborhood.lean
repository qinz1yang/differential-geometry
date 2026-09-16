import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodAttachments
import DifferentialGeometry.Topology.PiecewiseLinear.DiskUnion

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
noncomputable def derivedNeighborhoodCellBase (K : Geometry.SimplicialComplex ℝ E) (s : Finset E) :
    Geometry.SimplicialComplex ℝ E :=
  upperLink (PiecewiseLinear.barycentricSubdivision K) {s.centroid ℝ id}

open Classical in
theorem dualCell_faces_subset_upperLink (K : Geometry.SimplicialComplex ℝ E)
    {s t : Finset E} (ht : t ∈ K.faces) (hst : s ⊂ t) :
    (dualCell K t ht).faces ⊆ (upperLink K s).faces := by
  classical
  intro u hu
  obtain ⟨d, hd, hne, hsub, rfl⟩ := (mem_dualCell_faces_iff K ht).mp hu
  exact ⟨d, hd, hne, fun e he => hst.trans_le (hsub e he), rfl⟩

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLBall_upperLink_of_mem_boundaryComplex
    [FiniteDimensional ℝ E] {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) {s : Finset E}
    (hs : s ∈ (boundaryComplex (n + 1) K).faces) {k : ℕ} (hcard : s.card = k + 1) :
    IsPLBall (n - k) (upperLink K s).space := by
  classical
  obtain ⟨hsK, _, hball⟩ := (hK.mem_boundaryComplex_faces_iff K).mp hs
  obtain ⟨f, hf⟩ := exists_isPLHomeomorphOn_upperLink K hsK
  rw [hcard, Nat.add_sub_add_right] at hball
  exact hball.of_isPLHomeomorphOn hf.symm

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhoodCellBase
    [FiniteDimensional ℝ E] {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) {s : Finset E}
    (hs : s ∈ (boundaryComplex (n + 1) K).faces) :
    IsPLBall n (derivedNeighborhoodCellBase K s).space := by
  classical
  have hsK := boundaryComplex_faces_subset (n + 1) K hs
  have hv := singleton_centroid_mem_barycentricSubdivision K hsK
  have hx : s.centroid ℝ id ∈ (boundaryComplex (n + 1) (PiecewiseLinear.barycentricSubdivision K)).space := by
    rw [boundaryComplex_space_of_isSubdivision K _ hK (barycentricSubdivision_isSubdivision K)]
    exact (boundaryComplex (n + 1) K).convexHull_subset_space hs
      (s.centroid_mem_convexHull (K.nonempty_of_mem_faces hsK))
  have hvB : {s.centroid ℝ id} ∈ (boundaryComplex (n + 1) (PiecewiseLinear.barycentricSubdivision K)).faces :=
    mem_faces_of_mem_openSimplex_of_mem_space (boundaryComplex_faces_subset (n + 1) _)
      hv (by simpa only [Finset.centroid_singleton, id_eq] using
        centroid_mem_openSimplex (Finset.singleton_nonempty (s.centroid ℝ id))) hx
  exact hK.barycentricSubdivision.isPLBall_upperLink_of_mem_boundaryComplex _ hvB
    (k := 0) (Finset.card_singleton _)

theorem derivedNeighborhoodCell_inter_subset_base (K : Geometry.SimplicialComplex ℝ E)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hst : s ≠ t) :
    (derivedNeighborhoodCell K s).space ∩ (derivedNeighborhoodCell K t).space ⊆
      (derivedNeighborhoodCellBase K s).space := by
  classical
  intro x hx
  have hcomp := subset_or_subset_of_nonempty_derivedNeighborhoodCell_inter K hs ht ⟨x, hx⟩
  rw [derivedNeighborhoodCell_space_inter K hs ht hcomp] at hx
  have hcent : s.centroid ℝ id ≠ t.centroid ℝ id := fun h => hst
    (injOn_faces_of_mem_openSimplex K (centroid_mem_openSimplex_of_mem_faces K) hs ht h)
  apply space_mono_of_faces_subset (dualCell_faces_subset_upperLink _
    (pair_centroid_mem_barycentricSubdivision K hs ht hcomp) ?_) hx
  refine Finset.ssubset_iff_subset_ne.mpr ⟨by simp, ?_⟩
  intro heq
  have hmem : t.centroid ℝ id ∈ ({s.centroid ℝ id} : Finset E) :=
    heq.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  exact hcent (Finset.mem_singleton.mp hmem).symm

theorem IsCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhoodCell_inter_inter
    [FiniteDimensional ℝ E] {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {s t u : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hu : u ∈ K.faces)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (hcst : s ⊆ t ∨ t ⊆ s) (hcsu : s ⊆ u ∨ u ⊆ s) (hctu : t ⊆ u ∨ u ⊆ t) :
    IsPLBall 1 ((derivedNeighborhoodCell K s).space ∩
      (derivedNeighborhoodCell K t).space ∩ (derivedNeighborhoodCell K u).space) := by
  classical
  have hd : IsFlag K {s, t, u} := by
    refine ⟨?_, ?_⟩
    · intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;> assumption
    · intro v hv w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv hw
      rcases hv with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
        first | exact Or.inl subset_rfl | exact hcst | exact hcst.symm |
          exact hcsu | exact hcsu.symm | exact hctu | exact hctu.symm
  have hcard : ({s, t, u} : Finset (Finset E)).card = 2 + 1 := by simp [hst, hsu, htu]
  have h := hK.isPLBall_iInter_derivedNeighborhoodCell hd hcard (by decide : 2 ≤ 2)
  simpa [inter_assoc] using h

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhoodCell_inter_union
    [FiniteDimensional ℝ E] {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {s t : Finset E}
    (hs : s ∈ (boundaryComplex 3 K).faces) (ht : t ∈ K.faces) (hst : s ≠ t)
    (hcst : s ⊆ t ∨ t ⊆ s) (d : Finset (Finset E)) (hd : ∀ u ∈ d, u ∈ K.faces)
    (hne : ∀ u ∈ d, u ≠ s ∧ u ≠ t)
    (hcomp : ∀ u ∈ d, (s ⊆ u ∨ u ⊆ s) ∧ (t ⊆ u ∨ u ⊆ t))
    (hincomp : ∀ u ∈ d, ∀ v ∈ d, u ≠ v → ¬u ⊆ v ∧ ¬v ⊆ u) :
    IsPLBall 2 ((derivedNeighborhoodCell K s).space ∩
      ((derivedNeighborhoodCell K t).space ∪ ⋃ u ∈ d, (derivedNeighborhoodCell K u).space)) := by
  classical
  have hsK := boundaryComplex_faces_subset 3 K hs
  have hbase := hK.isPLBall_derivedNeighborhoodCellBase hs
  have hcenter := hK.isPLBall_derivedNeighborhoodCell_inter hsK ht hst hcst
  let A := fun u => (derivedNeighborhoodCell K s).space ∩ (derivedNeighborhoodCell K u).space
  have hA (u : Finset E) (hu : u ∈ d) : IsPLBall 2 (A u) :=
    hK.isPLBall_derivedNeighborhoodCell_inter hsK (hd u hu) (hne u hu).1.symm (hcomp u hu).1
  have hAB (u : Finset E) (hu : u ∈ d) : A u ⊆ (derivedNeighborhoodCellBase K s).space :=
    derivedNeighborhoodCell_inter_subset_base K hsK (hd u hu) (hne u hu).1.symm
  have hI (u : Finset E) (hu : u ∈ d) :
      IsPLBall 1 (((derivedNeighborhoodCell K s).space ∩ (derivedNeighborhoodCell K t).space) ∩ A u) := by
    have heq : ((derivedNeighborhoodCell K s).space ∩ (derivedNeighborhoodCell K t).space) ∩ A u =
        (derivedNeighborhoodCell K s).space ∩ (derivedNeighborhoodCell K t).space ∩
          (derivedNeighborhoodCell K u).space := by
      ext x
      simp only [A, mem_inter_iff]
      tauto
    rw [heq]
    exact hK.isPLBall_derivedNeighborhoodCell_inter_inter hsK ht (hd u hu) hst
      (hne u hu).1.symm (hne u hu).2.symm hcst (hcomp u hu).1 (hcomp u hu).2
  have hdis (u : Finset E) (hu : u ∈ d) (v : Finset E) (hv : v ∈ d) (hneuv : u ≠ v) :
      Disjoint (A u) (A v) :=
    (disjoint_derivedNeighborhoodCell_space K (hd u hu) (hd v hv)
      (hincomp u hu v hv hneuv).1 (hincomp u hu v hv hneuv).2).mono
        inter_subset_right inter_subset_right
  have h := isPLBall_union_iUnion_of_pairwiseDisjoint_in_ball hbase hcenter
    (derivedNeighborhoodCell_inter_subset_base K hsK ht hst) d A hA hAB hI hdis
  simpa only [inter_union_distrib_left, inter_iUnion] using h

open Classical in
theorem IsCombinatorialManifoldWithBoundary.derivedNeighborhoodCell_inter_subset_boundaryComplex
    [FiniteDimensional ℝ E] {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 2) K) {s t : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hne : s ≠ t) :
    (derivedNeighborhoodCell K s).space ∩ (derivedNeighborhoodCell K t).space ⊆
      (boundaryComplex (n + 2) (derivedNeighborhoodCell K s)).space := by
  classical
  let _ : Finite (derivedNeighborhoodCell K s).faces :=
    (derivedNeighborhoodCell_faces_finite K s).to_subtype
  let _ : Finite (derivedNeighborhoodCell K t).faces :=
    (derivedNeighborhoodCell_faces_finite K t).to_subtype
  by_cases hnon : ((derivedNeighborhoodCell K s).space ∩
      (derivedNeighborhoodCell K t).space).Nonempty
  · exact inter_subset_boundaryComplex_of_isPLBall (PiecewiseLinear.secondDerived K)
      (derivedNeighborhoodCell K s) (derivedNeighborhoodCell K t) hK.secondDerived
      (hK.isPLBall_derivedNeighborhoodCell hs) (hK.isPLBall_derivedNeighborhoodCell ht)
      (derivedNeighborhoodCell_faces_subset K s) (derivedNeighborhoodCell_faces_subset K t)
      (hK.isPLBall_derivedNeighborhoodCell_inter_of_nonempty hs ht hne hnon)
  · exact fun x hx => (hnon ⟨x, hx⟩).elim

end DifferentialGeometry.Topology.PiecewiseLinear

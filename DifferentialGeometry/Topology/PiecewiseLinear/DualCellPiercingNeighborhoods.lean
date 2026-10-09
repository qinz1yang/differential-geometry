/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.LocallyFiniteSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.CommonCircleNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.DualCellPiercing

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem IsCombinatorialManifold.exists_graphDualCell_piercing_with_nested_common_neighborhoods
    [FiniteDimensional ℝ E] (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 3 K) (hL : L.faces ⊆ K.faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {v w : E} (hvw : v ≠ w)
    (he : {v, w} ∈ L.faces) {U : Set E} (hU : IsOpen U)
    (hDU : (splittingDisk K {v, w} (hL he)).space ⊆ U) :
    ∃ (J C : Set E) (f : E → E) (A B : Set E),
      IsPLSphere 1 J ∧
      J ⊆ (splittingDisk K {v, w} (hL he)).space ∧
      Disjoint J (boundaryComplex 2 (splittingDisk K {v, w} (hL he))).space ∧
      IsPLHomeomorphOn f (graphDualCell K L w).space C ∧
      C ⊆ (graphDualCell K L w).space ∧ EqOn f id J ∧ IsPLBall 3 C ∧
      (graphDualCell K L v).space ∩ C = J ∧
      A ⊆ U ∧
      IsNestedCommonAnnularDerivedNeighborhood K A B J
        (boundaryComplex 3 (graphDualCell K L v)).space
        (f '' (boundaryComplex 3 (graphDualCell K L w)).space) := by
  let Cv := graphDualCell K L v
  let Cw := graphDualCell K L w
  let D := splittingDisk K {v, w} (hL he)
  let _ : Finite Cv.faces := (graphDualCell_faces_finite K L v).to_subtype
  let _ : Finite Cw.faces := (graphDualCell_faces_finite K L w).to_subtype
  let _ : Finite (boundaryComplex 3 Cv).faces :=
    (boundaryComplex_faces_finite 3 Cv).to_subtype
  let _ : Finite (boundaryComplex 3 Cw).faces :=
    (boundaryComplex_faces_finite 3 Cw).to_subtype
  have hv : {v} ∈ L.faces :=
    L.down_closed he (by simp) (Finset.singleton_nonempty v)
  have hw : {w} ∈ L.faces :=
    L.down_closed he (by simp) (Finset.singleton_nonempty w)
  have hCv : IsPLBall 3 Cv.space := hK.isPLBall_graphDualCell K L hL hcard hv
  have hCw : IsPLBall 3 Cw.space := hK.isPLBall_graphDualCell K L hL hcard hw
  obtain ⟨J, C, f, hJ, hJD, hJdis, hf, hCsub, hfix, hC, hinter⟩ :=
    hK.exists_graphDualCell_piercing K L hL hcard hvw he
  have hDbdv : D.space ⊆ (boundaryComplex 3 Cv).space := by
    have he' : {w, v} ∈ L.faces := by simpa [Finset.pair_comm] using he
    have h := hK.splittingDisk_subset_boundary_graphDualCell K L hL hcard hvw.symm he'
    simpa [Cv, D, Finset.pair_comm] using h
  have hDbdw : D.space ⊆ (boundaryComplex 3 Cw).space :=
    hK.splittingDisk_subset_boundary_graphDualCell K L hL hcard hvw he
  have hJbdv : J ⊆ (boundaryComplex 3 Cv).space := hJD.trans hDbdv
  have hJbdw : J ⊆ (boundaryComplex 3 Cw).space := hJD.trans hDbdw
  have hSv : IsPLSphere 2 (boundaryComplex 3 Cv).space :=
    isPLSphere_boundaryComplex_space_of_isPLBall Cv hCv
  have hfbd : IsPLHomeomorphOn f (boundaryComplex 3 Cw).space
      (f '' (boundaryComplex 3 Cw).space) :=
    hf.restrict (isPolyhedron_space (boundaryComplex 3 Cw))
      (boundaryComplex_space_subset 3 Cw)
  have hSw : IsPLSphere 2 (f '' (boundaryComplex 3 Cw).space) :=
    (isPLSphere_boundaryComplex_space_of_isPLBall Cw hCw).of_isPLHomeomorphOn hfbd
  have hJbdw' : J ⊆ f '' (boundaryComplex 3 Cw).space := by
    intro x hx
    exact ⟨x, hJbdw hx, by simpa using hfix hx⟩
  have hSvK : (boundaryComplex 3 Cv).space ⊆ K.space :=
    (boundaryComplex_space_subset 3 Cv).trans
      ((graphDualCell_space_subset K L v).trans (derivedNeighborhood_space_subset K L))
  have hSwK : f '' (boundaryComplex 3 Cw).space ⊆ K.space :=
    (image_mono (boundaryComplex_space_subset 3 Cw)).trans
      (hf.image_eq.subset.trans (hCsub.trans
        ((graphDualCell_space_subset K L w).trans (derivedNeighborhood_space_subset K L))))
  obtain ⟨A, B, hAU, hAB⟩ :=
    exists_nested_common_annular_derivedNeighborhoods K hJ hSv hSw
      (hJbdv.trans hSvK) hSvK hSwK hJbdv hJbdw' hU (hJD.trans hDU)
  exact ⟨J, C, f, A, B, hJ, hJD, hJdis, hf, hCsub, hfix, hC, hinter,
    hAU, hAB⟩

open Classical in
theorem IsCombinatorialManifold.exists_piercings_with_nested_common_neighborhoods
    {ι : Type*}
    [FiniteDimensional ℝ E] (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 3 K) (hL : L.faces ⊆ K.faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {v : E} (w : ι → E)
    (hwinj : Function.Injective w) (hvw : ∀ i, v ≠ w i)
    (hneighbors : ∀ u, u ≠ v → ({v, u} ∈ L.faces ↔ u ∈ Set.range w))
    {U : Set E} (hU : IsOpen U)
    (hDU : ∀ i, (splittingDisk K {v, w i}
      (hL ((hneighbors (w i) (hvw i).symm).mpr ⟨i, rfl⟩))).space ⊆ U) :
    ∃ (J C : ι → Set E) (f : ι → E → E) (A B : ι → Set E),
      (∀ i,
        IsPLSphere 1 (J i) ∧
        J i ⊆ (splittingDisk K {v, w i}
          (hL ((hneighbors (w i) (hvw i).symm).mpr ⟨i, rfl⟩))).space ∧
        Disjoint (J i) (boundaryComplex 2 (splittingDisk K {v, w i}
          (hL ((hneighbors (w i) (hvw i).symm).mpr ⟨i, rfl⟩)))).space ∧
        IsPLHomeomorphOn (f i) (graphDualCell K L (w i)).space (C i) ∧
        C i ⊆ (graphDualCell K L (w i)).space ∧ EqOn (f i) id (J i) ∧
        IsPLBall 3 (C i) ∧ (graphDualCell K L v).space ∩ C i = J i ∧
        A i ⊆ U ∧
        IsNestedCommonAnnularDerivedNeighborhood K (A i) (B i) (J i)
          (boundaryComplex 3 (graphDualCell K L v)).space
          (f i '' (boundaryComplex 3 (graphDualCell K L (w i))).space)) ∧
      Pairwise fun i j => Disjoint (J i) (J j) := by
  have hedge (i : ι) : {v, w i} ∈ L.faces :=
    (hneighbors (w i) (hvw i).symm).mpr ⟨i, rfl⟩
  have hpierce (i : ι) :=
    hK.exists_graphDualCell_piercing_with_nested_common_neighborhoods K L hL hcard
      (hvw i) (hedge i) hU (hDU i)
  choose J C f A B hdata using hpierce
  refine ⟨J, C, f, A, B, hdata, ?_⟩
  intro i j hij
  have hedgeNe : ({v, w i} : Finset E) ≠ {v, w j} := by
    intro heq
    have hmem : w i ∈ ({v, w j} : Finset E) := by
      rw [← heq]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self (w i))
    have hwij : w i = w j := by
      simpa [(hvw i).symm] using hmem
    exact hij (hwinj hwij)
  have hdis := disjoint_splittingDisk_space K (hL (hedge i)) (hL (hedge j))
    hedgeNe (by rw [Finset.card_pair (hvw i), Finset.card_pair (hvw j)])
  exact hdis.mono (hdata i).2.1 (hdata j).2.1

open Classical in
theorem IsCombinatorialManifold.exists_trivalent_piercings_with_nested_common_neighborhoods
    [FiniteDimensional ℝ E] (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 3 K) (hL : L.faces ⊆ K.faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {v : E} (w : Fin 3 → E)
    (hwinj : Function.Injective w) (hvw : ∀ i, v ≠ w i)
    (hneighbors : ∀ u, u ≠ v → ({v, u} ∈ L.faces ↔ u ∈ Set.range w))
    {U : Set E} (hU : IsOpen U)
    (hDU : ∀ i, (splittingDisk K {v, w i}
      (hL ((hneighbors (w i) (hvw i).symm).mpr ⟨i, rfl⟩))).space ⊆ U) :
    ∃ (J C : Fin 3 → Set E) (f : Fin 3 → E → E) (A B : Fin 3 → Set E),
      (∀ i,
        IsPLSphere 1 (J i) ∧
        J i ⊆ (splittingDisk K {v, w i}
          (hL ((hneighbors (w i) (hvw i).symm).mpr ⟨i, rfl⟩))).space ∧
        Disjoint (J i) (boundaryComplex 2 (splittingDisk K {v, w i}
          (hL ((hneighbors (w i) (hvw i).symm).mpr ⟨i, rfl⟩)))).space ∧
        IsPLHomeomorphOn (f i) (graphDualCell K L (w i)).space (C i) ∧
        C i ⊆ (graphDualCell K L (w i)).space ∧ EqOn (f i) id (J i) ∧
        IsPLBall 3 (C i) ∧ (graphDualCell K L v).space ∩ C i = J i ∧
        A i ⊆ U ∧
        IsNestedCommonAnnularDerivedNeighborhood K (A i) (B i) (J i)
          (boundaryComplex 3 (graphDualCell K L v)).space
          (f i '' (boundaryComplex 3 (graphDualCell K L (w i))).space)) ∧
      Pairwise fun i j => Disjoint (J i) (J j) :=
  hK.exists_piercings_with_nested_common_neighborhoods K L hL hcard w
    hwinj hvw hneighbors hU hDU

open Classical in
theorem IsCombinatorialManifold.exists_piercings_with_pairwise_disjoint_nested_common_neighborhoods
    {ι : Type*} [Finite ι]
    [FiniteDimensional ℝ E] (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 3 K) (hL : L.faces ⊆ K.faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {v : E} (w : ι → E)
    (hwinj : Function.Injective w) (hvw : ∀ i, v ≠ w i)
    (hneighbors : ∀ u, u ≠ v → ({v, u} ∈ L.faces ↔ u ∈ Set.range w))
    {U : Set E} (hU : IsOpen U)
    (hDU : ∀ i, (splittingDisk K {v, w i}
      (hL ((hneighbors (w i) (hvw i).symm).mpr ⟨i, rfl⟩))).space ⊆ U) :
    ∃ (J C : ι → Set E) (f : ι → E → E) (A B : ι → Set E),
      (∀ i,
        IsPLSphere 1 (J i) ∧
        J i ⊆ (splittingDisk K {v, w i}
          (hL ((hneighbors (w i) (hvw i).symm).mpr ⟨i, rfl⟩))).space ∧
        Disjoint (J i) (boundaryComplex 2 (splittingDisk K {v, w i}
          (hL ((hneighbors (w i) (hvw i).symm).mpr ⟨i, rfl⟩)))).space ∧
        IsPLHomeomorphOn (f i) (graphDualCell K L (w i)).space (C i) ∧
        C i ⊆ (graphDualCell K L (w i)).space ∧ EqOn (f i) id (J i) ∧
        IsPLBall 3 (C i) ∧ (graphDualCell K L v).space ∩ C i = J i ∧
        A i ⊆ U ∧
        IsNestedCommonAnnularDerivedNeighborhood K (A i) (B i) (J i)
          (boundaryComplex 3 (graphDualCell K L v)).space
          (f i '' (boundaryComplex 3 (graphDualCell K L (w i))).space)) ∧
      Pairwise (fun i j => Disjoint (J i) (J j)) ∧
      Pairwise (fun i j => Disjoint (A i) (A j)) ∧
      Pairwise fun i j => Disjoint (B i) (B j) := by
  have hedge (i : ι) : {v, w i} ∈ L.faces :=
    (hneighbors (w i) (hvw i).symm).mpr ⟨i, rfl⟩
  let D : ι → Set E := fun i => (splittingDisk K {v, w i} (hL (hedge i))).space
  have hDcompact (i : ι) : IsCompact (D i) := by
    exact (hK.isPLBall_splittingDisk K (hL (hedge i))
      (Finset.card_pair (hvw i)) (by omega)).isPolyhedron.isCompact
  have hDdis : Pairwise fun i j => Disjoint (D i) (D j) := by
    intro i j hij
    have hedgeNe : ({v, w i} : Finset E) ≠ {v, w j} := by
      intro heq
      have hmem : w i ∈ ({v, w j} : Finset E) := by
        rw [← heq]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self (w i))
      have hwij : w i = w j := by
        simpa [(hvw i).symm] using hmem
      exact hij (hwinj hwij)
    exact disjoint_splittingDisk_space K (hL (hedge i)) (hL (hedge j)) hedgeNe
      (by rw [Finset.card_pair (hvw i), Finset.card_pair (hvw j)])
  obtain ⟨V, hVopen, hDV, hVU, -, hVdis⟩ :=
    DifferentialGeometry.Topology.exists_locallyFinite_pairwise_disjoint_open_supersets
      D (fun i => (hDcompact i).isClosed) (locallyFinite_of_finite D) hDdis hU hDU
  have hV (i : ι) : IsOpen (V i) ∧ D i ⊆ V i ∧ V i ⊆ U :=
    ⟨hVopen i, hDV i, hVU i⟩
  have hpierce (i : ι) :=
    hK.exists_graphDualCell_piercing_with_nested_common_neighborhoods K L hL hcard
      (hvw i) (hedge i) (hV i).1 (hV i).2.1
  choose J C f A B hJ hJD hJbd hf hCsub hfix hCball hinter hAV hAB using hpierce
  refine ⟨J, C, f, A, B, fun i => ⟨hJ i, hJD i, hJbd i, hf i, hCsub i,
    hfix i, hCball i, hinter i, (hAV i).trans (hV i).2.2, hAB i⟩, ?_, ?_, ?_⟩
  · intro i j hij
    exact (hDdis hij).mono (hJD i) (hJD j)
  · intro i j hij
    exact (hVdis hij).mono (hAV i) (hAV j)
  · intro i j hij
    exact (hVdis hij).mono ((hAB i).inner_subset_outer.trans (hAV i))
      ((hAB j).inner_subset_outer.trans (hAV j))

end DifferentialGeometry.Topology.PiecewiseLinear

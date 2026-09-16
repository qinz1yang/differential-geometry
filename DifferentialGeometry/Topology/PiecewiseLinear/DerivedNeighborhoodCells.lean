import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.DualCells
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexComplement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
noncomputable def derivedNeighborhoodCell (K : Geometry.SimplicialComplex ℝ E) (s : Finset E) :
    Geometry.SimplicialComplex ℝ E :=
  starComplex (secondDerived K) (s.centroid ℝ id)

open Classical in
theorem mem_derivedNeighborhood_faces_iff_of_flag
    {K L : Geometry.SimplicialComplex ℝ E} {d : Finset (Finset E)}
    (hd : IsFlag (barycentricSubdivision K) d) (hne : d.Nonempty) :
    (d.image fun s => s.centroid ℝ id) ∈ (derivedNeighborhood K L).faces ↔
      ∀ e ∈ d, ∃ s ∈ L.faces, s.centroid ℝ id ∈ e := by
  constructor
  · intro hu
    obtain ⟨d', hd', _, hsub, himage⟩ := (mem_derivedNeighborhood_faces_iff K L).mp hu
    exact hd.eq_of_image_centroid_eq hd' himage ▸ hsub
  · intro hsub
    exact (mem_derivedNeighborhood_faces_iff K L).mpr ⟨d, hd, hne, hsub, rfl⟩

open Classical in
theorem derivedNeighborhoodCell_eq_dualCell (K : Geometry.SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) :
    derivedNeighborhoodCell K s = dualCell (barycentricSubdivision K) {s.centroid ℝ id}
      (singleton_centroid_mem_barycentricSubdivision K hs) :=
  starComplex_barycentricSubdivision_eq_dualCell _ _

open Classical in
theorem mem_derivedNeighborhoodCell_faces_iff_of_flag
    {K : Geometry.SimplicialComplex ℝ E} {s : Finset E} (hs : s ∈ K.faces)
    {d : Finset (Finset E)} (hd : IsFlag (barycentricSubdivision K) d) (hne : d.Nonempty) :
    (d.image fun e => e.centroid ℝ id) ∈ (derivedNeighborhoodCell K s).faces ↔
      ∀ e ∈ d, s.centroid ℝ id ∈ e := by
  rw [derivedNeighborhoodCell_eq_dualCell K hs, mem_dualCell_faces_iff_of_flag _ hd hne]
  simp only [Finset.singleton_subset_iff]

open Classical in
theorem derivedNeighborhoodCell_faces_subset (K : Geometry.SimplicialComplex ℝ E)
    (s : Finset E) : (derivedNeighborhoodCell K s).faces ⊆ (secondDerived K).faces :=
  starComplex_faces_subset _ _

theorem derivedNeighborhoodCell_faces_finite (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (s : Finset E) : (derivedNeighborhoodCell K s).faces.Finite := by
  classical
  exact (Set.toFinite (secondDerived K).faces).subset
    (derivedNeighborhoodCell_faces_subset K s)

open Classical in
theorem derivedNeighborhoodCell_eq_subcomplexGeneratedBy (K : Geometry.SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) :
    derivedNeighborhoodCell K s = subcomplexGeneratedBy
      (derivedNeighborhood K (simplexComplex s (K.indep hs)))
      (derivedNeighborhood K (simplexBoundary s (K.indep hs))).facesᶜ := by
  classical
  ext u
  constructor
  · intro hu
    obtain ⟨d, hd, hne, rfl⟩ := derivedNeighborhoodCell_faces_subset K s hu
    have hmem := (mem_derivedNeighborhoodCell_faces_iff_of_flag hs hd hne).mp hu
    have hb : {s.centroid ℝ id} ∈ (barycentricSubdivision K).faces :=
      singleton_centroid_mem_barycentricSubdivision K hs
    have hd' := hd.insert_of_subset hb (fun e he => Finset.singleton_subset_iff.mpr (hmem e he))
    refine ⟨(insert {s.centroid ℝ id} d).image (fun e => e.centroid ℝ id), ⟨?_, ?_⟩,
      Finset.image_subset_image (Finset.subset_insert _ _), hne.image _⟩
    · apply (mem_derivedNeighborhood_faces_iff_of_flag hd' (Finset.insert_nonempty _ _)).mpr
      intro e he
      refine ⟨s, ⟨K.nonempty_of_mem_faces hs, Finset.Subset.rfl⟩, ?_⟩
      rcases Finset.mem_insert.mp he with rfl | he
      · exact Finset.mem_singleton_self _
      · exact hmem e he
    · intro hbd
      obtain ⟨t, ht, hts⟩ :=
        (mem_derivedNeighborhood_faces_iff_of_flag hd' (Finset.insert_nonempty _ _)).mp hbd
          {s.centroid ℝ id} (Finset.mem_insert_self _ _)
      have heq : t = s := injOn_faces_of_mem_openSimplex K
        (centroid_mem_openSimplex_of_mem_faces K)
        (K.down_closed hs ht.1 ht.2.1) hs (Finset.mem_singleton.mp hts)
      exact ht.2.2 heq
  · rintro ⟨u, ⟨hu, hubd⟩, htu, ht⟩
    obtain ⟨d, hd, hne, rfl⟩ := derivedNeighborhood_faces_subset K _ hu
    have hmem := (mem_derivedNeighborhood_faces_iff_of_flag hd hne).mp hu
    have hnot : ¬∀ e ∈ d, ∃ t ∈ (simplexBoundary s (K.indep hs)).faces,
        t.centroid ℝ id ∈ e := fun h => hubd
          ((mem_derivedNeighborhood_faces_iff_of_flag hd hne).mpr h)
    push Not at hnot
    obtain ⟨e₀, he₀, hbad⟩ := hnot
    have hfull : ∀ t ∈ (simplexComplex s (K.indep hs)).faces,
        t.centroid ℝ id ∈ e₀ → t = s := by
      intro t ht hte
      by_contra hts
      exact hbad t ⟨ht.2, ht.1, hts⟩ hte
    obtain ⟨t, ht', hte⟩ := hmem e₀ he₀
    have hse₀ : s.centroid ℝ id ∈ e₀ := hfull t ht' hte ▸ hte
    have hu' : (d.image fun e => e.centroid ℝ id) ∈ (derivedNeighborhoodCell K s).faces := by
      apply (mem_derivedNeighborhoodCell_faces_iff_of_flag hs hd hne).mpr
      intro e he
      rcases hd.subset_or_subset he₀ he with h | h
      · exact h hse₀
      · obtain ⟨t, ht', hte⟩ := hmem e he
        exact hfull t ht' (h hte) ▸ hte
    exact (derivedNeighborhoodCell K s).down_closed hu' htu ht

open Classical in
theorem derivedNeighborhoodCell_space [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {s : Finset E} (hs : s ∈ K.faces) :
    (derivedNeighborhoodCell K s).space =
      closure ((derivedNeighborhood K (simplexComplex s (K.indep hs))).space \
        (derivedNeighborhood K (simplexBoundary s (K.indep hs))).space) := by
  classical
  let _ : Finite (derivedNeighborhood K (simplexComplex s (K.indep hs))).faces :=
    (derivedNeighborhood_faces_finite K _).to_subtype
  rw [closure_space_sdiff_space_eq_subcomplexGeneratedBy (secondDerived K) _ _
    (derivedNeighborhood_faces_subset K _) (derivedNeighborhood_faces_subset K _),
    ← derivedNeighborhoodCell_eq_subcomplexGeneratedBy K hs]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLSphere_or_isPLBall_upperLink
    [FiniteDimensional ℝ E] {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    {s : Finset E} (hs : s ∈ K.faces) {k : ℕ} (hcard : s.card = k + 1) (hk : k ≤ n) :
    IsPLSphere (n - k) (upperLink K s).space ∨ IsPLBall (n - k) (upperLink K s).space := by
  classical
  obtain ⟨f, hf⟩ := exists_isPLHomeomorphOn_upperLink K hs
  exact (hK.isPLSphere_or_isPLBall_geometricLink K hs hcard hk).imp
    (fun h => h.of_isPLHomeomorphOn hf.symm) (fun h => h.of_isPLHomeomorphOn hf.symm)

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLBall_dualCell
    [FiniteDimensional ℝ E] {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    {s : Finset E} (hs : s ∈ K.faces) {k : ℕ} (hcard : s.card = k + 1) (hk : k ≤ n) :
    IsPLBall (n - k + 1) (dualCell K s hs).space := by
  classical
  let _ : Finite (upperLink K s).faces := (upperLink_faces_finite K s).to_subtype
  rcases hK.isPLSphere_or_isPLBall_upperLink K hs hcard hk with h | h
  · exact (isConeBase_upperLink K hs).isPLBall_of_isPLSphere h
  · exact (isConeBase_upperLink K hs).isPLBall_of_isPLBall h

theorem IsCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhoodCell
    [FiniteDimensional ℝ E] {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) {s : Finset E} (hs : s ∈ K.faces) :
    IsPLBall (n + 1) (derivedNeighborhoodCell K s).space := by
  classical
  rw [derivedNeighborhoodCell_eq_dualCell K hs]
  exact hK.barycentricSubdivision.isPLBall_dualCell _ _
    (k := 0) (Finset.card_singleton _) (Nat.zero_le n)

open Classical in
theorem dualCell_space_inter_eq_dualCell (K : Geometry.SimplicialComplex ℝ E) {s t : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hst : s ∪ t ∈ K.faces) :
    (dualCell K s hs).space ∩ (dualCell K t ht).space = (dualCell K (s ∪ t) hst).space := by
  classical
  have hfaces := dualCell_faces_inter K hs ht hst
  apply Subset.antisymm
  · rintro x ⟨hxs, hxt⟩
    obtain ⟨u, hu, hxu⟩ := exists_face_mem_openSimplex (dualCell K s hs) hxs
    have hut := mem_faces_of_mem_openSimplex_of_mem_space (dualCell_faces_subset K ht)
      (dualCell_faces_subset K hs hu) hxu hxt
    have hust : u ∈ (dualCell K (s ∪ t) hst).faces := hfaces ▸ ⟨hu, hut⟩
    exact (dualCell K (s ∪ t) hst).convexHull_subset_space hust
      (openSimplex_subset_convexHull _ hxu)
  · intro x hx
    obtain ⟨u, hu, hxu⟩ := (dualCell K (s ∪ t) hst).mem_space_iff.mp hx
    have hust : u ∈ (dualCell K s hs).faces ∩ (dualCell K t ht).faces := hfaces.symm ▸ hu
    exact ⟨(dualCell K s hs).convexHull_subset_space hust.1 hxu,
      (dualCell K t ht).convexHull_subset_space hust.2 hxu⟩

theorem subset_or_subset_of_nonempty_derivedNeighborhoodCell_inter
    (K : Geometry.SimplicialComplex ℝ E) {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    (hne : ((derivedNeighborhoodCell K s).space ∩ (derivedNeighborhoodCell K t).space).Nonempty) :
    s ⊆ t ∨ t ⊆ s := by
  classical
  obtain ⟨x, hxs, hxt⟩ := hne
  obtain ⟨u, hu, hxu⟩ := exists_face_mem_openSimplex (derivedNeighborhoodCell K s) hxs
  have hut := mem_faces_of_mem_openSimplex_of_mem_space (derivedNeighborhoodCell_faces_subset K t)
    (derivedNeighborhoodCell_faces_subset K s hu) hxu hxt
  obtain ⟨d, hd, hne, rfl⟩ := derivedNeighborhoodCell_faces_subset K s hu
  obtain ⟨e, he⟩ := hne
  exact subset_or_subset_of_centroid_mem_face K hs ht (hd.mem_faces he)
    ((mem_derivedNeighborhoodCell_faces_iff_of_flag hs hd ⟨e, he⟩).mp hu e he)
    ((mem_derivedNeighborhoodCell_faces_iff_of_flag ht hd ⟨e, he⟩).mp hut e he)

open Classical in
theorem pair_centroid_mem_barycentricSubdivision_of_subset_or_subset (K : Geometry.SimplicialComplex ℝ E)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hst : s ⊆ t ∨ t ⊆ s) :
    {s.centroid ℝ id, t.centroid ℝ id} ∈ (barycentricSubdivision K).faces := by
  classical
  refine ⟨{s, t}, ⟨?_, ?_⟩, Finset.insert_nonempty _ _, by simp only [Finset.image_insert, Finset.image_singleton]⟩
  · intro u hu
    rcases (show u = s ∨ u = t by simpa only [Finset.mem_insert, Finset.mem_singleton] using hu) with rfl | rfl
    · exact hs
    · exact ht
  · intro u hu v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact Or.inl subset_rfl
    · exact hst
    · exact hst.symm
    · exact Or.inl subset_rfl

open Classical in
theorem derivedNeighborhoodCell_space_inter (K : Geometry.SimplicialComplex ℝ E)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hst : s ⊆ t ∨ t ⊆ s) :
    (derivedNeighborhoodCell K s).space ∩ (derivedNeighborhoodCell K t).space =
      (dualCell (barycentricSubdivision K) {s.centroid ℝ id, t.centroid ℝ id}
        (pair_centroid_mem_barycentricSubdivision_of_subset_or_subset K hs ht hst)).space := by
  classical
  rw [derivedNeighborhoodCell_eq_dualCell K hs, derivedNeighborhoodCell_eq_dualCell K ht]
  simpa only [Finset.singleton_union] using dualCell_space_inter_eq_dualCell _
    (singleton_centroid_mem_barycentricSubdivision K hs)
    (singleton_centroid_mem_barycentricSubdivision K ht)
    (show {s.centroid ℝ id} ∪ {t.centroid ℝ id} ∈ (barycentricSubdivision K).faces by
      simpa only [Finset.singleton_union] using pair_centroid_mem_barycentricSubdivision_of_subset_or_subset K hs ht hst)

theorem IsCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhoodCell_inter
    [FiniteDimensional ℝ E] {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 2) K) {s t : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hne : s ≠ t) (hst : s ⊆ t ∨ t ⊆ s) :
    IsPLBall (n + 1) ((derivedNeighborhoodCell K s).space ∩ (derivedNeighborhoodCell K t).space) := by
  classical
  have hcent : s.centroid ℝ id ≠ t.centroid ℝ id := fun h => hne
    (injOn_faces_of_mem_openSimplex K (centroid_mem_openSimplex_of_mem_faces K) hs ht h)
  rw [derivedNeighborhoodCell_space_inter K hs ht hst]
  exact hK.barycentricSubdivision.isPLBall_dualCell _ _
    (k := 1) (Finset.card_pair hcent) (Nat.succ_le_succ (Nat.zero_le n))

theorem disjoint_derivedNeighborhoodCell_space (K : Geometry.SimplicialComplex ℝ E)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hst : ¬s ⊆ t) (hts : ¬t ⊆ s) :
    Disjoint (derivedNeighborhoodCell K s).space (derivedNeighborhoodCell K t).space := by
  rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
  intro x hx
  exact (subset_or_subset_of_nonempty_derivedNeighborhoodCell_inter K hs ht ⟨x, hx⟩).elim hst hts

theorem derivedNeighborhoodCell_space_subset (K : Geometry.SimplicialComplex ℝ E) (s : Finset E) :
    (derivedNeighborhoodCell K s).space ⊆ K.space := by
  classical
  intro x hx
  obtain ⟨u, hu, hxu⟩ := (derivedNeighborhoodCell K s).mem_space_iff.mp hx
  apply (secondDerived_isSubdivision K).space_eq.subset
  exact (secondDerived K).convexHull_subset_space (derivedNeighborhoodCell_faces_subset K s hu) hxu

open Classical in
theorem derivedNeighborhoodCell_faces_subset_derivedNeighborhood
    (K L : Geometry.SimplicialComplex ℝ E) (hL : L.faces ⊆ K.faces) {s : Finset E}
    (hs : s ∈ L.faces) : (derivedNeighborhoodCell K s).faces ⊆ (derivedNeighborhood K L).faces := by
  classical
  intro u hu
  obtain ⟨d, hd, hne, rfl⟩ := derivedNeighborhoodCell_faces_subset K s hu
  exact (mem_derivedNeighborhood_faces_iff_of_flag hd hne).mpr fun e he =>
    ⟨s, hs, (mem_derivedNeighborhoodCell_faces_iff_of_flag (hL hs) hd hne).mp hu e he⟩

open Classical in
theorem iUnion_derivedNeighborhoodCell_space (K L : Geometry.SimplicialComplex ℝ E)
    (hL : L.faces ⊆ K.faces) :
    (⋃ s ∈ L.faces, (derivedNeighborhoodCell K s).space) = (derivedNeighborhood K L).space := by
  classical
  apply Subset.antisymm
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
    obtain ⟨u, hu, hxu⟩ := (derivedNeighborhoodCell K s).mem_space_iff.mp hxs
    exact (derivedNeighborhood K L).convexHull_subset_space
      (derivedNeighborhoodCell_faces_subset_derivedNeighborhood K L hL hs hu) hxu
  · intro x hx
    obtain ⟨u, hu, hxu⟩ := (derivedNeighborhood K L).mem_space_iff.mp hx
    obtain ⟨d, hd, hne, hmem, rfl⟩ := (mem_derivedNeighborhood_faces_iff K L).mp hu
    obtain ⟨e₀, he₀, hbot⟩ := hd.exists_bot hne
    obtain ⟨s, hs, hse₀⟩ := hmem e₀ he₀
    refine mem_iUnion₂.mpr ⟨s, hs, (derivedNeighborhoodCell K s).convexHull_subset_space ?_ hxu⟩
    exact (mem_derivedNeighborhoodCell_faces_iff_of_flag (hL hs) hd hne).mpr
      fun e he => hbot e he hse₀

theorem IsCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhoodCell_inter_of_nonempty
    [FiniteDimensional ℝ E] {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 2) K) {s t : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hst : s ≠ t)
    (hne : ((derivedNeighborhoodCell K s).space ∩ (derivedNeighborhoodCell K t).space).Nonempty) :
    IsPLBall (n + 1) ((derivedNeighborhoodCell K s).space ∩ (derivedNeighborhoodCell K t).space) :=
  hK.isPLBall_derivedNeighborhoodCell_inter hs ht hst
    (subset_or_subset_of_nonempty_derivedNeighborhoodCell_inter K hs ht hne)

theorem IsCombinatorialManifoldWithBoundary.derivedNeighborhoodCell_inter_subset_frontier
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (n + 2)))} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 2) K)
    {s t : Finset (EuclideanSpace ℝ (Fin (n + 2)))} (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    (hst : s ≠ t) :
    (derivedNeighborhoodCell K s).space ∩ (derivedNeighborhoodCell K t).space ⊆
      frontier (derivedNeighborhoodCell K s).space := by
  intro x hx
  have hI := hK.isPLBall_derivedNeighborhoodCell_inter_of_nonempty hs ht hst ⟨x, hx⟩
  exact (hK.isPLBall_derivedNeighborhoodCell ht).inter_subset_frontier_of_isPLBall hI
    (Nat.lt_succ_self _) hx

open Classical in
theorem derivedNeighborhoodCell_singleton (K : Geometry.SimplicialComplex ℝ E) {v : E}
    (hv : {v} ∈ K.faces) :
    derivedNeighborhoodCell K {v} = derivedNeighborhood K (simplexComplex {v} (K.indep hv)) := by
  classical
  ext u
  constructor
  · intro hu
    exact derivedNeighborhoodCell_faces_subset_derivedNeighborhood K (simplexComplex {v} (K.indep hv))
      (fun t ht => K.down_closed hv ht.2 ht.1)
      ⟨Finset.singleton_nonempty v, Finset.Subset.rfl⟩ hu
  · intro hu
    obtain ⟨d, hd, hne, hmem, rfl⟩ := (mem_derivedNeighborhood_faces_iff K _).mp hu
    apply (mem_derivedNeighborhoodCell_faces_iff_of_flag hv hd hne).mpr
    intro e he
    obtain ⟨s, hs, hse⟩ := hmem e he
    rcases Finset.subset_singleton_iff.mp hs.2 with hempty | heq
    · exact (hs.1.ne_empty hempty).elim
    · exact heq ▸ hse

open Classical in
theorem derivedNeighborhoodCell_space_eq_closedStar (K : Geometry.SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) :
    (derivedNeighborhoodCell K s).space = closedStar (secondDerived K) (s.centroid ℝ id) :=
  starComplex_space _ _ ((barycentricSubdivision_isSubdivision _).singleton_mem
    (singleton_centroid_mem_barycentricSubdivision K hs))

end DifferentialGeometry.Topology.PiecewiseLinear

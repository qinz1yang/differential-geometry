import DifferentialGeometry.Topology.PiecewiseLinear.Exhaustion

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem isConeBase_upperLink (K : Geometry.SimplicialComplex ℝ E) {e : Finset E}
    (he : e ∈ K.faces) : IsConeBase (e.centroid ℝ id) (upperLink K e) :=
  (isConeBase_geometricLink (barycentricSubdivision K)).of_faces_subset
    (upperLink_faces_subset_geometricLink K he)

open Classical in
noncomputable def dualCell (K : Geometry.SimplicialComplex ℝ E) (e : Finset E)
    (he : e ∈ K.faces) : Geometry.SimplicialComplex ℝ E :=
  coneComplex (isConeBase_upperLink K he)

open Classical in
theorem IsFlag.insert_of_subset {K : Geometry.SimplicialComplex ℝ E}
    {d : Finset (Finset E)} (hd : IsFlag K d) {e : Finset E} (he : e ∈ K.faces)
    (hed : ∀ s ∈ d, e ⊆ s) : IsFlag K (insert e d) := by
  classical
  refine ⟨fun s hs => ?_, fun s hs t ht => ?_⟩
  · rcases Finset.mem_insert.mp hs with rfl | hs'
    · exact he
    · exact hd.mem_faces hs'
  · rcases Finset.mem_insert.mp hs with rfl | hs'
    · rcases Finset.mem_insert.mp ht with rfl | ht'
      · exact Or.inl subset_rfl
      · exact Or.inl (hed t ht')
    · rcases Finset.mem_insert.mp ht with rfl | ht'
      · exact Or.inr (hed s hs')
      · exact hd.subset_or_subset hs' ht'

open Classical in
theorem mem_dualCell_faces_iff (K : Geometry.SimplicialComplex ℝ E) {e : Finset E}
    (he : e ∈ K.faces) {u : Finset E} :
    u ∈ (dualCell K e he).faces ↔ ∃ d : Finset (Finset E), IsFlag K d ∧ d.Nonempty ∧
      (∀ s ∈ d, e ⊆ s) ∧ u = d.image fun s => s.centroid ℝ id := by
  classical
  constructor
  · intro hu
    rcases hu with hu | rfl | ⟨s, hs, rfl⟩
    · obtain ⟨d, hd, hne, hlt, rfl⟩ := hu
      exact ⟨d, hd, hne, fun s hs => (hlt s hs).subset, rfl⟩
    · refine ⟨{e}, ?_, Finset.singleton_nonempty e, ?_, by rw [Finset.image_singleton]⟩
      · exact ⟨fun s hs => (Finset.mem_singleton.mp hs).symm ▸ he, fun s hs t ht =>
          Or.inl ((Finset.mem_singleton.mp hs).trans (Finset.mem_singleton.mp ht).symm ▸
            Finset.Subset.refl _)⟩
      · intro s hs
        rw [Finset.mem_singleton.mp hs]
    · obtain ⟨d, hd, _, hlt, rfl⟩ := hs
      refine ⟨insert e d, hd.insert_of_subset he (fun s hs => (hlt s hs).subset),
        Finset.insert_nonempty e d, ?_, (Finset.image_insert _ _ _).symm⟩
      intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact subset_rfl
      · exact (hlt s hs).subset
  · rintro ⟨d, hd, hne, hsub, rfl⟩
    by_cases hed : e ∈ d
    · rcases (d.erase e).eq_empty_or_nonempty with hempty | hrest
      · right
        left
        have hd' : d = {e} := by
          rw [← Finset.insert_erase hed, hempty, Finset.insert_empty]
        rw [hd', Finset.image_singleton]
      · right
        right
        refine ⟨(d.erase e).image fun s => s.centroid ℝ id, ?_, ?_⟩
        · refine ⟨d.erase e, hd.mono (Finset.erase_subset _ _), hrest, ?_, rfl⟩
          intro s hs
          exact Finset.ssubset_iff_subset_ne.mpr
            ⟨hsub s (Finset.mem_of_mem_erase hs), (Finset.ne_of_mem_erase hs).symm⟩
        · simpa only [Finset.insert_erase hed] using
            Finset.image_insert (fun s : Finset E => s.centroid ℝ id) e (d.erase e)
    · left
      refine ⟨d, hd, hne, ?_, rfl⟩
      intro s hs
      exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub s hs, (ne_of_mem_of_not_mem hs hed).symm⟩

open Classical in
theorem dualCell_faces_subset (K : Geometry.SimplicialComplex ℝ E) {e : Finset E}
    (he : e ∈ K.faces) : (dualCell K e he).faces ⊆ (barycentricSubdivision K).faces := by
  classical
  rintro s (hs | rfl | ⟨t, ht, rfl⟩)
  · exact upperLink_faces_subset K e hs
  · exact singleton_centroid_mem_barycentricSubdivision K he
  · exact (SimplicialComplex.mem_geometricLink_singleton _ _ _).mp
      (upperLink_faces_subset_geometricLink K he ht) |>.2.2

open Classical in
theorem dualCell_faces_finite (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {e : Finset E} (he : e ∈ K.faces) : (dualCell K e he).faces.Finite :=
  (Set.toFinite (barycentricSubdivision K).faces).subset (dualCell_faces_subset K he)

open Classical in
theorem singleton_centroid_mem_dualCell (K : Geometry.SimplicialComplex ℝ E) {e : Finset E}
    (he : e ∈ K.faces) : {e.centroid ℝ id} ∈ (dualCell K e he).faces :=
  Or.inr (Or.inl rfl)

open Classical in
theorem geometricLink_dualCell (K : Geometry.SimplicialComplex ℝ E) {e : Finset E}
    (he : e ∈ K.faces) :
    SimplicialComplex.geometricLink (dualCell K e he) {e.centroid ℝ id} = upperLink K e := by
  ext s
  simp only [dualCell, geometricLink_coneComplex_faces]

open Classical in
theorem eq_centroid_of_mem_dualCell_of_mem_convexHull (K : Geometry.SimplicialComplex ℝ E)
    {e t : Finset E} (he : e ∈ K.faces) (ht : t ∈ K.faces) (hcard : t.card ≤ e.card)
    {x : E} (hx : x ∈ (dualCell K e he).space) (hxt : x ∈ convexHull ℝ (t : Set E)) :
    x = e.centroid ℝ id := by
  classical
  obtain ⟨u, hu, hxu⟩ := exists_face_mem_openSimplex (dualCell K e he) hx
  obtain ⟨d, hd, hne, hes, rfl⟩ := (mem_dualCell_faces_iff K he).mp hu
  obtain ⟨s, hs, htop⟩ := hd.exists_top hne
  have hxs := mem_openSimplex_top K (centroid_mem_openSimplex_of_mem_faces K) hd hs htop hxu
  have hst := face_subset_of_mem_openSimplex_of_mem_convexHull K (hd.mem_faces hs) ht hxs hxt
  have hes' : e = s := Finset.eq_of_subset_of_card_le (hes s hs)
    ((Finset.card_le_card hst).trans hcard)
  have himg : ((d.image fun s => s.centroid ℝ id) : Set E) ⊆ {e.centroid ℝ id} := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
    have hte : t = e := Finset.Subset.antisymm (hes'.symm ▸ htop t ht) (hes t ht)
    rw [hte]
    exact mem_singleton _
  simpa only [convexHull_singleton, mem_singleton_iff] using
    convexHull_mono himg (openSimplex_subset_convexHull _ hxu)

open Classical in
theorem dualCell_space_inter (K L : Geometry.SimplicialComplex ℝ E)
    (hL : L.faces ⊆ K.faces) {e : Finset E} (he : e ∈ L.faces)
    (hcard : ∀ t ∈ L.faces, t.card ≤ e.card) :
    (dualCell K e (hL he)).space ∩ L.space = {e.centroid ℝ id} := by
  classical
  apply Subset.antisymm
  · rintro x ⟨hx, hxL⟩
    obtain ⟨t, ht, hxt⟩ := L.mem_space_iff.mp hxL
    exact eq_centroid_of_mem_dualCell_of_mem_convexHull K (hL he) (hL ht) (hcard t ht) hx hxt
  · rintro x rfl
    exact ⟨apex_mem_coneComplex_space (isConeBase_upperLink K (hL he)),
      L.convexHull_subset_space he (e.centroid_mem_convexHull (L.nonempty_of_mem_faces he))⟩

open Classical in
theorem IsCombinatorialManifold.isPLSphere_upperLink [FiniteDimensional ℝ E] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold (n + 1) K)
    {e : Finset E} (he : e ∈ K.faces) {k : ℕ} (hcard : e.card = k + 1) (hk : k ≤ n) :
    IsPLSphere (n - k) (upperLink K e).space := by
  classical
  obtain ⟨f, hf⟩ := exists_isPLHomeomorphOn_upperLink K he
  exact (hK.isPLSphere_geometricLink K he hcard hk).of_isPLHomeomorphOn hf.symm

open Classical in
theorem IsCombinatorialManifold.isPLBall_dualCell [FiniteDimensional ℝ E] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold (n + 1) K)
    {e : Finset E} (he : e ∈ K.faces) {k : ℕ} (hcard : e.card = k + 1) (hk : k ≤ n) :
    IsPLBall (n - k + 1) (dualCell K e he).space := by
  classical
  have := (upperLink_faces_finite K e).to_subtype
  exact (isConeBase_upperLink K he).isPLBall_of_isPLSphere (hK.isPLSphere_upperLink K he hcard hk)

open Classical in
noncomputable def splittingDisk (K : Geometry.SimplicialComplex ℝ E) (e : Finset E)
    (he : e ∈ K.faces) : Geometry.SimplicialComplex ℝ E :=
  starComplex (barycentricSubdivision (dualCell K e he)) (e.centroid ℝ id)

open Classical in
theorem splittingDisk_space (K : Geometry.SimplicialComplex ℝ E) {e : Finset E}
    (he : e ∈ K.faces) : (splittingDisk K e he).space =
    closedStar (barycentricSubdivision (dualCell K e he)) (e.centroid ℝ id) :=
  starComplex_space _ _ ((barycentricSubdivision_isSubdivision (dualCell K e he)).singleton_mem
    (singleton_centroid_mem_dualCell K he))

open Classical in
theorem splittingDisk_faces_subset (K : Geometry.SimplicialComplex ℝ E) {e : Finset E}
    (he : e ∈ K.faces) : (splittingDisk K e he).faces ⊆ (secondDerived K).faces :=
  (starComplex_faces_subset _ _).trans
    (barycentricSubdivision_faces_subset (dualCell_faces_subset K he))

open Classical in
theorem splittingDisk_faces_finite (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {e : Finset E} (he : e ∈ K.faces) : (splittingDisk K e he).faces.Finite :=
  (Set.toFinite (secondDerived K).faces).subset (splittingDisk_faces_subset K he)

open Classical in
theorem centroid_mem_splittingDisk_space (K : Geometry.SimplicialComplex ℝ E) {e : Finset E}
    (he : e ∈ K.faces) : e.centroid ℝ id ∈ (splittingDisk K e he).space := by
  classical
  rw [splittingDisk_space]
  exact mem_closedStar_self _ ((barycentricSubdivision_isSubdivision (dualCell K e he)).singleton_mem
    (singleton_centroid_mem_dualCell K he))

open Classical in
theorem splittingDisk_space_subset_dualCell (K : Geometry.SimplicialComplex ℝ E) {e : Finset E}
    (he : e ∈ K.faces) : (splittingDisk K e he).space ⊆ (dualCell K e he).space := by
  classical
  rw [splittingDisk_space]
  exact (closedStar_subset_space _ _).trans
    (barycentricSubdivision_isSubdivision (dualCell K e he)).space_eq.subset

open Classical in
theorem splittingDisk_space_inter (K L : Geometry.SimplicialComplex ℝ E)
    (hL : L.faces ⊆ K.faces) {e : Finset E} (he : e ∈ L.faces)
    (hcard : ∀ t ∈ L.faces, t.card ≤ e.card) :
    (splittingDisk K e (hL he)).space ∩ L.space = {e.centroid ℝ id} := by
  classical
  apply Subset.antisymm
  · rw [← dualCell_space_inter K L hL he hcard]
    exact inter_subset_inter_left _ (splittingDisk_space_subset_dualCell K (hL he))
  · rintro x rfl
    exact ⟨centroid_mem_splittingDisk_space K (hL he),
      L.convexHull_subset_space he (e.centroid_mem_convexHull (L.nonempty_of_mem_faces he))⟩

open Classical in
theorem IsCombinatorialManifold.isPLBall_splittingDisk [FiniteDimensional ℝ E] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold (n + 1) K)
    {e : Finset E} (he : e ∈ K.faces) {k : ℕ} (hcard : e.card = k + 1) (hk : k ≤ n) :
    IsPLBall (n - k + 1) (splittingDisk K e he).space := by
  classical
  have := (dualCell_faces_finite K he).to_subtype
  have hvertex := singleton_centroid_mem_dualCell K he
  have hsub := barycentricSubdivision_isSubdivision (dualCell K e he)
  have hlink : IsPLSphere (n - k)
      (SimplicialComplex.geometricLink (dualCell K e he) {e.centroid ℝ id}).space := by
    rw [geometricLink_dualCell]
    exact hK.isPLSphere_upperLink K he hcard hk
  rw [splittingDisk_space]
  exact PiecewiseLinear.isPLBall_closedStar _ (hsub.singleton_mem hvertex)
    ((isPLSphere_geometricLink_iff_of_isSubdivision hsub hvertex).mpr hlink)

open Classical in
noncomputable def graphDualCell (K L : Geometry.SimplicialComplex ℝ E) (v : E) :
    Geometry.SimplicialComplex ℝ E :=
  restrict (derivedNeighborhood K L) (closedStar (barycentricSubdivision K) v)

end DifferentialGeometry.Topology.PiecewiseLinear

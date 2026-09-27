/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Exhaustion

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mem_faces_of_mem_openSimplex_of_mem_space {K L : Geometry.SimplicialComplex ℝ E}
    (hL : L.faces ⊆ K.faces) {s : Finset E} (hs : s ∈ K.faces) {x : E}
    (hxs : x ∈ openSimplex s) (hxL : x ∈ L.space) : s ∈ L.faces := by
  obtain ⟨t, ht, hxt⟩ := L.mem_space_iff.mp hxL
  exact L.down_closed ht (face_subset_of_mem_openSimplex_of_mem_convexHull K hs (hL ht) hxs hxt)
    (K.nonempty_of_mem_faces hs)

open Classical in
theorem IsFlag.eq_of_image_centroid_eq {K : Geometry.SimplicialComplex ℝ E}
    {d d' : Finset (Finset E)} (hd : IsFlag K d) (hd' : IsFlag K d')
    (h : (d.image fun s => s.centroid ℝ id) = d'.image fun s => s.centroid ℝ id) : d = d' := by
  classical
  apply Finset.Subset.antisymm
  · intro s hs
    have hcs : s.centroid ℝ id ∈ d'.image (fun s => s.centroid ℝ id) :=
      h ▸ Finset.mem_image_of_mem _ hs
    obtain ⟨t, ht, hts⟩ := Finset.mem_image.mp hcs
    have heq := injOn_faces_of_mem_openSimplex K (centroid_mem_openSimplex_of_mem_faces K)
      (hd'.mem_faces ht) (hd.mem_faces hs) hts
    exact heq ▸ ht
  · intro s hs
    have hcs : s.centroid ℝ id ∈ d.image (fun s => s.centroid ℝ id) :=
      h.symm ▸ Finset.mem_image_of_mem _ hs
    obtain ⟨t, ht, hts⟩ := Finset.mem_image.mp hcs
    have heq := injOn_faces_of_mem_openSimplex K (centroid_mem_openSimplex_of_mem_faces K)
      (hd.mem_faces ht) (hd'.mem_faces hs) hts
    exact heq ▸ ht

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
theorem mem_dualCell_faces_iff_of_flag {K : Geometry.SimplicialComplex ℝ E} {e : Finset E}
    (he : e ∈ K.faces) {d : Finset (Finset E)} (hd : IsFlag K d) (hne : d.Nonempty) :
    (d.image fun s => s.centroid ℝ id) ∈ (dualCell K e he).faces ↔ ∀ s ∈ d, e ⊆ s := by
  constructor
  · intro hu
    obtain ⟨d', hd', _, hsub, himage⟩ := (mem_dualCell_faces_iff K he).mp hu
    exact hd.eq_of_image_centroid_eq hd' himage ▸ hsub
  · intro hsub
    exact (mem_dualCell_faces_iff K he).mpr ⟨d, hd, hne, hsub, rfl⟩

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
theorem subset_of_mem_dualCell_of_mem_convexHull (K : Geometry.SimplicialComplex ℝ E)
    {e t : Finset E} (he : e ∈ K.faces) (ht : t ∈ K.faces)
    {x : E} (hx : x ∈ (dualCell K e he).space) (hxt : x ∈ convexHull ℝ (t : Set E)) :
    e ⊆ t := by
  classical
  obtain ⟨u, hu, hxu⟩ := exists_face_mem_openSimplex (dualCell K e he) hx
  obtain ⟨d, hd, hne, hes, rfl⟩ := (mem_dualCell_faces_iff K he).mp hu
  obtain ⟨s, hs, htop⟩ := hd.exists_top hne
  have hxs := mem_openSimplex_top K (centroid_mem_openSimplex_of_mem_faces K) hd hs htop hxu
  exact (hes s hs).trans
    (face_subset_of_mem_openSimplex_of_mem_convexHull K (hd.mem_faces hs) ht hxs hxt)

open Classical in
theorem closedStar_barycentricSubdivision_eq_dualCell (K : Geometry.SimplicialComplex ℝ E)
    {v : E} (hv : {v} ∈ K.faces) :
    closedStar (barycentricSubdivision K) v = (dualCell K {v} hv).space := by
  classical
  apply Subset.antisymm
  · intro x hx
    obtain ⟨u, ⟨hu, hvu⟩, hxu⟩ := mem_iUnion₂.mp hx
    have hvu' := mem_of_mem_convexHull_of_singleton_mem (barycentricSubdivision K)
      ((barycentricSubdivision_isSubdivision K).singleton_mem hv) hu hvu
    obtain ⟨d, hd, hne, himage⟩ := hu
    obtain ⟨s, hs, hcs⟩ := Finset.mem_image.mp (himage ▸ hvu')
    have hseq : s = {v} := injOn_faces_of_mem_openSimplex K
      (centroid_mem_openSimplex_of_mem_faces K) (hd.mem_faces hs) hv
      (by simpa only [Finset.centroid_singleton, id_eq] using hcs)
    have hsing : {v} ∈ d := hseq ▸ hs
    refine (dualCell K {v} hv).convexHull_subset_space
      ((mem_dualCell_faces_iff K hv).mpr ⟨d, hd, hne, ?_, himage⟩) hxu
    intro t ht
    rcases hd.subset_or_subset hsing ht with h | h
    · exact h
    · rcases Finset.subset_singleton_iff.mp h with h | h
      · exact ((K.nonempty_of_mem_faces (hd.mem_faces ht)).ne_empty h).elim
      · rw [h]
  · intro x hx
    obtain ⟨u, hu, hxu⟩ := (dualCell K {v} hv).mem_space_iff.mp hx
    obtain ⟨d, hd, hne, hsub, himage⟩ := (mem_dualCell_faces_iff K hv).mp hu
    have hins : insert v u ∈ (barycentricSubdivision K).faces := by
      refine ⟨insert {v} d, hd.insert_of_subset hv hsub, Finset.insert_nonempty _ _, ?_⟩
      simp only [himage, Finset.image_insert, Finset.centroid_singleton, id_eq]
    exact mem_biUnion (x := insert v u) ⟨hins, subset_convexHull ℝ _ (by simp)⟩
      (convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert v u)) hxu)

open Classical in
theorem starComplex_barycentricSubdivision_eq_dualCell (K : Geometry.SimplicialComplex ℝ E)
    {v : E} (hv : {v} ∈ K.faces) :
    starComplex (barycentricSubdivision K) v = dualCell K {v} hv := by
  classical
  have hspace := (starComplex_space (barycentricSubdivision K) v
    ((barycentricSubdivision_isSubdivision K).singleton_mem hv)).trans
      (closedStar_barycentricSubdivision_eq_dualCell K hv)
  ext s
  constructor
  · intro hs
    have hx : s.centroid ℝ id ∈ (starComplex (barycentricSubdivision K) v).space :=
      (starComplex _ _).convexHull_subset_space hs
        (s.centroid_mem_convexHull ((starComplex _ _).nonempty_of_mem_faces hs))
    rw [hspace] at hx
    exact mem_faces_of_mem_openSimplex_of_mem_space (dualCell_faces_subset K hv) hs.1
      (centroid_mem_openSimplex ((barycentricSubdivision K).nonempty_of_mem_faces hs.1)) hx
  · intro hs
    have hx : s.centroid ℝ id ∈ (dualCell K {v} hv).space :=
      (dualCell K {v} hv).convexHull_subset_space hs
        (s.centroid_mem_convexHull ((dualCell K {v} hv).nonempty_of_mem_faces hs))
    rw [← hspace] at hx
    exact mem_faces_of_mem_openSimplex_of_mem_space (starComplex_faces_subset _ _)
      (dualCell_faces_subset K hv hs) (centroid_mem_openSimplex
        ((dualCell K {v} hv).nonempty_of_mem_faces hs)) hx

open Classical in
theorem dualCell_faces_inter (K : Geometry.SimplicialComplex ℝ E) {e f : Finset E}
    (he : e ∈ K.faces) (hf : f ∈ K.faces) (hef : e ∪ f ∈ K.faces) :
    (dualCell K e he).faces ∩ (dualCell K f hf).faces = (dualCell K (e ∪ f) hef).faces := by
  classical
  ext u
  constructor
  · rintro ⟨hu, hv⟩
    obtain ⟨d, hd, hne, rfl⟩ := dualCell_faces_subset K he hu
    have he' := (mem_dualCell_faces_iff_of_flag he hd hne).mp hu
    have hf' := (mem_dualCell_faces_iff_of_flag hf hd hne).mp hv
    exact (mem_dualCell_faces_iff_of_flag hef hd hne).mpr fun s hs =>
      Finset.union_subset (he' s hs) (hf' s hs)
  · intro hu
    obtain ⟨d, hd, hne, rfl⟩ := dualCell_faces_subset K hef hu
    have hef' := (mem_dualCell_faces_iff_of_flag hef hd hne).mp hu
    exact ⟨(mem_dualCell_faces_iff_of_flag he hd hne).mpr fun s hs =>
        Finset.subset_union_left.trans (hef' s hs),
      (mem_dualCell_faces_iff_of_flag hf hd hne).mpr fun s hs =>
        Finset.subset_union_right.trans (hef' s hs)⟩

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
theorem mem_splittingDisk_faces_iff_of_flag {K : Geometry.SimplicialComplex ℝ E} {e : Finset E}
    (he : e ∈ K.faces) {D : Finset (Finset E)} (hD : IsFlag (barycentricSubdivision K) D)
    (hne : D.Nonempty) :
    (D.image fun s => s.centroid ℝ id) ∈ (splittingDisk K e he).faces ↔
      (∀ s ∈ D, s ∈ (dualCell K e he).faces) ∧ ∀ s ∈ D, e.centroid ℝ id ∈ s := by
  classical
  rw [splittingDisk, starComplex_barycentricSubdivision_eq_dualCell _
    (singleton_centroid_mem_dualCell K he)]
  constructor
  · intro hu
    obtain ⟨D', hD', _, hsub, himage⟩ := (mem_dualCell_faces_iff _ _).mp hu
    have heq := hD.eq_of_image_centroid_eq (hD'.of_le (dualCell_faces_subset K he)) himage
    rw [heq]
    exact ⟨fun s hs => hD'.mem_faces hs,
      fun s hs => Finset.singleton_subset_iff.mp (hsub s hs)⟩
  · rintro ⟨hfaces, hmem⟩
    exact (mem_dualCell_faces_iff_of_flag (singleton_centroid_mem_dualCell K he)
      ⟨hfaces, hD.2⟩ hne).mpr fun s hs => Finset.singleton_subset_iff.mpr (hmem s hs)

open Classical in
theorem centroid_mem_splittingDisk_space (K : Geometry.SimplicialComplex ℝ E) {e : Finset E}
    (he : e ∈ K.faces) : e.centroid ℝ id ∈ (splittingDisk K e he).space := by
  classical
  rw [splittingDisk_space]
  exact mem_closedStar_self _ ((barycentricSubdivision_isSubdivision (dualCell K e
      he)).singleton_mem
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

open Classical in
theorem mem_graphDualCell_faces_iff_of_flag {K : Geometry.SimplicialComplex ℝ E}
    (L : Geometry.SimplicialComplex ℝ E) {v : E} (hv : {v} ∈ K.faces)
    {D : Finset (Finset E)} (hD : IsFlag (barycentricSubdivision K) D) (hne : D.Nonempty) :
    (D.image fun s => s.centroid ℝ id) ∈ (graphDualCell K L v).faces ↔
      (∀ e ∈ D, ∃ s ∈ L.faces, s.centroid ℝ id ∈ e) ∧
      ∀ e ∈ D, e ∈ (dualCell K {v} hv).faces := by
  classical
  constructor
  · rintro ⟨huN, huS⟩
    obtain ⟨D', hD', _, hDN, himage⟩ := huN
    have heq := hD.eq_of_image_centroid_eq hD' himage
    refine ⟨heq ▸ hDN, fun e he => ?_⟩
    have hmem : e.centroid ℝ id ∈ closedStar (barycentricSubdivision K) v :=
      huS (subset_convexHull ℝ _ (Finset.mem_image_of_mem _ he))
    rw [closedStar_barycentricSubdivision_eq_dualCell K hv] at hmem
    exact mem_faces_of_mem_openSimplex_of_mem_space (dualCell_faces_subset K hv) (hD.mem_faces he)
      (centroid_mem_openSimplex ((barycentricSubdivision K).nonempty_of_mem_faces (hD.mem_faces
          he)))
      hmem
  · rintro ⟨hDN, hfaces⟩
    refine ⟨⟨D, hD, hne, hDN, rfl⟩, ?_⟩
    rw [closedStar_barycentricSubdivision_eq_dualCell K hv]
    have hface : (D.image fun s => s.centroid ℝ id) ∈
        (barycentricSubdivision (dualCell K {v} hv)).faces :=
      ⟨D, ⟨hfaces, hD.2⟩, hne, rfl⟩
    exact ((barycentricSubdivision (dualCell K {v} hv)).convexHull_subset_space hface).trans
      (barycentricSubdivision_isSubdivision (dualCell K {v} hv)).space_eq.subset

open Classical in
theorem graphDualCell_faces_subset (K L : Geometry.SimplicialComplex ℝ E) (v : E) :
    (graphDualCell K L v).faces ⊆ (derivedNeighborhood K L).faces :=
  restrict_faces_subset _ _

open Classical in
theorem graphDualCell_faces_finite (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (v : E) : (graphDualCell K L v).faces.Finite :=
  (derivedNeighborhood_faces_finite K L).subset (graphDualCell_faces_subset K L v)

open Classical in
theorem graphDualCell_space_subset (K L : Geometry.SimplicialComplex ℝ E) (v : E) :
    (graphDualCell K L v).space ⊆ (derivedNeighborhood K L).space := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := (graphDualCell K L v).mem_space_iff.mp hx
  exact (derivedNeighborhood K L).convexHull_subset_space hs.1 hxs

open Classical in
theorem graphDualCell_space_subset_closedStar (K L : Geometry.SimplicialComplex ℝ E) (v : E) :
    (graphDualCell K L v).space ⊆ closedStar (barycentricSubdivision K) v :=
  restrict_space_subset _ _

open Classical in
theorem IsFlag.exists_bot {K : Geometry.SimplicialComplex ℝ E} {d : Finset (Finset E)}
    (hd : IsFlag K d) (hne : d.Nonempty) : ∃ e ∈ d, ∀ s ∈ d, e ⊆ s := by
  classical
  obtain ⟨e, he, hmin⟩ := d.exists_min_image Finset.card hne
  refine ⟨e, he, fun s hs => ?_⟩
  rcases hd.subset_or_subset he hs with h | h
  · exact h
  · exact (Finset.eq_of_subset_of_card_le h (hmin s hs)).symm.subset

open Classical in
theorem exists_mem_graphDualCell_faces (K L : Geometry.SimplicialComplex ℝ E)
    (hL : L.faces ⊆ K.faces) {u : Finset E} (hu : u ∈ (derivedNeighborhood K L).faces) :
    ∃ v, {v} ∈ L.faces ∧ u ∈ (graphDualCell K L v).faces := by
  classical
  obtain ⟨D, hD, hDne, hDL, huD⟩ := hu
  obtain ⟨e, he, htop⟩ := hD.exists_top hDne
  obtain ⟨d, hd, hne, hed⟩ := hD.mem_faces he
  obtain ⟨t, ht, hbot⟩ := hd.exists_bot hne
  obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces (hd.mem_faces ht)
  obtain ⟨s, hs, hcse⟩ := hDL e he
  obtain ⟨s', hs', hcs⟩ := Finset.mem_image.mp (hed ▸ hcse)
  have hs's : s' = s := injOn_faces_of_mem_openSimplex K
    (centroid_mem_openSimplex_of_mem_faces K) (hd.mem_faces hs') (hL hs) hcs
  have hvs : v ∈ s := hs's ▸ hbot s' hs' hv
  have hvL : {v} ∈ L.faces :=
    L.down_closed hs (Finset.singleton_subset_iff.mpr hvs) (Finset.singleton_nonempty v)
  have heD : e ∈ (dualCell K {v} (hL hvL)).faces :=
    (mem_dualCell_faces_iff K (hL hvL)).mpr
      ⟨d, hd, hne, fun s hs => Finset.singleton_subset_iff.mpr (hbot s hs hv), hed⟩
  refine ⟨v, hvL, ⟨D, hD, hDne, hDL, huD⟩, ?_⟩
  rw [closedStar_barycentricSubdivision_eq_dualCell K (hL hvL)]
  intro x hx
  apply (dualCell K {v} (hL hvL)).convexHull_subset_space heD
  rw [huD] at hx
  exact convexHull_image_subset (barycentricSubdivision K)
    (centroid_mem_openSimplex_of_mem_faces _) hD htop hx

open Classical in
theorem iUnion_graphDualCell_space (K L : Geometry.SimplicialComplex ℝ E)
    (hL : L.faces ⊆ K.faces) :
    ⋃ v ∈ {v : E | {v} ∈ L.faces}, (graphDualCell K L v).space =
      (derivedNeighborhood K L).space := by
  apply Subset.antisymm
  · exact iUnion_subset fun v => iUnion_subset fun _ => graphDualCell_space_subset K L v
  · intro x hx
    obtain ⟨u, hu, hxu⟩ := (derivedNeighborhood K L).mem_space_iff.mp hx
    obtain ⟨v, hv, huv⟩ := exists_mem_graphDualCell_faces K L hL hu
    exact mem_iUnion₂.mpr ⟨v, hv, (graphDualCell K L v).convexHull_subset_space huv hxu⟩

open Classical in
theorem mem_graphDualCell_space_of_singleton_mem (K L : Geometry.SimplicialComplex ℝ E)
    (hL : L.faces ⊆ K.faces) {v : E} (hv : {v} ∈ L.faces) :
    v ∈ (graphDualCell K L v).space := by
  classical
  have hvK' := (barycentricSubdivision_isSubdivision K).singleton_mem (hL hv)
  have hvN : {v} ∈ (derivedNeighborhood K L).faces := by
    simpa only [Finset.centroid_singleton, id_eq] using
      (singleton_centroid_mem_derivedNeighborhood_iff K L hvK').mpr
        ⟨{v}, hv, by simp only [Finset.centroid_singleton, id_eq, Finset.mem_singleton]⟩
  refine (graphDualCell K L v).convexHull_subset_space ⟨hvN, ?_⟩ (by simp)
  simpa using mem_closedStar_self (barycentricSubdivision K) hvK'

open Classical in
theorem mem_graphDualCell_space_iff_of_singleton_mem (K L : Geometry.SimplicialComplex ℝ E)
    (hL : L.faces ⊆ K.faces) {v w : E} (hv : {v} ∈ L.faces) (hw : {w} ∈ L.faces) :
    w ∈ (graphDualCell K L v).space ↔ w = v := by
  constructor
  · intro hwC
    have hwD := graphDualCell_space_subset_closedStar K L v hwC
    rw [closedStar_barycentricSubdivision_eq_dualCell K (hL hv)] at hwD
    simpa only [Finset.centroid_singleton, id_eq] using
      eq_centroid_of_mem_dualCell_of_mem_convexHull K (hL hv) (hL hw)
      (by simp) hwD (by simp)
  · rintro rfl
    exact mem_graphDualCell_space_of_singleton_mem K L hL hv

open Classical in
theorem eq_pair_of_centroid_mem_dualCell_face (K : Geometry.SimplicialComplex ℝ E)
    {v w : E} (hvw : v ≠ w) (he : {v, w} ∈ K.faces) {s u : Finset E} (hs : s ∈ K.faces)
    (hcard : s.card ≤ 2) (hu : u ∈ (dualCell K {v, w} he).faces)
    (hcs : s.centroid ℝ id ∈ u) : s = {v, w} := by
  classical
  have hsub := subset_of_mem_dualCell_of_mem_convexHull K he hs
    ((dualCell K {v, w} he).convexHull_subset_space hu (subset_convexHull ℝ _ hcs))
    (s.centroid_mem_convexHull (K.nonempty_of_mem_faces hs))
  exact (Finset.eq_of_subset_of_card_le hsub (by simpa [Finset.card_pair hvw] using hcard)).symm

open Classical in
theorem graphDualCell_faces_inter (K L : Geometry.SimplicialComplex ℝ E)
    (hL : L.faces ⊆ K.faces) (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {v w : E}
    (hvw : v ≠ w) (he : {v, w} ∈ L.faces) :
    (graphDualCell K L v).faces ∩ (graphDualCell K L w).faces =
      (splittingDisk K {v, w} (hL he)).faces := by
  classical
  have hv : {v} ∈ K.faces := K.down_closed (hL he)
    (by simp) (Finset.singleton_nonempty v)
  have hw : {w} ∈ K.faces := K.down_closed (hL he)
    (by simp) (Finset.singleton_nonempty w)
  have hdual : (dualCell K {v} hv).faces ∩ (dualCell K {w} hw).faces =
      (dualCell K {v, w} (hL he)).faces := by
    simpa only [Finset.singleton_union] using dualCell_faces_inter K hv hw
      (show {v} ∪ {w} ∈ K.faces by simpa using hL he)
  ext u
  constructor
  · rintro ⟨huv, huw⟩
    obtain ⟨D, hD, hne, rfl⟩ := derivedNeighborhood_faces_subset K L huv.1
    obtain ⟨hDN, hDv⟩ := (mem_graphDualCell_faces_iff_of_flag L hv hD hne).mp huv
    have hDw := ((mem_graphDualCell_faces_iff_of_flag L hw hD hne).mp huw).2
    have hDe : ∀ s ∈ D, s ∈ (dualCell K {v, w} (hL he)).faces := fun s hs =>
      hdual ▸ (show s ∈ (dualCell K {v} hv).faces ∩ (dualCell K {w} hw).faces from
        ⟨hDv s hs, hDw s hs⟩)
    refine (mem_splittingDisk_faces_iff_of_flag (hL he) hD hne).mpr ⟨hDe, ?_⟩
    intro s hs
    obtain ⟨t, ht, hcts⟩ := hDN s hs
    have hte := eq_pair_of_centroid_mem_dualCell_face K hvw (hL he) (hL ht)
      (hcard t ht) (hDe s hs) hcts
    exact hte ▸ hcts
  · intro hu
    obtain ⟨D, hD, hne, rfl⟩ := splittingDisk_faces_subset K (hL he) hu
    obtain ⟨hDe, hmem⟩ := (mem_splittingDisk_faces_iff_of_flag (hL he) hD hne).mp hu
    have hDv : ∀ s ∈ D, s ∈ (dualCell K {v} hv).faces ∩ (dualCell K {w} hw).faces :=
      fun s hs => hdual.symm ▸ hDe s hs
    have hDN : ∀ s ∈ D, ∃ t ∈ L.faces, t.centroid ℝ id ∈ s :=
      fun s hs => ⟨{v, w}, he, hmem s hs⟩
    exact ⟨(mem_graphDualCell_faces_iff_of_flag L hv hD hne).mpr ⟨hDN, fun s hs => (hDv s hs).1⟩,
      (mem_graphDualCell_faces_iff_of_flag L hw hD hne).mpr ⟨hDN, fun s hs => (hDv s hs).2⟩⟩

open Classical in
theorem graphDualCell_space_inter (K L : Geometry.SimplicialComplex ℝ E)
    (hL : L.faces ⊆ K.faces) (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {v w : E}
    (hvw : v ≠ w) (he : {v, w} ∈ L.faces) :
    (graphDualCell K L v).space ∩ (graphDualCell K L w).space =
      (splittingDisk K {v, w} (hL he)).space := by
  classical
  have hCv := (graphDualCell_faces_subset K L v).trans (derivedNeighborhood_faces_subset K L)
  have hCw := (graphDualCell_faces_subset K L w).trans (derivedNeighborhood_faces_subset K L)
  have hfaces := graphDualCell_faces_inter K L hL hcard hvw he
  apply Subset.antisymm
  · rintro x ⟨hxv, hxw⟩
    have hxK : x ∈ (secondDerived K).space :=
      derivedNeighborhood_space_subset_secondDerived K L (graphDualCell_space_subset K L v hxv)
    obtain ⟨u, hu, hxu⟩ := exists_face_mem_openSimplex (secondDerived K) hxK
    have huv := mem_faces_of_mem_openSimplex_of_mem_space hCv hu hxu hxv
    have huw := mem_faces_of_mem_openSimplex_of_mem_space hCw hu hxu hxw
    have huD : u ∈ (splittingDisk K {v, w} (hL he)).faces :=
      hfaces ▸ (show u ∈ (graphDualCell K L v).faces ∩ (graphDualCell K L w).faces from ⟨huv, huw⟩)
    exact (splittingDisk K {v, w} (hL he)).convexHull_subset_space huD
      (openSimplex_subset_convexHull _ hxu)
  · intro x hx
    obtain ⟨u, hu, hxu⟩ := (splittingDisk K {v, w} (hL he)).mem_space_iff.mp hx
    have huC : u ∈ (graphDualCell K L v).faces ∩ (graphDualCell K L w).faces := hfaces.symm ▸ hu
    exact ⟨(graphDualCell K L v).convexHull_subset_space huC.1 hxu,
      (graphDualCell K L w).convexHull_subset_space huC.2 hxu⟩

open Classical in
theorem pair_mem_of_mem_graphDualCell_faces (K L : Geometry.SimplicialComplex ℝ E)
    (hL : L.faces ⊆ K.faces) (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {v w : E}
    (hv : {v} ∈ L.faces) (hw : {w} ∈ L.faces) (hvw : v ≠ w) {u : Finset E}
    (huv : u ∈ (graphDualCell K L v).faces) (huw : u ∈ (graphDualCell K L w).faces) :
    {v, w} ∈ L.faces := by
  classical
  obtain ⟨D, hD, hne, rfl⟩ := derivedNeighborhood_faces_subset K L huv.1
  obtain ⟨hDN, hDv⟩ := (mem_graphDualCell_faces_iff_of_flag L (hL hv) hD hne).mp huv
  have hDw := ((mem_graphDualCell_faces_iff_of_flag L (hL hw) hD hne).mp huw).2
  obtain ⟨s, hs⟩ := hne
  obtain ⟨t, ht, hcts⟩ := hDN s hs
  have hvs := subset_of_mem_dualCell_of_mem_convexHull K (hL hv) (hL ht)
    ((dualCell K {v} (hL hv)).convexHull_subset_space (hDv s hs) (subset_convexHull ℝ _ hcts))
    (t.centroid_mem_convexHull (L.nonempty_of_mem_faces ht))
  have hws := subset_of_mem_dualCell_of_mem_convexHull K (hL hw) (hL ht)
    ((dualCell K {w} (hL hw)).convexHull_subset_space (hDw s hs) (subset_convexHull ℝ _ hcts))
    (t.centroid_mem_convexHull (L.nonempty_of_mem_faces ht))
  have hpair : {v, w} ⊆ t := Finset.insert_subset_iff.mpr
    ⟨Finset.singleton_subset_iff.mp hvs, hws⟩
  have heq : {v, w} = t := Finset.eq_of_subset_of_card_le hpair
    (by simpa [Finset.card_pair hvw] using hcard t ht)
  exact heq.symm ▸ ht

open Classical in
theorem graphDualCell_space_inter_eq_empty (K L : Geometry.SimplicialComplex ℝ E)
    (hL : L.faces ⊆ K.faces) (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {v w : E}
    (hv : {v} ∈ L.faces) (hw : {w} ∈ L.faces) (hvw : v ≠ w) (hnot : {v, w} ∉ L.faces) :
    (graphDualCell K L v).space ∩ (graphDualCell K L w).space = ∅ := by
  classical
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hxv, hxw⟩
  obtain ⟨u, hu, hxu⟩ := exists_face_mem_openSimplex (graphDualCell K L v) hxv
  have huK := derivedNeighborhood_faces_subset K L (graphDualCell_faces_subset K L v hu)
  have huw := mem_faces_of_mem_openSimplex_of_mem_space
    ((graphDualCell_faces_subset K L w).trans (derivedNeighborhood_faces_subset K L)) huK hxu hxw
  exact hnot (pair_mem_of_mem_graphDualCell_faces K L hL hcard hv hw hvw hu huw)

open Classical in
theorem subset_or_subset_of_centroid_mem_face (K : Geometry.SimplicialComplex ℝ E)
    {e f u : Finset E} (he : e ∈ K.faces) (hf : f ∈ K.faces)
    (hu : u ∈ (barycentricSubdivision K).faces)
    (heu : e.centroid ℝ id ∈ u) (hfu : f.centroid ℝ id ∈ u) : e ⊆ f ∨ f ⊆ e := by
  classical
  obtain ⟨d, hd, _, rfl⟩ := hu
  obtain ⟨e', he', hce⟩ := Finset.mem_image.mp heu
  obtain ⟨f', hf', hcf⟩ := Finset.mem_image.mp hfu
  have heq := injOn_faces_of_mem_openSimplex K (centroid_mem_openSimplex_of_mem_faces K)
    (hd.mem_faces he') he hce
  have hfq := injOn_faces_of_mem_openSimplex K (centroid_mem_openSimplex_of_mem_faces K)
    (hd.mem_faces hf') hf hcf
  exact heq ▸ hfq ▸ hd.subset_or_subset he' hf'

open Classical in
theorem disjoint_splittingDisk_space (K : Geometry.SimplicialComplex ℝ E)
    {e f : Finset E} (he : e ∈ K.faces) (hf : f ∈ K.faces) (hef : e ≠ f)
    (hcard : e.card = f.card) :
    Disjoint (splittingDisk K e he).space (splittingDisk K f hf).space := by
  classical
  apply Set.disjoint_left.mpr
  intro x hxe hxf
  obtain ⟨u, hu, hxu⟩ := exists_face_mem_openSimplex (splittingDisk K e he) hxe
  have huK := splittingDisk_faces_subset K he hu
  have huf := mem_faces_of_mem_openSimplex_of_mem_space (splittingDisk_faces_subset K hf)
    huK hxu hxf
  obtain ⟨D, hD, hne, rfl⟩ := huK
  have hDe := ((mem_splittingDisk_faces_iff_of_flag he hD hne).mp hu).2
  have hDf := ((mem_splittingDisk_faces_iff_of_flag hf hD hne).mp huf).2
  obtain ⟨s, hs⟩ := hne
  rcases subset_or_subset_of_centroid_mem_face K he hf (hD.mem_faces hs)
      (hDe s hs) (hDf s hs) with h | h
  · exact hef (Finset.eq_of_subset_of_card_le h hcard.ge)
  · exact hef (Finset.eq_of_subset_of_card_le h hcard.le).symm

open Classical in
theorem diam_graphDualCell_le (K L : Geometry.SimplicialComplex ℝ E) (v : E) {δ : ℝ}
    (hδ : 0 ≤ δ) (hdiam : ∀ s ∈ K.faces, Metric.diam (convexHull ℝ (s : Set E)) ≤ δ) :
    Metric.diam (graphDualCell K L v).space ≤ 2 * δ := by
  classical
  have hdist : ∀ x ∈ (graphDualCell K L v).space, dist x v ≤ δ := by
    intro x hx
    obtain ⟨u, ⟨hu, hvu⟩, hxu⟩ :=
      mem_iUnion₂.mp (graphDualCell_space_subset_closedStar K L v hx)
    obtain ⟨s, hs, hsub⟩ := (barycentricSubdivision_isSubdivision K).exists_face_subset hu
    exact (Metric.dist_le_diam_of_mem (s.finite_toSet.isCompact_convexHull ℝ).isBounded
      (hsub hxu) (hsub hvu)).trans (hdiam s hs)
  apply Metric.diam_le_of_forall_dist_le (by positivity)
  intro x hx y hy
  calc dist x y ≤ dist x v + dist y v := dist_triangle_right x y v
    _ ≤ δ + δ := add_le_add (hdist x hx) (hdist y hy)
    _ = 2 * δ := by ring

theorem IsSubdivision.card_le {E : Type*} [AddCommGroup E] [Module ℝ E]
    {K K' : Geometry.SimplicialComplex ℝ E} (h : IsSubdivision K' K) {N : ℕ}
    (hcard : ∀ s ∈ K.faces, s.card ≤ N) {s : Finset E} (hs : s ∈ K'.faces) : s.card ≤ N := by
  obtain ⟨t, ht, hst⟩ := h.exists_face_subset hs
  exact ((K'.indep hs).card_le_card_of_subset_affineSpan
    ((subset_convexHull ℝ _).trans (hst.trans (convexHull_subset_affineSpan _)))).trans (hcard t ht)

open Classical in
theorem exists_isSubdivision_graphDualCell_diam_lt [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hL : L.faces ⊆ K.faces)
    {N : ℕ} (hcard : ∀ s ∈ L.faces, s.card ≤ N) {ε : ℝ} (hε : 0 < ε) :
    ∃ K' L' : Geometry.SimplicialComplex ℝ E, IsSubdivision K' K ∧ IsSubdivision L' L ∧
      K'.faces.Finite ∧ L'.faces ⊆ K'.faces ∧ (∀ s ∈ L'.faces, s.card ≤ N) ∧
      ∀ v, Metric.diam (graphDualCell K' L' v).space < ε := by
  classical
  obtain ⟨K', hK', hfin, _, hdiam⟩ := exists_isSubdivision_diam_lt K
    (fun s hs => card_le_finrank_succ_of_mem_faces K hs) (div_pos hε (by norm_num : (0 : ℝ) < 3))
  let L' := restrict K' L.space
  have hL' : IsSubdivision L' L := restrict_isSubdivision L fun t ht => hK'.convexHull_eq_biUnion
      (hL ht)
  refine ⟨K', L', hK', hL', hfin, restrict_faces_subset _ _, fun s hs => hL'.card_le hcard hs,
    fun v => ?_⟩
  have hbound := diam_graphDualCell_le K' L' v (δ := ε / 3)
    (le_of_lt (div_pos hε (by norm_num : (0 : ℝ) < 3))) fun s hs => (hdiam s hs).le
  linarith

end DifferentialGeometry.Topology.PiecewiseLinear

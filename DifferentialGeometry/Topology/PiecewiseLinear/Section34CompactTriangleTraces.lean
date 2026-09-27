/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryDerivedNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.DualCellDecomposition

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem pair_centroid_mem_dualCell_of_subset (K : Geometry.SimplicialComplex ℝ E)
    {e s : Finset E} (he : e ∈ K.faces) (hs : s ∈ K.faces) (hes : e ⊆ s) :
    {e.centroid ℝ id, s.centroid ℝ id} ∈ (dualCell K e he).faces := by
  have hflag : IsFlag K {e, s} := by
    refine ⟨?_, ?_⟩
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl <;> assumption
    · intro t ht u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht hu
      rcases ht with rfl | rfl <;> rcases hu with rfl | rfl
      · exact Or.inl subset_rfl
      · exact Or.inl hes
      · exact Or.inr hes
      · exact Or.inl subset_rfl
  have h := (mem_dualCell_faces_iff_of_flag he hflag (Finset.insert_nonempty _ _)).mpr
    (fun t ht => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact subset_rfl
      · exact hes)
  simpa only [Finset.image_insert, Finset.image_singleton] using h

open Classical in
theorem splittingDisk_inter_derivedNeighborhoodCell_eq_dualCell
    (K : Geometry.SimplicialComplex ℝ E) {e s : Finset E}
    (he : e ∈ K.faces) (hs : s ∈ K.faces) (hes : e ⊆ s) :
    (splittingDisk K e he).space ∩ (derivedNeighborhoodCell K s).space =
      (dualCell (dualCell K e he) {e.centroid ℝ id, s.centroid ℝ id}
        (pair_centroid_mem_dualCell_of_subset K he hs hes)).space := by
  let A := dualCell K e he
  apply Subset.antisymm
  · rintro x ⟨hxE, hxS⟩
    obtain ⟨u, hu, hxu⟩ := exists_face_mem_openSimplex (splittingDisk K e he) hxE
    have huK := splittingDisk_faces_subset K he hu
    have huS := mem_faces_of_mem_openSimplex_of_mem_space
      (derivedNeighborhoodCell_faces_subset K s) huK hxu hxS
    obtain ⟨D, hD, hne, rfl⟩ := huK
    obtain ⟨hDA, hDe⟩ := (mem_splittingDisk_faces_iff_of_flag he hD hne).mp hu
    have hDs := (mem_derivedNeighborhoodCell_faces_iff_of_flag hs hD hne).mp huS
    apply (dualCell A _ _).convexHull_subset_space ?_ (openSimplex_subset_convexHull _ hxu)
    exact (mem_dualCell_faces_iff_of_flag _ ⟨hDA, hD.2⟩ hne).mpr fun r hr =>
      (by
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hDe r hr
        · rcases Finset.mem_singleton.mp hy with rfl
          exact hDs r hr)
  · intro x hx
    obtain ⟨u, hu, hxu⟩ := (dualCell A _ _).mem_space_iff.mp hx
    obtain ⟨D, hD, hne, hsub, rfl⟩ := (mem_dualCell_faces_iff A _).mp hu
    have hDK := hD.of_le (dualCell_faces_subset K he)
    constructor
    · apply (splittingDisk K e he).convexHull_subset_space ?_ hxu
      exact (mem_splittingDisk_faces_iff_of_flag he hDK hne).mpr
        ⟨fun r hr => hD.mem_faces hr,
          fun r hr => hsub r hr (Finset.mem_insert_self _ _)⟩
    · apply (derivedNeighborhoodCell K s).convexHull_subset_space ?_ hxu
      exact (mem_derivedNeighborhoodCell_faces_iff_of_flag hs hDK hne).mpr
        fun r hr => hsub r hr (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

open Classical in
theorem splittingDisk_inter_derivedNeighborhoodCell_eq_singleton
    (K : Geometry.SimplicialComplex ℝ E) {e s : Finset E}
    (he : e ∈ K.faces) (hs : s ∈ K.faces) (hes : e ⊆ s)
    (hcard : s.card = e.card + 1) (hmax : ∀ r ∈ K.faces, r ⊆ s) :
    (splittingDisk K e he).space ∩ (derivedNeighborhoodCell K s).space =
      {({e.centroid ℝ id, s.centroid ℝ id} : Finset E).centroid ℝ id} := by
  rw [splittingDisk_inter_derivedNeighborhoodCell_eq_dualCell K he hs hes]
  apply dualCell_space_eq_singleton_of_card
  intro u hu
  have hsub : u ⊆ {e.centroid ℝ id, s.centroid ℝ id} := by
    obtain ⟨d, hd, hne, hde, rfl⟩ := (mem_dualCell_faces_iff K he).mp hu
    intro y hy
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hy
    have her := hde r hr
    have hrs := hmax r (hd.mem_faces hr)
    have hrc := Finset.card_le_card hrs
    have herc := Finset.card_le_card her
    by_cases hre : r.card = e.card
    · have hre' : r = e := (Finset.eq_of_subset_of_card_le her hre.le).symm
      simp only [hre', Finset.mem_insert, Finset.mem_singleton, true_or]
    · have hrs' : r = s := Finset.eq_of_subset_of_card_le hrs (by omega)
      simp only [hrs', Finset.mem_insert, Finset.mem_singleton, or_true]
  exact Finset.card_le_card hsub

open Classical in
theorem graphDualCell_inter_derivedNeighborhoodCell_eq_upperLink
    (K L : Geometry.SimplicialComplex ℝ E) {v : E} {s : Finset E}
    (hv : {v} ∈ K.faces) (hs : s ∈ K.faces)
    (hL : ∀ r, r ∈ L.faces ↔ r ∈ K.faces ∧ r ≠ s) :
    (graphDualCell K L v).space ∩ (derivedNeighborhoodCell K s).space =
      (upperLink (dualCell K {v} hv) {s.centroid ℝ id}).space := by
  let A := dualCell K {v} hv
  apply Subset.antisymm
  · rintro x ⟨hxG, hxS⟩
    obtain ⟨u, hu, hxu⟩ := exists_face_mem_openSimplex (graphDualCell K L v) hxG
    have huK := derivedNeighborhood_faces_subset K L hu.1
    have huS := mem_faces_of_mem_openSimplex_of_mem_space
      (derivedNeighborhoodCell_faces_subset K s) huK hxu hxS
    obtain ⟨D, hD, hne, rfl⟩ := huK
    obtain ⟨hDN, hDA⟩ := (mem_graphDualCell_faces_iff_of_flag L hv hD hne).mp hu
    have hDs := (mem_derivedNeighborhoodCell_faces_iff_of_flag hs hD hne).mp huS
    apply (upperLink A {s.centroid ℝ id}).convexHull_subset_space ?_
      (openSimplex_subset_convexHull _ hxu)
    refine ⟨D, ⟨hDA, hD.2⟩, hne, ?_, rfl⟩
    intro r hr
    refine Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.singleton_subset_iff.mpr (hDs r hr), ?_⟩
    intro hsingle
    obtain ⟨t, ht, htr⟩ := hDN r hr
    have heq : t.centroid ℝ id = s.centroid ℝ id := by
      rw [← hsingle] at htr
      exact Finset.mem_singleton.mp htr
    exact ((hL t).mp ht).2 (injOn_faces_of_mem_openSimplex K
      (centroid_mem_openSimplex_of_mem_faces K) ((hL t).mp ht).1 hs heq)
  · intro x hx
    obtain ⟨u, hu, hxu⟩ := (upperLink A {s.centroid ℝ id}).mem_space_iff.mp hx
    obtain ⟨D, hD, hne, hproper, rfl⟩ := hu
    have hDK := hD.of_le (dualCell_faces_subset K hv)
    have hDs : ∀ r ∈ D, s.centroid ℝ id ∈ r :=
      fun r hr => Finset.singleton_subset_iff.mp (hproper r hr).subset
    have hDN : ∀ r ∈ D, ∃ t ∈ L.faces, t.centroid ℝ id ∈ r := by
      intro r hr
      obtain ⟨d, hd, hdne, hsub, heq⟩ := (mem_dualCell_faces_iff K hv).mp (hD.mem_faces hr)
      have hex : ∃ t ∈ d, t ≠ s := by
        by_contra hn
        have hall : ∀ t ∈ d, t = s := by simpa only [not_exists, not_and, not_not] using hn
        have hle : r ⊆ {s.centroid ℝ id} := by
          rw [heq]
          intro y hy
          obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
          simp only [hall t ht, Finset.mem_singleton]
        exact (not_le_of_gt (hproper r hr)) hle
      obtain ⟨t, ht, hts⟩ := hex
      refine ⟨t, (hL t).mpr ⟨hd.mem_faces ht, hts⟩, ?_⟩
      rw [heq]
      exact Finset.mem_image_of_mem _ ht
    constructor
    · apply (graphDualCell K L v).convexHull_subset_space ?_ hxu
      exact (mem_graphDualCell_faces_iff_of_flag L hv hDK hne).mpr
        ⟨hDN, fun r hr => hD.mem_faces hr⟩
    · apply (derivedNeighborhoodCell K s).convexHull_subset_space ?_ hxu
      exact (mem_derivedNeighborhoodCell_faces_iff_of_flag hs hDK hne).mpr hDs

open Classical in
theorem isPLBall_graphDualCell_inter_triangleCell [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {v : E} {s : Finset E} (hs : s ∈ K.faces) (hvs : v ∈ s) (hcard : s.card = 3)
    (hmax : ∀ r ∈ K.faces, r ⊆ s)
    (hL : ∀ r, r ∈ L.faces ↔ r ∈ K.faces ∧ r ≠ s) :
    IsPLBall 1 ((graphDualCell K L v).space ∩ (derivedNeighborhoodCell K s).space) := by
  have hv : {v} ∈ K.faces := K.down_closed hs
    (Finset.singleton_subset_iff.mpr hvs) (Finset.singleton_nonempty v)
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
  let A := dualCell K {v} hv
  let _ : Finite A.faces := (dualCell_faces_finite K hv).to_subtype
  have hA : IsPLBall 2 A.space :=
    hK.isPLBall_dualCell K hv (k := 0) (Finset.card_singleton v) (by omega)
  obtain ⟨w, hws, hwv⟩ := Finset.exists_mem_ne (by omega : 1 < s.card) v
  have hw : {w} ∈ K.faces := K.down_closed hs
    (Finset.singleton_subset_iff.mpr hws) (Finset.singleton_nonempty w)
  have hp : {v, w} ∈ K.faces := K.down_closed hs
    (by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact hvs
      · rcases Finset.mem_singleton.mp ha with rfl
        exact hws) (Finset.insert_nonempty _ _)
  have hcent (a : E) (ha : {a} ∈ K.faces) (has : a ∈ s) :
      s.centroid ℝ id ∈ (dualCell K {a} ha).space := by
    have hpair := pair_centroid_mem_dualCell_of_subset K ha hs
      (Finset.singleton_subset_iff.mpr has)
    exact (dualCell K {a} ha).subset_space hpair
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hbd : s.centroid ℝ id ∈ (boundaryComplex 2 A).space :=
    hK.inter_dualCell_singleton_subset_boundaryComplex K hv hw hwv.symm hp
      ⟨hcent v hv hvs, hcent w hw hws⟩
  have hvertex : {s.centroid ℝ id} ∈ A.faces :=
    A.down_closed (pair_centroid_mem_dualCell_of_subset K hv hs
      (Finset.singleton_subset_iff.mpr hvs))
      (by simp) (Finset.singleton_nonempty _)
  have hvertexB : {s.centroid ℝ id} ∈ (boundaryComplex 2 A).faces :=
    mem_faces_of_mem_openSimplex_of_mem_space (boundaryComplex_faces_subset 2 A) hvertex
      (by
        have hp : ({s.centroid ℝ id} : Finset E).centroid ℝ id ∈
            openSimplex ({s.centroid ℝ id} : Finset E) :=
          centroid_mem_openSimplex (Finset.singleton_nonempty _)
        simpa only [Finset.centroid_singleton, id_eq] using hp)
      hbd
  rw [graphDualCell_inter_derivedNeighborhoodCell_eq_upperLink K L hv hs hL]
  exact hA.isCombinatorialManifoldWithBoundary.isPLBall_upperLink_of_mem_boundaryComplex A
    hvertexB (k := 0) (Finset.card_singleton _)

end DifferentialGeometry.Topology.PiecewiseLinear

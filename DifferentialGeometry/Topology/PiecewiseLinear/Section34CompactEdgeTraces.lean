/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTriangleTraces

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem splittingDisk_inter_iUnion_derivedNeighborhoodCell_eq_upperLink
    (K : Geometry.SimplicialComplex ℝ E) {e : Finset E} (he : e ∈ K.faces) :
    (splittingDisk K e he).space ∩
        (⋃ s ∈ {s : Finset E | s ∈ K.faces ∧ e.card < s.card},
          (derivedNeighborhoodCell K s).space) =
      (upperLink (dualCell K e he) {e.centroid ℝ id}).space := by
  let A := dualCell K e he
  apply Subset.antisymm
  · rintro x ⟨hxE, hxR⟩
    obtain ⟨s, ⟨hs, hcard⟩, hxS⟩ := mem_iUnion₂.mp hxR
    obtain ⟨u, hu, hxu⟩ := exists_face_mem_openSimplex (splittingDisk K e he) hxE
    have huK := splittingDisk_faces_subset K he hu
    have huS := mem_faces_of_mem_openSimplex_of_mem_space
      (derivedNeighborhoodCell_faces_subset K s) huK hxu hxS
    obtain ⟨D, hD, hne, rfl⟩ := huK
    obtain ⟨hDA, hDe⟩ := (mem_splittingDisk_faces_iff_of_flag he hD hne).mp hu
    have hDs := (mem_derivedNeighborhoodCell_faces_iff_of_flag hs hD hne).mp huS
    have hcent : e.centroid ℝ id ≠ s.centroid ℝ id := by
      intro h
      have heq := injOn_faces_of_mem_openSimplex K
        (centroid_mem_openSimplex_of_mem_faces K) he hs h
      have hc := congrArg Finset.card heq
      omega
    apply (upperLink A {e.centroid ℝ id}).convexHull_subset_space ?_
      (openSimplex_subset_convexHull _ hxu)
    refine ⟨D, ⟨hDA, hD.2⟩, hne, ?_, rfl⟩
    intro r hr
    refine Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.singleton_subset_iff.mpr (hDe r hr), ?_⟩
    intro heq
    have hs' := hDs r hr
    rw [← heq] at hs'
    exact hcent (Finset.mem_singleton.mp hs').symm
  · intro x hx
    obtain ⟨u, hu, hxu⟩ := (upperLink A {e.centroid ℝ id}).mem_space_iff.mp hx
    obtain ⟨D, hD, hne, hproper, rfl⟩ := hu
    have hDK := hD.of_le (dualCell_faces_subset K he)
    have hDe : ∀ r ∈ D, e.centroid ℝ id ∈ r :=
      fun r hr => Finset.singleton_subset_iff.mp (hproper r hr).subset
    have hxE : x ∈ (splittingDisk K e he).space :=
      (splittingDisk K e he).convexHull_subset_space
        ((mem_splittingDisk_faces_iff_of_flag he hDK hne).mpr
          ⟨fun r hr => hD.mem_faces hr, hDe⟩) hxu
    obtain ⟨r, hr, hbot⟩ := hD.exists_bot hne
    obtain ⟨d, hd, hdne, hsub, heq⟩ := (mem_dualCell_faces_iff K he).mp (hD.mem_faces hr)
    have hex : ∃ s ∈ d, s ≠ e := by
      by_contra hn
      have hall : ∀ s ∈ d, s = e := by simpa only [not_exists, not_and, not_not] using hn
      have hle : r ⊆ {e.centroid ℝ id} := by
        rw [heq]
        intro y hy
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
        simp only [hall s hs, Finset.mem_singleton]
      exact (not_le_of_gt (hproper r hr)) hle
    obtain ⟨s, hs, hse⟩ := hex
    have hlt : e.card < s.card := Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨hsub s hs, hse.symm⟩)
    have hsr : s.centroid ℝ id ∈ r := by
      rw [heq]
      exact Finset.mem_image_of_mem _ hs
    refine ⟨hxE, mem_iUnion₂.mpr ⟨s, ⟨hd.mem_faces hs, hlt⟩, ?_⟩⟩
    apply (derivedNeighborhoodCell K s).convexHull_subset_space ?_ hxu
    exact (mem_derivedNeighborhoodCell_faces_iff_of_flag (hd.mem_faces hs) hDK hne).mpr
      fun q hq => hbot q hq hsr

open Classical in
theorem splittingDisk_inter_tetraResidual_eq_upperLink
    (K : Geometry.SimplicialComplex ℝ E) {e t : Finset E}
    (he : e ∈ K.faces) (ht : t ∈ K.faces) (hec : e.card = 2) (htc : t.card = 4)
    (hmax : ∀ s ∈ K.faces, s ⊆ t) :
    (splittingDisk K e he).space ∩
        ((derivedNeighborhoodCell K t).space ∪
          ⋃ s ∈ t.powersetCard 3, (derivedNeighborhoodCell K s).space) =
      (upperLink (dualCell K e he) {e.centroid ℝ id}).space := by
  have hcover :
      (⋃ s ∈ {s : Finset E | s ∈ K.faces ∧ e.card < s.card},
        (derivedNeighborhoodCell K s).space) =
      (derivedNeighborhoodCell K t).space ∪
        ⋃ s ∈ t.powersetCard 3, (derivedNeighborhoodCell K s).space := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨s, ⟨hs, hsc⟩, hxs⟩ := mem_iUnion₂.mp hx
      have hst := hmax s hs
      have hsc' := Finset.card_le_card hst
      by_cases heq : s.card = 4
      · have heq' : s = t := Finset.eq_of_subset_of_card_le hst (by omega)
        exact Or.inl (heq' ▸ hxs)
      · exact Or.inr (mem_iUnion₂.mpr
          ⟨s, Finset.mem_powersetCard.mpr ⟨hst, by omega⟩, hxs⟩)
    · rintro x (hxt | hx)
      · exact mem_iUnion₂.mpr ⟨t, ⟨ht, by omega⟩, hxt⟩
      · obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
        obtain ⟨hst, hsc⟩ := Finset.mem_powersetCard.mp hs
        exact mem_iUnion₂.mpr
          ⟨s, ⟨K.down_closed ht hst (Finset.card_pos.mp (by omega)), by omega⟩, hxs⟩
  rw [← hcover]
  exact splittingDisk_inter_iUnion_derivedNeighborhoodCell_eq_upperLink K he

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLBall_upperLink_dualCell_apex_of_mem_boundaryComplex
    [FiniteDimensional ℝ E] {n k : ℕ} (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    {e : Finset E} (he : e ∈ (boundaryComplex (n + 1) K).faces) (hec : e.card = k + 1) :
    IsPLBall (n - k)
      (upperLink (dualCell K e (boundaryComplex_faces_subset (n + 1) K he))
        {e.centroid ℝ id}).space := by
  have heK := boundaryComplex_faces_subset (n + 1) K he
  let A := dualCell K e heK
  let _ : Finite A.faces := (dualCell_faces_finite K heK).to_subtype
  obtain ⟨f, hf⟩ := exists_isPLHomeomorphOn_upperLink A
    (singleton_centroid_mem_dualCell K heK)
  have hlink : IsPLBall (n - k) (SimplicialComplex.geometricLink A {e.centroid ℝ id}).space := by
    rw [show A = dualCell K e heK from rfl, geometricLink_dualCell K heK]
    exact hK.isPLBall_upperLink_of_mem_boundaryComplex K he hec
  exact hlink.of_isPLHomeomorphOn hf.symm

open Classical in
theorem isPLBall_splittingDisk_inter_tetraResidual [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {e t : Finset E}
    (he : e ∈ (boundaryComplex 3 K).faces) (ht : t ∈ K.faces)
    (hec : e.card = 2) (htc : t.card = 4) (hmax : ∀ s ∈ K.faces, s ⊆ t) :
    IsPLBall 1 ((splittingDisk K e (boundaryComplex_faces_subset 3 K he)).space ∩
      ((derivedNeighborhoodCell K t).space ∪
        ⋃ s ∈ t.powersetCard 3, (derivedNeighborhoodCell K s).space)) := by
  rw [splittingDisk_inter_tetraResidual_eq_upperLink K
    (boundaryComplex_faces_subset 3 K he) ht hec htc hmax]
  exact hK.isPLBall_upperLink_dualCell_apex_of_mem_boundaryComplex K he (k := 1) hec

end DifferentialGeometry.Topology.PiecewiseLinear

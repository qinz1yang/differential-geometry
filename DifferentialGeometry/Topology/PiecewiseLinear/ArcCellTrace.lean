/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedCellCone
import DifferentialGeometry.Topology.PiecewiseLinear.StarIntersection
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhood

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsFlag.card_le_two {G : Geometry.SimplicialComplex ℝ E} {d : Finset (Finset E)}
    (hd : IsFlag G d) (hG : ∀ f ∈ G.faces, f.card ≤ 2) : d.card ≤ 2 := by
  have hinj : Set.InjOn Finset.card (d : Set (Finset E)) := by
    intro s hs t ht hst
    rcases hd.subset_or_subset hs ht with h | h
    · exact Finset.eq_of_subset_of_card_le h hst.ge
    · exact (Finset.eq_of_subset_of_card_le h hst.le).symm
  have hmaps : Set.MapsTo Finset.card (d : Set (Finset E)) (({1, 2} : Finset ℕ) : Set ℕ) := by
    intro s hs
    have h1 : 0 < s.card := Finset.card_pos.mpr (G.nonempty_of_mem_faces (hd.mem_faces hs))
    have h2 : s.card ≤ 2 := hG s (hd.mem_faces hs)
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  exact (Finset.card_le_card_of_injOn Finset.card hmaps hinj).trans (by decide)

open Classical in
theorem barycentricSubdivision_card_le_two (G : Geometry.SimplicialComplex ℝ E)
    (hG : ∀ f ∈ G.faces, f.card ≤ 2) :
    ∀ f ∈ (barycentricSubdivision G).faces, f.card ≤ 2 := by
  rintro f ⟨d, hd, -, rfl⟩
  exact Finset.card_image_le.trans (hd.card_le_two hG)

open Classical in
theorem upperLink_singleton_space_of_card_le_two (G : Geometry.SimplicialComplex ℝ E)
    (hG : ∀ f ∈ G.faces, f.card ≤ 2) (x : E) :
    (upperLink G {x}).space = {c | ∃ e ∈ G.faces, {x} ⊂ e ∧ c = e.centroid ℝ id} := by
  ext y
  constructor
  · intro hy
    obtain ⟨u, hu, hyu⟩ := (upperLink G {x}).mem_space_iff.mp hy
    obtain ⟨d, hd, hne, hlt, rfl⟩ := (mem_upperLink_faces_iff G {x}).mp hu
    obtain ⟨e, he, htop⟩ := hd.exists_top hne
    have hde : ∀ s ∈ d, s = e := by
      intro s hs
      have hcard_e : e.card ≤ 2 := hG e (hd.mem_faces he)
      have hcard_s : ({x} : Finset E).card < s.card := Finset.card_lt_card (hlt s hs)
      rw [Finset.card_singleton] at hcard_s
      exact Finset.eq_of_subset_of_card_le (htop s hs) (by omega)
    have himg : d.image (fun s => s.centroid ℝ id) = {e.centroid ℝ id} := by
      ext c
      simp only [Finset.mem_image, Finset.mem_singleton]
      constructor
      · rintro ⟨s, hs, rfl⟩
        rw [hde s hs]
      · rintro rfl
        exact ⟨e, he, rfl⟩
    rw [himg, Finset.coe_singleton, convexHull_singleton, Set.mem_singleton_iff] at hyu
    exact ⟨e, hd.mem_faces he, hlt e he, hyu⟩
  · rintro ⟨e, he, hxe, rfl⟩
    have hflag : IsFlag G {e} := by
      refine ⟨fun s hs => ?_, fun s hs t ht => ?_⟩
      · rw [Finset.mem_singleton.mp hs]
        exact he
      · rw [Finset.mem_singleton.mp hs, Finset.mem_singleton.mp ht]
        exact Or.inl subset_rfl
    have hu : ({e.centroid ℝ id} : Finset E) ∈ (upperLink G {x}).faces :=
      (mem_upperLink_faces_iff G {x}).mpr ⟨{e}, hflag, Finset.singleton_nonempty e,
        fun s hs => by rw [Finset.mem_singleton.mp hs]; exact hxe, by rw [Finset.image_singleton]⟩
    refine (upperLink G {x}).convexHull_subset_space hu ?_
    rw [Finset.coe_singleton, convexHull_singleton]
    exact Set.mem_singleton _

open Classical in
theorem closedStar_barycentricSubdivision_eq_coneSet_of_card_le_two
    (G : Geometry.SimplicialComplex ℝ E) (hG : ∀ f ∈ G.faces, f.card ≤ 2) {x : E}
    (hx : {x} ∈ G.faces) :
    closedStar (barycentricSubdivision G) x =
      coneSet x {c | ∃ e ∈ G.faces, {x} ⊂ e ∧ c = e.centroid ℝ id} := by
  rw [closedStar_barycentricSubdivision_eq_dualCell G hx, dualCell, coneComplex_space_eq_coneSet,
    Finset.centroid_singleton, upperLink_singleton_space_of_card_le_two G hG x]
  rfl

open Classical in
theorem mem_barycentricSubdivision_ssubset_singleton_centroid_iff
    (G : Geometry.SimplicialComplex ℝ E) (hG : ∀ f ∈ G.faces, f.card ≤ 2) {s : Finset E}
    (hs : s ∈ G.faces) {e : Finset E} :
    (e ∈ (barycentricSubdivision G).faces ∧ {s.centroid ℝ id} ⊂ e) ↔
      ∃ t ∈ G.faces, t ≠ s ∧ (s ⊆ t ∨ t ⊆ s) ∧ e = {s.centroid ℝ id, t.centroid ℝ id} := by
  constructor
  · rintro ⟨⟨d, hd, -, rfl⟩, hlt⟩
    have hinj := injOn_faces_of_mem_openSimplex G (centroid_mem_openSimplex_of_mem_faces G)
    obtain ⟨s', hs'd, hs'⟩ := Finset.mem_image.mp (hlt.1 (Finset.mem_singleton_self _))
    have hs's : s' = s := hinj (hd.mem_faces hs'd) hs hs'
    subst hs's
    obtain ⟨c, hc, hcs⟩ := Finset.exists_of_ssubset hlt
    obtain ⟨t, htd, rfl⟩ := Finset.mem_image.mp hc
    have hts : t ≠ s' := fun h => hcs (by rw [h]; exact Finset.mem_singleton_self _)
    have hpair : ({s', t} : Finset (Finset E)) ⊆ d := by
      intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hr
      · exact hs'd
      · rw [Finset.mem_singleton.mp hr]
        exact htd
    have hd_eq : ({s', t} : Finset (Finset E)) = d :=
      Finset.eq_of_subset_of_card_le hpair (by
        rw [Finset.card_pair hts.symm]
        exact hd.card_le_two hG)
    refine ⟨t, hd.mem_faces htd, hts, hd.subset_or_subset hs'd htd, ?_⟩
    rw [← hd_eq, Finset.image_insert, Finset.image_singleton]
  · rintro ⟨t, ht, hts, hcomp, rfl⟩
    refine ⟨pair_centroid_mem_barycentricSubdivision_of_subset_or_subset G hs ht hcomp, ?_⟩
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _), fun h => ?_⟩
    have hmem : t.centroid ℝ id ∈ ({s.centroid ℝ id} : Finset E) := by
      rw [h]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    exact centroid_ne_centroid_of_ne G hs ht hts.symm (Finset.mem_singleton.mp hmem).symm

open Classical in
theorem derivedNeighborhoodCell_inter_space_eq_coneSet (K L : Geometry.SimplicialComplex ℝ E)
    (hL : L.faces ⊆ K.faces) (hG : ∀ f ∈ L.faces, f.card ≤ 2) {s : Finset E}
    (hs : s ∈ L.faces) :
    (derivedNeighborhoodCell K s).space ∩ L.space =
      coneSet (s.centroid ℝ id)
        {c | ∃ t ∈ L.faces, t ≠ s ∧ (s ⊆ t ∨ t ⊆ s) ∧
          c = ({s.centroid ℝ id, t.centroid ℝ id} : Finset E).centroid ℝ id} := by
  have hL' : (barycentricSubdivision L).faces ⊆ (barycentricSubdivision K).faces :=
    barycentricSubdivision_faces_subset hL
  have hcL : {s.centroid ℝ id} ∈ (barycentricSubdivision L).faces :=
    singleton_centroid_mem_barycentricSubdivision L hs
  rw [derivedNeighborhoodCell_space_eq_closedStar K (hL hs),
    ← (barycentricSubdivision_isSubdivision L).space_eq, secondDerived,
    closedStar_barycentricSubdivision_inter_space_eq hL' hcL,
    closedStar_barycentricSubdivision_eq_coneSet_of_card_le_two _
      (barycentricSubdivision_card_le_two L hG) hcL]
  congr 1
  ext c
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨e, he, hlt, rfl⟩
    obtain ⟨t, ht, hts, hcomp, rfl⟩ :=
      (mem_barycentricSubdivision_ssubset_singleton_centroid_iff L hG hs).mp ⟨he, hlt⟩
    exact ⟨t, ht, hts, hcomp, rfl⟩
  · rintro ⟨t, ht, hts, hcomp, rfl⟩
    have h := (mem_barycentricSubdivision_ssubset_singleton_centroid_iff L hG hs).mpr
      ⟨t, ht, hts, hcomp, rfl⟩
    exact ⟨_, h.1, h.2, rfl⟩

end DifferentialGeometry.Topology.PiecewiseLinear

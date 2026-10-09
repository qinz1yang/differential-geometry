/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryFacets
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleDeletion

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem mem_eraseTriangleComplex_edge_iff_not_mem_boundaryComplex
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K)
    {t e : Finset E} (ht : t ∈ K.faces) (htcard : t.card = 3)
    (het : e ⊆ t) (hecard : e.card = 2) :
    e ∈ (eraseTriangleComplex K t).faces ↔ e ∉ (boundaryComplex 2 K).faces := by
  classical
  have he : e ∈ K.faces := K.down_closed ht het (Finset.card_pos.mp (by omega))
  obtain ⟨v, hve, htv⟩ := Finset.exists_eq_insert_iff.mpr ⟨het, by omega⟩
  have hv : v ∉ e ∧ insert v e ∈ K.faces := ⟨hve, htv.symm ▸ ht⟩
  constructor
  · rintro ⟨u, hu, hucard, hut, heu, -⟩ hb
    obtain ⟨a, ha⟩ := (hK.mem_boundaryComplex_iff_unique_coface K hecard).mp hb
    obtain ⟨w, hwe, huw⟩ := Finset.exists_eq_insert_iff.mpr ⟨heu, by omega⟩
    have hva : v = a := by
      have : v ∈ {w | w ∉ e ∧ insert w e ∈ K.faces} := hv
      simpa only [ha, mem_singleton_iff] using this
    have hwa : w = a := by
      have : w ∈ {w | w ∉ e ∧ insert w e ∈ K.faces} := ⟨hwe, huw.symm ▸ hu⟩
      simpa only [ha, mem_singleton_iff] using this
    exact hut (huw.symm.trans ((congrArg (fun z => insert z e) (hwa.trans hva.symm)).trans htv))
  · intro hb
    rcases hK.codimension_one_cofaces K he hecard with ⟨a, ha⟩ | ⟨a, b, hab, habV⟩
    · exact (hb ((hK.mem_boundaryComplex_iff_unique_coface K hecard).mpr ⟨a, ha⟩)).elim
    · have hvab : v = a ∨ v = b := by
        have : v ∈ {w | w ∉ e ∧ insert w e ∈ K.faces} := hv
        simpa only [habV, mem_insert_iff, mem_singleton_iff] using this
      obtain ⟨w, hwab, hwv⟩ : ∃ w, (w = a ∨ w = b) ∧ w ≠ v := by
        rcases hvab with rfl | rfl
        · exact ⟨b, Or.inr rfl, hab.symm⟩
        · exact ⟨a, Or.inl rfl, hab⟩
      have hw : w ∉ e ∧ insert w e ∈ K.faces := by
        change w ∈ {w | w ∉ e ∧ insert w e ∈ K.faces}
        simpa only [habV, mem_insert_iff, mem_singleton_iff] using hwab
      refine ⟨insert w e, hw.2, by rw [Finset.card_insert_of_notMem hw.1, hecard], ?_,
        Finset.subset_insert _ _, K.nonempty_of_mem_faces he⟩
      intro heq
      exact hwv ((Finset.insert_inj hw.1).mp (heq.trans htv.symm))

omit [FiniteDimensional ℝ E] in
open Classical in
theorem mem_boundaryComplex_erase_iff_of_boundary_trace
    (K : Geometry.SimplicialComplex ℝ E)
    {t s : Finset E} (ht : t ∈ K.faces) (htcard : t.card = 3) (hst : s ⊆ t)
    (htrace : (boundaryComplex 2 K).space ∩ convexHull ℝ (t : Set E) =
      ⋃ w ∈ s, convexHull ℝ ((t.erase w : Finset E) : Set E))
    {v : E} (hv : v ∈ t) :
    t.erase v ∈ (boundaryComplex 2 K).faces ↔ v ∈ s := by
  classical
  have hcard : (t.erase v).card = 2 := by rw [Finset.card_erase_of_mem hv, htcard]
  have hne : (t.erase v).Nonempty := Finset.card_pos.mp (by omega)
  have heK : t.erase v ∈ K.faces := K.down_closed ht (Finset.erase_subset _ _) hne
  have hx := centroid_mem_openSimplex hne
  have hxt := convexHull_mono (Finset.coe_subset.mpr (Finset.erase_subset v t))
    (openSimplex_subset_convexHull _ hx)
  constructor
  · intro he
    have hmem : (t.erase v).centroid ℝ id ∈
        ⋃ w ∈ s, convexHull ℝ ((t.erase w : Finset E) : Set E) :=
      htrace ▸ ⟨(boundaryComplex 2 K).convexHull_subset_space he
        (openSimplex_subset_convexHull _ hx), hxt⟩
    obtain ⟨w, hw, hxw⟩ := mem_iUnion₂.mp hmem
    have hsub := subset_of_mem_openSimplex_of_mem_convexHull (K.indep ht)
      (Finset.erase_subset v t) (Finset.erase_subset w t) hx hxw
    have hwv : w = v := by
      by_contra hn
      exact Finset.notMem_erase w t (hsub (Finset.mem_erase.mpr ⟨hn, hst hw⟩))
    exact hwv ▸ hw
  · intro hvs
    have hxB : (t.erase v).centroid ℝ id ∈ (boundaryComplex 2 K).space := by
      have : (t.erase v).centroid ℝ id ∈
          (boundaryComplex 2 K).space ∩ convexHull ℝ (t : Set E) := by
        rw [htrace]
        exact mem_iUnion₂.mpr ⟨v, hvs, openSimplex_subset_convexHull _ hx⟩
      exact this.1
    by_contra hnot
    exact notMem_space_of_notMem_faces (boundaryComplex_faces_subset 2 K) heK hnot hx hxB

open Classical in
theorem mem_eraseTriangleComplex_iff_of_free_triangle
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 2 K.space)
    {t s : Finset E} (ht : t ∈ K.faces) (htcard : t.card = 3)
    (hst : s ⊆ t) (hscard : s.card = 1 ∨ s.card = 2)
    (htrace : (boundaryComplex 2 K).space ∩ convexHull ℝ (t : Set E) =
      ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset E) : Set E))
    (hinter : ∀ u ∈ K.faces, u.card = 3 → ¬s ⊆ u →
      (u ∩ t).card ≤ 1 ∧ (s.card = 2 → u ∩ t ⊆ s))
    {r : Finset E} :
    r ∈ (eraseTriangleComplex K t).faces ↔ r ∈ K.faces ∧ ¬t \ s ⊆ r := by
  classical
  have hedge (v : E) (hv : v ∈ t) (hvs : v ∉ s) :
      t.erase v ∈ (eraseTriangleComplex K t).faces :=
    (mem_eraseTriangleComplex_edge_iff_not_mem_boundaryComplex K
      hK.isCombinatorialManifoldWithBoundary ht htcard (Finset.erase_subset _ _)
      (by rw [Finset.card_erase_of_mem hv, htcard])).mpr
      (fun h => hvs ((mem_boundaryComplex_erase_iff_of_boundary_trace K ht htcard hst htrace hv).mp
          h))
  constructor
  · intro hr
    refine ⟨eraseTriangleComplex_faces_subset K t hr, ?_⟩
    intro hqr
    obtain ⟨u, hu, huc, hut, hru, -⟩ := hr
    have hqu : t \ s ⊆ u := hqr.trans hru
    by_cases hsu : s ⊆ u
    · have htu : t ⊆ u := by
        intro v hv
        by_cases hvs : v ∈ s
        · exact hsu hvs
        · exact hqu (Finset.mem_sdiff.mpr ⟨hv, hvs⟩)
      exact hut (Finset.eq_of_subset_of_card_le htu (by omega)).symm
    · have hi := hinter u hu huc hsu
      have hqint : t \ s ⊆ u ∩ t := fun v hv =>
        Finset.mem_inter.mpr ⟨hqu hv, (Finset.mem_sdiff.mp hv).1⟩
      rcases hscard with hsc | hsc
      · have hc := Finset.card_le_card hqint
        rw [Finset.card_sdiff_of_subset hst, htcard, hsc] at hc
        omega
      · obtain ⟨v, hv⟩ : (t \ s).Nonempty := Finset.card_pos.mp (by
          rw [Finset.card_sdiff_of_subset hst, htcard, hsc]; decide)
        exact (Finset.mem_sdiff.mp hv).2 (hi.2 hsc (hqint hv))
  · rintro ⟨hr, hnot⟩
    by_cases hrt : r ⊆ t
    · have hnr := hnot
      obtain ⟨v, hvq, hvr⟩ := Finset.not_subset.mp hnr
      have hv := Finset.mem_sdiff.mp hvq
      exact (eraseTriangleComplex K t).down_closed (hedge v hv.1 hv.2)
        (Finset.subset_erase.mpr ⟨hrt, hvr⟩) (K.nonempty_of_mem_faces hr)
    · obtain ⟨u, hu, hru, huc⟩ := exists_face_superset_card_eq_of_isPLBall K hK hr
      exact ⟨u, hu, huc, fun heq => hrt (heq ▸ hru), hru, K.nonempty_of_mem_faces hr⟩

end DifferentialGeometry.Topology.PiecewiseLinear

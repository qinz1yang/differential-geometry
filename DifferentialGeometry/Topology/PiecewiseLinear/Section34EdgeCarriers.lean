/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteSubdivisionEdgeEnds
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IncidentEdges

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}

omit [FiniteDimensional ℝ Ea] in
open Classical in
theorem exists_coarse_edge_of_section34_edge (hsub : IsSubdivision 𝒦'.complex 𝒦.complex)
    (hmap : 𝒦'.map = 𝒦.map) (e : Section34EdgeIndex 𝒦 𝒦') :
    ∃ E ∈ 𝒦.complex.faces, E.card = 2 ∧ Section34Incident e.1 E := by
  let Γ : Set Ea := ⋃ t ∈ {t : Finset Ea | t ∈ 𝒦.complex.faces ∧ t.card ≤ 2},
    convexHull ℝ (t : Set Ea)
  have hΓ (t : Finset Ea) (ht : t ∈ 𝒦.complex.faces) (hc : t.card ≤ 2) :
      convexHull ℝ (t : Set Ea) ⊆ Γ := fun x hx => mem_iUnion₂.mpr ⟨t, ⟨ht, hc⟩, hx⟩
  have hΓspace : (restrict 𝒦.complex Γ).space = Γ := by
    refine Subset.antisymm (restrict_space_subset _ _) ?_
    rintro x hx
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
    exact (restrict 𝒦.complex Γ).convexHull_subset_space ⟨ht.1, hΓ t ht.1 ht.2⟩ hxt
  have heΓ : convexHull ℝ (e.1 : Set Ea) ⊆ Γ := by
    intro x hx
    have hxg := e.2.2.2 ⟨x, hx, rfl⟩
    change 𝒦'.map x ∈ graphSkeletonSpace 𝒦 at hxg
    rw [hmap] at hxg
    obtain ⟨t, ht, y, hyt, hyx⟩ := mem_iUnion₂.mp hxg
    have hxy : y = x := 𝒦.bijOn.injOn (𝒦.complex.convexHull_subset_space ht.1 hyt)
      (hsub.space_eq ▸ 𝒦'.complex.convexHull_subset_space e.2.1 hx) hyx
    exact hxy ▸ hΓ t ht.1 ht.2 hyt
  have hg := hsub.restrict (restrict 𝒦.complex Γ) (restrict_faces_subset _ _)
  rw [hΓspace] at hg
  obtain ⟨E, hE, heE⟩ := hg.exists_face_subset ⟨e.2.1, heΓ⟩
  have hne := 𝒦.complex.nonempty_of_mem_faces hE.1
  obtain ⟨t, ht, hEt⟩ := mem_iUnion₂.mp
    (hE.2 (openSimplex_subset_convexHull E (centroid_mem_openSimplex hne)))
  have hEt' := face_subset_of_mem_openSimplex_of_mem_convexHull 𝒦.complex hE.1 ht.1
    (centroid_mem_openSimplex hne) hEt
  have hle := (𝒦'.complex.indep e.2.1).card_le_card_of_subset_affineSpan
    ((subset_convexHull ℝ _).trans (heE.trans (convexHull_subset_affineSpan _)))
  have hcard := (Finset.card_le_card hEt').trans ht.2
  refine ⟨E, hE.1, ?_, (subset_convexHull ℝ _).trans heE⟩
  rw [e.2.2.1] at hle
  omega

omit [FiniteDimensional ℝ Ea] in
open Classical in
theorem exists_unique_section34_edge_at_coarse_edge
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (w : Section34VertexIndex 𝒦 𝒦') {a : Ea} (hwa : w.1 = {a}) {E : Finset Ea}
    (hE : E ∈ 𝒦.complex.faces) (hcard : E.card = 2) (ha : a ∈ E) :
    ∃ e : Section34EdgeIndex 𝒦 𝒦', w.1 ⊆ e.1 ∧ Section34Incident e.1 E ∧
      ∀ d : Section34EdgeIndex 𝒦 𝒦', w.1 ⊆ d.1 → Section34Incident d.1 E → d = e := by
  have herase : (E.erase a).card = 1 := by rw [Finset.card_erase_of_mem ha, hcard]
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp herase
  have hbE : b ∈ E.erase a := hb.symm ▸ Finset.mem_singleton_self b
  have hab : a ≠ b := (Finset.mem_erase.mp hbE).1.symm
  have hEb : E = {a, b} := by rw [← Finset.insert_erase ha, hb]
  rw [hEb]
  have he : ({a, b} : Finset Ea) ∈ 𝒦.complex.faces := hEb ▸ hE
  obtain ⟨c, hca, hac, hc, huniq⟩ :=
    𝒦'.exists_unique_neighbor_in_segment hsub hab he (hwa ▸ w.2.1)
  have hacE : (({a, c} : Finset Ea) : Set Ea) ⊆
      convexHull ℝ (({a, b} : Finset Ea) : Set Ea) := by
    rw [Finset.coe_pair, Finset.coe_pair, convexHull_pair]
    exact insert_subset_iff.mpr ⟨left_mem_segment ℝ a b, singleton_subset_iff.mpr hc⟩
  let e : Section34EdgeIndex 𝒦 𝒦' :=
    ⟨{a, c}, hac, Finset.card_pair hca.symm, by
      rintro _ ⟨z, hz, rfl⟩
      rw [hmap]
      exact mem_iUnion₂.mpr ⟨{a, b}, ⟨he, Finset.card_le_two⟩,
        z, convexHull_min hacE (convex_convexHull ℝ _) hz, rfl⟩⟩
  refine ⟨e, ?_, hacE, fun d hwd hdE => ?_⟩
  · rw [hwa]
    exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self a {c})
  · have had : a ∈ d.1 := hwd (hwa.symm ▸ Finset.mem_singleton_self a)
    have hcard : (d.1.erase a).card = 1 := by rw [Finset.card_erase_of_mem had, d.2.2.1]
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
    have hze : z ∈ d.1.erase a := hz.symm ▸ Finset.mem_singleton_self z
    have hza : z ≠ a := (Finset.mem_erase.mp hze).1
    have hdz : d.1 = {a, z} := by rw [← Finset.insert_erase had, hz]
    have hzseg : z ∈ segment ℝ a b := by
      rw [← convexHull_pair, ← Finset.coe_pair]
      exact hdE (Finset.mem_erase.mp hze).2
    have hzc := huniq z hza (hdz ▸ d.2.1) hzseg
    apply Subtype.ext
    change d.1 = {a, c}
    rw [hdz, hzc]

omit [FiniteDimensional ℝ Ea] in
open Classical in
theorem exists_other_section34_face_of_edge_subset
    {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M}
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (s : Section34SimplexIndex 𝒦 3) {E : Finset Ea}
    (hEcard : E.card = 2) (hEs : E ⊆ s.1) :
    ∃ t : Section34SimplexIndex 𝒦 3, t ≠ s ∧ E ⊆ t.1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, htetra⟩ := hcut
  obtain ⟨T, hsT⟩ := htetra s
  have hsT' : s.1 ⊆ T.1 := fun x hx =>
    mem_of_mem_convexHull_of_singleton_mem 𝒦.complex
      (𝒦.complex.down_closed s.2.1 (Finset.singleton_subset_iff.mpr hx)
        (Finset.singleton_nonempty x)) T.2.1 (hsT hx)
  have hnot : ¬ T.1 ⊆ s.1 := by
    intro h
    have := Finset.card_le_card h
    rw [T.2.2, s.2.2] at this
    omega
  obtain ⟨a, haT, has⟩ := Finset.not_subset.mp hnot
  have haE : a ∉ E := fun ha => has (hEs ha)
  let t : Section34SimplexIndex 𝒦 3 :=
    ⟨insert a E, 𝒦.complex.down_closed T.2.1
      (Finset.insert_subset_iff.mpr ⟨haT, hEs.trans hsT'⟩) (Finset.insert_nonempty a E),
      by rw [Finset.card_insert_of_notMem haE, hEcard]⟩
  refine ⟨t, fun hts => has ?_, Finset.subset_insert a E⟩
  have ha : a ∈ t.1 := Finset.mem_insert_self a E
  rwa [hts] at ha

end DifferentialGeometry.Topology.PiecewiseLinear

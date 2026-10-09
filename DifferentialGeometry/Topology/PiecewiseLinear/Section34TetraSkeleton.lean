/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IncidentEdges
import DifferentialGeometry.Topology.PiecewiseLinear.SubdivisionEdgePath

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}

omit [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] in
private theorem subset_pair_of_card_le_two {v : Finset Ea} (hv : v.card ≤ 2) {x : Ea}
    (hx : x ∈ v) : ∃ y ∈ v, (v : Set Ea) ⊆ {x, y} := by
  classical
  by_cases h : ∃ y ∈ v, y ≠ x
  · obtain ⟨y, hy, hyx⟩ := h
    refine ⟨y, hy, fun z hz => ?_⟩
    have hsub : ({x, y} : Finset Ea) ⊆ v :=
      Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy)
    have heq : ({x, y} : Finset Ea) = v :=
      Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hyx.symm]; exact hv)
    rw [← heq] at hz
    simpa using hz
  · push Not at h
    refine ⟨x, hx, fun z hz => ?_⟩
    simp [h z hz]

theorem exists_mem_segment_of_mem_convexHull_of_map_mem_graphSkeleton
    {t : Finset Ea} (ht : t ∈ 𝒦.complex.faces) {p : Ea}
    (hpt : p ∈ convexHull ℝ (t : Set Ea)) (hpg : 𝒦.map p ∈ graphSkeletonSpace 𝒦) :
    ∃ x ∈ t, ∃ y ∈ t, p ∈ segment ℝ x y := by
  classical
  obtain ⟨v, ⟨hv, hvcard⟩, q, hqv, hqp⟩ := mem_iUnion₂.mp hpg
  have hqp' : q = p := 𝒦.bijOn.injOn (𝒦.complex.convexHull_subset_space hv hqv)
    (𝒦.complex.convexHull_subset_space ht hpt) hqp
  subst q
  have hp := 𝒦.complex.inter_subset_convexHull ht hv ⟨hpt, hqv⟩
  rw [← Finset.coe_inter] at hp
  obtain ⟨x, hx⟩ : (t ∩ v).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.coe_empty, convexHull_empty] at hp
    exact hp
  obtain ⟨y, hy, hsub⟩ := subset_pair_of_card_le_two
    ((Finset.card_le_card Finset.inter_subset_right).trans hvcard) hx
  refine ⟨x, Finset.mem_of_mem_inter_left hx, y, Finset.mem_of_mem_inter_left hy, ?_⟩
  rw [← convexHull_pair]
  exact convexHull_mono hsub hp

open Classical in
theorem map_mem_graphSkeletonSpace_of_mem_segment {x y p : Ea}
    (h : ({x, y} : Finset Ea) ∈ 𝒦.complex.faces) (hp : p ∈ segment ℝ x y) :
    𝒦.map p ∈ graphSkeletonSpace 𝒦 := by
  refine mem_iUnion₂.mpr ⟨{x, y}, ⟨h, Finset.card_le_two⟩, p, ?_, rfl⟩
  rwa [Finset.coe_pair, convexHull_pair]

theorem exists_section34VertexIndex_eq_singleton (hmap : 𝒦'.map = 𝒦.map) {p : Ea}
    (hp : ({p} : Finset Ea) ∈ 𝒦'.complex.faces) (hpg : 𝒦.map p ∈ graphSkeletonSpace 𝒦) :
    ∃ w : Section34VertexIndex 𝒦 𝒦', w.1 = {p} := by
  refine ⟨⟨{p}, hp, Finset.card_singleton p, ?_⟩, rfl⟩
  simpa only [simplexBody, Finset.coe_singleton, convexHull_singleton, image_singleton,
    singleton_subset_iff, hmap] using hpg

open Classical in
theorem exists_section34EdgeIndex_eq_pair (hmap : 𝒦'.map = 𝒦.map) {p q : Ea}
    (hpq : p ≠ q) (h : ({p, q} : Finset Ea) ∈ 𝒦'.complex.faces)
    (hg : ∀ z ∈ segment ℝ p q, 𝒦.map z ∈ graphSkeletonSpace 𝒦) :
    ∃ e : Section34EdgeIndex 𝒦 𝒦', e.1 = {p, q} := by
  refine ⟨⟨{p, q}, h, Finset.card_pair hpq, ?_⟩, rfl⟩
  rintro _ ⟨z, hz, rfl⟩
  rw [hmap]
  exact hg z (by simpa only [Finset.coe_pair, convexHull_pair] using hz)

theorem exists_segment_of_incident_section34EdgeIndex
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    {t : Finset Ea} (ht : t ∈ 𝒦.complex.faces) (e : Section34EdgeIndex 𝒦 𝒦')
    (he : Section34Incident e.1 t) :
    ∃ x ∈ t, ∃ y ∈ t, x ≠ y ∧ convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ x y := by
  classical
  have hne : e.1.Nonempty := Finset.card_pos.mp (by rw [e.2.2.1]; norm_num)
  have hm := centroid_mem_openSimplex hne
  have hmconv : e.1.centroid ℝ id ∈ convexHull ℝ (e.1 : Set Ea) :=
    openSimplex_subset_convexHull e.1 hm
  have hmg : 𝒦.map (e.1.centroid ℝ id) ∈ graphSkeletonSpace 𝒦 := by
    rw [← hmap]
    exact e.2.2.2 ⟨_, hmconv, rfl⟩
  obtain ⟨v, ⟨hv, hvcard⟩, q, hqv, hqm⟩ := mem_iUnion₂.mp hmg
  have hqm' : q = e.1.centroid ℝ id :=
    𝒦.bijOn.injOn (𝒦.complex.convexHull_subset_space hv hqv)
      (hsub.space_eq ▸ 𝒦'.complex.convexHull_subset_space e.2.1 hmconv) hqm
  subst q
  have hev : convexHull ℝ (e.1 : Set Ea) ⊆ convexHull ℝ (v : Set Ea) :=
    hsub.convexHull_subset_of_mem_openSimplex hv e.2.1 hm hqv
  have het : convexHull ℝ (e.1 : Set Ea) ⊆ convexHull ℝ (t : Set Ea) :=
    convexHull_min he (convex_convexHull ℝ _)
  have hevt : convexHull ℝ (e.1 : Set Ea) ⊆ convexHull ℝ ((v ∩ t : Finset Ea) : Set Ea) := by
    intro z hz
    have h := 𝒦.complex.inter_subset_convexHull hv ht ⟨hev hz, het hz⟩
    rwa [← Finset.coe_inter] at h
  obtain ⟨a, b, hab, hepair⟩ := Finset.card_eq_two.mp e.2.2.1
  have haconv : a ∈ convexHull ℝ ((v ∩ t : Finset Ea) : Set Ea) :=
    hevt (subset_convexHull ℝ _ (by rw [hepair]; simp))
  have hbconv : b ∈ convexHull ℝ ((v ∩ t : Finset Ea) : Set Ea) :=
    hevt (subset_convexHull ℝ _ (by rw [hepair]; simp))
  obtain ⟨x, hx⟩ : (v ∩ t).Nonempty := by
    by_contra hne'
    rw [Finset.not_nonempty_iff_eq_empty] at hne'
    rw [hne', Finset.coe_empty, convexHull_empty] at haconv
    exact haconv
  obtain ⟨y, hy, hsubxy⟩ := subset_pair_of_card_le_two
    ((Finset.card_le_card Finset.inter_subset_left).trans hvcard) hx
  have hconv : convexHull ℝ ((v ∩ t : Finset Ea) : Set Ea) ⊆ segment ℝ x y := by
    rw [← convexHull_pair]
    exact convexHull_mono hsubxy
  refine ⟨x, Finset.mem_of_mem_inter_right hx, y, Finset.mem_of_mem_inter_right hy, ?_,
    hevt.trans hconv⟩
  rintro rfl
  have ha := hconv haconv
  have hb := hconv hbconv
  rw [segment_same] at ha hb
  exact hab ((mem_singleton_iff.mp ha).trans (mem_singleton_iff.mp hb).symm)

open Classical in
theorem LocallyFinitePLPieceIn.exists_path_of_edge
    (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U) (hsub : IsSubdivision 𝒦'.complex 𝒦.complex)
    {x y : Ea} (hxy : x ≠ y) (hxyK : ({x, y} : Finset Ea) ∈ 𝒦.complex.faces) :
    ∃ (n : ℕ) (c : ℕ → ℝ), 0 < n ∧ c 0 = 0 ∧ c n = 1 ∧ StrictMonoOn c (Iic n) ∧
      (∀ i ≤ n, ({AffineMap.lineMap x y (c i)} : Finset Ea) ∈ 𝒦'.complex.faces) ∧
      (∀ i < n, ({AffineMap.lineMap x y (c i), AffineMap.lineMap x y (c (i + 1))} : Finset Ea) ∈
        𝒦'.complex.faces) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ({AffineMap.lineMap x y t} : Finset Ea) ∈ 𝒦'.complex.faces →
        ∃ i ≤ n, c i = t) ∧
      ∀ σ ∈ 𝒦'.complex.faces, convexHull ℝ (σ : Set Ea) ⊆ segment ℝ x y → σ.card = 2 →
        ∃ i < n, σ = {AffineMap.lineMap x y (c i), AffineMap.lineMap x y (c (i + 1))} := by
  classical
  let L := simplexComplex ({x, y} : Finset Ea) (𝒦.complex.indep hxyK)
  have hLsub : L.faces ⊆ 𝒦.complex.faces :=
    fun σ hσ => 𝒦.complex.down_closed hxyK hσ.2 hσ.1
  have hLspace : L.space = segment ℝ x y := by
    rw [simplexComplex_space _ _ (Finset.insert_nonempty _ _), Finset.coe_pair, convexHull_pair]
  let J := restrict 𝒦'.complex L.space
  have hJsub : IsSubdivision J L := hsub.restrict L hLsub
  have hsegK : segment ℝ x y ⊆ 𝒦'.complex.space := by
    rw [hsub.space_eq, ← hLspace]
    exact space_mono_of_faces_subset hLsub
  have hsegC : IsCompact (segment ℝ x y) := by
    rw [← convexHull_pair, ← Finset.coe_pair]
    exact ({x, y} : Finset Ea).finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have hJfin : J.faces.Finite := by
    refine (𝒦'.finite_faces_inter_of_isCompact hsegC hsegK).subset ?_
    rintro σ ⟨hσ, hσL⟩
    obtain ⟨q, hq⟩ := 𝒦'.complex.nonempty_of_mem_faces hσ
    refine ⟨hσ, q, subset_convexHull ℝ _ (Finset.mem_coe.mpr hq), ?_⟩
    rw [← hLspace]
    exact hσL (subset_convexHull ℝ _ (Finset.mem_coe.mpr hq))
  have hxyL : ({x, y} : Finset Ea) ∈ L.faces := ⟨Finset.insert_nonempty _ _, le_rfl⟩
  obtain ⟨n, c, hn, hc0, hcn, hmono, hvert, hedge, hsurj, hσedge⟩ :=
    hJsub.exists_path_of_edge hJfin hxy hxyL
  refine ⟨n, c, hn, hc0, hcn, hmono, fun i hi => (hvert i hi).1,
    fun i hi => (hedge i hi).1, ?_, ?_⟩
  · intro t ht htv
    apply hsurj t ht
    refine ⟨htv, ?_⟩
    rw [Finset.coe_singleton, convexHull_singleton, singleton_subset_iff, hLspace]
    exact (segment_eq_image_lineMap ℝ x y).symm ▸ ⟨t, ht, rfl⟩
  · intro σ hσ hσseg hσcard
    exact hσedge σ ⟨hσ, hLspace.symm ▸ hσseg⟩ hσseg hσcard

end DifferentialGeometry.Topology.PiecewiseLinear

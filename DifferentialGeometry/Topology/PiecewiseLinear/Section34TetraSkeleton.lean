import DifferentialGeometry.Topology.Combinatorics.Finset
import DifferentialGeometry.Topology.PiecewiseLinear.Subdivision.EdgePath
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IncidentEdges
import DifferentialGeometry.Topology.PiecewiseLinear.SubdivisionEdgePath

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}

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
  obtain ⟨y, hy, hsub⟩ := Finset.exists_mem_subset_pair_of_card_le_two
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
  obtain ⟨y, hy, hsubxy⟩ := Finset.exists_mem_subset_pair_of_card_le_two
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

end DifferentialGeometry.Topology.PiecewiseLinear

/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactIncidentEdges
import DifferentialGeometry.Topology.PiecewiseLinear.SubdivisionEdgePath

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K K' : Geometry.SimplicialComplex ℝ E3}

theorem exists_subset_pair_of_card_le_two {v : Finset E3} (hv : v.card ≤ 2) {x : E3}
    (hx : x ∈ v) : ∃ y ∈ v, (v : Set E3) ⊆ {x, y} := by
  classical
  by_cases h : ∃ y ∈ v, y ≠ x
  · obtain ⟨y, hy, hyx⟩ := h
    refine ⟨y, hy, fun z hz => ?_⟩
    have hsub : ({x, y} : Finset E3) ⊆ v :=
      Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy)
    have heq : ({x, y} : Finset E3) = v :=
      Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hyx.symm]; exact hv)
    rw [← heq] at hz
    simpa using hz
  · push Not at h
    refine ⟨x, hx, fun z hz => ?_⟩
    simp [h z hz]

theorem exists_mem_segment_of_mem_convexHull_graphSkeleton {t : Finset E3} (ht : t ∈ K.faces)
    {p : E3} (hpt : p ∈ convexHull ℝ (t : Set E3)) (hpg : p ∈ section34CompactGraphSkeleton K) :
    ∃ x ∈ t, ∃ y ∈ t, p ∈ segment ℝ x y := by
  classical
  obtain ⟨u, ⟨hu, hucard⟩, hpu⟩ := mem_iUnion₂.mp hpg
  have hp := K.inter_subset_convexHull ht hu ⟨hpt, hpu⟩
  rw [← Finset.coe_inter] at hp
  obtain ⟨x, hx⟩ : (t ∩ u).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.coe_empty, convexHull_empty] at hp
    exact hp
  obtain ⟨y, hy, hsub⟩ := exists_subset_pair_of_card_le_two
    ((Finset.card_le_card Finset.inter_subset_right).trans hucard) hx
  refine ⟨x, Finset.mem_of_mem_inter_left hx, y, Finset.mem_of_mem_inter_left hy, ?_⟩
  rw [← convexHull_pair]
  exact convexHull_mono hsub hp

theorem segment_subset_section34CompactGraphSkeleton {x y : E3}
    (h : ({x, y} : Finset E3) ∈ K.faces) :
    segment ℝ x y ⊆ section34CompactGraphSkeleton K := by
  intro p hp
  refine mem_iUnion₂.mpr ⟨{x, y}, ⟨h, Finset.card_le_two⟩, ?_⟩
  rw [Finset.coe_pair, convexHull_pair]
  exact hp

theorem exists_section34CompactVertexIndex_eq_singleton {p : E3}
    (hp : ({p} : Finset E3) ∈ K'.faces) (hpg : p ∈ section34CompactGraphSkeleton K) :
    ∃ w : Section34CompactVertexIndex K K', w.1 = {p} := by
  refine ⟨⟨{p}, hp, Finset.card_singleton p, ?_⟩, rfl⟩
  rw [Finset.coe_singleton, convexHull_singleton]
  exact singleton_subset_iff.mpr hpg

theorem exists_section34CompactEdgeIndex_eq_pair {p q : E3} (hpq : p ≠ q)
    (h : ({p, q} : Finset E3) ∈ K'.faces) (hg : segment ℝ p q ⊆ section34CompactGraphSkeleton K) :
    ∃ e : Section34CompactEdgeIndex K K', e.1 = {p, q} := by
  refine ⟨⟨{p, q}, h, Finset.card_pair hpq, ?_⟩, rfl⟩
  rw [Finset.coe_pair, convexHull_pair]
  exact hg

theorem segment_inter_segment_subset_of_mem_faces {x y u v : E3}
    (hxy : ({x, y} : Finset E3) ∈ K.faces) (huv : ({u, v} : Finset E3) ∈ K.faces) :
    segment ℝ x y ∩ segment ℝ u v ⊆ convexHull ℝ (({x, y} : Set E3) ∩ {u, v}) := by
  have h := K.inter_subset_convexHull hxy huv
  rwa [Finset.coe_pair, Finset.coe_pair, convexHull_pair, convexHull_pair] at h

theorem exists_segment_of_incident_section34CompactEdgeIndex (hsub : IsSubdivision K' K)
    {t : Finset E3} (ht : t ∈ K.faces) (e : Section34CompactEdgeIndex K K')
    (he : Section34Incident e.1 t) :
    ∃ x ∈ t, ∃ y ∈ t, x ≠ y ∧ convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ x y := by
  classical
  have hne : e.1.Nonempty := Finset.card_pos.mp (by rw [e.2.2.1]; norm_num)
  have hm := centroid_mem_openSimplex hne
  have hmconv : e.1.centroid ℝ id ∈ convexHull ℝ (e.1 : Set E3) :=
    openSimplex_subset_convexHull e.1 hm
  obtain ⟨u, ⟨hu, hucard⟩, hmu⟩ := mem_iUnion₂.mp (e.2.2.2 hmconv)
  have heu : convexHull ℝ (e.1 : Set E3) ⊆ convexHull ℝ (u : Set E3) :=
    hsub.convexHull_subset_of_mem_openSimplex hu e.2.1 hm hmu
  have het : convexHull ℝ (e.1 : Set E3) ⊆ convexHull ℝ (t : Set E3) :=
    convexHull_min he (convex_convexHull ℝ _)
  have heut : convexHull ℝ (e.1 : Set E3) ⊆ convexHull ℝ ((u ∩ t : Finset E3) : Set E3) := by
    intro z hz
    have h := K.inter_subset_convexHull hu ht ⟨heu hz, het hz⟩
    rwa [← Finset.coe_inter] at h
  obtain ⟨a, b, hab, hepair⟩ := Finset.card_eq_two.mp e.2.2.1
  have haconv : a ∈ convexHull ℝ ((u ∩ t : Finset E3) : Set E3) :=
    heut (subset_convexHull ℝ _ (by rw [hepair]; simp))
  have hbconv : b ∈ convexHull ℝ ((u ∩ t : Finset E3) : Set E3) :=
    heut (subset_convexHull ℝ _ (by rw [hepair]; simp))
  obtain ⟨x, hx⟩ : (u ∩ t).Nonempty := by
    by_contra hne'
    rw [Finset.not_nonempty_iff_eq_empty] at hne'
    rw [hne', Finset.coe_empty, convexHull_empty] at haconv
    exact haconv
  obtain ⟨y, hy, hsubxy⟩ := exists_subset_pair_of_card_le_two
    ((Finset.card_le_card Finset.inter_subset_left).trans hucard) hx
  have hconv : convexHull ℝ ((u ∩ t : Finset E3) : Set E3) ⊆ segment ℝ x y := by
    rw [← convexHull_pair]
    exact convexHull_mono hsubxy
  refine ⟨x, Finset.mem_of_mem_inter_right hx, y, Finset.mem_of_mem_inter_right hy, ?_,
    heut.trans hconv⟩
  rintro rfl
  have ha := hconv haconv
  have hb := hconv hbconv
  rw [segment_same] at ha hb
  exact hab ((mem_singleton_iff.mp ha).trans (mem_singleton_iff.mp hb).symm)

end DifferentialGeometry.Topology.PiecewiseLinear

/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactGraphApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.SubdivisionEdgeEnds

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K K' : Geometry.SimplicialComplex ℝ E3}

theorem exists_coarse_edge_of_compact_edge (hsub : IsSubdivision K' K)
    (e : Section34CompactEdgeIndex K K') :
    ∃ E ∈ K.faces, E.card = 2 ∧ Section34Incident e.1 E := by
  have hg := hsub.restrict (restrict K (section34CompactGraphSkeleton K))
    (restrict_faces_subset K _)
  rw [restrict_section34CompactGraphSkeleton_space] at hg
  obtain ⟨E, hE, heE⟩ := hg.exists_face_subset ⟨e.2.1, e.2.2.2⟩
  have hle := (K'.indep e.2.1).card_le_card_of_subset_affineSpan
    ((subset_convexHull ℝ _).trans (heE.trans (convexHull_subset_affineSpan _)))
  have hcard := card_le_two_of_mem_restrict_section34CompactGraphSkeleton hE
  refine ⟨E, hE.1, ?_, (subset_convexHull ℝ _).trans heE⟩
  rw [e.2.2.1] at hle
  omega

theorem exists_unique_compact_edge_at_coarse_edge (hsub : IsSubdivision K' K)
    (hK' : K'.faces.Finite) (w : Section34CompactVertexIndex K K')
    {a : E3} (hwa : w.1 = {a}) {E : Finset E3} (hE : E ∈ K.faces)
    (hcard : E.card = 2) (ha : a ∈ E) :
    ∃ e : Section34CompactEdgeIndex K K', w.1 ⊆ e.1 ∧ Section34Incident e.1 E ∧
      ∀ d : Section34CompactEdgeIndex K K', w.1 ⊆ d.1 → Section34Incident d.1 E → d = e := by
  classical
  have herase : (E.erase a).card = 1 := by rw [Finset.card_erase_of_mem ha, hcard]
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp herase
  have hbE : b ∈ E.erase a := hb.symm ▸ Finset.mem_singleton_self b
  have hab : a ≠ b := (Finset.mem_erase.mp hbE).1.symm
  have hEb : E = {a, b} := by rw [← Finset.insert_erase ha, hb]
  rw [hEb]
  have he : ({a, b} : Finset E3) ∈ K.faces := hEb ▸ hE
  have : Finite K'.faces := hK'.to_subtype
  obtain ⟨c, hca, hac, hc, huniq⟩ := hsub.exists_unique_neighbor_in_segment hab he (hwa ▸ w.2.1)
  have hEΓ := convexHull_subset_section34CompactGraphSkeleton he Finset.card_le_two
  have hacE : (({a, c} : Finset E3) : Set E3) ⊆ convexHull ℝ (({a, b} : Finset E3) : Set E3) := by
    rw [Finset.coe_pair, Finset.coe_pair, convexHull_pair]
    exact insert_subset_iff.mpr ⟨left_mem_segment ℝ a b, singleton_subset_iff.mpr hc⟩
  let e : Section34CompactEdgeIndex K K' :=
    ⟨{a, c}, hac, Finset.card_pair hca.symm,
      (convexHull_min hacE (convex_convexHull ℝ _)).trans hEΓ⟩
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

theorem exists_other_face_of_edge_subset
    {C : Set E3} {src srcBd : Section34CompactLabelOf K K' → Set E3}
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (s : Section34CompactSimplexIndex K 3) {E : Finset E3}
    (hEcard : E.card = 2) (hEs : E ⊆ s.1) :
    ∃ t : Section34CompactSimplexIndex K 3, t ≠ s ∧ E ⊆ t.1 := by
  classical
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    htetra⟩ := hcut
  obtain ⟨T, hsT⟩ := htetra s
  have hsT' : s.1 ⊆ T.1 := fun x hx =>
    mem_of_mem_convexHull_of_singleton_mem K
      (K.down_closed s.2.1 (Finset.singleton_subset_iff.mpr hx) (Finset.singleton_nonempty x))
      T.2.1 (hsT hx)
  have hnot : ¬ T.1 ⊆ s.1 := by
    intro h
    have := Finset.card_le_card h
    rw [T.2.2, s.2.2] at this
    omega
  obtain ⟨a, haT, has⟩ := Finset.not_subset.mp hnot
  have haE : a ∉ E := fun ha => has (hEs ha)
  let t : Section34CompactSimplexIndex K 3 :=
    ⟨insert a E, K.down_closed T.2.1
      (Finset.insert_subset_iff.mpr ⟨haT, hEs.trans hsT'⟩) (Finset.insert_nonempty a E),
      by rw [Finset.card_insert_of_notMem haE, hEcard]⟩
  refine ⟨t, fun hts => has ?_, Finset.subset_insert a E⟩
  have ha : a ∈ t.1 := Finset.mem_insert_self a E
  rwa [hts] at ha

end DifferentialGeometry.Topology.PiecewiseLinear

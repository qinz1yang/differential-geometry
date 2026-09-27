/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactEdgeCarriers

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K K' : Geometry.SimplicialComplex ℝ E3}

theorem coarse_edge_subset_of_incident_compact_edge (e : Section34CompactEdgeIndex K K')
    {E F : Finset E3} (hE : E ∈ K.faces) (hF : F ∈ K.faces) (hEcard : E.card = 2)
    (heE : Section34Incident e.1 E) (heF : Section34Incident e.1 F) : E ⊆ F := by
  classical
  have hsub : (e.1 : Set E3) ⊆ affineSpan ℝ ((E ∩ F : Finset E3) : Set E3) := by
    intro x hx
    apply convexHull_subset_affineSpan _
    rw [Finset.coe_inter]
    exact K.inter_subset_convexHull hE hF ⟨heE hx, heF hx⟩
  have hcard := (K'.indep e.2.1).card_le_card_of_subset_affineSpan hsub
  rw [e.2.2.1] at hcard
  have hleft : E ∩ F = E := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
    rw [hEcard]
    exact hcard)
  exact Finset.inter_eq_left.mp hleft

theorem coarse_edges_eq_of_compact_edge (e : Section34CompactEdgeIndex K K')
    {E F : Finset E3} (hE : E ∈ K.faces) (hF : F ∈ K.faces)
    (hEcard : E.card = 2) (hFcard : F.card = 2)
    (heE : Section34Incident e.1 E) (heF : Section34Incident e.1 F) : E = F :=
  Finset.eq_of_subset_of_card_le
    (coarse_edge_subset_of_incident_compact_edge e hE hF hEcard heE heF)
    (by rw [hEcard, hFcard])

theorem exists_coarse_edge_at_subdivision_vertex (hsub : IsSubdivision K' K)
    (w : Section34CompactVertexIndex K K') {v : E3} (hwv : w.1 = {v}) (hv : {v} ∉ K.faces)
    (e : Section34CompactEdgeIndex K K') (hwe : w.1 ⊆ e.1) :
    ∃ E ∈ K.faces, E.card = 2 ∧ v ∈ openSimplex E ∧
      ∀ d : Section34CompactEdgeIndex K K', w.1 ⊆ d.1 → Section34Incident d.1 E := by
  classical
  obtain ⟨E, hE, hEcard, heE⟩ := exists_coarse_edge_of_compact_edge hsub e
  have hvw : v ∈ w.1 := hwv.symm ▸ Finset.mem_singleton_self v
  obtain ⟨σ, hσ, hvσ⟩ := exists_face_mem_openSimplex K
    (K.convexHull_subset_space hE (heE (hwe hvw)))
  have hσE := face_subset_of_mem_openSimplex_of_mem_convexHull K hσ hE hvσ (heE (hwe hvw))
  have hσcard : σ.card = 2 := by
    have hle : σ.card ≤ 2 := hEcard ▸ Finset.card_le_card hσE
    have hpos := Finset.card_pos.mpr (K.nonempty_of_mem_faces hσ)
    have hne : σ.card ≠ 1 := by
      intro h1
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
      have hva : v = a := by
        have hvc := openSimplex_subset_convexHull σ hvσ
        simpa only [ha, Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] using hvc
      exact hv (by simpa only [ha, hva] using hσ)
    omega
  refine ⟨σ, hσ, hσcard, hvσ, fun d hwd => ?_⟩
  obtain ⟨D, hD, hDcard, hdD⟩ := exists_coarse_edge_of_compact_edge hsub d
  have hσD := face_subset_of_mem_openSimplex_of_mem_convexHull K hσ hD hvσ (hdD (hwd hvw))
  have heq : σ = D := Finset.eq_of_subset_of_card_le hσD (by rw [hσcard, hDcard])
  rwa [← heq] at hdD
theorem exists_compact_edge_parametrization_of_vertex_link [DecidableEq E3]
    (hsub : IsSubdivision K' K) (hK' : K'.faces.Finite)
    (w : Section34CompactVertexIndex K K') {v : E3} (hwv : w.1 = {v})
    (hv : ({v} : Finset E3) ∈ K.faces) :
    ∃ f : (SimplicialComplex.geometricLink K {v}).vertices → Section34CompactEdgeIndex K K',
      (∀ x, w.1 ⊆ (f x).1) ∧
      (∀ x, Section34Incident (f x).1 {v, (x : E3)}) ∧ Function.Injective f ∧
      ∀ e : Section34CompactEdgeIndex K K', w.1 ⊆ e.1 → ∃ x, f x = e := by
  classical
  let L := SimplicialComplex.geometricLink K {v}
  have hneighbor : ∀ x : L.vertices, (x : E3) ≠ v ∧ ({v, (x : E3)} : Finset E3) ∈ K.faces := by
    intro x
    obtain ⟨-, hvx, hpair⟩ :=
      (SimplicialComplex.mem_geometricLink_singleton K v {(x : E3)}).mp x.2
    exact ⟨fun h => hvx (by simp [h]), by simpa using hpair⟩
  choose f hfw hfE hfuniq using fun x : L.vertices =>
    exists_unique_compact_edge_at_coarse_edge hsub hK' w hwv
      (hneighbor x).2 (Finset.card_pair (hneighbor x).1.symm) (by simp)
  refine ⟨f, hfw, hfE, ?_, ?_⟩
  · intro x y hxy
    have heq := coarse_edges_eq_of_compact_edge (f x) (hneighbor x).2 (hneighbor y).2
      (Finset.card_pair (hneighbor x).1.symm) (Finset.card_pair (hneighbor y).1.symm)
      (hfE x) (by rw [hxy]; exact hfE y)
    have hset : ({v, (x : E3)} : Set E3) = {v, (y : E3)} := by
      simpa only [Finset.coe_pair] using congrArg (fun z : Finset E3 => (z : Set E3)) heq
    rcases Set.pair_eq_pair_iff.mp hset with ⟨-, hxy⟩ | ⟨hvy, -⟩
    · exact Subtype.ext hxy
    · exact ((hneighbor y).1 hvy.symm).elim
  · intro e hwe
    obtain ⟨E, hE, hEcard, heE⟩ := exists_coarse_edge_of_compact_edge hsub e
    have hvE : v ∈ E := mem_of_mem_convexHull_of_singleton_mem K hv hE
      (heE (hwe (hwv.symm ▸ Finset.mem_singleton_self v)))
    have hcard : (E.erase v).card = 1 := by rw [Finset.card_erase_of_mem hvE, hEcard]
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
    have hAE : a ∈ E.erase v := ha.symm ▸ Finset.mem_singleton_self a
    have hEa : E = {v, a} := by rw [← Finset.insert_erase hvE, ha]
    have haL : ({a} : Finset E3) ∈ L.faces := by
      apply (SimplicialComplex.mem_geometricLink_singleton K v {a}).mpr
      refine ⟨by simp, ?_, ?_⟩
      · simpa only [Finset.mem_singleton] using (Finset.mem_erase.mp hAE).1.symm
      · simpa only [hEa] using hE
    exact ⟨⟨a, haL⟩, (hfuniq ⟨a, haL⟩ e hwe (by rwa [← hEa])).symm⟩

end DifferentialGeometry.Topology.PiecewiseLinear

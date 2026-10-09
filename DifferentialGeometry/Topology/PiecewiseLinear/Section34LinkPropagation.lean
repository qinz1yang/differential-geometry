/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LinkGraphConnectivity
import DifferentialGeometry.Topology.PiecewiseLinear.Section34EdgeCarriers

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M} {α : Type*}

omit [FiniteDimensional ℝ Ea] in
private theorem section34_incident_edges_share_other_face
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦')
    (hws : Section34Incident w.1 s.1) {v : Ea} (hwv : w.1 = {v}) (hv : {v} ∉ 𝒦.complex.faces)
    {e : Section34EdgeIndex 𝒦 𝒦'} (hwe : w.1 ⊆ e.1) :
    ∃ t : Section34SimplexIndex 𝒦 3, t ≠ s ∧
      ∀ d : Section34EdgeIndex 𝒦 𝒦', w.1 ⊆ d.1 → Section34Incident d.1 t.1 := by
  classical
  have hsub := hcut.2.1
  have hmap := hcut.2.2.1
  obtain ⟨E, hE, hEcard, heE⟩ := exists_coarse_edge_of_section34_edge hsub hmap e
  have hvw : v ∈ w.1 := hwv.symm ▸ Finset.mem_singleton_self v
  obtain ⟨σ, hσ, hvσ⟩ := exists_face_mem_openSimplex 𝒦.complex
    (𝒦.complex.convexHull_subset_space hE (heE (hwe hvw)))
  have hσE := face_subset_of_mem_openSimplex_of_mem_convexHull 𝒦.complex hσ hE hvσ (heE (hwe hvw))
  have hσcard : σ.card = 2 := by
    have hle : σ.card ≤ 2 := hEcard ▸ Finset.card_le_card hσE
    have hpos := Finset.card_pos.mpr (𝒦.complex.nonempty_of_mem_faces hσ)
    have hne : σ.card ≠ 1 := by
      intro h1
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
      have hva : v = a := by
        have hvc := openSimplex_subset_convexHull σ hvσ
        simpa only [ha, Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] using hvc
      exact hv (by simpa only [ha, hva] using hσ)
    omega
  have hσs := face_subset_of_mem_openSimplex_of_mem_convexHull 𝒦.complex hσ s.2.1 hvσ (hws hvw)
  obtain ⟨t, hts, hσt⟩ := exists_other_section34_face_of_edge_subset hcut s hσcard hσs
  refine ⟨t, hts, fun d hwd => ?_⟩
  obtain ⟨D, hD, hDcard, hdD⟩ := exists_coarse_edge_of_section34_edge hsub hmap d
  have hσD := face_subset_of_mem_openSimplex_of_mem_convexHull 𝒦.complex hσ hD hvσ (hdD (hwd hvw))
  have heq : σ = D := Finset.eq_of_subset_of_card_le hσD (by rw [hσcard, hDcard])
  rw [← heq] at hdD
  exact hdD.trans (convexHull_mono (Finset.coe_subset.mpr hσt))

theorem Section34CutFrame.eq_on_incident_edges_of_eq_on_other_faces
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦')
    (hws : Section34Incident w.1 s.1) (c : Section34EdgeIndex 𝒦 𝒦' → α)
    (hface : ∀ t : Section34SimplexIndex 𝒦 3, t ≠ s →
      ∀ e d : Section34EdgeIndex 𝒦 𝒦', w.1 ⊆ e.1 → w.1 ⊆ d.1 →
        Section34Incident e.1 t.1 → Section34Incident d.1 t.1 → c e = c d) :
    ∀ e d : Section34EdgeIndex 𝒦 𝒦', w.1 ⊆ e.1 → w.1 ⊆ d.1 → c e = c d := by
  classical
  let _ : DecidableEq Ea := fun a b => Classical.propDecidable (a = b)
  obtain ⟨v, hwv⟩ := Finset.card_eq_one.mp w.2.2.1
  by_cases hv : ({v} : Finset Ea) ∈ 𝒦.complex.faces
  swap
  · intro e d hwe hwd
    obtain ⟨t, hts, ht⟩ :=
      section34_incident_edges_share_other_face hcut s w hws hwv hv hwe
    exact hface t hts e d hwe hwd (ht e hwe) (ht d hwd)
  obtain ⟨hKm, hsub, hmap, -⟩ := id hcut
  let L := SimplicialComplex.geometricLink 𝒦.complex {v}
  have : Finite L.faces := (𝒦.geometricLink_faces_finite hv).to_subtype
  have hL : IsCombinatorialManifoldWithBoundary 2 L ∧ IsConnected L.space := by
    have hS := hKm v hv
    exact ⟨hS.isCombinatorialManifold.isCombinatorialManifoldWithBoundary, hS.isConnected⟩
  have hneighbor : ∀ x : L.vertices, (x : Ea) ≠ v ∧
      ({v, (x : Ea)} : Finset Ea) ∈ 𝒦.complex.faces := by
    intro x
    obtain ⟨-, hvx, hpair⟩ :=
      (SimplicialComplex.mem_geometricLink_singleton 𝒦.complex v {(x : Ea)}).mp x.2
    exact ⟨fun h => hvx (by simp [h]), by simpa using hpair⟩
  choose f hfw hfE hfuniq using fun x : L.vertices =>
    exists_unique_section34_edge_at_coarse_edge hsub hmap w hwv
      (hneighbor x).2 (Finset.card_pair (hneighbor x).1.symm) (by simp)
  have hsurj : ∀ e : Section34EdgeIndex 𝒦 𝒦', w.1 ⊆ e.1 → ∃ x, e = f x := by
    intro e hwe
    obtain ⟨E, hE, hEcard, heE⟩ := exists_coarse_edge_of_section34_edge hsub hmap e
    have hvE : v ∈ E := mem_of_mem_convexHull_of_singleton_mem 𝒦.complex hv hE
      (heE (hwe (hwv.symm ▸ Finset.mem_singleton_self v)))
    have hcard : (E.erase v).card = 1 := by rw [Finset.card_erase_of_mem hvE, hEcard]
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
    have hAE : a ∈ E.erase v := ha.symm ▸ Finset.mem_singleton_self a
    have hEa : E = {v, a} := by rw [← Finset.insert_erase hvE, ha]
    have haL : ({a} : Finset Ea) ∈ L.faces := by
      apply (SimplicialComplex.mem_geometricLink_singleton 𝒦.complex v {a}).mpr
      refine ⟨by simp, ?_, ?_⟩
      · simpa only [Finset.mem_singleton] using (Finset.mem_erase.mp hAE).1.symm
      · simpa only [hEa] using hE
    exact ⟨⟨a, haL⟩, hfuniq ⟨a, haL⟩ e hwe (by rwa [← hEa])⟩
  have hvs : v ∈ s.1 := mem_of_mem_convexHull_of_singleton_mem 𝒦.complex hv s.2.1
    (hws (hwv.symm ▸ Finset.mem_singleton_self v))
  have hcard : (s.1.erase v).card = 2 := by rw [Finset.card_erase_of_mem hvs, s.2.2]
  obtain ⟨a, b, hab, hsab⟩ := Finset.card_eq_two.mp hcard
  have habL : ({a, b} : Finset Ea) ∈ L.faces := by
    apply (SimplicialComplex.mem_geometricLink_singleton 𝒦.complex v {a, b}).mpr
    refine ⟨by simp, ?_, ?_⟩
    · rw [← hsab]
      exact Finset.notMem_erase v s.1
    · rw [← hsab, Finset.insert_erase hvs]
      exact s.2.1
  let a' : L.vertices := ⟨a, L.down_closed habL (by simp) (Finset.singleton_nonempty a)⟩
  let b' : L.vertices := ⟨b, L.down_closed habL (by simp) (Finset.singleton_nonempty b)⟩
  have habG : (SimplicialComplex.edgeGraph L).Adj a' b' :=
    ⟨fun h => hab (congrArg Subtype.val h), habL⟩
  let G := (SimplicialComplex.edgeGraph L).deleteEdges {s(a', b')}
  have hG : G.Connected :=
    edgeGraph_connected_delete_edge_of_isCombinatorialManifoldWithBoundary L hL.1 hL.2 habG
  have hstep : ∀ p q : L.vertices, G.Adj p q → c (f p) = c (f q) := by
    intro p q hpq
    rw [SimpleGraph.deleteEdges_adj] at hpq
    have hpq' : (p : Ea) ≠ (q : Ea) := fun h => hpq.1.1 (Subtype.ext h)
    obtain ⟨-, hvpq, htri⟩ :=
      (SimplicialComplex.mem_geometricLink_singleton 𝒦.complex v {(p : Ea), (q : Ea)}).mp hpq.1.2
    let t : Section34SimplexIndex 𝒦 3 :=
      ⟨insert v {(p : Ea), (q : Ea)}, htri,
        by rw [Finset.card_insert_of_notMem hvpq, Finset.card_pair hpq']⟩
    have hts : t ≠ s := by
      intro hts
      have heq := congrArg (fun z : Finset Ea => z.erase v) (congrArg Subtype.val hts)
      change (insert v ({(p : Ea), (q : Ea)} : Finset Ea)).erase v = s.1.erase v at heq
      rw [Finset.erase_insert hvpq, hsab] at heq
      have hset : ({(p : Ea), (q : Ea)} : Set Ea) = {a, b} := by
        simpa only [Finset.coe_pair] using congrArg (fun z : Finset Ea => (z : Set Ea)) heq
      apply hpq.2
      rw [mem_singleton_iff, Sym2.eq_iff]
      rcases Set.pair_eq_pair_iff.mp hset with ⟨hpa, hqb⟩ | ⟨hpb, hqa⟩
      · exact Or.inl ⟨Subtype.ext hpa, Subtype.ext hqb⟩
      · exact Or.inr ⟨Subtype.ext hpb, Subtype.ext hqa⟩
    apply hface t hts (f p) (f q) (hfw p) (hfw q)
    · refine (hfE p).trans (convexHull_mono ?_)
      rw [Finset.coe_pair]
      exact insert_subset_iff.mpr ⟨by simp [t], singleton_subset_iff.mpr (by simp [t])⟩
    · refine (hfE q).trans (convexHull_mono ?_)
      rw [Finset.coe_pair]
      exact insert_subset_iff.mpr ⟨by simp [t], singleton_subset_iff.mpr (by simp [t])⟩
  have hpath : ∀ p q : L.vertices, G.Reachable p q → c (f p) = c (f q) := by
    intro p q ⟨path⟩
    induction path with
    | nil => rfl
    | @cons p r q hpr path ih => exact (hstep p r hpr).trans ih
  intro e d hwe hwd
  obtain ⟨p, rfl⟩ := hsurj e hwe
  obtain ⟨q, rfl⟩ := hsurj d hwd
  exact hpath p q (hG.preconnected p q)

end DifferentialGeometry.Topology.PiecewiseLinear

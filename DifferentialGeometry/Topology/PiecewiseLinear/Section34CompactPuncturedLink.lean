/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LinkGraphConnectivity
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldConnectivity
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactIncidentEdges
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactVertexLink

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {α : Type*}

theorem Section34CompactCutFrame.eq_on_other_edges_of_eq_on_faces_avoiding_edge
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (w : Section34CompactVertexIndex K K') (e₀ : Section34CompactEdgeIndex K K')
    (hwe₀ : w.1 ⊆ e₀.1) (c : Section34CompactEdgeIndex K K' → α)
    (hface : ∀ t : Section34CompactSimplexIndex K 3, ¬ Section34Incident e₀.1 t.1 →
      ∀ e d : Section34CompactEdgeIndex K K', w.1 ⊆ e.1 → w.1 ⊆ d.1 →
        Section34Incident e.1 t.1 → Section34Incident d.1 t.1 → c e = c d) :
    ∀ e d : Section34CompactEdgeIndex K K', w.1 ⊆ e.1 → w.1 ⊆ d.1 →
      e ≠ e₀ → d ≠ e₀ → c e = c d := by
  classical
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  obtain ⟨-, hKfin, hK'fin, hKm, hsub, -⟩ := id hcut
  have : Finite K.faces := hKfin.to_subtype
  obtain ⟨v, hwv⟩ := Finset.card_eq_one.mp w.2.2.1
  by_cases hv : ({v} : Finset E3) ∈ K.faces
  swap
  · obtain ⟨E, hE, hEcard, -, hEd⟩ := exists_coarse_edge_at_subdivision_vertex hsub w hwv hv e₀ hwe₀
    obtain ⟨T, hT, hET, hTcard⟩ := hKm.exists_face_superset_card_eq hE
    have hnot : ¬ T ⊆ E := by
      intro h
      have := Finset.card_le_card h
      rw [hTcard, hEcard] at this
      omega
    obtain ⟨a, haT, haE⟩ := Finset.not_subset.mp hnot
    let t : Section34CompactSimplexIndex K 3 :=
      ⟨insert a E, K.down_closed hT (Finset.insert_subset_iff.mpr ⟨haT, hET⟩)
        (Finset.insert_nonempty a E), by rw [Finset.card_insert_of_notMem haE, hEcard]⟩
    have hall : ∀ e : Section34CompactEdgeIndex K K', w.1 ⊆ e.1 →
        Section34Incident e.1 t.1 := fun e hwe => (hEd e hwe).trans
          (convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert a E)))
    have hwt : Section34Incident w.1 t.1 := (Finset.coe_subset.mpr hwe₀).trans (hall e₀ hwe₀)
    obtain ⟨e₁, e₂, -, -, -, -, -, honly⟩ :=
      exists_section34CompactEdgeIndex_pair_of_incident hsub hK'fin t w hwt
    intro e d hwe hwd he₀ hd₀
    rcases honly e₀ (hall e₀ hwe₀) hwe₀ with h₀ | h₀
    · have he₂ : e = e₂ := (honly e (hall e hwe) hwe).resolve_left
        (fun he₁ => he₀ (he₁.trans h₀.symm))
      have hd₂ : d = e₂ := (honly d (hall d hwd) hwd).resolve_left
        (fun hd₁ => hd₀ (hd₁.trans h₀.symm))
      exact congrArg c (he₂.trans hd₂.symm)
    · have he₁ : e = e₁ := (honly e (hall e hwe) hwe).resolve_right
        (fun he₂ => he₀ (he₂.trans h₀.symm))
      have hd₁ : d = e₁ := (honly d (hall d hwd) hwd).resolve_right
        (fun hd₂ => hd₀ (hd₂.trans h₀.symm))
      exact congrArg c (he₁.trans hd₁.symm)
  let L := SimplicialComplex.geometricLink K {v}
  have : Finite L.faces := (hKfin.subset (geometricLink_faces_subset K {v})).to_subtype
  have hL : IsCombinatorialManifoldWithBoundary 2 L ∧ IsConnected L.space := by
    rcases hKm v hv with hS | hB
    · exact ⟨hS.isCombinatorialManifold.isCombinatorialManifoldWithBoundary, hS.isConnected⟩
    · exact ⟨hB.isCombinatorialManifoldWithBoundary, hB.isConnected⟩
  obtain ⟨f, hfw, hfE, -, hsurj⟩ :=
    exists_compact_edge_parametrization_of_vertex_link hsub hK'fin w hwv hv
  obtain ⟨z, hz⟩ := hsurj e₀ hwe₀
  have hneighbor : ∀ x : L.vertices, (x : E3) ≠ v ∧ ({v, (x : E3)} : Finset E3) ∈ K.faces := by
    intro x
    obtain ⟨-, hvx, hpair⟩ :=
      (SimplicialComplex.mem_geometricLink_singleton K v {(x : E3)}).mp x.2
    exact ⟨fun h => hvx (by simp [h]), by simpa using hpair⟩
  let G := (SimplicialComplex.edgeGraph L).induce {x : L.vertices | x ≠ z}
  have hG : G.Connected :=
    edgeGraph_connected_delete_vertex_of_isCombinatorialManifoldWithBoundary L hL.1 hL.2
  have hstep : ∀ p q : {x : L.vertices // x ≠ z}, G.Adj p q → c (f p.1) = c (f q.1) := by
    intro p q hpq
    have hadj : (SimplicialComplex.edgeGraph L).Adj p.1 q.1 := hpq
    have hpq' : (p.1 : E3) ≠ (q.1 : E3) := fun h => hadj.1 (Subtype.ext h)
    obtain ⟨-, hvpq, htri⟩ :=
      (SimplicialComplex.mem_geometricLink_singleton K v {(p.1 : E3), (q.1 : E3)}).mp hadj.2
    let t : Section34CompactSimplexIndex K 3 :=
      ⟨insert v {(p.1 : E3), (q.1 : E3)}, htri,
        by rw [Finset.card_insert_of_notMem hvpq, Finset.card_pair hpq']⟩
    have hnot : ¬ Section34Incident e₀.1 t.1 := by
      intro he₀t
      have hzt := coarse_edge_subset_of_incident_compact_edge e₀ (hneighbor z).2 htri
        (Finset.card_pair (hneighbor z).1.symm) (by rw [← hz]; exact hfE z) he₀t
      have hzmem := hzt (Finset.mem_insert_of_mem (Finset.mem_singleton_self (z : E3)))
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzmem
      rcases hzmem with hzv | hzp | hzq
      · exact (hneighbor z).1 hzv
      · exact p.2 (Subtype.ext hzp.symm)
      · exact q.2 (Subtype.ext hzq.symm)
    apply hface t hnot (f p.1) (f q.1) (hfw p.1) (hfw q.1)
    · refine (hfE p.1).trans (convexHull_mono ?_)
      rw [Finset.coe_pair]
      exact insert_subset_iff.mpr ⟨by simp [t], singleton_subset_iff.mpr (by simp [t])⟩
    · refine (hfE q.1).trans (convexHull_mono ?_)
      rw [Finset.coe_pair]
      exact insert_subset_iff.mpr ⟨by simp [t], singleton_subset_iff.mpr (by simp [t])⟩
  have hpath : ∀ p q : {x : L.vertices // x ≠ z}, G.Reachable p q → c (f p.1) = c (f q.1) := by
    intro p q ⟨path⟩
    induction path with
    | nil => rfl
    | @cons p r q hpr path ih => exact (hstep p r hpr).trans ih
  intro e d hwe hwd he₀ hd₀
  obtain ⟨p, hp⟩ := hsurj e hwe
  obtain ⟨q, hq⟩ := hsurj d hwd
  have hpz : p ≠ z := fun h => he₀ (hp.symm.trans ((congrArg f h).trans hz))
  have hqz : q ≠ z := fun h => hd₀ (hq.symm.trans ((congrArg f h).trans hz))
  have h := hpath ⟨p, hpz⟩ ⟨q, hqz⟩ (hG.preconnected _ _)
  simpa only [hp, hq] using h

end DifferentialGeometry.Topology.PiecewiseLinear

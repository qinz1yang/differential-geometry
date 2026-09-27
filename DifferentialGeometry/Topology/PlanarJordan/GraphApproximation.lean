/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PlanarJordan.GraphStraightening
import DifferentialGeometry.Topology.PlanarJordan.GraphSubdivision

open Set Schoenflies
open DifferentialGeometry.Topology.PlanarJordan DifferentialGeometry.Topology.PiecewiseLinear
open scoped Graph

namespace Graph

theorem IsDrawing.exists_homeomorph_polygonal_edges_dist_lt_const
    {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} [G.Finite]
    (h : IsDrawing G drawing) {ε : ℝ} (hε : 0 < ε)
    {U : Set Plane} (hU : IsOpen U) (hGU : pointSet G drawing ⊆ U) :
    ∃ e : Plane ≃ₜ Plane, (∀ d ∈ E(G), IsPolygonal (e '' edgeArc drawing d)) ∧
      EqOn e id V(G) ∧ EqOn e id Uᶜ ∧ ∀ x, dist (e x) x < ε := by
  obtain ⟨n, hn, hdiam⟩ := h.exists_subdivisionDrawing_diam_lt (show 0 < ε / 8 by positivity)
  let f := subdivisionDrawing G drawing n
  let H := curveGraph f V(G)
  let _ : H.Finite := finite_curveGraph f (finite_vertexSet (G := G))
  have hH : IsDrawing H f := h.subdivision n
  have hpoint : pointSet H f = pointSet G drawing := pointSet_subdivisionDrawing hn
  obtain ⟨e, hpoly, hfixV, hfixU, hdist⟩ := hH.exists_homeomorph_polygonal_edges_of_diam_lt hε
    (fun d _ => hdiam d) hU (hpoint ▸ hGU)
  refine ⟨e, ?_, ?_, hfixU, hdist⟩
  · intro d hd
    have hP : IsPolyhedron (e '' edgeArc drawing d) := by
      rw [edgeArc_eq_iUnion_subdivisionDrawing hn ⟨d, hd⟩, image_iUnion]
      apply IsPolyhedron.iUnion
      intro i
      have hi : (⟨⟨d, hd⟩, i⟩ : Σ d : E(G), Fin (n d)) ∈ E(H) := mem_univ _
      exact (isPLBall_one_of_isArcBetween_of_isPolygonal
        (isArcBetween_image e (hH.edge_isArcBetween (hH.edge_param hi).2.2)) (hpoly _
            hi)).isPolyhedron
    exact hP.isPolygonal_of_isArcBetween
      (isArcBetween_image e (h.edge_isArcBetween (h.edge_param hd).2.2))
  · exact hfixV.mono (fun _ hx => Or.inl (Or.inl hx))

theorem IsDrawing.exists_homeomorph_polygonal_edges_dist_lt
    {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} [G.Finite]
    (h : IsDrawing G drawing) {U : Set Plane} (hU : IsOpen U) (hGU : pointSet G drawing ⊆ U)
    {ε : Plane → ℝ}
    (hε : ∀ K : Set Plane, IsCompact K → K ⊆ U → ∃ c > 0, ∀ x ∈ K, c ≤ ε x) :
    ∃ e : Plane ≃ₜ Plane, (∀ d ∈ E(G), IsPolygonal (e '' edgeArc drawing d)) ∧
      EqOn e id V(G) ∧ EqOn e id Uᶜ ∧ ∀ x ∈ U, dist (e x) x < ε x := by
  obtain ⟨K, hK, hGK, hKU⟩ := exists_compact_between h.isCompact_pointSet hU hGU
  obtain ⟨c, hc, hbound⟩ := hε K hK hKU
  obtain ⟨e, hpoly, hfixV, hfixK, hdist⟩ :=
    h.exists_homeomorph_polygonal_edges_dist_lt_const hc isOpen_interior hGK
  refine ⟨e, hpoly, hfixV,
    hfixK.mono (compl_subset_compl.mpr (interior_subset.trans hKU)), ?_⟩
  intro x hxU
  by_cases hx : x ∈ interior K
  · exact (hdist x).trans_le (hbound x (interior_subset hx))
  · rw [hfixK hx, id_eq, dist_self]
    obtain ⟨a, ha, hax⟩ := hε {x} isCompact_singleton (singleton_subset_iff.mpr hxU)
    exact ha.trans_le (hax x (mem_singleton x))

theorem IsDrawing.exists_homeomorph_polygonal_edges_dist_lt_of_continuous
    {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} [G.Finite]
    (h : IsDrawing G drawing) {ε : Plane → ℝ} (hε : Continuous ε) (hεpos : ∀ x, 0 < ε x)
    {U : Set Plane} (hU : IsOpen U) (hGU : pointSet G drawing ⊆ U) :
    ∃ e : Plane ≃ₜ Plane, (∀ d ∈ E(G), IsPolygonal (e '' edgeArc drawing d)) ∧
      EqOn e id V(G) ∧ EqOn e id Uᶜ ∧ ∀ x, dist (e x) x < ε x := by
  obtain ⟨e, hpoly, hfixV, hfixU, hdist⟩ := h.exists_homeomorph_polygonal_edges_dist_lt hU hGU
    (fun K hK _ => hK.exists_forall_le' hε.continuousOn (fun x _ => hεpos x))
  refine ⟨e, hpoly, hfixV, hfixU, fun x => ?_⟩
  by_cases hx : x ∈ U
  · exact hdist x hx
  · rw [hfixU hx, id_eq, dist_self]
    exact hεpos x

end Graph

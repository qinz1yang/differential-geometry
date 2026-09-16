import DifferentialGeometry.Topology.PlanarJordan.EndpointAccess
import DifferentialGeometry.Topology.PlanarJordan.VertexFan

open Set Topology

namespace DifferentialGeometry.Topology.PlanarJordan

open Schoenflies

theorem exists_homeomorph_radial_initial_arc
    {A : Set Plane} {v w : Plane} (hA : IsArcBetween A v w)
    {N : Set Plane} (hN : N ∈ 𝓝 v) :
    ∃ (r : ℝ) (B : Set Plane) (p : Plane) (e : Plane ≃ₜ Plane),
      0 < r ∧ Plane.closedSquare v r ⊆ N ∧ B ⊆ A ∧ IsArcBetween B v p ∧
      p ∈ frontier (Plane.closedSquare v r) ∧ B \ {p} ⊆ Plane.openSquare v r ∧
      e '' B = segment ℝ v p ∧ e v = v ∧ EqOn e id (Plane.openSquare v r)ᶜ ∧
      ∀ x, dist (e x) x ≤ Metric.diam (Plane.closedSquare v r) := by
  obtain ⟨C, z, hC, _, hCA⟩ := hA.exists_isArcBetween_inter_eq_singleton (U := univ) Filter.univ_mem
  have hZ : IsClosed ({w, z} : Set Plane) := ((finite_singleton z).insert w).isClosed
  have hvZ : v ∉ ({w, z} : Set Plane) := by
    rintro (hv | hv)
    · exact hA.ne hv
    · exact hC.ne hv
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem hN (hZ.isOpen_compl.mem_nhds hvZ))
  let r := ρ / 2
  have hr : 0 < r := half_pos hρ
  have hsub : Plane.closedSquare v r ⊆ N \ {w, z} :=
    (Plane.closedSquare_subset_ball hρ).trans hball
  have hv : v ∈ Plane.openSquare v r := by
    change Plane.supDist v v < r
    simpa only [Plane.supDist_self] using hr
  have hw : w ∉ Plane.openSquare v r := fun hx =>
    (hsub (Plane.openSquare_subset_closedSquare _ _ hx)).2 (Or.inl rfl)
  have hz : z ∉ Plane.openSquare v r := fun hx =>
    (hsub (Plane.openSquare_subset_closedSquare _ _ hx)).2 (Or.inr rfl)
  obtain ⟨B, hBA, p, hp, hB, hBI⟩ :=
    exists_initial_arc_to_frontier hA (Plane.isOpen_openSquare _ _) hv hw
  obtain ⟨D, hDC, q, hq, hD, hDI⟩ :=
    exists_initial_arc_to_frontier hC (Plane.isOpen_openSquare _ _) hv hz
  have hmeet : ∀ x ∈ B, x ∈ D → x = v :=
    fun x hx hy => hCA.subset ⟨hDC hy, hBA hx⟩
  have hp' := Plane.frontier_openSquare_subset _ _ hp
  have hq' := Plane.frontier_openSquare_subset _ _ hq
  obtain ⟨e, heB, _, hev, hefix, hedist⟩ :=
    exists_homeomorph_image_two_vertex_arcs_radial hr hp' hq' hB hD hmeet hBI hDI
  exact ⟨r, B, p, e, hr, hsub.trans sdiff_subset, hBA, hB, hp', hBI, heB, hev, hefix, hedist⟩

end DifferentialGeometry.Topology.PlanarJordan

namespace Graph

open Schoenflies DifferentialGeometry.Topology.PlanarJordan
open scoped Graph

theorem IsDrawing.exists_homeomorph_radial_vertex_fan_of_nonempty
    {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} [G.Finite]
    (h : IsDrawing G drawing) {v : Plane} (hincident : (G.incidenceSet v).Nonempty)
    {N : Set Plane} (hN : N ∈ 𝓝 v) :
    ∃ r > 0, Plane.closedSquare v r ⊆ N ∧
      (∀ d ∈ E(G), ¬ G.Inc d v →
        Disjoint (Plane.closedSquare v r) (edgeArc drawing d)) ∧
      ∃ (A : {d // G.Inc d v} → Set Plane) (p : {d // G.Inc d v} → Plane)
        (e : Plane ≃ₜ Plane),
        (∀ d, A d ⊆ edgeArc drawing d ∧ IsArcBetween (A d) v (p d) ∧
          p d ∈ frontier (Plane.closedSquare v r) ∧ A d \ {p d} ⊆ Plane.openSquare v r) ∧
        (∀ d, e '' A d = segment ℝ v (p d)) ∧ e v = v ∧
        EqOn e id (Plane.openSquare v r)ᶜ ∧
        ∀ x, dist (e x) x ≤ Metric.diam (Plane.closedSquare v r) := by
  by_cases htwo : (G.incidenceSet v).Nontrivial
  · exact h.exists_homeomorph_radial_vertex_fan htwo hN
  have hsingle : (G.incidenceSet v).Subsingleton := not_nontrivial_iff.mp htwo
  obtain ⟨a, ha⟩ := hincident
  obtain ⟨w, hw⟩ := ha
  obtain ⟨R, hR, hRN, havoid, _, _, _, _, _⟩ :=
    h.exists_vertex_arcs_in_square hw.left_mem hN
  have hcenter : Plane.openSquare v R ∈ 𝓝 v :=
    (Plane.isOpen_openSquare v R).mem_nhds (by
      change Plane.supDist v v < R
      simpa only [Plane.supDist_self] using hR)
  obtain ⟨r, B, p, e, hr, hsub, hBA, hB, hp, hBI, heB, hev, hefix, hedist⟩ :=
    exists_homeomorph_radial_initial_arc (h.edge_isArcBetween hw) hcenter
  have hsmall : Plane.closedSquare v r ⊆ Plane.closedSquare v R :=
    hsub.trans (Plane.openSquare_subset_closedSquare _ _)
  refine ⟨r, hr, hsmall.trans hRN, fun d hd hnot => (havoid d hd hnot).mono_left hsmall,
    (fun _ => B), (fun _ => p), e, ?_, fun _ => heB, hev, hefix, hedist⟩
  intro d
  have hda : d.1 = a := hsingle d.2 hw.inc_left
  exact ⟨by simpa only [hda] using hBA, hB, hp, hBI⟩

end Graph

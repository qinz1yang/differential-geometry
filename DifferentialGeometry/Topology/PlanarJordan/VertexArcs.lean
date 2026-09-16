import DifferentialGeometry.External.Schoenflies.Graph.VertexSquares
import DifferentialGeometry.External.Schoenflies.Subarc

open Set

namespace DifferentialGeometry.Topology.PlanarJordan

open Schoenflies

theorem exists_initial_arc_to_frontier {A U : Set Plane} {p q : Plane}
    (hA : IsArcBetween A p q) (hU : IsOpen U) (hp : p ∈ U) (hq : q ∉ U) :
    ∃ B ⊆ A, ∃ r ∈ frontier U, IsArcBetween B p r ∧ B \ {r} ⊆ U := by
  obtain ⟨f, hf, hi, himage, hzero, hone⟩ := hA
  obtain ⟨t, ht, _, htU, hbefore⟩ := exists_first_mem hf hU.isClosed_compl
    one_mem_I (show f 1 ∈ Uᶜ by simpa only [hone, mem_compl_iff] using hq)
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (by
    intro heq
    apply htU
    simpa only [← heq, hzero] using hp)
  have hinitial : ∀ s ∈ Ico (0 : ℝ) t, f s ∈ U := by
    intro s hs
    exact not_not.mp (hbefore s ⟨hs.1, hs.2.le.trans ht.2⟩ hs.2)
  have hclosure : f t ∈ closure U := by
    apply ((hf t ht).mono (show Ico (0 : ℝ) t ⊆ Icc 0 1 from
      fun s hs => ⟨hs.1, hs.2.le.trans ht.2⟩)).mem_closure
    · rw [closure_Ico htpos.ne]
      exact ⟨htpos.le, le_rfl⟩
    · exact hinitial
  have hfrontier : f t ∈ frontier U := by
    rw [hU.frontier_eq]
    exact ⟨hclosure, htU⟩
  refine ⟨f '' Icc 0 t, ?_, f t, hfrontier, ?_, ?_⟩
  · rw [← himage]
    exact image_mono (Icc_subset_Icc le_rfl ht.2)
  · simpa only [uIcc_of_le htpos.le, hzero] using
      isArcBetween_subarc_of_injOn_I hf hi zero_mem_I ht htpos.ne
  · rintro x ⟨⟨s, hs, rfl⟩, hx⟩
    apply hinitial s
    refine ⟨hs.1, lt_of_le_of_ne hs.2 ?_⟩
    rintro rfl
    exact hx rfl

end DifferentialGeometry.Topology.PlanarJordan

namespace Graph

open Schoenflies DifferentialGeometry.Topology.PlanarJordan
open scoped Graph

theorem IsDrawing.exists_vertex_arcs {β : Type*} {G : Graph Plane β}
    {drawing : β → ℝ → Plane} (h : IsDrawing G drawing) {v : Plane} {U : Set Plane}
    (hU : IsOpen U) (hv : v ∈ U) (hvertices : closure U ∩ V(G) ⊆ {v}) :
    ∃ (A : {e // G.Inc e v} → Set Plane) (p : {e // G.Inc e v} → Plane),
      (∀ e, A e ⊆ edgeArc drawing e ∧ IsArcBetween (A e) v (p e) ∧
        p e ∈ frontier U ∧ A e \ {p e} ⊆ U) ∧
      (∀ e f, e ≠ f → A e ∩ A f = {v}) ∧ Function.Injective p := by
  classical
  have hex : ∀ e : {e // G.Inc e v}, ∃ A ⊆ edgeArc drawing e,
      ∃ p ∈ frontier U, IsArcBetween A v p ∧ A \ {p} ⊆ U := by
    intro e
    obtain ⟨w, hw⟩ := e.property
    have harc := h.edge_isArcBetween hw
    have hvw : v ≠ w := by
      obtain ⟨f, _, hi, _, hf0, hf1⟩ := harc
      intro heq
      exact zero_ne_one (hi zero_mem_I one_mem_I (hf0.trans (heq.trans hf1.symm)))
    have hwU : w ∉ U := by
      intro hwU
      exact hvw (hvertices ⟨subset_closure hwU, hw.right_mem⟩).symm
    exact exists_initial_arc_to_frontier harc hU hv hwU
  choose A hsub p hfront harc hinside using hex
  have hAcl : ∀ e, A e ⊆ closure U := by
    intro e x hx
    by_cases hxp : x = p e
    · subst x
      exact frontier_subset_closure (hfront e)
    · exact subset_closure (hinside e ⟨hx, hxp⟩)
  have hmeet : ∀ e f, e ≠ f → A e ∩ A f = {v} := by
    intro e f hef
    apply Subset.antisymm
    · intro x hx
      exact hvertices ⟨hAcl e hx.1,
        h.arcs_meet_at_vertex e.property.edge_mem f.property.edge_mem
          (fun heq => hef (Subtype.ext heq)) (hsub e hx.1) (hsub f hx.2)⟩
    · exact singleton_subset_iff.mpr ⟨(harc e).left_mem, (harc f).left_mem⟩
  refine ⟨A, p, fun e => ⟨hsub e, harc e, hfront e, hinside e⟩, hmeet, ?_⟩
  intro e f heq
  by_contra hef
  have hpe : p e = v := (hmeet e f hef).subset
    ⟨(harc e).right_mem, heq.symm ▸ (harc f).right_mem⟩
  have hpU : p e ∉ U := by
    have hpfront := hfront e
    rw [hU.frontier_eq] at hpfront
    exact hpfront.2
  exact hpU (hpe ▸ hv)

theorem IsDrawing.exists_vertex_arcs_in_square {β : Type*} {G : Graph Plane β}
    {drawing : β → ℝ → Plane} [G.Finite] (h : IsDrawing G drawing)
    {v : Plane} (hv : v ∈ V(G)) {N : Set Plane} (hN : N ∈ nhds v) :
    ∃ r > 0, Plane.closedSquare v r ⊆ N ∧
      (∀ e ∈ E(G), ¬ G.Inc e v →
        Disjoint (Plane.closedSquare v r) (edgeArc drawing e)) ∧
      ∃ (A : {e // G.Inc e v} → Set Plane) (p : {e // G.Inc e v} → Plane),
        (∀ e, A e ⊆ edgeArc drawing e ∧ IsArcBetween (A e) v (p e) ∧
          p e ∈ frontier (Plane.openSquare v r) ∧
          A e \ {p e} ⊆ Plane.openSquare v r) ∧
        (∀ e f, e ≠ f → A e ∩ A f = {v}) ∧ Function.Injective p := by
  obtain ⟨r₀, hr₀, hvertices, hedges⟩ := h.exists_square_at hv
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hN
  let r := min r₀ (ρ / 2)
  have hr : 0 < r := lt_min hr₀ (half_pos hρ)
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  have hrρ : r ≤ ρ / 2 := min_le_right _ _
  have hcl : closure (Plane.openSquare v r) ⊆ Plane.closedSquare v r :=
    (Plane.isClosed_closedSquare v r).closure_subset_iff.mpr (by
      intro x hx
      change Plane.supDist x v ≤ r
      exact le_of_lt hx)
  refine ⟨r, hr, ?_, ?_, ?_⟩
  · exact (Plane.closedSquare_mono_center v hrρ).trans
      ((Plane.closedSquare_subset_ball hρ).trans hball)
  · intro e he hinc
    exact (hedges e he hinc).mono_left (Plane.closedSquare_mono_center v hrr₀)
  · apply h.exists_vertex_arcs (Plane.isOpen_openSquare v r)
    · change Plane.supDist v v < r
      simpa only [Plane.supDist_self] using hr
    · intro x hx
      by_contra hxv
      exact hvertices x hx.2 hxv (Plane.closedSquare_mono_center v hrr₀ (hcl hx.1))

end Graph

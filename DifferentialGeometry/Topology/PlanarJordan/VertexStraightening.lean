import DifferentialGeometry.Topology.PlanarJordan.EndpointStraightening
import DifferentialGeometry.Topology.Homeomorph.DisjointGluing

open Set Topology

namespace Graph

open Schoenflies
open scoped Graph

theorem IsDrawing.exists_homeomorph_radial_vertex_fans
    {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} [G.Finite]
    (h : IsDrawing G drawing) (s : Finset Plane)
    (hs : ∀ v ∈ s, (G.incidenceSet v).Nonempty)
    {U : Set Plane} (hU : IsOpen U) (hsU : (s : Set Plane) ⊆ U)
    {ε : Plane → ℝ} (hε : Continuous ε) (hεpos : ∀ x, 0 < ε x) :
    ∃ (r : {v // v ∈ s} → ℝ)
      (A : (v : {v // v ∈ s}) → {d // G.Inc d v.1} → Set Plane)
      (p : (v : {v // v ∈ s}) → {d // G.Inc d v.1} → Plane) (e : Plane ≃ₜ Plane),
      (∀ v, 0 < r v ∧ Plane.closedSquare v.1 (r v) ⊆ U) ∧
      (Pairwise fun v w => Disjoint (Plane.closedSquare v.1 (r v))
        (Plane.closedSquare w.1 (r w))) ∧
      (∀ v, ∀ d ∈ E(G), ¬ G.Inc d v.1 →
        Disjoint (Plane.closedSquare v.1 (r v)) (edgeArc drawing d)) ∧
      (∀ v d, A v d ⊆ edgeArc drawing d ∧ IsArcBetween (A v d) v.1 (p v d) ∧
        p v d ∈ frontier (Plane.closedSquare v.1 (r v)) ∧
        A v d \ {p v d} ⊆ Plane.openSquare v.1 (r v)) ∧
      (∀ v d, e '' A v d = segment ℝ v.1 (p v d)) ∧
      EqOn e id V(G) ∧ EqOn e id Uᶜ ∧ ∀ x, dist (e x) x < ε x := by
  classical
  let I := {v // v ∈ s}
  have hv (v : I) : v.1 ∈ V(G) := by
    obtain ⟨a, ha⟩ := hs v.1 v.2
    exact ha.vertex_mem
  obtain ⟨R, hR, hvertices, _, hdis⟩ := h.exists_vertexSquares
  let N (v : I) : Set Plane := U ∩ (Plane.openSquare v.1 R ∩
    (Metric.ball v.1 (ε v.1 / 4) ∩ {x | ε v.1 / 2 < ε x}))
  have hN (v : I) : N v ∈ 𝓝 v.1 := by
    have hsquare : Plane.openSquare v.1 R ∈ 𝓝 v.1 :=
      (Plane.isOpen_openSquare v.1 R).mem_nhds (by
        change Plane.supDist v.1 v.1 < R
        simpa only [Plane.supDist_self] using hR)
    have hcontrol : {x | ε v.1 / 2 < ε x} ∈ 𝓝 v.1 :=
      (isOpen_lt continuous_const hε).mem_nhds (by
        change ε v.1 / 2 < ε v.1
        linarith [hεpos v.1])
    exact Filter.inter_mem (hU.mem_nhds (hsU v.2)) (Filter.inter_mem hsquare
      (Filter.inter_mem (Metric.ball_mem_nhds _ (div_pos (hεpos v.1) (by norm_num))) hcontrol))
  have hlocal (v : I) := h.exists_homeomorph_radial_vertex_fan_of_nonempty (hs v.1 v.2) (hN v)
  choose r hr hsub hedge A p f hA hf hfv hfix hdist using hlocal
  let C (v : I) := Plane.closedSquare v.1 (r v)
  have hCR (v : I) : C v ⊆ Plane.closedSquare v.1 R := fun x hx =>
    Plane.openSquare_subset_closedSquare _ _ (hsub v hx).2.1
  have hCU (v : I) : C v ⊆ U := fun x hx => (hsub v hx).1
  have hCC : Pairwise fun v w => Disjoint (C v) (C w) := by
    intro v w hvw
    exact (hdis v.1 (hv v) w.1 (hv w) (fun heq => hvw (Subtype.ext heq))).mono (hCR v) (hCR w)
  have hfixC (v : I) : EqOn (f v) id (C v)ᶜ := by
    intro x hx
    exact hfix v (fun hxopen => hx (Plane.openSquare_subset_closedSquare _ _ hxopen))
  have hmaps (v : I) : MapsTo (f v) (C v) (C v) := by
    intro x hx
    by_contra hnot
    have heq : f v x = x := (f v).injective (hfixC v hnot)
    exact hnot (heq.symm ▸ hx)
  have hsmall (v : I) (x : Plane) (hx : x ∈ C v) : dist (f v x) x < ε x := by
    have h₁ := Metric.mem_ball.mp (hsub v (hmaps v hx)).2.2.1
    have h₂ := Metric.mem_ball.mp (hsub v hx).2.2.1
    have h₃ := (hsub v hx).2.2.2
    calc
      dist (f v x) x ≤ dist (f v x) v.1 + dist v.1 x := dist_triangle _ _ _
      _ < ε v.1 / 2 := by rw [dist_comm v.1 x]; linarith
      _ < ε x := h₃
  obtain ⟨e, he, hefix, hesmall⟩ :=
    Homeomorph.exists_gluing_dist_lt f C hfixC hCC hεpos hsmall
  have hAC (v : I) (d : {d // G.Inc d v.1}) : A v d ⊆ C v := by
    intro x hx
    by_cases hxp : x = p v d
    · subst x
      exact (Plane.isClosed_closedSquare _ _).frontier_subset (hA v d).2.2.1
    · exact Plane.openSquare_subset_closedSquare _ _ ((hA v d).2.2.2 ⟨hx, hxp⟩)
  refine ⟨r, A, p, e, fun v => ⟨hr v, hCU v⟩, hCC, hedge, hA, ?_, ?_, ?_, hesmall⟩
  · intro v d
    exact ((he v).mono (hAC v d)).image_eq.trans (hf v d)
  · intro x hx
    by_cases hxC : x ∈ ⋃ v, C v
    · obtain ⟨v, hxC⟩ := mem_iUnion.mp hxC
      have hxv : x = v.1 := by
        by_contra hne
        exact hvertices v.1 (hv v) x hx hne (hCR v hxC)
      rw [he v hxC, hxv, hfv v]
      rfl
    · exact hefix hxC
  · exact hefix.mono (compl_subset_compl.mpr (iUnion_subset hCU))

end Graph

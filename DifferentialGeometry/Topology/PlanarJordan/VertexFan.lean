import DifferentialGeometry.Topology.PlanarJordan.CrosscutExtension
import DifferentialGeometry.Topology.PlanarJordan.VertexArcs

open Set

namespace DifferentialGeometry.Topology.PlanarJordan

open Schoenflies

theorem exists_homeomorph_extending_two_vertex_arcs
    {C A B A' B' : Set Plane} {v w p q : Plane}
    (hC : IsJordanCurve C) (hp : p ∈ C) (hq : q ∈ C)
    (hA : IsArcBetween A v p) (hB : IsArcBetween B v q)
    (hA' : IsArcBetween A' w p) (hB' : IsArcBetween B' w q)
    (hmeet : ∀ x ∈ A, x ∈ B → x = v)
    (hmeet' : ∀ x ∈ A', x ∈ B' → x = w)
    (hAI : A \ {p} ⊆ inside C) (hBI : B \ {q} ⊆ inside C)
    (hAI' : A' \ {p} ⊆ inside C) (hBI' : B' \ {q} ⊆ inside C)
    (f : ArcHomeo A A' v p w p) (g : ArcHomeo B B' v q w q) :
    ∃ e : Plane ≃ₜ Plane, EqOn e f.toFun A ∧ EqOn e g.toFun B ∧
      EqOn e id (inside C)ᶜ ∧ ∀ x, dist (e x) x ≤ Metric.diam (C ∪ inside C) := by
  classical
  have hagree : EqOn f.toFun g.toFun (A ∩ B) := by
    intro x hx
    rw [hmeet x hx.1 hx.2, f.map_left, g.map_left]
  have hsurj : SurjOn f.toFun (A ∩ B) (A' ∩ B') := by
    intro y hy
    rw [hmeet' y hy.1 hy.2]
    exact ⟨v, ⟨hA.left_mem, hB.left_mem⟩, f.map_left⟩
  obtain ⟨d, hdA, hdB⟩ := Homeomorph.exists_gluing_of_isCompact
    hA.isArc.isCompact hB.isArc.isCompact f.continuousOn_toFun g.continuousOn_toFun
    ⟨f.mapsTo, f.injOn, fun _ hy => f.image_eq.symm ▸ hy⟩
    ⟨g.mapsTo, g.injOn, fun _ hy => g.image_eq.symm ▸ hy⟩ hagree hsurj
  let φ : Plane → Plane := fun x => if hx : x ∈ A ∪ B then (d ⟨x, hx⟩ : Plane) else x
  let ψ : Plane → Plane := fun y => if hy : y ∈ A' ∪ B' then (d.symm ⟨y, hy⟩ : Plane) else y
  have hφ (x : Plane) (hx : x ∈ A ∪ B) : φ x = (d ⟨x, hx⟩ : Plane) := by
    simp only [φ, dif_pos hx]
  have hψ (y : Plane) (hy : y ∈ A' ∪ B') : ψ y = (d.symm ⟨y, hy⟩ : Plane) := by
    simp only [ψ, dif_pos hy]
  have hφcont : ContinuousOn φ (A ∪ B) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp d.continuous).congr (fun x => (hφ x x.property).symm)
  have hψcont : ContinuousOn ψ (A' ∪ B') := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp d.symm.continuous).congr
      (fun y => (hψ y y.property).symm)
  have hφimage : φ '' (A ∪ B) = A' ∪ B' := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [hφ x hx]
      exact (d ⟨x, hx⟩).property
    · intro y hy
      refine ⟨d.symm ⟨y, hy⟩, (d.symm ⟨y, hy⟩).property, ?_⟩
      rw [hφ _ (d.symm ⟨y, hy⟩).property]
      exact congrArg Subtype.val (d.apply_symm_apply ⟨y, hy⟩)
  let F : ArcHomeo (A ∪ B) (A' ∪ B') p q p q := {
    toFun := φ
    invFun := ψ
    continuousOn_toFun := hφcont
    continuousOn_invFun := hψcont
    leftInvOn := by
      intro x hx
      rw [hφ x hx, hψ _ (d ⟨x, hx⟩).property]
      exact congrArg Subtype.val (d.symm_apply_apply ⟨x, hx⟩)
    rightInvOn := by
      intro y hy
      rw [hψ y hy, hφ _ (d.symm ⟨y, hy⟩).property]
      exact congrArg Subtype.val (d.apply_symm_apply ⟨y, hy⟩)
    image_eq := hφimage
    map_left := (hφ p (Or.inl hA.right_mem)).trans ((hdA p hA.right_mem).trans f.map_right)
    map_right := (hφ q (Or.inr hB.right_mem)).trans ((hdB q hB.right_mem).trans g.map_right) }
  have hP := hA.reverse.concatenate hB hmeet
  have hQ := hA'.reverse.concatenate hB' hmeet'
  have hPI : (A ∪ B) \ {p, q} ⊆ inside C := by
    rintro x ⟨hx, hends⟩
    rcases hx with hx | hx
    · exact hAI ⟨hx, fun hxp => hends (Or.inl hxp)⟩
    · exact hBI ⟨hx, fun hxq => hends (Or.inr hxq)⟩
  have hQI : (A' ∪ B') \ {p, q} ⊆ inside C := by
    rintro x ⟨hx, hends⟩
    rcases hx with hx | hx
    · exact hAI' ⟨hx, fun hxp => hends (Or.inl hxp)⟩
    · exact hBI' ⟨hx, fun hxq => hends (Or.inr hxq)⟩
  obtain ⟨e, he, hfix, hdist⟩ :=
    exists_homeomorph_extending_crosscut hC hP hQ hp hq hPI hQI F
  refine ⟨e, ?_, ?_, hfix, hdist⟩
  · intro x hx
    exact (he (Or.inl hx)).trans ((hφ x (Or.inl hx)).trans (hdA x hx))
  · intro x hx
    exact (he (Or.inr hx)).trans ((hφ x (Or.inr hx)).trans (hdB x hx))

theorem exists_homeomorph_image_two_vertex_arcs
    {C A B A' B' : Set Plane} {v w p q : Plane}
    (hC : IsJordanCurve C) (hp : p ∈ C) (hq : q ∈ C)
    (hA : IsArcBetween A v p) (hB : IsArcBetween B v q)
    (hA' : IsArcBetween A' w p) (hB' : IsArcBetween B' w q)
    (hmeet : ∀ x ∈ A, x ∈ B → x = v)
    (hmeet' : ∀ x ∈ A', x ∈ B' → x = w)
    (hAI : A \ {p} ⊆ inside C) (hBI : B \ {q} ⊆ inside C)
    (hAI' : A' \ {p} ⊆ inside C) (hBI' : B' \ {q} ⊆ inside C) :
    ∃ e : Plane ≃ₜ Plane, e '' A = A' ∧ e '' B = B' ∧ e v = w ∧
      EqOn e id (inside C)ᶜ ∧ ∀ x, dist (e x) x ≤ Metric.diam (C ∪ inside C) := by
  obtain ⟨f⟩ := exists_arcHomeo hA hA'
  obtain ⟨g⟩ := exists_arcHomeo hB hB'
  obtain ⟨e, heA, heB, hfix, hdist⟩ := exists_homeomorph_extending_two_vertex_arcs
    hC hp hq hA hB hA' hB' hmeet hmeet' hAI hBI hAI' hBI' f g
  exact ⟨e, heA.image_eq.trans f.image_eq, heB.image_eq.trans g.image_eq,
    (heA hA.left_mem).trans f.map_left, hfix, hdist⟩

theorem exists_homeomorph_image_two_vertex_arcs_radial
    {A B : Set Plane} {v p q : Plane} {r : ℝ} (hr : 0 < r)
    (hp : p ∈ frontier (Plane.closedSquare v r))
    (hq : q ∈ frontier (Plane.closedSquare v r))
    (hA : IsArcBetween A v p) (hB : IsArcBetween B v q)
    (hmeet : ∀ x ∈ A, x ∈ B → x = v)
    (hAI : A \ {p} ⊆ Plane.openSquare v r) (hBI : B \ {q} ⊆ Plane.openSquare v r) :
    ∃ e : Plane ≃ₜ Plane, e '' A = segment ℝ v p ∧ e '' B = segment ℝ v q ∧
      e v = v ∧ EqOn e id (Plane.openSquare v r)ᶜ ∧
      ∀ x, dist (e x) x ≤ Metric.diam (Plane.closedSquare v r) := by
  have hpdist : Plane.supDist p v = r := by
    simpa only [Plane.frontier_closedSquare, mem_ofPred_eq] using hp
  have hqdist : Plane.supDist q v = r := by
    simpa only [Plane.frontier_closedSquare, mem_ofPred_eq] using hq
  have hne {x : Plane} (hx : Plane.supDist x v = r) : v ≠ x := by
    rintro rfl
    rw [Plane.supDist_self] at hx
    exact hr.ne' hx.symm
  have hpq : p ≠ q := by
    intro heq
    exact hne hpdist (hmeet p hA.right_mem (heq.symm ▸ hB.right_mem)).symm
  have hradial {x : Plane} (hx : Plane.supDist x v = r) :
      segment ℝ v x \ {x} ⊆ Plane.openSquare v r := by
    intro y hy
    change Plane.supDist y v < r
    rw [← hx]
    exact Plane.supDist_lt_of_mem_segment (by rwa [hx]) hy.1 hy.2
  obtain ⟨e, heA, heB, hev, hfix, hdist⟩ := exists_homeomorph_image_two_vertex_arcs
    (isJordanCurve_frontier_closedSquare v hr) hp hq hA hB
    (isArcBetween_segment (hne hpdist)) (isArcBetween_segment (hne hqdist)) hmeet
    (fun _ hx hy => Plane.radial_meet hr hpdist hqdist hpq (fun h => (h rfl).elim) hx hy)
    (by simpa only [inside_frontier_closedSquare] using hAI)
    (by simpa only [inside_frontier_closedSquare] using hBI)
    (by simpa only [inside_frontier_closedSquare] using hradial hpdist)
    (by simpa only [inside_frontier_closedSquare] using hradial hqdist)
  have hclosed : frontier (Plane.closedSquare v r) ∪
      inside (frontier (Plane.closedSquare v r)) = Plane.closedSquare v r := by
    rw [inside_frontier_closedSquare, Plane.frontier_closedSquare]
    ext x
    change (Plane.supDist x v = r ∨ Plane.supDist x v < r) ↔ Plane.supDist x v ≤ r
    exact ⟨fun hx => hx.elim le_of_eq le_of_lt, eq_or_lt_of_le⟩
  refine ⟨e, heA, heB, hev, ?_, ?_⟩
  · simpa only [inside_frontier_closedSquare] using hfix
  · simpa only [hclosed] using hdist
end DifferentialGeometry.Topology.PlanarJordan

namespace Graph

open Schoenflies DifferentialGeometry.Topology.PlanarJordan
open scoped Graph

theorem IsDrawing.exists_homeomorph_radial_vertex_arc_pair
    {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} [G.Finite]
    (h : IsDrawing G drawing) {v : Plane} {a b : β}
    (ha : G.Inc a v) (hb : G.Inc b v) (hab : a ≠ b)
    {N : Set Plane} (hN : N ∈ nhds v) :
    ∃ (r : ℝ) (A B : Set Plane) (p q : Plane) (e : Plane ≃ₜ Plane),
      0 < r ∧ Plane.closedSquare v r ⊆ N ∧
      (∀ d ∈ E(G), ¬ G.Inc d v →
        Disjoint (Plane.closedSquare v r) (edgeArc drawing d)) ∧
      A ⊆ edgeArc drawing a ∧ B ⊆ edgeArc drawing b ∧
      IsArcBetween A v p ∧ IsArcBetween B v q ∧
      p ∈ frontier (Plane.closedSquare v r) ∧ q ∈ frontier (Plane.closedSquare v r) ∧
      e '' A = segment ℝ v p ∧ e '' B = segment ℝ v q ∧ e v = v ∧
      EqOn e id (Plane.openSquare v r)ᶜ ∧
      ∀ x, dist (e x) x ≤ Metric.diam (Plane.closedSquare v r) := by
  obtain ⟨r, hr, hN', hedge, A, p, hall, hmeet, _⟩ :=
    h.exists_vertex_arcs_in_square ha.vertex_mem hN
  let a' : {e // G.Inc e v} := ⟨a, ha⟩
  let b' : {e // G.Inc e v} := ⟨b, hb⟩
  have hab' : a' ≠ b' := fun heq => hab (congrArg Subtype.val heq)
  have hp := Plane.frontier_openSquare_subset v r (hall a').2.2.1
  have hq := Plane.frontier_openSquare_subset v r (hall b').2.2.1
  obtain ⟨e, heA, heB, hev, hfix, hdist⟩ := exists_homeomorph_image_two_vertex_arcs_radial
    hr hp hq (hall a').2.1 (hall b').2.1
    (fun _ hx hy => (hmeet a' b' hab').subset ⟨hx, hy⟩)
    (hall a').2.2.2 (hall b').2.2.2
  exact ⟨r, A a', A b', p a', p b', e, hr, hN', hedge, (hall a').1, (hall b').1,
    (hall a').2.1, (hall b').2.1, hp, hq, heA, heB, hev, hfix, hdist⟩

end Graph

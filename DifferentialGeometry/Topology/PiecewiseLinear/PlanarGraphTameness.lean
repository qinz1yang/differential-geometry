import DifferentialGeometry.Topology.PlanarJordan.GraphApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.CombinatorialZero

open Set Schoenflies
open DifferentialGeometry.Topology.PiecewiseLinear DifferentialGeometry.Topology.PlanarJordan
open scoped Graph

namespace Graph

theorem isPolyhedron_image_pointSet
    {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} [G.Finite]
    (f : Plane → Plane) (hpoly : ∀ d ∈ E(G), IsPolyhedron (f '' edgeArc drawing d)) :
    IsPolyhedron (f '' pointSet G drawing) := by
  have hV : IsPolyhedron (f '' V(G)) := by
    have hsingle : IsPolyhedron (⋃ v : V(G), ({f v} : Set Plane)) :=
      IsPolyhedron.iUnion fun v => (isHPolytope_singleton (f v)).isPolyhedron
    convert hsingle using 1
    ext x
    simp
  rw [pointSet, image_union, image_iUnion₂]
  apply hV.union
  have hE : IsPolyhedron (⋃ d : E(G), f '' edgeArc drawing d) :=
    IsPolyhedron.iUnion fun d => hpoly d d.2
  simpa only [iUnion_subtype] using hE

theorem IsDrawing.exists_homeomorph_isPolyhedron_image_dist_lt
    {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} [G.Finite]
    (h : IsDrawing G drawing) {U : Set Plane} (hU : IsOpen U) (hGU : pointSet G drawing ⊆ U)
    {ε : Plane → ℝ}
    (hε : ∀ K : Set Plane, IsCompact K → K ⊆ U → ∃ c > 0, ∀ x ∈ K, c ≤ ε x) :
    ∃ e : Plane ≃ₜ Plane, IsPolyhedron (e '' pointSet G drawing) ∧
      (∀ d ∈ E(G), IsPLBall 1 (e '' edgeArc drawing d)) ∧
      EqOn e id V(G) ∧ EqOn e id Uᶜ ∧ ∀ x ∈ U, dist (e x) x < ε x := by
  obtain ⟨e, hpoly, hfixV, hfixU, hdist⟩ := h.exists_homeomorph_polygonal_edges_dist_lt hU hGU hε
  have hball (d : β) (hd : d ∈ E(G)) : IsPLBall 1 (e '' edgeArc drawing d) :=
    isPLBall_one_of_isArcBetween_of_isPolygonal
      (isArcBetween_image e (h.edge_isArcBetween (h.edge_param hd).2.2)) (hpoly d hd)
  exact ⟨e, isPolyhedron_image_pointSet e (fun d hd => (hball d hd).isPolyhedron),
    hball, hfixV, hfixU, hdist⟩

theorem IsDrawing.exists_homeomorph_isPolyhedron_image_dist_lt_of_continuous
    {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} [G.Finite]
    (h : IsDrawing G drawing) {ε : Plane → ℝ} (hε : Continuous ε) (hεpos : ∀ x, 0 < ε x)
    {U : Set Plane} (hU : IsOpen U) (hGU : pointSet G drawing ⊆ U) :
    ∃ e : Plane ≃ₜ Plane, IsPolyhedron (e '' pointSet G drawing) ∧
      (∀ d ∈ E(G), IsPLBall 1 (e '' edgeArc drawing d)) ∧
      EqOn e id V(G) ∧ EqOn e id Uᶜ ∧ ∀ x, dist (e x) x < ε x := by
  obtain ⟨e, hpoly, hball, hfixV, hfixU, hdist⟩ :=
    h.exists_homeomorph_isPolyhedron_image_dist_lt hU hGU
      (fun K hK _ => hK.exists_forall_le' hε.continuousOn (fun x _ => hεpos x))
  refine ⟨e, hpoly, hball, hfixV, hfixU, fun x => ?_⟩
  by_cases hx : x ∈ U
  · exact hdist x hx
  · rw [hfixU hx, id_eq, dist_self]
    exact hεpos x

end Graph

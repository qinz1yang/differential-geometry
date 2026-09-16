import DifferentialGeometry.Topology.PlanarJordan.ArcNeighborhood
import DifferentialGeometry.Topology.PlanarJordan.VertexStraightening
import DifferentialGeometry.Topology.PlanarJordan.Transport

open Set Topology

namespace DifferentialGeometry.Topology.PlanarJordan

open Schoenflies

private theorem closedSquare_inter_segment {v p : Plane} {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hsr : s ≤ r) (hp : Plane.supDist p v = r) :
    Plane.closedSquare v s ∩ segment ℝ v p =
      segment ℝ v (v + (s / r) • (p - v)) := by
  have hratio : 0 < s / r := div_pos hs hr
  have hratiole : s / r ≤ 1 := (div_le_one hr).mpr hsr
  ext x
  rw [segment_eq_image' ℝ v p, segment_eq_image' ℝ v (v + (s / r) • (p - v))]
  constructor
  · rintro ⟨hx, ⟨t, ht, rfl⟩⟩
    have htr : t * r ≤ s := by
      change Plane.supDist (v + t • (p - v)) v ≤ s at hx
      rw [Plane.supDist_add_smul, abs_of_nonneg ht.1, ← Plane.supDist, hp] at hx
      exact hx
    refine ⟨t * r / s, ⟨div_nonneg (mul_nonneg ht.1 hr.le) hs.le,
      (div_le_one hs).mpr htr⟩, ?_⟩
    have hcoeff : (t * r / s) * (s / r) = t := by field_simp
    calc
      v + (t * r / s) • (v + (s / r) • (p - v) - v) =
          v + ((t * r / s) * (s / r)) • (p - v) := by module
      _ = v + t • (p - v) := by rw [hcoeff]
  · rintro ⟨t, ht, rfl⟩
    have heq : v + t • (v + (s / r) • (p - v) - v) =
        v + (t * (s / r)) • (p - v) := by module
    dsimp only
    rw [heq]
    refine ⟨?_, t * (s / r), ⟨mul_nonneg ht.1 hratio.le,
      (mul_le_mul_of_nonneg_left hratiole ht.1).trans (by simpa using ht.2)⟩, rfl⟩
    change Plane.supDist (v + (t * (s / r)) • (p - v)) v ≤ s
    rw [Plane.supDist_add_smul, abs_of_nonneg (mul_nonneg ht.1 hratio.le),
      ← Plane.supDist, hp, mul_assoc, div_mul_cancel₀ s hr.ne']
    exact mul_le_of_le_one_left hs.le ht.2

end DifferentialGeometry.Topology.PlanarJordan

namespace Graph

open Schoenflies DifferentialGeometry.Topology.PlanarJordan
open scoped Graph

open Classical in
theorem IsDrawing.exists_radial_vertex_square
    {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} [G.Finite]
    (h : IsDrawing G drawing) {v : Plane} (hv : v ∈ V(G))
    (e : Plane ≃ₜ Plane) (hev : e v = v) {R : ℝ} (hR : 0 < R)
    (p : {d // G.Inc d v} → Plane)
    (hp : ∀ d, p d ∈ frontier (Plane.closedSquare v R))
    (hsegment : ∀ d, segment ℝ v (p d) ⊆ e '' edgeArc drawing d)
    {N : Set Plane} (hN : N ∈ 𝓝 v) :
    ∃ r > 0, r < R ∧ Plane.closedSquare v r ⊆ N ∧
      ∃ q : {d // G.Inc d v} → Plane,
        (∀ d, q d ∈ frontier (Plane.closedSquare v r) ∧
          Plane.closedSquare v r ∩ e '' edgeArc drawing d = segment ℝ v (q d)) ∧
        (∀ d ∈ E(G), ¬G.Inc d v →
          Disjoint (Plane.closedSquare v r) (e '' edgeArc drawing d)) := by
  let _ : _root_.Finite {d // G.Inc d v} := (finite_incidenceSet (G := G) v).to_subtype
  have hgerm (d : {d // G.Inc d v}) :
      segment ℝ v (p d) ∈ 𝓝[e '' edgeArc drawing d] v := by
    obtain ⟨w, hw⟩ := d.property
    have hE : IsArcBetween (e '' edgeArc drawing d) v (e w) := by
      simpa only [hev] using isArcBetween_image e (h.edge_isArcBetween hw)
    have hdist : Plane.supDist (p d) v = R := by
      simpa only [Plane.frontier_closedSquare, mem_ofPred_eq] using hp d
    have hne : v ≠ p d := by
      intro heq
      rw [← heq, Plane.supDist_self] at hdist
      exact hR.ne' hdist.symm
    exact hE.mem_nhdsWithin_of_subarc (isArcBetween_segment hne) (hsegment d)
  have hO (d : {d // G.Inc d v}) :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (hgerm d)
  choose O hOnhds hOsub using hO
  let K := ⋃ d ∈ {d ∈ E(G) | ¬G.Inc d v}, e '' edgeArc drawing d
  have hKcompact : IsCompact K :=
    ((finite_edgeSet (G := G)).subset (sep_subset _ _)).isCompact_biUnion
      (fun d hd => (h.isCompact_edgeArc hd.1).image e.continuous)
  have hvK : v ∉ K := by
    intro hvK
    obtain ⟨d, hd⟩ := mem_iUnion.mp hvK
    obtain ⟨hd, x, hx, hxe⟩ := mem_iUnion.mp hd
    have hxv : x = v := e.injective (hxe.trans hev.symm)
    exact h.notMem_edgeArc_of_not_inc hd.1 hv hd.2 (hxv ▸ hx)
  have hU : N ∩ (⋂ d, O d) ∩ Kᶜ ∈ 𝓝 v :=
    Filter.inter_mem (Filter.inter_mem hN (Filter.iInter_mem.mpr hOnhds))
      (hKcompact.isClosed.isOpen_compl.mem_nhds hvK)
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hU
  let r := min (R / 2) (ρ / 2)
  have hr : 0 < r := lt_min (half_pos hR) (half_pos hρ)
  have hrR : r < R := (min_le_left _ _).trans_lt (half_lt_self hR)
  have hsub : Plane.closedSquare v r ⊆ N ∩ (⋂ d, O d) ∩ Kᶜ :=
    (Plane.closedSquare_mono_center v (min_le_right _ _)).trans
      ((Plane.closedSquare_subset_ball hρ).trans hball)
  let q (d : {d // G.Inc d v}) := v + (r / R) • (p d - v)
  refine ⟨r, hr, hrR, fun x hx => (hsub hx).1.1, q, ?_, ?_⟩
  · intro d
    have hdist : Plane.supDist (p d) v = R := by
      simpa only [Plane.frontier_closedSquare, mem_ofPred_eq] using hp d
    refine ⟨?_, ?_⟩
    · rw [Plane.frontier_closedSquare]
      change Plane.supDist (v + (r / R) • (p d - v)) v = r
      rw [Plane.supDist_add_smul, abs_of_pos (div_pos hr hR),
        ← Plane.supDist, hdist, div_mul_cancel₀ r hR.ne']
    · rw [← closedSquare_inter_segment hR hr hrR.le hdist]
      apply Subset.antisymm
      · intro x hx
        exact ⟨hx.1, hOsub d ⟨mem_iInter.mp (hsub hx.1).1.2 d, hx.2⟩⟩
      · intro x hx
        exact ⟨hx.1, hsegment d hx.2⟩
  · intro d hd hinc
    exact disjoint_left.mpr fun x hx hxe => (hsub hx).2
      (mem_iUnion.mpr ⟨d, mem_iUnion.mpr ⟨⟨hd, hinc⟩, hxe⟩⟩)

open Classical in
theorem IsDrawing.exists_homeomorph_radial_vertex_neighborhoods
    {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} [G.Finite]
    (h : IsDrawing G drawing) (s : Finset Plane)
    (hs : ∀ v ∈ s, (G.incidenceSet v).Nontrivial)
    {U : Set Plane} (hU : IsOpen U) (hsU : (s : Set Plane) ⊆ U)
    {ε : Plane → ℝ} (hε : Continuous ε) (hεpos : ∀ x, 0 < ε x) :
    ∃ (r : {v // v ∈ s} → ℝ)
      (p : (v : {v // v ∈ s}) → {d // G.Inc d v.1} → Plane) (e : Plane ≃ₜ Plane),
      (∀ v, 0 < r v ∧ Plane.closedSquare v.1 (r v) ⊆ U) ∧
      (Pairwise fun v w => Disjoint (Plane.closedSquare v.1 (r v))
        (Plane.closedSquare w.1 (r w))) ∧
      (∀ v d, p v d ∈ frontier (Plane.closedSquare v.1 (r v)) ∧
        Plane.closedSquare v.1 (r v) ∩ e '' edgeArc drawing d = segment ℝ v.1 (p v d)) ∧
      (∀ v, ∀ d ∈ E(G), ¬G.Inc d v.1 →
        Disjoint (Plane.closedSquare v.1 (r v)) (e '' edgeArc drawing d)) ∧
      (∀ v, Plane.closedSquare v.1 (r v) ∩ V(G) = {v.1}) ∧
      (∀ v, Function.Injective (p v)) ∧
      EqOn e id V(G) ∧ EqOn e id Uᶜ ∧ ∀ x, dist (e x) x < ε x := by
  let I := {v // v ∈ s}
  have hv (v : I) : v.1 ∈ V(G) := by
    obtain ⟨d, hd, _, _, _⟩ := hs v.1 v.2
    exact hd.vertex_mem
  obtain ⟨R, A, q, e, hR, hdis, _, hA, heA, heV, heU, hesmall⟩ :=
    h.exists_homeomorph_radial_vertex_fans s hs hU hsU hε hεpos
  have hlocal (v : I) : ∃ r > 0, r < R v ∧
      Plane.closedSquare v.1 r ⊆ (V(G) \ {v.1})ᶜ ∧
      ∃ p : {d // G.Inc d v.1} → Plane,
        (∀ d, p d ∈ frontier (Plane.closedSquare v.1 r) ∧
          Plane.closedSquare v.1 r ∩ e '' edgeArc drawing d = segment ℝ v.1 (p d)) ∧
        (∀ d ∈ E(G), ¬G.Inc d v.1 →
          Disjoint (Plane.closedSquare v.1 r) (e '' edgeArc drawing d)) := by
    apply h.exists_radial_vertex_square (hv v) e (heV (hv v)) (hR v).1
      (q v) (fun d => (hA v d).2.2.1)
    · intro d
      rw [← heA v d]
      exact image_mono (hA v d).1
    · have hclosed : IsClosed (V(G) \ {v.1}) :=
        ((finite_vertexSet (G := G)).subset sdiff_subset).isClosed
      exact hclosed.isOpen_compl.mem_nhds (fun hmem => hmem.2 rfl)
  choose r hr hrR hN p hp hnoninc using hlocal
  have hsub (v : I) : Plane.closedSquare v.1 (r v) ⊆ Plane.closedSquare v.1 (R v) :=
    Plane.closedSquare_mono_center v.1 (hrR v).le
  have hvertices (v : I) : Plane.closedSquare v.1 (r v) ∩ V(G) = {v.1} := by
    apply Subset.antisymm
    · intro x hx
      by_contra hne
      exact hN v hx.1 ⟨hx.2, hne⟩
    · exact singleton_subset_iff.mpr ⟨Plane.mem_closedSquare_self v.1 (hr v).le, hv v⟩
  refine ⟨r, p, e, fun v => ⟨hr v, (hsub v).trans (hR v).2⟩,
    fun v w hvw => (hdis hvw).mono (hsub v) (hsub w), hp, hnoninc, hvertices,
    ?_, heV, heU, hesmall⟩
  intro v d f heq
  by_contra hdf
  have hqd : p v d ∈ e '' edgeArc drawing d :=
    ((hp v d).2.symm.subset (right_mem_segment ℝ v.1 (p v d))).2
  have hqf : p v d ∈ e '' edgeArc drawing f := by
    rw [heq]
    exact ((hp v f).2.symm.subset (right_mem_segment ℝ v.1 (p v f))).2
  obtain ⟨x, hxd, hxe⟩ := hqd
  obtain ⟨y, hyf, hye⟩ := hqf
  have hxy := e.injective (hxe.trans hye.symm)
  have hxV := h.arcs_meet_at_vertex d.property.edge_mem f.property.edge_mem
    (fun heq => hdf (Subtype.ext heq)) hxd (hxy ▸ hyf)
  have hqV : p v d ∈ V(G) := by rw [← hxe, heV hxV]; exact hxV
  have hqv : p v d = v.1 := (hvertices v).subset
    ⟨(Plane.isClosed_closedSquare _ _).frontier_subset (hp v d).1, hqV⟩
  have hboundary := (hp v d).1
  rw [Plane.frontier_closedSquare, hqv] at hboundary
  exact (hr v).ne' (by simpa only [mem_ofPred_eq, Plane.supDist_self] using hboundary.symm)

end Graph

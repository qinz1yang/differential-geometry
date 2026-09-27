/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarSchoenflies
import DifferentialGeometry.Topology.SimplicialComplex.EdgeGraph
import Mathlib.Combinatorics.SimpleGraph.Matching

open Set
open LeanEval.Topology.ClassificationOfSurfaces.Moise

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable def polygonalCircleOfCycleVertices (K : Geometry.SimplicialComplex ℝ Plane)
    {n : ℕ} (hn : 3 ≤ n) (v : ZMod n → Plane) (hv : Function.Injective v)
    (he : ∀ i, {v i, v (i + 1)} ∈ K.faces) : PolygonalCircle := by
  classical
  let _ : NeZero n := ⟨by omega⟩
  have hone : (1 : ZMod n) ≠ 0 := by
    intro h
    have := congrArg ZMod.val h
    rw [ZMod.val_one'' (by omega), ZMod.val_zero] at this
    omega
  have htwo : (2 : ZMod n) ≠ 0 := by
    intro h
    have := congrArg ZMod.val h
    rw [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega), ZMod.val_zero] at this
    omega
  have hnext : ∀ i : ZMod n, i ≠ i + 1 := by
    intro i h
    exact hone (add_left_cancel (show i + 1 = i + 0 by simpa only [add_zero] using h.symm))
  have hnext₂ : ∀ i : ZMod n, i ≠ i + 2 := by
    intro i h
    exact htwo (add_left_cancel (show i + 2 = i + 0 by simpa only [add_zero] using h.symm))
  refine
    { n := n
      three_le := hn
      vertex := v
      adjacent_ne := fun i => hv.ne (hnext i)
      consecutive_inter := ?_
      nonadjacent_disjoint := ?_ }
  · intro i
    have hinter : ({v i, v (i + 1)} : Set Plane) ∩ {v (i + 1), v (i + 2)} =
        {v (i + 1)} := by
      ext x
      simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
      constructor
      · rintro ⟨rfl | rfl, hx⟩
        · rcases hx with hx | hx
          · exact ((hnext i) (hv hx)).elim
          · exact ((hnext₂ i) (hv hx)).elim
        · rfl
      · rintro rfl
        exact ⟨Or.inr rfl, Or.inl rfl⟩
    have h := K.convexHull_inter_convexHull (he i) (he (i + 1))
    simpa only [Finset.coe_pair, add_assoc, one_add_one_eq_two, hinter,
      convexHull_pair, convexHull_singleton] using h
  · intro i j hij hip hjn
    have hinter : ({v i, v (i + 1)} : Set Plane) ∩ {v j, v (j + 1)} = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_empty_iff_false, iff_false]
      rintro ⟨rfl | rfl, hx | hx⟩
      · exact hij (hv hx)
      · exact hip (hv hx)
      · exact hjn (hv hx).symm
      · exact hij (add_right_cancel (hv hx))
    have h := K.convexHull_inter_convexHull (he i) (he j)
    simpa only [Finset.coe_pair, hinter, convexHull_pair, convexHull_empty] using h

theorem exists_polygonalCircle_of_isCycle (K : Geometry.SimplicialComplex ℝ Plane)
    {a : K.vertices} (p : (SimplicialComplex.edgeGraph K).Walk a a) (hp : p.IsCycle) :
    ∃ J : PolygonalCircle, J.carrier ⊆ K.space ∧
      range J.vertex = ((↑) : K.vertices → Plane) '' p.toSubgraph.verts ∧
      (∀ i, {J.vertex i, J.vertex (i + 1)} ∈ K.faces) ∧
      ∀ u w : K.vertices, p.toSubgraph.Adj u w →
        segment ℝ (u : Plane) (w : Plane) ⊆ J.carrier := by
  classical
  have hn : 3 ≤ p.length := hp.three_le_length
  let _ : NeZero p.length := ⟨by omega⟩
  let v : ZMod p.length → Plane := fun i => (p.getVert i.val : Plane)
  have hstep (i : ZMod p.length) : p.getVert (i + 1).val = p.getVert (i.val + 1) := by
    rw [ZMod.val_add, ZMod.val_one'' (by omega)]
    by_cases hi : i.val + 1 < p.length
    · rw [Nat.mod_eq_of_lt hi]
    · have hi' : i.val + 1 = p.length := by have := i.val_lt; omega
      rw [hi', Nat.mod_self, p.getVert_zero, p.getVert_length]
  have hv : Function.Injective v := by
    intro i j h
    apply ZMod.val_injective p.length
    exact hp.getVert_injOn' (by have := i.val_lt; change i.val ≤ p.length - 1; omega)
      (by have := j.val_lt; change j.val ≤ p.length - 1; omega) (Subtype.val_injective h)
  have he : ∀ i, {v i, v (i + 1)} ∈ K.faces := by
    intro i
    dsimp [v]
    rw [hstep]
    convert (p.adj_getVert_succ i.val_lt).2 using 1
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
  let J := polygonalCircleOfCycleVertices K hn v hv he
  have hJv : J.vertex = v := rfl
  have hJedge (i : ZMod p.length) : J.edgeSegment i = segment ℝ (v i) (v (i + 1)) := rfl
  have hJmem (i : ZMod p.length) : segment ℝ (v i) (v (i + 1)) ⊆ J.carrier :=
    subset_iUnion_of_subset i (by rw [hJedge])
  refine ⟨J, ?_, ?_, he, ?_⟩
  · intro x hx
    change x ∈ ⋃ i : ZMod p.length, segment ℝ (v i) (v (i + 1)) at hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact K.convexHull_subset_space (he i) (by
      simpa only [Finset.coe_pair, convexHull_pair] using hi)
  · rw [hJv]
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨p.getVert i.val, p.mem_verts_toSubgraph.mpr (p.getVert_mem_support _), rfl⟩
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨k, hk, hkle⟩ := p.mem_support_iff_exists_getVert.mp (p.mem_verts_toSubgraph.mp hu)
      by_cases hkn : k = p.length
      · refine ⟨(0 : ZMod p.length), ?_⟩
        change (p.getVert (0 : ZMod p.length).val : Plane) = (u : Plane)
        rw [ZMod.val_zero, p.getVert_zero]
        simpa only [hkn, p.getVert_length] using congrArg Subtype.val hk
      · refine ⟨(k : ZMod p.length), ?_⟩
        dsimp [v]
        rw [ZMod.val_natCast_of_lt (by omega)]
        exact congrArg Subtype.val hk
  · intro u w huw
    obtain ⟨k, hk, hkn⟩ := p.toSubgraph_adj_iff.mp huw
    have h0 : v (k : ZMod p.length) = (p.getVert k : Plane) := by
      dsimp [v]
      rw [ZMod.val_natCast_of_lt hkn]
    have h1 : v ((k : ZMod p.length) + 1) = (p.getVert (k + 1) : Plane) := by
      dsimp [v]
      rw [hstep, ZMod.val_natCast_of_lt hkn]
    have hsub := hJmem (k : ZMod p.length)
    rw [h0, h1] at hsub
    rcases Sym2.eq_iff.mp hk with ⟨hu, hw⟩ | ⟨hw, hu⟩
    · simpa only [hu, hw] using hsub
    · simpa only [hu, hw, segment_symm] using hsub

theorem disjoint_carrier_of_disjoint_vertex_range (K : Geometry.SimplicialComplex ℝ Plane)
    (J L : PolygonalCircle) (hJ : ∀ i, {J.vertex i, J.vertex (i + 1)} ∈ K.faces)
    (hL : ∀ i, {L.vertex i, L.vertex (i + 1)} ∈ K.faces)
    (hd : Disjoint (range J.vertex) (range L.vertex)) : Disjoint J.carrier L.carrier := by
  classical
  apply Set.disjoint_left.mpr
  intro x hxJ hxL
  obtain ⟨i, hi⟩ := mem_iUnion.mp hxJ
  obtain ⟨j, hj⟩ := mem_iUnion.mp hxL
  have hx : x ∈ convexHull ℝ (({J.vertex i, J.vertex (i + 1)} : Finset Plane) : Set Plane) ∩
      convexHull ℝ (({L.vertex j, L.vertex (j + 1)} : Finset Plane) : Set Plane) := by
    simpa only [Finset.coe_pair, convexHull_pair, PolygonalCircle.edgeSegment, mem_inter_iff] using
        And.intro hi hj
  have hv := convexHull_nonempty_iff.mp
    ⟨x, K.inter_subset_convexHull (hJ i) (hL j) hx⟩
  obtain ⟨v, hvJ, hvL⟩ := hv
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hvJ hvL
  have hvJ' : v ∈ range J.vertex := by
    rcases (show v = J.vertex i ∨ v = J.vertex (i + 1) from hvJ) with rfl | rfl
    · exact ⟨i, rfl⟩
    · exact ⟨i + 1, rfl⟩
  have hvL' : v ∈ range L.vertex := by
    rcases (show v = L.vertex j ∨ v = L.vertex (j + 1) from hvL) with rfl | rfl
    · exact ⟨j, rfl⟩
    · exact ⟨j + 1, rfl⟩
  exact Set.disjoint_left.mp hd hvJ' hvL'

theorem exists_polygonalCircle_of_connectedComponent (K : Geometry.SimplicialComplex ℝ Plane)
    [Finite K.faces] (hK : IsCombinatorialManifold 1 K)
    (c : (SimplicialComplex.edgeGraph K).ConnectedComponent) :
    ∃ J : PolygonalCircle, J.carrier ⊆ K.space ∧
      range J.vertex = ((↑) : K.vertices → Plane) '' c.supp ∧
      (∀ i, {J.vertex i, J.vertex (i + 1)} ∈ K.faces) ∧
      ∀ u w : K.vertices, u ∈ c.supp → (SimplicialComplex.edgeGraph K).Adj u w →
        segment ℝ (u : Plane) (w : Plane) ⊆ J.carrier := by
  classical
  let _ : Fintype K.vertices := (SimplicialComplex.finite_vertices K).fintype
  let _ : (SimplicialComplex.edgeGraph K).LocallyFinite := fun _ => Fintype.ofFinite _
  have hdegree (v : K.vertices) : ((SimplicialComplex.edgeGraph K).neighborSet v).ncard = 2 := by
    rw [SimplicialComplex.ncard_neighborSet_edgeGraph]
    obtain ⟨a, b, hab, hpair⟩ := (isCombinatorialManifold_one_iff K).mp hK |>.2 v v.2
    convert hpair ▸ Set.ncard_pair hab using 1
  have hcycles : (SimplicialComplex.edgeGraph K).IsCycles := fun v _ => hdegree v
  obtain ⟨a, ha⟩ := c.nonempty_supp
  have hnonempty : ((SimplicialComplex.edgeGraph K).neighborSet a).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [hdegree]; decide)
  obtain ⟨p, hp, hpc⟩ := hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp ha
      hnonempty
  obtain ⟨J, hJK, hJv, hJe, hJp⟩ := exists_polygonalCircle_of_isCycle K p hp
  refine ⟨J, hJK, by rw [hJv, hpc], hJe, ?_⟩
  intro u w hu huw
  exact hJp u w ((hp.adj_toSubgraph_iff_of_isCycles hcycles (hpc.symm ▸ hu) w).mpr huw)

theorem exists_polygonalCircle_decomposition (K : Geometry.SimplicialComplex ℝ Plane)
    [Finite K.faces] (hK : IsCombinatorialManifold 1 K) :
    ∃ J : (SimplicialComplex.edgeGraph K).ConnectedComponent → PolygonalCircle,
      (∀ c, range (J c).vertex = ((↑) : K.vertices → Plane) '' c.supp) ∧
      K.space = ⋃ c, (J c).carrier ∧ Pairwise (fun c d => Disjoint (J c).carrier (J d).carrier) :=
          by
  classical
  choose J hJK hJv hJe hJseg using exists_polygonalCircle_of_connectedComponent K hK
  refine ⟨J, hJv, ?_, ?_⟩
  · apply Subset.antisymm ?_ (iUnion_subset hJK)
    intro x hx
    obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
    have hcard : s.card ≤ 2 := hK.card_le K hs
    by_cases hcard₁ : s.card = 1
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard₁
      have hxv : x = v := by simpa only [Finset.coe_singleton, convexHull_singleton,
          mem_singleton_iff] using hxs
      subst x
      let c := (SimplicialComplex.edgeGraph K).connectedComponentMk ⟨v, hs⟩
      have hvJ : v ∈ range (J c).vertex := by
        rw [hJv]
        exact ⟨⟨v, hs⟩, rfl, rfl⟩
      obtain ⟨i, hi⟩ := hvJ
      exact mem_iUnion.mpr ⟨c, hi ▸ (J c).vertex_mem_carrier i⟩
    · have hcard₂ : s.card = 2 := by
        have := Finset.card_pos.mpr (K.nonempty_of_mem_faces hs)
        omega
      obtain ⟨u, w, huw, rfl⟩ := Finset.card_eq_two.mp hcard₂
      have huK : u ∈ K.vertices := K.down_closed hs (by simp) (Finset.singleton_nonempty u)
      have hwK : w ∈ K.vertices := K.down_closed hs (by simp) (Finset.singleton_nonempty w)
      let c := (SimplicialComplex.edgeGraph K).connectedComponentMk ⟨u, huK⟩
      have hadj : (SimplicialComplex.edgeGraph K).Adj ⟨u, huK⟩ ⟨w, hwK⟩ := by
        refine ⟨fun h => huw (congrArg Subtype.val h), ?_⟩
        convert hs using 1
        ext y
        simp only [Finset.mem_insert, Finset.mem_singleton]
      exact mem_iUnion.mpr ⟨c, hJseg c ⟨u, huK⟩ ⟨w, hwK⟩ rfl hadj
        (by simpa only [Finset.coe_pair, convexHull_pair] using hxs)⟩
  · intro c d hcd
    apply disjoint_carrier_of_disjoint_vertex_range K (J c) (J d) (hJe c) (hJe d)
    rw [hJv, hJv]
    apply Set.disjoint_left.mpr
    rintro x ⟨u, hu, rfl⟩ ⟨w, hw, hwu⟩
    have hwu' : w = u := Subtype.val_injective hwu
    subst w
    exact hcd (SimpleGraph.ConnectedComponent.eq_of_common_vertex hu hw)
theorem exists_finite_isPLSphere_decomposition (K : Geometry.SimplicialComplex ℝ Plane)
    [Finite K.faces] (hK : IsCombinatorialManifold 1 K) :
    ∃ C : Set (Set Plane), C.Finite ∧ (∀ S ∈ C, IsPLSphere 1 S) ∧
      C.PairwiseDisjoint id ∧ K.space = ⋃₀ C := by
  classical
  let _ : Finite K.vertices := (SimplicialComplex.finite_vertices K).to_subtype
  obtain ⟨J, -, hcover, hdisjoint⟩ := exists_polygonalCircle_decomposition K hK
  refine ⟨range (fun c => (J c).carrier), Set.finite_range _, ?_, ?_, ?_⟩
  · rintro S ⟨c, rfl⟩
    exact isPLSphere_one_carrier (J c)
  · rintro S ⟨c, rfl⟩ T ⟨d, rfl⟩ hcd
    exact hdisjoint (fun h => hcd (congrArg (fun a => (J a).carrier) h))
  · simpa only [sUnion_range] using hcover
end DifferentialGeometry.Topology.PiecewiseLinear

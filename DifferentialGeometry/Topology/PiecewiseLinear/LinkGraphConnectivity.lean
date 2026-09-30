/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryFaces
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSpanningTrees
import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open SimpleGraph

private def avoidGraph {V : Type*} (G : SimpleGraph V) (z : V) :
    SimpleGraph {v : V // v ≠ z} := G.induce {v : V | v ≠ z}

private theorem connected_induce_compl_singleton_of_neighbor_reachable
    {V : Type*} (G : SimpleGraph V) (z : V) (hG : G.Connected)
    (hz : ∃ c, G.Adj z c)
    (hN : ∀ (u v : V) (hu : u ≠ z) (hv : v ≠ z),
      G.Adj z u → G.Adj z v →
        (avoidGraph G z).Reachable ⟨u, hu⟩ ⟨v, hv⟩) :
    (avoidGraph G z).Connected := by
  obtain ⟨c, hzc⟩ := hz
  have hcz : c ≠ z := hzc.ne.symm
  let C := (avoidGraph G z).connectedComponentMk ⟨c, hcz⟩
  let S : Set V := ((↑) : {v : V // v ≠ z} → V) '' C.supp
  have hcS : c ∈ S := by
    refine ⟨⟨c, hcz⟩, SimpleGraph.ConnectedComponent.connectedComponentMk_mem, rfl⟩
  have hclosure : ∀ {a b : V}, a ∈ S ∨ a = z → G.Adj a b →
      b ∈ S ∨ b = z := by
    intro a b ha hab
    rcases ha with ha | haz
    · by_cases hb : b = z
      · exact Or.inr hb
      · left
        obtain ⟨a', haC, rfl⟩ := ha
        have hab' : (avoidGraph G z).Adj a' ⟨b, hb⟩ := hab
        exact ⟨⟨b, hb⟩, C.mem_supp_of_adj_mem_supp haC hab', rfl⟩
    · subst a
      by_cases hb : b = z
      · exact Or.inr hb
      · left
        have hreach := hN c b hcz hb hzc hab
        have heq : (avoidGraph G z).connectedComponentMk ⟨b, hb⟩ = C :=
          (SimpleGraph.ConnectedComponent.sound hreach).symm
        exact ⟨⟨b, hb⟩, (C.mem_supp_iff ⟨b, hb⟩).mpr heq, rfl⟩
  have hwalk : ∀ {a b : V}, a ∈ S ∨ a = z → G.Reachable a b →
      b ∈ S ∨ b = z := by
    intro a b ha hab
    obtain ⟨p⟩ := hab
    induction p with
    | nil => exact ha
    | @cons a b c hab p ih =>
        exact ih (hclosure ha hab)
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨⟨c, hcz⟩, ?_⟩
  intro v
  rcases v with ⟨v, hv⟩
  have hcv := hwalk (a := c) (b := v) (Or.inl hcS) (hG c v)
  rcases hcv with hcv | hcv
  · obtain ⟨w, hwC, hwv⟩ := hcv
    subst v
    exact C.reachable_of_mem_supp
      SimpleGraph.ConnectedComponent.connectedComponentMk_mem hwC
  · exact (hv hcv).elim

theorem edgeGraph_connected_delete_edge_of_triangle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hconn : IsConnected K.space)
    (htri : ∀ s ∈ K.faces, s.card = 2 →
      ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3) {u v : K.vertices}
    (huv : (SimplicialComplex.edgeGraph K).Adj u v) :
    (SimplicialComplex.edgeGraph K).deleteEdges {s(u, v)} |>.Connected := by
  classical
  let G := SimplicialComplex.edgeGraph K
  have hG : G.Connected := edgeGraph_connected_of_isConnected_space K hconn
  have huv' : (u : E) ≠ (v : E) := by
    intro h
    exact huv.1 (Subtype.ext h)
  have hface : ({(u : E), (v : E)} : Finset E) ∈ K.faces := huv.2
  have hcard : ({(u : E), (v : E)} : Finset E).card = 2 := by
    simp [huv']
  obtain ⟨t, ht, hst, htcard⟩ := htri _ hface hcard
  have hne : ({(u : E), (v : E)} : Finset E) ≠ t := by
    intro h
    rw [← h] at htcard
    omega
  have hss : ({(u : E), (v : E)} : Finset E) ⊂ t :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hst, hne⟩
  obtain ⟨w, hwts, hwtSub⟩ := Finset.ssubset_iff_exists_cons_subset.mp hss
  have hwt : w ∈ t := hwtSub (by simp)
  have hwne : (w : E) ≠ (u : E) ∧ (w : E) ≠ (v : E) := by
    constructor
    · intro h
      exact hwts (h ▸ by simp)
    · intro h
      exact hwts (h ▸ by simp)
  have hwK : w ∈ K.vertices := K.down_closed ht (Finset.singleton_subset_iff.mpr hwt)
    (Finset.singleton_nonempty w)
  let w' : K.vertices := ⟨w, hwK⟩
  have huw : G.Adj u w' := by
    refine ⟨fun h => hwne.1 (congrArg Subtype.val h).symm, ?_⟩
    apply K.down_closed ht
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hst (by simp)
      · exact hwt
    · simp
  have hwv : G.Adj w' v := by
    refine ⟨fun h => hwne.2 (congrArg Subtype.val h), ?_⟩
    apply K.down_closed ht
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hwt
      · exact hst (by simp)
    · simp
  apply hG.preconnected.connected_deleteEdges_of_not_isBridge
  intro hbridge
  apply (SimpleGraph.isBridge_iff.mp hbridge)
  let hp : G.Walk u v := Walk.cons huw (Walk.cons hwv Walk.nil)
  exact hp.toDeleteEdges {s(u, v)} (by
    intro e he
    simp only [hp, Walk.edges_cons, Walk.edges_nil, List.mem_cons, List.not_mem_nil] at he
    rcases he with he | he
    · subst e
      intro h
      have hEq : s(u, w') = s(u, v) := by simpa using h
      rw [Sym2.eq_iff] at hEq
      rcases hEq with h | h
      · exact hwne.2 (congrArg Subtype.val h.2)
      · exact huv' (congrArg Subtype.val h.1)
    · rcases he with he | he
      · subst e
        intro h
        have hEq : s(w', v) = s(u, v) := by simpa using h
        rw [Sym2.eq_iff] at hEq
        rcases hEq with h | h
        · exact hwne.1 (congrArg Subtype.val h.1)
        · exact huv' (congrArg Subtype.val h.2).symm
      · exact False.elim he)
    |>.reachable

open Classical in
theorem edgeGraph_connected_delete_edge_of_isCombinatorialManifoldWithBoundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hconn : IsConnected K.space)
    {u v : K.vertices} (huv : (SimplicialComplex.edgeGraph K).Adj u v) :
    (SimplicialComplex.edgeGraph K).deleteEdges {s(u, v)} |>.Connected := by
  apply edgeGraph_connected_delete_edge_of_triangle K hconn ?_ huv
  intro s hs hcard
  rcases hK.codimension_one_cofaces K hs hcard with hsingle | hdouble
  · obtain ⟨a, ha⟩ := hsingle
    have ha' : a ∉ s ∧ insert a s ∈ K.faces := by
      have : a ∈ {w | w ∉ s ∧ insert w s ∈ K.faces} := by
        rw [ha]
        simp
      exact this
    refine ⟨insert a s, ha'.2, Finset.subset_insert a s, ?_⟩
    rw [Finset.card_insert_of_notMem ha'.1, hcard]
  · obtain ⟨a, b, hab, habs⟩ := hdouble
    have ha' : a ∉ s ∧ insert a s ∈ K.faces := by
      have : a ∈ {w | w ∉ s ∧ insert w s ∈ K.faces} := by
        rw [habs]
        simp
      exact this
    refine ⟨insert a s, ha'.2, Finset.subset_insert a s, ?_⟩
    rw [Finset.card_insert_of_notMem ha'.1, hcard]

open Classical in
theorem edgeGraph_connected_delete_vertex_of_link_connected
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hconn : IsConnected K.space)
    (hlink : ∀ z : E, {z} ∈ K.faces →
      IsConnected (SimplicialComplex.geometricLink K {z}).space)
    {z : K.vertices} :
    (SimplicialComplex.edgeGraph K).induce
      {v : K.vertices | v ≠ z} |>.Connected := by
  let G := SimplicialComplex.edgeGraph K
  let L := SimplicialComplex.geometricLink K {(z : E)}
  have hzface : ({(z : E)} : Finset E) ∈ K.faces := z.property
  have hLconn : IsConnected L.space := hlink (z : E) hzface
  have hGL : (SimplicialComplex.edgeGraph L).Connected :=
    edgeGraph_connected_of_isConnected_space L hLconn
  let f : (SimplicialComplex.edgeGraph L) →g
      (G.induce {v : K.vertices | v ≠ z}) := {
    toFun := fun x => by
      have hxK : (x : E) ∈ K.vertices :=
        Geometry.SimplicialComplex.mem_vertices.mpr
          (SimplicialComplex.geometricLink_le K {(z : E)} x.property)
      have hxne : (x : E) ≠ (z : E) := by
        have hx := (SimplicialComplex.mem_geometricLink_singleton K (z : E)
          ({(x : E)} : Finset E)).mp x.property
        exact fun h => hx.2.1 (by simp [h])
      exact ⟨⟨x, hxK⟩, fun h => hxne (congrArg Subtype.val h)⟩
    map_rel' := by
      intro x y hxy
      have hxK : (x : E) ∈ K.vertices :=
        Geometry.SimplicialComplex.mem_vertices.mpr
          (SimplicialComplex.geometricLink_le K {(z : E)} x.property)
      have hyK : (y : E) ∈ K.vertices :=
        Geometry.SimplicialComplex.mem_vertices.mpr
          (SimplicialComplex.geometricLink_le K {(z : E)} y.property)
      have hxne : (x : E) ≠ (z : E) := by
        have hx := (SimplicialComplex.mem_geometricLink_singleton K (z : E)
          ({(x : E)} : Finset E)).mp x.property
        exact fun h => hx.2.1 (by simp [h])
      have hyne : (y : E) ≠ (z : E) := by
        have hy := (SimplicialComplex.mem_geometricLink_singleton K (z : E)
          ({(y : E)} : Finset E)).mp y.property
        exact fun h => hy.2.1 (by simp [h])
      refine ⟨?_, ?_⟩
      · intro h
        apply hxy.1
        apply Subtype.ext
        exact congrArg (fun q : K.vertices => (q : E)) h
      · have hxyface : ({(x : E), (y : E)} : Finset E) ∈ L.faces := hxy.2
        have hxyK : ({(x : E), (y : E)} : Finset E) ∈ K.faces :=
          SimplicialComplex.geometricLink_le K {(z : E)} hxyface
        exact hxyK
  }
  have hz : ∃ c, G.Adj z c := by
    obtain ⟨x, hx⟩ := hLconn.nonempty
    obtain ⟨s, hs, hxs⟩ := L.mem_space_iff.mp hx
    obtain ⟨xv, hxv⟩ := L.nonempty_of_mem_faces hs
    have hxvL : ({xv} : Finset E) ∈ L.faces :=
      L.down_closed hs (Finset.singleton_subset_iff.mpr hxv) (Finset.singleton_nonempty xv)
    have hxvne : xv ≠ (z : E) := by
      have hx := (SimplicialComplex.mem_geometricLink_singleton K (z : E)
        ({xv} : Finset E)).mp hxvL
      exact fun h => hx.2.1 (by simp [h])
    have hxvK : xv ∈ K.vertices :=
      Geometry.SimplicialComplex.mem_vertices.mpr
        (SimplicialComplex.geometricLink_le K {(z : E)} hxvL)
    let xv' : K.vertices := ⟨xv, hxvK⟩
    refine ⟨xv', ?_⟩
    refine ⟨fun h => hxvne (congrArg Subtype.val h).symm, ?_⟩
    have hface := (SimplicialComplex.mem_geometricLink_singleton K (z : E)
      ({xv} : Finset E)).mp hxvL |>.2.2
    simpa using hface
  have hG : G.Connected := edgeGraph_connected_of_isConnected_space K hconn
  have hN : ∀ (u v : K.vertices) (hu : u ≠ z) (hv : v ≠ z),
      G.Adj z u → G.Adj z v →
        (avoidGraph G z).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
    intro u v hu hv huz hvz
    have huL : ({(u : E)} : Finset E) ∈ L.faces := by
      apply (SimplicialComplex.mem_geometricLink_singleton K (z : E)
        ({(u : E)} : Finset E)).mpr
      refine ⟨by simp, ?_, ?_⟩
      · intro h
        apply hu
        apply Subtype.ext
        have h' : (z : E) = (u : E) := by simpa using h
        exact h'.symm
      · simpa using huz.2
    have hvL : ({(v : E)} : Finset E) ∈ L.faces := by
      apply (SimplicialComplex.mem_geometricLink_singleton K (z : E)
        ({(v : E)} : Finset E)).mpr
      refine ⟨by simp, ?_, ?_⟩
      · intro h
        apply hv
        apply Subtype.ext
        have h' : (z : E) = (v : E) := by simpa using h
        exact h'.symm
      · simpa using hvz.2
    let uL : L.vertices := ⟨u, huL⟩
    let vL : L.vertices := ⟨v, hvL⟩
    have hpath : (SimplicialComplex.edgeGraph L).Reachable uL vL := hGL uL vL
    have hu_eq : f uL = ⟨u, hu⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    have hv_eq : f vL = ⟨v, hv⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    have hm := hpath.map f
    rw [hu_eq, hv_eq] at hm
    exact hm
  have hdel := connected_induce_compl_singleton_of_neighbor_reachable G z hG hz hN
  simpa [avoidGraph, G] using hdel

open Classical in
theorem edgeGraph_connected_delete_vertex_of_isCombinatorialManifold
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : IsConnected K.space)
    {z : K.vertices} :
    (SimplicialComplex.edgeGraph K).induce
      {v : K.vertices | v ≠ z} |>.Connected := by
  apply edgeGraph_connected_delete_vertex_of_link_connected K hconn
  intro w hw
  exact (hK w hw).isConnected

open Classical in
theorem edgeGraph_connected_delete_vertex_of_isCombinatorialManifoldWithBoundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hconn : IsConnected K.space)
    {z : K.vertices} :
    (SimplicialComplex.edgeGraph K).induce
      {v : K.vertices | v ≠ z} |>.Connected := by
  apply edgeGraph_connected_delete_vertex_of_link_connected K hconn
  intro w hw
  rcases hK w hw with hS | hB
  · exact hS.isConnected
  · exact hB.isConnected

end DifferentialGeometry.Topology.PiecewiseLinear

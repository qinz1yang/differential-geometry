import DifferentialGeometry.Topology.PiecewiseLinear.OneComplex
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarSchoenflies
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Matching

open Set
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

open Classical in
noncomputable def Copy.toIsoOfBijectiveOfNeighborSetNcardEq
    {W : Type*} [Finite V] [Finite W] {H : SimpleGraph W}
    (f : Copy G H) (hbij : Function.Bijective f) {n : ℕ}
    (hG : ∀ v, (G.neighborSet v).ncard = n)
    (hH : ∀ w, (H.neighborSet w).ncard = n) : G ≃g H where
  toEquiv := Equiv.ofBijective f hbij
  map_rel_iff' := by
    intro u v
    constructor
    · intro huv
      have hsub : f '' G.neighborSet u ⊆ H.neighborSet (f u) := by
        rintro _ ⟨w, hwu, rfl⟩
        exact f.toHom.map_adj hwu
      have heq : f '' G.neighborSet u = H.neighborSet (f u) := by
        apply Set.eq_of_subset_of_ncard_le hsub
        exact le_of_eq ((hH (f u)).trans
          ((hG u).symm.trans (Set.ncard_image_of_injective _ f.injective).symm))
      have hfvmem : f v ∈ f '' G.neighborSet u := heq ▸ huv
      obtain ⟨w, hwu, hwv⟩ := hfvmem
      exact f.injective hwv ▸ hwu
    · exact f.toHom.map_adj

open Classical in
theorem exists_spanning_cycle_of_connected_degree_two [Finite V]
    (hconn : G.Connected) (hdegree : ∀ v, (G.neighborSet v).ncard = 2) :
    ∃ (a : V) (p : G.Walk a a), p.IsCycle ∧ p.toSubgraph.verts = univ := by
  let _ : Fintype V := Fintype.ofFinite V
  let _ : G.LocallyFinite := fun _ => Fintype.ofFinite _
  have hcycles : G.IsCycles := fun v _ => hdegree v
  obtain ⟨a⟩ := hconn.nonempty
  have hneighbors : (G.neighborSet a).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [hdegree]; decide)
  let c := G.connectedComponentMk a
  obtain ⟨p, hp, hpc⟩ :=
    hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (c := c) SimpleGraph.ConnectedComponent.connectedComponentMk_mem hneighbors
  refine ⟨a, p, hp, hpc.trans ?_⟩
  apply eq_univ_iff_forall.mpr
  intro v
  change G.connectedComponentMk v = G.connectedComponentMk a
  exact SimpleGraph.ConnectedComponent.sound (hconn v a)

open Classical in
noncomputable def cycleVertexEquiv [Finite V] {a : V} (p : G.Walk a a)
    (hp : p.IsCycle) (hverts : p.toSubgraph.verts = univ) : ZMod p.length ≃ V := by
  let _ : NeZero p.length := ⟨by have := hp.three_le_length; omega⟩
  let f : ZMod p.length → V := fun i => p.getVert i.val
  apply Equiv.ofBijective f
  constructor
  · intro i j hij
    apply ZMod.val_injective p.length
    exact hp.getVert_injOn'
      (by have := i.val_lt; change i.val ≤ p.length - 1; omega)
      (by have := j.val_lt; change j.val ≤ p.length - 1; omega) hij
  · intro v
    have hv : v ∈ p.toSubgraph.verts := by rw [hverts]; exact mem_univ v
    obtain ⟨k, hk, hkle⟩ :=
      p.mem_support_iff_exists_getVert.mp (p.mem_verts_toSubgraph.mp hv)
    by_cases hkn : k = p.length
    · refine ⟨(0 : ZMod p.length), ?_⟩
      change p.getVert (0 : ZMod p.length).val = v
      rw [ZMod.val_zero, p.getVert_zero]
      simpa only [hkn, p.getVert_length] using hk
    · refine ⟨(k : ZMod p.length), ?_⟩
      change p.getVert (k : ZMod p.length).val = v
      rw [ZMod.val_natCast_of_lt (by omega)]
      exact hk

open Classical in
theorem three_le_card_of_connected_degree_two [Fintype V]
    (hconn : G.Connected) (hdegree : ∀ v, (G.neighborSet v).ncard = 2) :
    3 ≤ Fintype.card V := by
  obtain ⟨a, p, hp, hverts⟩ :=
    G.exists_spanning_cycle_of_connected_degree_two hconn hdegree
  let _ : NeZero p.length := ⟨by have := hp.three_le_length; omega⟩
  let e := G.cycleVertexEquiv p hp hverts
  calc
    3 ≤ p.length := hp.three_le_length
    _ = Fintype.card (ZMod p.length) := by simp
    _ = Fintype.card V := Fintype.card_congr e

open Classical in
theorem exists_cycleGraphIsoOfConnectedDegreeTwo [Fintype V]
    (hconn : G.Connected) (hdegree : ∀ v, (G.neighborSet v).ncard = 2) :
    Nonempty (cycleGraph (Fintype.card V) ≃g G) := by
  obtain ⟨a, p, hp, hverts⟩ :=
    G.exists_spanning_cycle_of_connected_degree_two hconn hdegree
  let _ : NeZero p.length := ⟨by have := hp.three_le_length; omega⟩
  let e := G.cycleVertexEquiv p hp hverts
  have hcard : p.length = Fintype.card V := by
    calc
      p.length = Fintype.card (ZMod p.length) := by simp
      _ = Fintype.card V := Fintype.card_congr e
  obtain ⟨hcontained⟩ : cycleGraph p.length ⊑ G :=
    (cycleGraph_isContained_iff hp.three_le_length).mpr ⟨a, p, hp, rfl⟩
  rw [hcard] at hcontained
  have hbij : Function.Bijective hcontained :=
    (Fintype.bijective_iff_injective_and_card hcontained).mpr
      ⟨hcontained.injective, by simp⟩
  have hthree := G.three_le_card_of_connected_degree_two hconn hdegree
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hthree
  have hm' : Fintype.card V = m + 3 := by omega
  have hcycleDegree :
      ∀ v : Fin (Fintype.card V), ((cycleGraph (Fintype.card V)).neighborSet v).ncard = 2 := by
    rw [hm']
    intro v
    change Nat.card ((cycleGraph (m + 3)).neighborSet v) = 2
    rw [Nat.card_eq_fintype_card, card_neighborSet_eq_degree]
    exact cycleGraph_degree_three_le
  exact ⟨Copy.toIsoOfBijectiveOfNeighborSetNcardEq
    (G := cycleGraph (Fintype.card V)) (H := G) hcontained hbij hcycleDegree hdegree⟩

end SimpleGraph

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_polygonalCircle_n {n : ℕ} (hn : 3 ≤ n) :
    ∃ J : PolygonalCircle, J.n = n := by
  induction n, hn using Nat.le_induction with
  | base =>
      exact ⟨polygonalCircleOfAffineIndependentTriple standardTrianglePosition
        standardTrianglePosition_affineIndependent, rfl⟩
  | succ n _ ih =>
      obtain ⟨J, hJn⟩ := ih
      let p := midpoint ℝ (J.vertex 0) (J.vertex 1)
      have h01 : J.vertex 0 ≠ J.vertex 1 := by
        simpa only [zero_add] using J.adjacent_ne 0
      have hp : p ∈ J.edgeSegment 0 := by
        simpa only [p, edgeSegment, zero_add] using midpoint_mem_segment (J.vertex 0) (J.vertex 1)
      have hp0 : p ≠ J.vertex 0 := by
        intro h
        exact h01 ((midpoint_eq_left_iff (R := ℝ)).mp h)
      have hp1 : p ≠ J.vertex 1 := by
        intro h
        exact h01 ((midpoint_eq_right_iff (R := ℝ)).mp h)
      exact ⟨J.insertZero p hp hp0 hp1, by simp [hJn]⟩

open Classical in
noncomputable def polygonComplex (J : PolygonalCircle) :
    Geometry.SimplicialComplex ℝ Plane :=
  simplicialComplexOfPlaneComplex J.edgeComplex

open Classical in
theorem mem_polygonComplex_faces_iff (J : PolygonalCircle) {s : Finset Plane} :
    s ∈ (polygonComplex J).faces ↔
      ∃ t : Finset (ZMod J.n), t ∈ J.edgeFaces ∧ s = t.image J.vertex := by
  change (∃ t ∈ J.edgeComplex.simplexes, s = t.image J.edgeComplex.position) ↔ _
  rfl

theorem polygonComplex_faces_finite (J : PolygonalCircle) :
    (polygonComplex J).faces.Finite :=
  simplicialComplexOfPlaneComplex_faces_finite J.edgeComplex

theorem polygonComplex_space (J : PolygonalCircle) :
    (polygonComplex J).space = J.carrier :=
  (simplicialComplexOfPlaneComplex_space J.edgeComplex).trans J.edgeComplex_support

open Classical in
noncomputable def polygonVertex (J : PolygonalCircle) (i : ZMod J.n) :
    (polygonComplex J).vertices := by
  refine ⟨J.vertex i, ?_⟩
  apply (mem_polygonComplex_faces_iff J).mpr
  refine ⟨{i}, J.mem_edgeFaces_iff.mpr ⟨by simp, ⟨i, by simp⟩⟩, ?_⟩
  simp

theorem polygonVertex_injective (J : PolygonalCircle) :
    Function.Injective (polygonVertex J) := by
  intro i j hij
  apply J.vertex_injective
  exact congrArg Subtype.val hij

open Classical in
theorem polygonVertex_surjective (J : PolygonalCircle) :
    Function.Surjective (polygonVertex J) := by
  intro w
  obtain ⟨t, ht, hwt⟩ :=
    (mem_polygonComplex_faces_iff J).mp w.2
  obtain ⟨i, hi⟩ := J.mem_edgeFaces_iff.mp ht |>.1
  have hiv : J.vertex i ∈ t.image J.vertex := Finset.mem_image.mpr ⟨i, hi, rfl⟩
  rw [← hwt] at hiv
  have hiw : J.vertex i = w := by simpa using hiv
  exact ⟨i, Subtype.ext hiw⟩

open Classical in
noncomputable def polygonVertexEquiv (J : PolygonalCircle) :
    ZMod J.n ≃ (polygonComplex J).vertices :=
  Equiv.ofBijective (polygonVertex J) ⟨polygonVertex_injective J, polygonVertex_surjective J⟩

open Classical in
theorem polygonVertex_adj_add_one (J : PolygonalCircle) (i : ZMod J.n) :
    (SimplicialComplex.edgeGraph (polygonComplex J)).Adj
      (polygonVertex J i) (polygonVertex J (i + 1)) := by
  refine ⟨?_, ?_⟩
  · intro h
    exact J.adjacent_ne i (congrArg Subtype.val h)
  · apply (mem_polygonComplex_faces_iff J).mpr
    refine ⟨{i, i + 1}, J.mem_edgeFaces_iff.mpr ⟨by simp, ⟨i, Finset.Subset.rfl⟩⟩, ?_⟩
    ext x
    simp [polygonVertex]

open Classical in
theorem polygonEdgeGraph_connected (J : PolygonalCircle) :
    (SimplicialComplex.edgeGraph (polygonComplex J)).Connected := by
  let _ : NeZero J.n := ⟨by have := J.three_le; omega⟩
  have hreachNat : ∀ k : ℕ, k < J.n →
      (SimplicialComplex.edgeGraph (polygonComplex J)).Reachable
        (polygonVertex J 0) (polygonVertex J (k : ZMod J.n)) := by
    intro k hk
    induction k with
    | zero =>
        simpa only [Nat.cast_zero] using
          (SimpleGraph.Reachable.rfl :
            (SimplicialComplex.edgeGraph (polygonComplex J)).Reachable
              (polygonVertex J 0) (polygonVertex J 0))
    | succ k ih =>
        exact (ih (by omega)).trans (by
          simpa only [Nat.cast_add, Nat.cast_one] using
            (polygonVertex_adj_add_one J (k : ZMod J.n)).reachable)
  have hreach (i : ZMod J.n) :
      (SimplicialComplex.edgeGraph (polygonComplex J)).Reachable
        (polygonVertex J 0) (polygonVertex J i) := by
    simpa only [ZMod.natCast_zmod_val] using hreachNat i.val i.val_lt
  let _ : Nonempty (polygonComplex J).vertices := ⟨polygonVertex J 0⟩
  constructor
  intro u v
  let i := (polygonVertexEquiv J).symm u
  let j := (polygonVertexEquiv J).symm v
  have hi : polygonVertex J i = u := (polygonVertexEquiv J).apply_symm_apply u
  have hj : polygonVertex J j = v := (polygonVertexEquiv J).apply_symm_apply v
  rw [← hi, ← hj]
  exact (hreach i).symm.trans (hreach j)

open Classical in
theorem polygonComplex_isManifold (J : PolygonalCircle) :
    IsCombinatorialManifold 1 (polygonComplex J) := by
  let _ : Finite (polygonComplex J).faces := (polygonComplex_faces_finite J).to_subtype
  apply IsPLSphere.isCombinatorialManifold
  rw [polygonComplex_space]
  exact isPLSphere_one_carrier J

open Classical in
theorem polygonEdgeGraph_neighborSet_ncard (J : PolygonalCircle)
    (v : (polygonComplex J).vertices) :
    ((SimplicialComplex.edgeGraph (polygonComplex J)).neighborSet v).ncard = 2 := by
  let _ : Finite (polygonComplex J).faces := (polygonComplex_faces_finite J).to_subtype
  rw [SimplicialComplex.ncard_neighborSet_edgeGraph]
  obtain ⟨a, b, hab, hpair⟩ :=
    (isCombinatorialManifold_one_iff (polygonComplex J)).mp (polygonComplex_isManifold J) |>.2
      v v.2
  convert hpair ▸ Set.ncard_pair hab using 1

open Classical in
theorem exists_polygonEdgeGraphIso (J : PolygonalCircle) :
    Nonempty (SimpleGraph.cycleGraph J.n ≃g
      SimplicialComplex.edgeGraph (polygonComplex J)) := by
  let _ : Finite (polygonComplex J).faces := (polygonComplex_faces_finite J).to_subtype
  let _ : Fintype (polygonComplex J).vertices :=
    (SimplicialComplex.finite_vertices (polygonComplex J)).fintype
  obtain ⟨e⟩ :=
    (SimplicialComplex.edgeGraph (polygonComplex J)).exists_cycleGraphIsoOfConnectedDegreeTwo
      (polygonEdgeGraph_connected J) (polygonEdgeGraph_neighborSet_ncard J)
  let _ : NeZero J.n := ⟨by have := J.three_le; omega⟩
  have hcard : Fintype.card (polygonComplex J).vertices = J.n := by
    rw [← Fintype.card_congr (polygonVertexEquiv J)]
    simp
  rw [hcard] at e
  exact ⟨e⟩

open Classical in
theorem isPLSphere_one_of_edgeGraph_connected
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 1 K)
    (hconn : (SimplicialComplex.edgeGraph K).Connected) :
    IsPLSphere 1 K.space := by
  let _ : Fintype K.vertices := (SimplicialComplex.finite_vertices K).fintype
  have hdegree (v : K.vertices) :
      ((SimplicialComplex.edgeGraph K).neighborSet v).ncard = 2 := by
    rw [SimplicialComplex.ncard_neighborSet_edgeGraph]
    obtain ⟨a, b, hab, hpair⟩ := (isCombinatorialManifold_one_iff K).mp hK |>.2 v v.2
    convert hpair ▸ Set.ncard_pair hab using 1
  have hn := (SimplicialComplex.edgeGraph K).three_le_card_of_connected_degree_two hconn hdegree
  obtain ⟨J, hJn⟩ := exists_polygonalCircle_n hn
  let _ : Finite (polygonComplex J).faces := (polygonComplex_faces_finite J).to_subtype
  obtain ⟨eK⟩ :=
    (SimplicialComplex.edgeGraph K).exists_cycleGraphIsoOfConnectedDegreeTwo hconn hdegree
  obtain ⟨eJ⟩ := exists_polygonEdgeGraphIso J
  rw [hJn] at eJ
  let e := eK.symm.trans eJ
  have hJL : IsPLSphere 1 (polygonComplex J).space := by
    rw [polygonComplex_space]
    exact isPLSphere_one_carrier J
  exact hJL.of_isPLHomeomorphOn
    (isPLHomeomorphOn_of_edgeGraphIso K (polygonComplex J)
      (fun s hs => hK.card_le K hs)
      (fun t ht => (polygonComplex_isManifold J).card_le (polygonComplex J) ht) e).symm

end DifferentialGeometry.Topology.PiecewiseLinear

import DifferentialGeometry.Topology.PiecewiseLinear.OneComplex
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarSchoenflies
import Mathlib.Combinatorics.SimpleGraph.Acyclic
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

open Classical in
theorem exists_longest_path [Nonempty V] [Finite G.edgeSet] :
    ∃ (u v : V) (p : G.Walk u v) (_ : p.IsPath),
      ∀ (u' v' : V) (p' : G.Walk u' v') (_ : p'.IsPath), p'.length ≤ p.length := by
  let _ := Fintype.ofFinite G.edgeSet
  let s := {n | ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ p.length = n}
  have hs : s.Finite := Set.Finite.subset (Set.finite_le_nat G.edgeFinset.card)
    fun n ⟨_, _, _, hp, hn⟩ => hn ▸ hp.isTrail.length_le_card_edgeFinset
  obtain ⟨x⟩ := (inferInstance : Nonempty V)
  obtain ⟨_, ⟨⟨u, v, p, hp, _⟩, hn⟩⟩ :=
    hs.exists_maximal ⟨0, ⟨x, x, Walk.nil, by simp⟩⟩
  refine ⟨u, v, p, hp, fun u' v' p' hp' => ?_⟩
  have h := hn ⟨u', v', p', hp', Eq.refl p'.length⟩
  omega

open Classical in
theorem exists_spanning_path_of_connected_degree_one_or_two [Finite V]
    (hconn : G.Connected)
    (hdegree : ∀ v, (G.neighborSet v).ncard = 1 ∨ (G.neighborSet v).ncard = 2)
    (hleaf : ∃ v, (G.neighborSet v).ncard = 1) :
    ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ p.toSubgraph = ⊤ := by
  let _ : Fintype V := Fintype.ofFinite V
  let _ : G.LocallyFinite := fun _ => Fintype.ofFinite _
  let _ : Nonempty V := hconn.nonempty
  obtain ⟨u, v, p, hp, hmax⟩ := G.exists_longest_path
  obtain ⟨b, hb⟩ := hleaf
  have hbne : (G.neighborSet b).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [hb]; decide)
  obtain ⟨c, hbc⟩ := hbne
  have hpos : 0 < p.length := by
    have hle := hmax b c hbc.toWalk hbc.isPath_toWalk
    rw [hbc.length_toWalk] at hle
    omega
  have hverts : p.toSubgraph.verts = univ := by
    apply eq_univ_iff_forall.mpr
    intro x
    rw [p.mem_verts_toSubgraph]
    by_contra hx
    obtain ⟨q, hq⟩ := hconn.exists_isPath u x
    obtain ⟨⟨⟨a, z⟩, haz⟩, _, ha, hz⟩ :=
      q.exists_boundary_dart {z | z ∈ p.support} p.start_mem_support hx
    change G.Adj a z at haz
    change a ∈ p.support at ha
    change z ∉ p.support at hz
    obtain ⟨i, hia, hile⟩ := p.mem_support_iff_exists_getVert.mp ha
    subst a
    by_cases hi0 : i = 0
    · subst i
      rw [p.getVert_zero] at haz
      have hlong := hmax z v (p.cons haz.symm) (hp.cons hz)
      simp only [Walk.length_cons] at hlong
      omega
    by_cases hil : i = p.length
    · rw [hil, p.getVert_length] at haz
      have hlong := hmax u z (p.concat haz) (hp.concat hz haz)
      simp only [Walk.length_concat] at hlong
      omega
    · have hstrict :
          p.toSubgraph.neighborSet (p.getVert i) ⊂ G.neighborSet (p.getVert i) := by
        apply (p.toSubgraph.neighborSet_subset _).ssubset_of_mem_notMem
        · exact haz
        · intro h
          exact hz (p.mem_verts_toSubgraph.mp
            (p.toSubgraph.neighborSet_subset_verts _ h))
      have hlt := Set.ncard_lt_ncard hstrict
      rw [hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 (by omega)] at hlt
      rcases hdegree (p.getVert i) with hi | hi <;> omega
  have hclassify (x : V) :
      x = u ∨ x = v ∨ ∃ i, x = p.getVert i ∧ i ≠ 0 ∧ i < p.length := by
    have hx : x ∈ p.support := by
      apply p.mem_verts_toSubgraph.mp
      rw [hverts]
      exact mem_univ x
    obtain ⟨i, hix, hile⟩ := p.mem_support_iff_exists_getVert.mp hx
    by_cases hi0 : i = 0
    · left
      subst i
      simpa only [p.getVert_zero] using hix.symm
    by_cases hil : i = p.length
    · right
      left
      rw [hil, p.getVert_length] at hix
      exact hix.symm
    · exact Or.inr (Or.inr ⟨i, hix.symm, hi0, by omega⟩)
  have hbendpoint : b = u ∨ b = v := by
    rcases hclassify b with hbu | hbv | ⟨i, hbi, hi0, hil⟩
    · exact Or.inl hbu
    · exact Or.inr hbv
    · have hsub := p.toSubgraph.neighborSet_subset (p.getVert i)
      have hle := Set.ncard_le_ncard hsub
      rw [hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hil, ← hbi, hb] at hle
      omega
  have hleafNeighbor : p.toSubgraph.neighborSet b = G.neighborSet b := by
    apply Set.eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset b)
    rw [hb]
    rcases hbendpoint with hbu | hbv
    · rw [hbu, hp.neighborSet_toSubgraph_startpoint (by
          rw [Walk.not_nil_iff_lt_length]
          exact hpos)]
      simp
    · rw [hbv, hp.neighborSet_toSubgraph_endpoint (by
          rw [Walk.not_nil_iff_lt_length]
          exact hpos)]
      simp
  have hinternalNeighbor (i : ℕ) (hi0 : i ≠ 0) (hil : i < p.length) :
      p.toSubgraph.neighborSet (p.getVert i) = G.neighborSet (p.getVert i) := by
    have hsub := p.toSubgraph.neighborSet_subset (p.getVert i)
    apply Set.eq_of_subset_of_ncard_le hsub
    have hle := Set.ncard_le_ncard hsub
    rw [hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hil] at hle ⊢
    rcases hdegree (p.getVert i) with hi | hi
    · omega
    · omega
  have hadjOfNeighborEq {x y : V}
      (heq : p.toSubgraph.neighborSet x = G.neighborSet x) (hxy : G.Adj x y) :
      p.toSubgraph.Adj x y := by
    change y ∈ p.toSubgraph.neighborSet x
    rw [heq]
    exact hxy
  refine ⟨u, v, p, hp, ?_⟩
  apply SimpleGraph.Subgraph.ext
  · simpa using hverts
  · apply funext
    intro x
    apply funext
    intro y
    apply propext
    change p.toSubgraph.Adj x y ↔ G.Adj x y
    constructor
    · exact p.toSubgraph.adj_sub
    · intro hxy
      rcases hclassify x with hxu | hxv | ⟨i, hxi, hi0, hil⟩
      · by_cases hxb : x = b
        · rw [hxb] at hxy ⊢
          exact hadjOfNeighborEq hleafNeighbor hxy
        · rcases hclassify y with hyu | hyv | ⟨j, hyj, hj0, hjl⟩
          · exact False.elim (hxy.ne (hxu.trans hyu.symm))
          · have hyb : y = b := by rcases hbendpoint with hbu | hbv <;> grind
            rw [hyb] at hxy ⊢
            exact (hadjOfNeighborEq hleafNeighbor hxy.symm).symm
          · rw [hyj] at hxy ⊢
            exact (hadjOfNeighborEq (hinternalNeighbor j hj0 hjl) hxy.symm).symm
      · by_cases hxb : x = b
        · rw [hxb] at hxy ⊢
          exact hadjOfNeighborEq hleafNeighbor hxy
        · rcases hclassify y with hyu | hyv | ⟨j, hyj, hj0, hjl⟩
          · have hyb : y = b := by rcases hbendpoint with hbu | hbv <;> grind
            rw [hyb] at hxy ⊢
            exact (hadjOfNeighborEq hleafNeighbor hxy.symm).symm
          · exact False.elim (hxy.ne (hxv.trans hyv.symm))
          · rw [hyj] at hxy ⊢
            exact (hadjOfNeighborEq (hinternalNeighbor j hj0 hjl) hxy.symm).symm
      · rw [hxi] at hxy ⊢
        exact hadjOfNeighborEq (hinternalNeighbor i hi0 hil) hxy

open Classical in
theorem exists_pathGraphIsoOfConnectedDegreeOneOrTwo [Fintype V]
    (hconn : G.Connected)
    (hdegree : ∀ v, (G.neighborSet v).ncard = 1 ∨ (G.neighborSet v).ncard = 2)
    (hleaf : ∃ v, (G.neighborSet v).ncard = 1) :
    Nonempty (pathGraph (Fintype.card V) ≃g G) := by
  obtain ⟨u, v, p, hp, htop⟩ :=
    G.exists_spanning_path_of_connected_degree_one_or_two hconn hdegree hleaf
  have e : pathGraph (p.length + 1) ≃g G := by
    let e' := hp.pathGraphIsoToSubgraph
    rw [htop] at e'
    exact Subgraph.topIso.comp e'
  have hcard : p.length + 1 = Fintype.card V := by
    simpa using Fintype.card_congr e.toEquiv
  rw [← hcard]
  exact ⟨e⟩

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

open Classical in
noncomputable def polygonPathFaces (J : PolygonalCircle) :
    Finset (Finset (ZMod J.n)) :=
  (Finset.univ : Finset (Fin (J.n - 1))).biUnion fun i =>
    ({(i.val : ZMod J.n), ((i.val + 1 : ℕ) : ZMod J.n)} :
      Finset (ZMod J.n)).powerset.filter (·.Nonempty)

open Classical in
theorem mem_polygonPathFaces_iff (J : PolygonalCircle) {s : Finset (ZMod J.n)} :
    s ∈ polygonPathFaces J ↔
      s.Nonempty ∧ ∃ i : Fin (J.n - 1),
        s ⊆ {(i.val : ZMod J.n), ((i.val + 1 : ℕ) : ZMod J.n)} := by
  simp [polygonPathFaces, and_comm]

open Classical in
theorem mem_edgeFaces_of_mem_polygonPathFaces (J : PolygonalCircle) {s : Finset (ZMod J.n)}
    (hs : s ∈ polygonPathFaces J) : s ∈ J.edgeFaces := by
  obtain ⟨hsne, i, hsi⟩ := (mem_polygonPathFaces_iff J).mp hs
  apply J.mem_edgeFaces_iff.mpr
  refine ⟨hsne, (i.val : ZMod J.n), ?_⟩
  simpa only [Nat.cast_add, Nat.cast_one] using hsi

open Classical in
noncomputable def polygonPathPlaneComplex (J : PolygonalCircle) : PlaneComplex where
  Vertex := ZMod J.n
  position := J.vertex
  position_injective := J.vertex_injective
  simplexes := polygonPathFaces J
  nonempty_of_mem := fun s hs => (mem_polygonPathFaces_iff J).mp hs |>.1
  card_le_three := by
    intro s hs
    obtain ⟨_, i, hsi⟩ := (mem_polygonPathFaces_iff J).mp hs
    have hp : ({(i.val : ZMod J.n), ((i.val + 1 : ℕ) : ZMod J.n)} :
        Finset (ZMod J.n)).card ≤ 2 := by
      rcases Finset.card_pair_eq_one_or_two (a := (i.val : ZMod J.n))
        (b := ((i.val + 1 : ℕ) : ZMod J.n)) with h | h <;> omega
    exact (Finset.card_le_card hsi).trans hp |>.trans (by omega)
  down_closed := by
    intro s hs t hts ht
    obtain ⟨_, i, hsi⟩ := (mem_polygonPathFaces_iff J).mp hs
    exact (mem_polygonPathFaces_iff J).mpr ⟨ht, i, hts.trans hsi⟩
  affineIndependent := by
    intro s hs
    exact J.edgeComplex.affineIndependent s (mem_edgeFaces_of_mem_polygonPathFaces J hs)
  face_inter := by
    intro s hs t ht
    exact J.edgeComplex.face_inter s (mem_edgeFaces_of_mem_polygonPathFaces J hs)
      t (mem_edgeFaces_of_mem_polygonPathFaces J ht)

open Classical in
theorem polygonPathCellCarrier_pair (J : PolygonalCircle) (i : Fin (J.n - 1)) :
    (polygonPathPlaneComplex J).cellCarrier
        ({(i.val : ZMod J.n), ((i.val + 1 : ℕ) : ZMod J.n)} : Finset (ZMod J.n)) =
      J.edgeSegment (i.val : ZMod J.n) := by
  change convexHull ℝ (J.vertex '' (({(i.val : ZMod J.n),
    ((i.val + 1 : ℕ) : ZMod J.n)} : Finset (ZMod J.n)) : Set (ZMod J.n))) = _
  rw [PolygonalCircle.edgeSegment, ← convexHull_pair]
  congr 1
  rw [Finset.coe_pair, Set.image_pair]
  simp only [Nat.cast_add, Nat.cast_one]

open Classical in
theorem polygonPathPlaneComplex_support (J : PolygonalCircle) :
    (polygonPathPlaneComplex J).support = ProperChord.forwardArc (J := J) (J.n - 1) := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [PlaneComplex.support] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨s, hs, hxs⟩ := hx
    obtain ⟨_, i, hsi⟩ := (mem_polygonPathFaces_iff J).mp hs
    simp only [ProperChord.forwardArc, Set.mem_iUnion]
    refine ⟨i, ?_⟩
    rw [← polygonPathCellCarrier_pair J i]
    exact convexHull_mono (Set.image_mono (Finset.coe_subset.mpr hsi)) hxs
  · intro x hx
    simp only [ProperChord.forwardArc, Set.mem_iUnion] at hx
    obtain ⟨i, hxi⟩ := hx
    rw [PlaneComplex.support]
    simp only [Set.mem_iUnion]
    let s : Finset (ZMod J.n) :=
      {(i.val : ZMod J.n), ((i.val + 1 : ℕ) : ZMod J.n)}
    have hs : s ∈ polygonPathFaces J := by
      apply (mem_polygonPathFaces_iff J).mpr
      refine ⟨?_, i, Finset.Subset.rfl⟩
      simp [s]
    refine ⟨s, hs, ?_⟩
    rw [polygonPathCellCarrier_pair J i]
    exact hxi

open Classical in
theorem forwardArc_card_sub_one_eq_carrier_sdiff_open_lastEdge (J : PolygonalCircle) :
    ProperChord.forwardArc (J := J) (J.n - 1) =
      J.carrier \ (J.edgeSegment (((J.n - 1 : ℕ) : ZMod J.n)) \
        {J.vertex (((J.n - 1 : ℕ) : ZMod J.n)),
          J.vertex (((J.n - 1 : ℕ) : ZMod J.n) + 1)}) := by
  have hn := J.three_le
  let last : ZMod J.n := ((J.n - 1 : ℕ) : ZMod J.n)
  have hlastlt : J.n - 1 < J.n := by omega
  have hwrap : last + 1 = 0 := by
    calc
      last + 1 = ((J.n - 1 + 1 : ℕ) : ZMod J.n) := by
        simp only [last, Nat.cast_add, Nat.cast_one]
      _ = (J.n : ℕ) := by rw [Nat.sub_add_cancel (by omega)]
      _ = 0 := ZMod.natCast_self J.n
  change ProperChord.forwardArc (J := J) (J.n - 1) =
    J.carrier \ (J.edgeSegment last \ {J.vertex last, J.vertex (last + 1)})
  apply Set.Subset.antisymm
  · intro x hx
    refine ⟨ProperChord.forwardArc_subset_carrier (J := J) hx, ?_⟩
    rintro ⟨hxlast, hxends⟩
    simp only [ProperChord.forwardArc, Set.mem_iUnion] at hx
    obtain ⟨i, hxi⟩ := hx
    have hne : last ≠ (i.val : ZMod J.n) := by
      intro h
      have hv := congrArg ZMod.val h
      rw [ZMod.val_natCast_of_lt hlastlt,
        ZMod.val_natCast_of_lt (by omega : i.val < J.n)] at hv
      omega
    have hxpair := J.edgeSegment_inter_subset_endpoints hne ⟨hxlast, hxi⟩
    exact hxends hxpair
  · rintro x ⟨hxcarrier, hxnot⟩
    rw [PolygonalCircle.carrier] at hxcarrier
    simp only [Set.mem_iUnion] at hxcarrier
    obtain ⟨i, hxi⟩ := hxcarrier
    by_cases hi : i.val < J.n - 1
    · simp only [ProperChord.forwardArc, Set.mem_iUnion]
      exact ⟨⟨i.val, hi⟩, by simpa only [ZMod.natCast_zmod_val] using hxi⟩
    · have hival : i.val = J.n - 1 := by
        have hivlt := i.val_lt
        omega
      have hilast : i = last := by
        calc
          i = (i.val : ZMod J.n) := (ZMod.natCast_zmod_val i).symm
          _ = last := by rw [hival]
      rw [hilast] at hxi
      have hxends : x ∈ ({J.vertex last, J.vertex (last + 1)} : Set Plane) := by
        by_contra h
        exact hxnot ⟨hxi, h⟩
      rcases hxends with hx | hx
      · simp only [ProperChord.forwardArc, Set.mem_iUnion]
        let m : Fin (J.n - 1) := ⟨J.n - 2, by omega⟩
        refine ⟨m, ?_⟩
        subst x
        apply (J.vertex_mem_edgeSegment_iff last (m.val : ZMod J.n)).mpr
        right
        calc
          last = ((J.n - 2 + 1 : ℕ) : ZMod J.n) := by
            apply congrArg (fun q : ℕ => (q : ZMod J.n))
            omega
          _ = ((J.n - 2 : ℕ) : ZMod J.n) + 1 := by
            rw [Nat.cast_add, Nat.cast_one]
      · simp only [ProperChord.forwardArc, Set.mem_iUnion]
        let z : Fin (J.n - 1) := ⟨0, by omega⟩
        refine ⟨z, ?_⟩
        subst x
        rw [hwrap]
        have hz : (z.val : ZMod J.n) = 0 := by simp [z]
        rw [hz]
        exact left_mem_segment ℝ _ _

open Classical in
noncomputable def polygonPathComplex (J : PolygonalCircle) :
    Geometry.SimplicialComplex ℝ Plane :=
  simplicialComplexOfPlaneComplex (polygonPathPlaneComplex J)

theorem polygonPathComplex_faces_finite (J : PolygonalCircle) :
    (polygonPathComplex J).faces.Finite :=
  simplicialComplexOfPlaneComplex_faces_finite (polygonPathPlaneComplex J)

theorem polygonPathComplex_space (J : PolygonalCircle) :
    (polygonPathComplex J).space = ProperChord.forwardArc (J := J) (J.n - 1) :=
  (simplicialComplexOfPlaneComplex_space (polygonPathPlaneComplex J)).trans
    (polygonPathPlaneComplex_support J)

open Classical in
theorem polygonPathComplex_isPLBall (J : PolygonalCircle) :
    IsPLBall 1 (polygonPathComplex J).space := by
  rw [polygonPathComplex_space, forwardArc_card_sub_one_eq_carrier_sdiff_open_lastEdge]
  apply isPLBall_compl_openArc_of_isPLSphere_one (isPLSphere_one_carrier J)
  · exact Schoenflies.isArcBetween_segment (J.adjacent_ne _)
  · exact J.edgeSegment_subset_carrier _

open Classical in
noncomputable def polygonPathVertex (J : PolygonalCircle) (i : Fin J.n) :
    (polygonPathComplex J).vertices := by
  refine ⟨J.vertex (i.val : ZMod J.n), ?_⟩
  apply (mem_simplicialComplexOfPlaneComplex_faces_iff (polygonPathPlaneComplex J)).mpr
  change ∃ t : Finset (ZMod J.n), t ∈ polygonPathFaces J ∧
    {J.vertex (i.val : ZMod J.n)} = t.image J.vertex
  refine ⟨{(i.val : ZMod J.n)}, ?_, by simp⟩
  apply (mem_polygonPathFaces_iff J).mpr
  refine ⟨by simp, ?_⟩
  by_cases hi : i.val < J.n - 1
  · refine ⟨⟨i.val, hi⟩, ?_⟩
    intro x hx
    simp only [Finset.mem_singleton] at hx
    subst x
    exact Finset.mem_insert_self _ _
  · have hival : i.val = J.n - 1 := by
      have := i.isLt
      omega
    let m : Fin (J.n - 1) := ⟨J.n - 2, by have := J.three_le; omega⟩
    refine ⟨m, ?_⟩
    simp only [Finset.singleton_subset_iff, Finset.mem_insert, Finset.mem_singleton]
    right
    rw [hival]
    apply congrArg (fun q : ℕ => (q : ZMod J.n))
    simp only [m]
    have := J.three_le
    omega

open Classical in
theorem polygonPathVertex_injective (J : PolygonalCircle) :
    Function.Injective (polygonPathVertex J) := by
  intro i j hij
  have hvertex := J.vertex_injective (congrArg Subtype.val hij)
  have hval := congrArg ZMod.val hvertex
  rw [ZMod.val_natCast_of_lt i.isLt, ZMod.val_natCast_of_lt j.isLt] at hval
  exact Fin.ext hval

open Classical in
theorem polygonPathVertex_surjective (J : PolygonalCircle) :
    Function.Surjective (polygonPathVertex J) := by
  intro w
  have hwface : ∃ t : Finset (ZMod J.n), t ∈ polygonPathFaces J ∧
      ({(w : Plane)} : Finset Plane) = t.image J.vertex :=
    (mem_simplicialComplexOfPlaneComplex_faces_iff (polygonPathPlaneComplex J)).mp w.2
  obtain ⟨t, ht, hwt⟩ := hwface
  obtain ⟨i, hi⟩ := (mem_polygonPathFaces_iff J).mp ht |>.1
  have hiv : J.vertex i ∈ t.image J.vertex := Finset.mem_image.mpr ⟨i, hi, rfl⟩
  rw [← hwt] at hiv
  have hiw : J.vertex i = w := by simpa using hiv
  let _ : NeZero J.n := ⟨by have := J.three_le; omega⟩
  let j : Fin J.n := ⟨i.val, i.val_lt⟩
  refine ⟨j, ?_⟩
  apply Subtype.ext
  change J.vertex (j.val : ZMod J.n) = w
  rw [show (j.val : ZMod J.n) = i by exact ZMod.natCast_zmod_val i]
  exact hiw

open Classical in
noncomputable def polygonPathVertexEquiv (J : PolygonalCircle) :
    Fin J.n ≃ (polygonPathComplex J).vertices :=
  Equiv.ofBijective (polygonPathVertex J)
    ⟨polygonPathVertex_injective J, polygonPathVertex_surjective J⟩

open Classical in
theorem polygonPathVertex_adj_succ (J : PolygonalCircle) (i : Fin (J.n - 1)) :
    (SimplicialComplex.edgeGraph (polygonPathComplex J)).Adj
      (polygonPathVertex J ⟨i.val, by have := J.three_le; omega⟩)
      (polygonPathVertex J ⟨i.val + 1, by have := J.three_le; omega⟩) := by
  refine ⟨?_, ?_⟩
  · intro h
    have hv := congrArg (fun z : (polygonPathComplex J).vertices => (z : Plane)) h
    apply J.adjacent_ne (i.val : ZMod J.n)
    simpa only [polygonPathVertex, Nat.cast_add, Nat.cast_one] using hv
  · apply (mem_simplicialComplexOfPlaneComplex_faces_iff (polygonPathPlaneComplex J)).mpr
    refine ⟨({(i.val : ZMod J.n), ((i.val + 1 : ℕ) : ZMod J.n)} :
      Finset (ZMod J.n)), ?_, ?_⟩
    · apply (mem_polygonPathFaces_iff J).mpr
      exact ⟨by simp, i, Finset.Subset.rfl⟩
    · ext x
      simp [polygonPathVertex, polygonPathPlaneComplex]

open Classical in
theorem polygonPathEdgeGraph_connected (J : PolygonalCircle) :
    (SimplicialComplex.edgeGraph (polygonPathComplex J)).Connected := by
  have hreachNat (k : ℕ) (hk : k < J.n) :
      (SimplicialComplex.edgeGraph (polygonPathComplex J)).Reachable
        (polygonPathVertex J ⟨0, by have := J.three_le; omega⟩)
        (polygonPathVertex J ⟨k, hk⟩) := by
    induction k with
    | zero => exact SimpleGraph.Reachable.rfl
    | succ k ih =>
        exact (ih (by omega)).trans (by
          simpa only using (polygonPathVertex_adj_succ J ⟨k, by omega⟩).reachable)
  let _ : Nonempty (polygonPathComplex J).vertices :=
    ⟨polygonPathVertex J ⟨0, by have := J.three_le; omega⟩⟩
  constructor
  intro u v
  let i := (polygonPathVertexEquiv J).symm u
  let j := (polygonPathVertexEquiv J).symm v
  have hi : polygonPathVertex J i = u := (polygonPathVertexEquiv J).apply_symm_apply u
  have hj : polygonPathVertex J j = v := (polygonPathVertexEquiv J).apply_symm_apply v
  rw [← hi, ← hj]
  exact (hreachNat i.val i.isLt).symm.trans (hreachNat j.val j.isLt)

open Classical in
theorem polygonPathEdgeGraph_neighborSet_ncard_eq_one_or_two
    (J : PolygonalCircle) (v : (polygonPathComplex J).vertices) :
    ((SimplicialComplex.edgeGraph (polygonPathComplex J)).neighborSet v).ncard = 1 ∨
      ((SimplicialComplex.edgeGraph (polygonPathComplex J)).neighborSet v).ncard = 2 := by
  let _ : Finite (polygonPathComplex J).faces := (polygonPathComplex_faces_finite J).to_subtype
  have hman := (polygonPathComplex_isPLBall J).isCombinatorialManifoldWithBoundary
  rw [SimplicialComplex.ncard_neighborSet_edgeGraph]
  rcases (isCombinatorialManifoldWithBoundary_one_iff
    (polygonPathComplex J)).mp hman |>.2 v v.2 with h | h
  · exact Or.inl (Set.ncard_eq_one.mpr h)
  · exact Or.inr (Set.ncard_eq_two.mpr h)

open Classical in
theorem polygonPathEdgeGraph_exists_degree_one (J : PolygonalCircle) :
    ∃ v : (polygonPathComplex J).vertices,
      ((SimplicialComplex.edgeGraph (polygonPathComplex J)).neighborSet v).ncard = 1 := by
  let _ : Finite (polygonPathComplex J).faces := (polygonPathComplex_faces_finite J).to_subtype
  by_contra hleaf
  push Not at hleaf
  have hdegree (v : (polygonPathComplex J).vertices) :
      ((SimplicialComplex.edgeGraph (polygonPathComplex J)).neighborSet v).ncard = 2 :=
    (polygonPathEdgeGraph_neighborSet_ncard_eq_one_or_two J v).resolve_left (hleaf v)
  have hman : IsCombinatorialManifold 1 (polygonPathComplex J) := by
    apply (isCombinatorialManifold_one_iff (polygonPathComplex J)).mpr
    refine ⟨?_, ?_⟩
    · intro s hs
      simpa using (polygonPathComplex_isPLBall J).isCombinatorialManifoldWithBoundary.card_le _ hs
    · intro x hx
      have hd := hdegree (⟨x, hx⟩ : (polygonPathComplex J).vertices)
      rw [SimplicialComplex.ncard_neighborSet_edgeGraph] at hd
      exact Set.ncard_eq_two.mp hd
  exact (polygonPathComplex_isPLBall J).not_isPLSphere
    (isPLSphere_one_of_edgeGraph_connected (polygonPathComplex J) hman
      (polygonPathEdgeGraph_connected J))

open Classical in
theorem exists_polygonPathEdgeGraphIso (J : PolygonalCircle) :
    Nonempty (SimpleGraph.pathGraph J.n ≃g
      SimplicialComplex.edgeGraph (polygonPathComplex J)) := by
  let _ : Finite (polygonPathComplex J).faces := (polygonPathComplex_faces_finite J).to_subtype
  let _ : Fintype (polygonPathComplex J).vertices :=
    (SimplicialComplex.finite_vertices (polygonPathComplex J)).fintype
  obtain ⟨e⟩ :=
    (SimplicialComplex.edgeGraph
      (polygonPathComplex J)).exists_pathGraphIsoOfConnectedDegreeOneOrTwo
      (polygonPathEdgeGraph_connected J)
      (polygonPathEdgeGraph_neighborSet_ncard_eq_one_or_two J)
      (polygonPathEdgeGraph_exists_degree_one J)
  have hcard : Fintype.card (polygonPathComplex J).vertices = J.n := by
    rw [← Fintype.card_congr (polygonPathVertexEquiv J)]
    simp
  rw [hcard] at e
  exact ⟨e⟩

open Classical in
theorem isPLBall_one_of_edgeGraph_connected_of_exists_degree_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 1 K)
    (hconn : (SimplicialComplex.edgeGraph K).Connected)
    (hleaf : ∃ v, ((SimplicialComplex.edgeGraph K).neighborSet v).ncard = 1) :
    IsPLBall 1 K.space := by
  let _ : Fintype K.vertices := (SimplicialComplex.finite_vertices K).fintype
  have hdegree (v : K.vertices) :
      ((SimplicialComplex.edgeGraph K).neighborSet v).ncard = 1 ∨
        ((SimplicialComplex.edgeGraph K).neighborSet v).ncard = 2 := by
    rw [SimplicialComplex.ncard_neighborSet_edgeGraph]
    rcases (isCombinatorialManifoldWithBoundary_one_iff K).mp hK |>.2 v v.2 with h | h
    · exact Or.inl (Set.ncard_eq_one.mpr h)
    · exact Or.inr (Set.ncard_eq_two.mpr h)
  obtain ⟨eK⟩ :=
    (SimplicialComplex.edgeGraph K).exists_pathGraphIsoOfConnectedDegreeOneOrTwo
      hconn hdegree hleaf
  have htwo : 2 ≤ Fintype.card K.vertices := by
    obtain ⟨v, hv⟩ := hleaf
    have hne : ((SimplicialComplex.edgeGraph K).neighborSet v).Nonempty :=
      Set.nonempty_of_ncard_ne_zero (by rw [hv]; decide)
    obtain ⟨w, hw⟩ := hne
    change (SimplicialComplex.edgeGraph K).Adj v w at hw
    exact Nat.succ_le_iff.mpr (Fintype.one_lt_card_iff.mpr ⟨v, w, hw.ne⟩)
  by_cases hcard : Fintype.card K.vertices = 2
  · let i0 : Fin (Fintype.card K.vertices) := ⟨0, by omega⟩
    let i1 : Fin (Fintype.card K.vertices) := ⟨1, by omega⟩
    let a : K.vertices := eK i0
    let b : K.vertices := eK i1
    have hi01 : i0 ≠ i1 := by
      intro h
      have := congrArg Fin.val h
      simp only [i0, i1] at this
      omega
    have hab : a ≠ b := eK.injective.ne hi01
    have hadj : (SimplicialComplex.edgeGraph K).Adj a b := by
      apply eK.map_rel_iff.mpr
      rw [SimpleGraph.pathGraph_adj]
      exact Or.inl (by simp [i0, i1])
    have hvertices (v : K.vertices) : v = a ∨ v = b := by
      obtain ⟨i, rfl⟩ := eK.surjective v
      have hi : i = i0 ∨ i = i1 := by
        have hival : i.val = 0 ∨ i.val = 1 := by
          have := i.isLt
          omega
        rcases hival with hival | hival
        · left
          apply Fin.ext
          simpa only [i0] using hival
        · right
          apply Fin.ext
          simpa only [i1] using hival
      exact hi.imp (congrArg eK) (congrArg eK)
    have hspace : K.space = segment ℝ (a : E) (b : E) := by
      apply Set.Subset.antisymm
      · intro x hx
        obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
        rw [← convexHull_pair]
        apply convexHull_mono _ hxs
        intro z hzs
        have hzvertex : z ∈ K.vertices :=
          K.down_closed hs (Finset.singleton_subset_iff.mpr hzs) (Finset.singleton_nonempty z)
        rcases hvertices ⟨z, hzvertex⟩ with hz | hz
        · left
          exact congrArg Subtype.val hz
        · right
          exact congrArg Subtype.val hz
      · rw [← convexHull_pair]
        simpa only [Finset.coe_pair] using K.convexHull_subset_space hadj.2
    rw [hspace]
    exact isPLBall_segment (fun h => hab (Subtype.ext h))
  · have hthree : 3 ≤ Fintype.card K.vertices := by omega
    obtain ⟨J, hJn⟩ := exists_polygonalCircle_n hthree
    let _ : Finite (polygonPathComplex J).faces :=
      (polygonPathComplex_faces_finite J).to_subtype
    obtain ⟨eJ⟩ := exists_polygonPathEdgeGraphIso J
    rw [hJn] at eJ
    let e := eK.symm.trans eJ
    exact (polygonPathComplex_isPLBall J).of_isPLHomeomorphOn
      (isPLHomeomorphOn_of_edgeGraphIso K (polygonPathComplex J)
        (fun s hs => hK.card_le K hs)
        (fun t ht =>
          (polygonPathComplex_isPLBall J).isCombinatorialManifoldWithBoundary.card_le
            (polygonPathComplex J) ht) e).symm

end DifferentialGeometry.Topology.PiecewiseLinear

import Mathlib.Combinatorics.SimpleGraph.Matching
import DifferentialGeometry.Topology.FundamentalGroup.CircleLoopGenerator
import DifferentialGeometry.Topology.PiecewiseLinear.NeighborhoodCycle
import DifferentialGeometry.Topology.PiecewiseLinear.WalkArcPath

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Set SimpleGraph

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Geometry.SimplicialComplex ℝ E}

open Classical in
theorem ncard_neighborSet_edgeGraph_eq_two [FiniteDimensional ℝ E] [Finite K.faces]
    (hK : IsCombinatorialManifold 1 K) (v : K.vertices) :
    ((SimplicialComplex.edgeGraph K).neighborSet v).ncard = 2 := by
  rw [SimplicialComplex.ncard_neighborSet_edgeGraph]
  obtain ⟨a, b, hab, hpair⟩ := (isCombinatorialManifold_one_iff K).mp hK |>.2 v v.property
  convert hpair ▸ Set.ncard_pair hab using 1

open Classical in
theorem mem_edges_of_adj_of_spanning_cycle [FiniteDimensional ℝ E] [Finite K.faces]
    (hK : IsCombinatorialManifold 1 K) {v₀ : K.vertices}
    (γ : (SimplicialComplex.edgeGraph K).Walk v₀ v₀) (hcyc : γ.IsCycle)
    (hspan : γ.toSubgraph.verts = Set.univ) {a b : K.vertices}
    (hab : (SimplicialComplex.edgeGraph K).Adj a b) : s(a, b) ∈ γ.edges := by
  let _ : Fintype K.vertices := (SimplicialComplex.finite_vertices K).fintype
  let _ : (SimplicialComplex.edgeGraph K).LocallyFinite := fun _ => Fintype.ofFinite _
  have hcycles : (SimplicialComplex.edgeGraph K).IsCycles := fun v _ =>
    ncard_neighborSet_edgeGraph_eq_two hK v
  have hv : a ∈ γ.toSubgraph.verts := hspan ▸ Set.mem_univ a
  exact Walk.adj_toSubgraph_iff_mem_edges.mp
    ((hcyc.adj_toSubgraph_iff_of_isCycles hcycles hv b).mpr hab)

open Classical in
theorem space_subset_arcCarrier [FiniteDimensional ℝ E] [Finite K.faces]
    (hK : IsCombinatorialManifold 1 K) {v₀ : K.vertices}
    (γ : (SimplicialComplex.edgeGraph K).Walk v₀ v₀) (hcyc : γ.IsCycle)
    (hspan : γ.toSubgraph.verts = Set.univ) : K.space ⊆ arcCarrier γ := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
  have hcard : s.card ≤ 2 := ((isCombinatorialManifold_one_iff K).mp hK).1 s hs
  have hpos : 1 ≤ s.card := Finset.card_pos.mpr (Geometry.SimplicialComplex.nonempty_of_mem_faces hs)
  interval_cases hc : s.card
  · obtain ⟨y, rfl⟩ := Finset.card_eq_one.mp hc
    have hy : y ∈ K.vertices := hs
    rw [Finset.coe_singleton, convexHull_singleton, Set.mem_singleton_iff] at hxs
    subst hxs
    exact mem_arcCarrier_of_mem_support γ
      ((Walk.mem_verts_toSubgraph γ).mp (hspan ▸ Set.mem_univ (⟨x, hy⟩ : K.vertices)))
  · obtain ⟨y, z, hyz, rfl⟩ := Finset.card_eq_two.mp hc
    have hyv : y ∈ K.vertices :=
      Geometry.SimplicialComplex.down_closed hs (by simp) ⟨y, by simp⟩
    have hzv : z ∈ K.vertices :=
      Geometry.SimplicialComplex.down_closed hs (by simp) ⟨z, by simp⟩
    have hadj : (SimplicialComplex.edgeGraph K).Adj ⟨y, hyv⟩ ⟨z, hzv⟩ :=
      ⟨fun hh => hyz (congrArg Subtype.val hh), hs⟩
    refine mem_arcCarrier_of_mem_edges γ
      (mem_edges_of_adj_of_spanning_cycle hK γ hcyc hspan hadj) ?_
    rwa [← segment_eq_convexHull_pair] at hxs

open Classical in
theorem pathToCircle_arcPath_bijective [FiniteDimensional ℝ E] [Finite K.faces]
    (hK : IsCombinatorialManifold 1 K) {v₀ : K.vertices}
    (γ : (SimplicialComplex.edgeGraph K).Walk v₀ v₀) (hcyc : γ.IsCycle)
    (hspan : γ.toSubgraph.verts = Set.univ) :
    Function.Bijective (pathToCircle (arcPath γ)) := by
  have hsurj : Function.Surjective (pathToCircle (arcPath γ)) := by
    refine pathToCircle_surjective (arcPath γ) (Set.eq_univ_iff_forall.mpr fun z => ?_)
    obtain ⟨t, ht⟩ := space_subset_arcCarrier hK γ hcyc hspan z.2
    exact ⟨t, Subtype.ext ht⟩
  refine ⟨?_, hsurj⟩
  cases γ with
  | nil => exact absurd rfl hcyc.ne_nil
  | @cons _ v₁ _ h p =>
      have hlen3 : 3 ≤ (Walk.cons h p).length := hcyc.three_le_length
      rw [Walk.length_cons] at hlen3
      have hppos : 0 < p.length := by omega
      obtain ⟨hppath, hpedge⟩ := (Walk.cons_isCycle_iff p h).mp hcyc
      have hsub := segment_inter_arcCarrier_subset_pair h p hppos hpedge
      rw [← pathCarrier_edgePath h, arcCarrier_def] at hsub
      rw [arcPath_cons_of_pos h p hppos]
      refine pathToCircle_trans_injective (edgePath_injective h)
        (arcPath_injective p hppath hppos) ?_
      rintro y ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
      have hy : (y : E) ∈ ({(v₀ : E), (v₁ : E)} : Set E) :=
        hsub ⟨⟨s, congrArg (fun w : K.space => (w : E)) hs⟩,
          ⟨t, congrArg (fun w : K.space => (w : E)) ht⟩⟩
      rcases hy with hy | hy
      · exact Or.inl (Subtype.ext hy)
      · exact Or.inr (Subtype.ext hy)

open Classical in
theorem exists_homotopic_loopZPow_walkPath [FiniteDimensional ℝ E] [Finite K.faces]
    (hK : IsCombinatorialManifold 1 K) {v₀ : K.vertices}
    (γ : (SimplicialComplex.edgeGraph K).Walk v₀ v₀) (hcyc : γ.IsCycle)
    (hspan : γ.toSubgraph.verts = Set.univ)
    (ℓ : Path (vertexPoint K v₀) (vertexPoint K v₀)) :
    ∃ k : ℤ, ℓ.Homotopic (loopZPow (walkPath γ) k) := by
  obtain ⟨k, hk⟩ := exists_homotopic_loopZPow_of_bijective
    (pathToCircle (arcPath γ)) (pathToCircle_arcPath_bijective hK γ hcyc hspan)
    (pathToCircle_zero (arcPath γ)) (arcPath γ)
    (fun t => (pathToCircle_coe (arcPath γ) t).symm) ℓ
  exact ⟨k, hk.trans (loopZPow_homotopic (homotopic_walkPath_arcPath γ).symm k)⟩

open Classical in
theorem exists_spanning_cycle_of_isCombinatorialManifold_one [FiniteDimensional ℝ E]
    [Finite K.faces] (hK : IsCombinatorialManifold 1 K) (hconn : IsConnected K.space) :
    ∃ (v₀ : K.vertices) (γ : (SimplicialComplex.edgeGraph K).Walk v₀ v₀),
      γ.IsCycle ∧ γ.toSubgraph.verts = Set.univ := by
  have _ : Finite K.vertices := (SimplicialComplex.finite_vertices K)
  exact (SimplicialComplex.edgeGraph K).exists_spanning_cycle_of_connected_degree_two
    (edgeGraph_connected_of_isConnected_space K hconn)
    (ncard_neighborSet_edgeGraph_eq_two hK)

open Classical in
theorem exists_cycle_generating_loops [FiniteDimensional ℝ E] [Finite K.faces]
    (hK : IsCombinatorialManifold 1 K) (hconn : IsConnected K.space) :
    ∃ (v₀ : K.vertices) (γ : (SimplicialComplex.edgeGraph K).Walk v₀ v₀),
      γ.IsCycle ∧ γ.toSubgraph.verts = Set.univ ∧
        ∀ ℓ : Path (vertexPoint K v₀) (vertexPoint K v₀),
          ∃ k : ℤ, ℓ.Homotopic (loopZPow (walkPath γ) k) := by
  obtain ⟨v₀, γ, hcyc, hspan⟩ := exists_spanning_cycle_of_isCombinatorialManifold_one hK hconn
  exact ⟨v₀, γ, hcyc, hspan, exists_homotopic_loopZPow_walkPath hK γ hcyc hspan⟩

end DifferentialGeometry.Topology.PiecewiseLinear

import DifferentialGeometry.Topology.PiecewiseLinear.OneManifoldComponents

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem edgeGraph_preconnected_of_isPreconnected_space
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPreconnected K.space) : (SimplicialComplex.edgeGraph K).Preconnected := by
  classical
  let _ : Finite K.vertices := (SimplicialComplex.finite_vertices K).to_subtype
  let G := SimplicialComplex.edgeGraph K
  let F := fun c : G.ConnectedComponent => (graphComponentComplex K c).space
  have hclosed (c : G.ConnectedComponent) : IsClosed (F c) := by
    have hfin := graphComponentComplex_faces_finite K c
    change IsClosed (⋃ s ∈ (graphComponentComplex K c).faces, convexHull ℝ (s : Set E))
    exact hfin.isClosed_biUnion fun s _ => (s.finite_toSet.isCompact_convexHull ℝ).isClosed
  have hvertex (v : K.vertices) : (v : E) ∈ F (G.connectedComponentMk v) := by
    apply (graphComponentComplex K (G.connectedComponentMk v)).vertices_subset_space
    refine ⟨v.2, ?_⟩
    intro x hx
    have hxv : x = (v : E) := by simpa using hx
    exact ⟨v, SimpleGraph.ConnectedComponent.connectedComponentMk_mem, hxv.symm⟩
  intro u v
  by_contra huv
  let c := G.connectedComponentMk u
  let d := G.connectedComponentMk v
  have hcd : c ≠ d := fun h => huv (SimpleGraph.ConnectedComponent.exact h)
  have hcover : K.space ⊆ F c ∪ ⋃ e : {e : G.ConnectedComponent // e ≠ c}, F e := by
    intro x hx
    obtain ⟨e, he⟩ := mem_iUnion.mp ((space_eq_iUnion_graphComponentComplex K).subset hx)
    by_cases hec : e = c
    · exact Or.inl (hec ▸ he)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨e, hec⟩, he⟩)
  obtain ⟨x, -, hxc, hxe⟩ := isPreconnected_closed_iff.mp hK (F c)
    (⋃ e : {e : G.ConnectedComponent // e ≠ c}, F e)
    (hclosed c) (isClosed_iUnion_of_finite fun e => hclosed e) hcover
    ⟨u, K.vertices_subset_space u.2, hvertex u⟩
    ⟨v, K.vertices_subset_space v.2, mem_iUnion.mpr ⟨⟨d, hcd.symm⟩, hvertex v⟩⟩
  obtain ⟨e, hxe⟩ := mem_iUnion.mp hxe
  exact (pairwise_disjoint_graphComponentComplex_space K e.2).le_bot ⟨hxe, hxc⟩

theorem isPreconnected_space_of_edgeGraph_preconnected
    (K : Geometry.SimplicialComplex ℝ E)
    (hK : (SimplicialComplex.edgeGraph K).Preconnected) : IsPreconnected K.space := by
  classical
  rw [space_eq_iUnion_closedStar]
  apply IsPreconnected.iUnion_of_reflTransGen
  · intro v
    exact (isConnected_closedStar K v.2).isPreconnected
  · intro u v
    apply Relation.ReflTransGen.mono
      (fun a b hab => closedStar_inter_closedStar_nonempty_of_edgeGraph_adj K hab)
    exact ((SimplicialComplex.edgeGraph K).reachable_iff_reflTransGen u v).mp (hK u v)

theorem edgeGraph_preconnected_iff_isPreconnected_space
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    (SimplicialComplex.edgeGraph K).Preconnected ↔ IsPreconnected K.space :=
  ⟨isPreconnected_space_of_edgeGraph_preconnected K, edgeGraph_preconnected_of_isPreconnected_space K⟩

end DifferentialGeometry.Topology.PiecewiseLinear

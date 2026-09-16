import DifferentialGeometry.Topology.PiecewiseLinear.PLPath
import DifferentialGeometry.Topology.SimplicialComplex.EdgeGraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem space_eq_iUnion_closedStar (K : Geometry.SimplicialComplex ℝ E) :
    K.space = ⋃ v : K.vertices, closedStar K v := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
    obtain ⟨v, hvs⟩ := K.nonempty_of_mem_faces hs
    have hv : v ∈ K.vertices :=
      K.down_closed hs (Finset.singleton_subset_iff.mpr hvs) (Finset.singleton_nonempty v)
    apply mem_iUnion.mpr
    refine ⟨⟨v, hv⟩, ?_⟩
    exact mem_biUnion ⟨hs, subset_convexHull ℝ (s : Set E) hvs⟩ hxs
  · apply iUnion_subset
    intro v
    exact closedStar_subset_space K v

theorem isConnected_closedStar (K : Geometry.SimplicialComplex ℝ E) {v : E}
    (hv : {v} ∈ K.faces) : IsConnected (closedStar K v) :=
  ((starConvex_closedStar K).isPathConnected (mem_closedStar_of_singleton_mem K hv)).isConnected

open Classical in
theorem closedStar_inter_closedStar_nonempty_of_edgeGraph_adj
    (K : Geometry.SimplicialComplex ℝ E) {u v : K.vertices}
    (huv : (SimplicialComplex.edgeGraph K).Adj u v) :
    (closedStar K u ∩ closedStar K v).Nonempty := by
  refine ⟨u, mem_closedStar_of_singleton_mem K u.2, ?_⟩
  exact mem_biUnion
    ⟨huv.2, subset_convexHull ℝ (({(u : E), (v : E)} : Finset E) : Set E) (by simp)⟩
    (subset_convexHull ℝ (({(u : E), (v : E)} : Finset E) : Set E) (by simp))

open Classical in
theorem isConnected_space_of_edgeGraph_connected
    (K : Geometry.SimplicialComplex ℝ E)
    (hK : (SimplicialComplex.edgeGraph K).Connected) : IsConnected K.space := by
  rw [space_eq_iUnion_closedStar]
  let _ : Nonempty K.vertices := hK.nonempty
  apply IsConnected.iUnion_of_reflTransGen
  · intro v
    exact isConnected_closedStar K v.2
  · intro u v
    apply Relation.ReflTransGen.mono
      (fun a b hab => closedStar_inter_closedStar_nonempty_of_edgeGraph_adj K hab)
    exact ((SimplicialComplex.edgeGraph K).reachable_iff_reflTransGen u v).mp
      (hK.preconnected u v)

end DifferentialGeometry.Topology.PiecewiseLinear

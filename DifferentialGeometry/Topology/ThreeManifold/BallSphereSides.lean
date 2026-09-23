import DifferentialGeometry.Topology.Manifold.SphereBoundaryDomain
import DifferentialGeometry.Topology.Manifold.PartialChartEmbedding
import DifferentialGeometry.Topology.Embedding.Sphere

noncomputable section

open Set Metric Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.ThreeManifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by norm_num [Module.finrank_fin_fun]⟩
private abbrev S2 := sphere (0 : E3) 1

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [PreconnectedSpace M]

theorem eq_ball_or_complement_of_connected_sphere_frontier
    (G : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (hG : closedBall (0 : E3) 1 ⊆ G.source)
    {C : Set M} (hC : IsOpen C) (hconn : IsConnected C)
    (hfront : frontier C = G '' sphere (0 : E3) 1) :
    C = G '' ball (0 : E3) 1 ∨ C = (G '' closedBall (0 : E3) 1)ᶜ := by
  let K := G '' closedBall (0 : E3) 1
  have hK : IsCompact K := (isCompact_closedBall _ _).image_of_continuousOn
    (G.contMDiffOn_toFun.continuousOn.mono hG)
  have hKi : interior K = G '' ball (0 : E3) 1 := by
    have hh := G.toOpenPartialHomeomorph.image_interior_of_subset_source hG
    change G '' interior (closedBall (0 : E3) 1) = interior K at hh
    rw [interior_closedBall _ one_ne_zero] at hh
    exact hh.symm
  have hKf : frontier K = G '' sphere (0 : E3) 1 := by
    have hh := G.image_frontier_of_isCompact (isCompact_closedBall (0 : E3) 1) hG
    rw [frontier_closedBall _ one_ne_zero] at hh
    exact hh.symm
  let e : S2 → M := G ∘ Subtype.val
  have he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e :=
    DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph G
      (isSmoothEmbedding_coe_sphere (E := E3) (n := 2))
      (by rw [Subtype.range_val]; exact sphere_subset_closedBall.trans hG)
  have hfr : frontier K = range e := by rw [hKf, range_comp, Subtype.range_val]
  have hi : (interior K).Nonempty := by
    rw [hKi]
    exact (nonempty_ball.mpr zero_lt_one).image G
  have hsides :=
    DifferentialGeometry.Topology.Manifold.isConnected_interior_and_compl_of_sphere_boundary
    hK.isClosed hi e he hfr
  have havoid : Disjoint C (frontier K) := by
    rw [hKf, ← hfront]
    exact disjoint_left.mpr fun x hx hxf => hxf.2 (hC.interior_eq.symm ▸ hx)
  have hcover : C ⊆ interior K ∪ Kᶜ := by
    intro x hx
    have hh : x ∈ (frontier K)ᶜ := fun h => havoid.le_bot ⟨hx, h⟩
    rwa [compl_frontier_eq_union_interior, hK.isClosed.isOpen_compl.interior_eq] at hh
  have hreverse {U : Set M} (hU : IsPreconnected U) (hUK : Disjoint U (frontier K))
      (hCU : C ⊆ U) : U ⊆ C := by
    apply hU.subset_of_closure_inter_subset hC
    · obtain ⟨x, hx⟩ := hconn.nonempty
      exact ⟨x, hCU hx, hx⟩
    · rintro x ⟨hxc, hxU⟩
      by_contra hxn
      have hxf : x ∈ frontier C := ⟨hxc, fun h => hxn (interior_subset h)⟩
      exact hUK.le_bot ⟨hxU, (hfront.trans hKf.symm) ▸ hxf⟩
  rcases hconn.isPreconnected.subset_or_subset isOpen_interior hK.isClosed.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset) hcover with hiC | hoC
  · left
    rw [← hKi]
    exact subset_antisymm hiC (hreverse hsides.1.isPreconnected disjoint_interior_frontier hiC)
  · right
    exact subset_antisymm hoC (hreverse hsides.2.isPreconnected
      (disjoint_compl_left.mono_right hK.isClosed.frontier_subset) hoC)

end DifferentialGeometry.Topology.ThreeManifold

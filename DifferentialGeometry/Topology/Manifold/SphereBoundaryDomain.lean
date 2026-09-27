import DifferentialGeometry.Topology.Embedding.LocalSeparation
import DifferentialGeometry.Topology.Connected.OpenPartition
import DifferentialGeometry.Topology.Connected.Frontier
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Boundary
import DifferentialGeometry.Topology.OpenPartialHomeomorph.Images

noncomputable section

open Set Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [PreconnectedSpace M] [T2Space M]

theorem isConnected_interior_and_compl_of_sphere_boundary
    {K : Set M} (hK : IsClosed K) (hne : (interior K).Nonempty)
    (e : S2 → M) (he : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hfront : frontier K = range e) :
    IsConnected (interior K) ∧ IsConnected Kᶜ := by
  let _ : ConnectedSpace S2 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp))
      (0 : E3) zero_le_one)
  have hout : Kᶜ.Nonempty := by
    by_contra h
    have hKU : K = univ := eq_univ_of_forall fun x => by
      by_contra hx
      exact h ⟨x, hx⟩
    have hfne : (frontier K).Nonempty := hfront.symm ▸ range_nonempty e
    simp only [hKU, frontier_univ, Set.not_nonempty_empty] at hfne
  have hcover : interior K ∪ Kᶜ = (frontier K)ᶜ := by
    rw [compl_frontier_eq_union_interior, hK.isOpen_compl.interior_eq]
  have hcard : ENat.card (ConnectedComponents ↥(interior K ∪ Kᶜ)) ≤ 2 := by
    rw [hcover, hfront]
    exact he.card_connectedComponents_compl_le_two_of_compact (by simp)
  exact DifferentialGeometry.Topology.isConnected_open_partition_of_card_connectedComponents_le_two
    isOpen_interior hK.isOpen_compl (disjoint_compl_right.mono_left interior_subset) hne hout hcard

omit [ChartedSpace E3 M] [PreconnectedSpace M] [T2Space M] in
theorem subset_or_union_eq_univ_of_frontier_subset_interior
    {A K : Set M} (hA : IsClosed A) (hKcompl : IsPreconnected Kᶜ)
    (hfront : frontier A ⊆ interior K) : A ⊆ K ∨ A ∪ K = univ := by
  have havoid : Kᶜ ⊆ (frontier A)ᶜ :=
    fun _ h hA => h (interior_subset (hfront hA))
  have hcover : Kᶜ ⊆ interior A ∪ Aᶜ := by
    rw [← hA.isOpen_compl.interior_eq, ← compl_frontier_eq_union_interior]
    exact havoid
  rcases hKcompl.subset_or_subset isOpen_interior hA.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset) hcover with hin | hout
  · right
    apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ K
    · exact Or.inr hx
    · exact Or.inl (interior_subset (hin hx))
  · exact Or.inl (fun x hx => by by_contra h; exact hout h hx)

theorem ball_union_eq_univ_of_sphere_boundary_and_point_outside
    {K : Set M} (hK : IsClosed K) (hne : (interior K).Nonempty)
    (e : S2 → M) (he : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hfrontK : frontier K = range e)
    (B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (hB : closedBall (0 : E3) 1 ⊆ B.source)
    (hinside : B '' sphere (0 : E3) 1 ⊆ interior K)
    {y : M} (hy : y ∈ B '' closedBall (0 : E3) 1) (hyK : y ∉ K) :
    B '' closedBall (0 : E3) 1 ∪ K = univ := by
  have hBc : IsClosed (B '' closedBall (0 : E3) 1) :=
    ((isCompact_closedBall _ _).image_of_continuousOn
      (B.contMDiffOn_toFun.continuousOn.mono hB)).isClosed
  have hBfront : frontier (B '' closedBall (0 : E3) 1) = B '' sphere (0 : E3) 1 := by
    have h := B.toOpenPartialHomeomorph.image_frontier_of_subset_source hB isClosed_closedBall hBc
    rw [frontier_closedBall _ one_ne_zero] at h
    exact h.symm
  have hconn := (isConnected_interior_and_compl_of_sphere_boundary hK hne e he hfrontK).2
  rcases subset_or_union_eq_univ_of_frontier_subset_interior hBc hconn.isPreconnected
    (hBfront ▸ hinside) with h | h
  · exact (hyK (h hy)).elim
  · exact h

end DifferentialGeometry.Topology.Manifold

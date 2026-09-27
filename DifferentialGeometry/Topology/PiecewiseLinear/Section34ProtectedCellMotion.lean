import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingDiskComponents
import DifferentialGeometry.Topology.PiecewiseLinear.BallUnionFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellRelativeOrientation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem image_subset_of_fixed_closed_support {X : Type*} [TopologicalSpace X]
    {C K : Set X} (φ : X ≃ₜ X) (hC : IsClosed C) (hreg : closure (interior C) = C)
    (hconn : IsPreconnected (interior C)) (hboundary : (frontier C).Nonempty)
    (hK : IsClosed K) (hdis : Disjoint K (frontier C)) (hfix : EqOn φ id Kᶜ) :
    φ '' C ⊆ C := by
  have hex : ∃ x ∈ interior C, x ∉ K := by
    by_contra! h
    have hCK : C ⊆ K := hreg ▸ closure_minimal h hK
    obtain ⟨x, hx⟩ := hboundary
    exact disjoint_left.mp hdis (hCK (hC.frontier_subset hx)) hx
  obtain ⟨x, hx, hxK⟩ := hex
  have hdis' : Disjoint (φ '' interior C) (frontier C) := by
    refine disjoint_left.mpr ?_
    rintro y ⟨z, hz, hzy⟩ hy
    have hyK : y ∉ K := fun hyK => disjoint_left.mp hdis hyK hy
    have hzy' : z = y := φ.injective (hzy.trans (hfix hyK).symm)
    exact hy.2 (hzy' ▸ hz)
  have hsub : φ '' interior C ⊆ C :=
    IsPreconnected.subset_of_disjoint_frontier
      (hconn.image φ φ.continuous.continuousOn)
      ⟨x, ⟨x, hx, hfix hxK⟩, interior_subset hx⟩ hdis'
  calc φ '' C = φ '' closure (interior C) := by rw [hreg]
    _ = closure (φ '' interior C) := φ.image_closure _
    _ ⊆ C := closure_minimal hsub hC

theorem Homeomorph.image_eq_of_fixed_closed_support {X : Type*} [TopologicalSpace X]
    {C K : Set X} (φ : X ≃ₜ X) (hC : IsClosed C) (hreg : closure (interior C) = C)
    (hconn : IsPreconnected (interior C)) (hboundary : (frontier C).Nonempty)
    (hK : IsClosed K) (hdis : Disjoint K (frontier C)) (hfix : EqOn φ id Kᶜ) :
    φ '' C = C := by
  have hsub := image_subset_of_fixed_closed_support φ hC hreg hconn hboundary hK hdis hfix
  have hfix' : EqOn φ.symm id Kᶜ := by
    intro x hx
    exact φ.symm_apply_eq.mpr (hfix hx).symm
  have hsub' := image_subset_of_fixed_closed_support φ.symm hC hreg hconn hboundary
    hK hdis hfix'
  refine Subset.antisymm hsub fun x hx => ?_
  exact ⟨φ.symm x, hsub' ⟨x, hx, rfl⟩, φ.apply_symm_apply x⟩

theorem IsPLCellOn.image_eq_of_supported_off_boundary {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {C B K : Set M}
    (hC : IsPLCellOn 3 C B) (φ : M ≃ₜ M) (hK : IsClosed K)
    (hdis : Disjoint K B) (hfix : EqOn φ id Kᶜ) : φ '' C = C := by
  have hreg : closure (interior C) = C := by
    rw [← hC.sdiff_boundary_eq_interior]
    exact hC.closure_sdiff_boundary
  have hboundary : B.Nonempty := by
    obtain ⟨_, r, u, -, -, -, hB⟩ := hC
    rw [hB]
    exact ((nonempty_stdSimplexBoundary_of_pos (by decide : 0 < 3)).image r).image u
  rw [hC.boundary_eq_frontier] at hdis hboundary
  exact Homeomorph.image_eq_of_fixed_closed_support φ hC.isCompact.isClosed hreg
    hC.isConnected_interior.isPreconnected hboundary hK hdis hfix

end DifferentialGeometry.Topology.PiecewiseLinear

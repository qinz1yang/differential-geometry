/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscut
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryCrossing

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

namespace NormalSingularCellData

universe u

variable {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  {D : SingularTwoCell X} {BdM B : Set X}

theorem preimage_boundary_eq_frontier (hD : NormalSingularCellData D BdM B) :
    D.domain ∩ D ⁻¹' BdM = frontier D.domain := by
  apply Subset.antisymm
  · rintro x ⟨hx, hxb⟩
    have hrange : D x ∈ Set.range D.boundary := by
      rw [← hD.image_inter_boundary]
      exact ⟨⟨x, hx, rfl⟩, hxb⟩
    obtain ⟨z, hz⟩ := hrange
    have hzx : D (z : EuclideanSpace ℝ (Fin 2)) = D x := by simpa using hz
    by_cases hxz : x = (z : EuclideanSpace ℝ (Fin 2))
    · rw [hxz]
      exact z.2
    · have hdouble : D x ∈ doublePointSet D D.domain :=
        ⟨x, hx, (z : EuclideanSpace ℝ (Fin 2)),
          D.frontier_subset_domain z.2, hxz, rfl, hzx⟩
      obtain ⟨e, -, hye, N, hcross⟩ :=
        hD.exists_boundary_crossing_chart ⟨hdouble, hxb⟩
      exact hD.fiber_subset_frontier_of_boundary_crossing hye hcross ⟨hx, rfl⟩
  · intro z hz
    have hrange : D z ∈ Set.range D.boundary := ⟨⟨z, hz⟩, rfl⟩
    rw [← hD.image_inter_boundary] at hrange
    exact ⟨D.frontier_subset_domain hz, hrange.2⟩

theorem image_interior_subset_or_subset (hD : NormalSingularCellData D BdM B)
    {W₁ W₂ : Set X} (hW₁ : IsOpen W₁) (hW₂ : IsOpen W₂)
    (hcover : BdMᶜ = W₁ ∪ W₂) (hdisjoint : Disjoint W₁ W₂) :
    D '' interior D.domain ⊆ W₁ ∨ D '' interior D.domain ⊆ W₂ := by
  have hsub : D '' interior D.domain ⊆ W₁ ∪ W₂ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hcover, Set.mem_compl_iff]
    intro hxb
    have hfrontier : x ∈ frontier D.domain := by
      rw [← hD.preimage_boundary_eq_frontier]
      exact ⟨interior_subset hx, hxb⟩
    exact (mem_frontier_iff_notMem_interior (interior_subset hx)).mp hfrontier hx
  have hconn : IsPreconnected (D '' interior D.domain) :=
    D.isPLBall_domain.isConnected_interior.isPreconnected.image D
      (D.continuousOn.mono interior_subset)
  exact hconn.subset_or_subset hW₁ hW₂ hdisjoint hsub

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear

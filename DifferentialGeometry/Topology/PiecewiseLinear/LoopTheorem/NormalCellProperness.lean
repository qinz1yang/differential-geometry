/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscut
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryCrossing

/-!
# Properness of a normal singular cell over the manifold boundary

A normal singular two-cell `D` in a three-manifold with boundary `BdM` meets `BdM` exactly
along the image of its own boundary circle.  This file upgrades that set-level statement,
recorded as the field `NormalSingularCellData.image_inter_boundary`, to the sharper
statement about the source: the part of `D.domain` that `D` sends into `BdM` is precisely
`frontier D.domain`.

The inclusion `frontier D.domain ⊆ D.domain ∩ D ⁻¹' BdM` is immediate, since a frontier
point lies in the domain and its image lies in the range of `D.boundary`.  The converse
uses the boundary crossing analysis: a domain point mapped into `BdM` is matched by a
frontier point with the same image, and if the two points differ then their common image
is a double point lying on `BdM`, so a boundary crossing chart places the whole fibre on
`frontier D.domain`.

As a consequence, `D` maps the open cell `interior D.domain` into a single side of `BdM`,
for any splitting of the complement of `BdM` into two disjoint open sets.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

namespace NormalSingularCellData

universe u

variable {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  {D : SingularTwoCell X} {BdM B : Set X}

/-- A normal singular cell is proper over the boundary: the points of its domain that are
mapped into `BdM` are exactly the frontier points of the domain, so `D` meets `BdM` only
along its own boundary circle. -/
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

/-- A normal singular cell sends its open cell into one side of the boundary: if the
complement of `BdM` is covered by two disjoint open sets `W₁` and `W₂`, then the image
`D '' interior D.domain` is contained in `W₁` or in `W₂`. -/
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

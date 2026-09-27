/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedCapTrace
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedCellCore

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem derived_cap_neighbor_data
    (R Γ : Geometry.SimplicialComplex ℝ E) (hΓR : Γ.faces ⊆ R.faces)
    {s t : Finset E} (hs : s ∈ Γ.faces) (ht : t ∈ Γ.faces)
    {D₀ D₁ : Set E} {y₀ y₁ : E}
    (hpoles : Γ.space ∩ (derivedNeighborhoodCellBase R s).space = {y₀, y₁})
    (hcap : (derivedNeighborhoodCell R s).space ∩ (derivedNeighborhoodCell R t).space = D₁)
    (hD₁S : D₁ ⊆ (derivedNeighborhoodCellBase R s).space)
    (hdis : Disjoint D₀ D₁) (hy₀ : y₀ ∈ D₀) (hy₁ : y₁ ∈ D₁) :
    s ≠ t ∧ (s ⊆ t ∨ t ⊆ s) ∧
      ({s.centroid ℝ id, t.centroid ℝ id} : Finset E).centroid ℝ id = y₁ := by
  have hne : s ≠ t := ne_of_derivedNeighborhoodCell_inter_subset_base R (hΓR hs)
    (by rw [hcap]; exact hD₁S)
  have hcomp := subset_or_subset_of_nonempty_derivedNeighborhoodCell_inter R
    (hΓR hs) (hΓR ht) (hcap.symm ▸ (show D₁.Nonempty from ⟨y₁, hy₁⟩))
  exact ⟨hne, hcomp,
    (derived_cap_core_eq_pole R Γ hΓR hs ht hcomp hcap hD₁S hpoles hdis hy₀ hy₁).2⟩

end DifferentialGeometry.Topology.PiecewiseLinear

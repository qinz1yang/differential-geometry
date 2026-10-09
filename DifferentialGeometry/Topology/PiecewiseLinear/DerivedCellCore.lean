/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedCellSurfaceTrace

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem derivedNeighborhoodCell_inter_eq_coneSet_of_poles
    (R Γ : Geometry.SimplicialComplex ℝ E) (hΓR : Γ.faces ⊆ R.faces)
    {s : Finset E} (hs : s ∈ Γ.faces) {y₀ y₁ : E}
    (hpoles : Γ.space ∩ (derivedNeighborhoodCellBase R s).space = {y₀, y₁}) :
    (derivedNeighborhoodCell R s).space ∩ Γ.space = coneSet (s.centroid ℝ id) {y₀, y₁} := by
  rw [derivedNeighborhoodCell_inter_subcomplex R Γ hΓR hs,
    derivedNeighborhoodCell_space_eq_coneSet Γ hs]
  change coneSet (s.centroid ℝ id) (derivedNeighborhoodCellBase Γ s).space = _
  rw [← derivedNeighborhoodCellBase_inter_subcomplex R Γ hΓR hs, inter_comm, hpoles]

open Classical in
theorem ne_of_derivedNeighborhoodCell_inter_subset_base
    (R : Geometry.SimplicialComplex ℝ E) {s t : Finset E} (hs : s ∈ R.faces)
    (hsub : (derivedNeighborhoodCell R s).space ∩ (derivedNeighborhoodCell R t).space ⊆
      (derivedNeighborhoodCellBase R s).space) : s ≠ t := by
  rintro rfl
  have hc : s.centroid ℝ id ∈ (derivedNeighborhoodCell R s).space := by
    rw [derivedNeighborhoodCell_space_eq_coneSet R hs]
    exact mem_coneSet_iff.mpr (Or.inl rfl)
  exact (isConeBase_centroid_upperLink R hs).notMem_space (hsub ⟨hc, hc⟩)

theorem inter_cap_eq_singleton_of_pair_inter
    {X : Type*} {Γ S D₀ D₁ : Set X} {y₀ y₁ : X}
    (hpoles : Γ ∩ S = {y₀, y₁}) (hD₀ : D₀ ⊆ S) (hD₁ : D₁ ⊆ S)
    (hdis : Disjoint D₀ D₁) (hy₀ : y₀ ∈ D₀) (hy₁ : y₁ ∈ D₁) :
    Γ ∩ D₀ = {y₀} ∧ Γ ∩ D₁ = {y₁} := by
  constructor
  · ext y
    constructor
    · rintro ⟨hyΓ, hyD⟩
      rcases hpoles.subset ⟨hyΓ, hD₀ hyD⟩ with h | rfl
      · exact h
      · exact (disjoint_left.mp hdis hyD hy₁).elim
    · rintro rfl
      exact ⟨(hpoles.symm.subset (Or.inl rfl)).1, hy₀⟩
  · ext y
    constructor
    · rintro ⟨hyΓ, hyD⟩
      rcases hpoles.subset ⟨hyΓ, hD₁ hyD⟩ with rfl | h
      · exact (disjoint_left.mp hdis hy₀ hyD).elim
      · exact h
    · rintro rfl
      exact ⟨(hpoles.symm.subset (Or.inr rfl)).1, hy₁⟩

end DifferentialGeometry.Topology.PiecewiseLinear

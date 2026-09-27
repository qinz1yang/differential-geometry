/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Compactness.FiniteSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.DualCellPiercingNeighborhoods

open Set Topology
open DifferentialGeometry.Topology.Compactness
  (exists_perturbation_radius_preserving_containment_pairwise_disjoint)

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
def HasImageDerivedNeighborhoodSurfaceTraces
    (K : Geometry.SimplicialComplex ℝ E) (h : E → E) (N J S₀ S₁ : Set E) : Prop :=
  ∃ R L P₀ P₁ : Geometry.SimplicialComplex ℝ E,
    R.faces.Finite ∧ L.faces.Finite ∧ P₀.faces.Finite ∧ P₁.faces.Finite ∧
    IsSubdivision R K ∧ L.space = J ∧ P₀.space = S₀ ∧ P₁.space = S₁ ∧
    P₀.faces ⊆ R.faces ∧ P₁.faces ⊆ R.faces ∧
    L.faces ⊆ P₀.faces ∧ L.faces ⊆ P₁.faces ∧
    h '' N ∩ h '' S₀ = h '' (derivedNeighborhood P₀ L).space ∧
    h '' N ∩ h '' S₁ = h '' (derivedNeighborhood P₁ L).space

open Classical in
theorem IsCommonAnnularDerivedNeighborhood.hasImageDerivedNeighborhoodSurfaceTraces
    {K : Geometry.SimplicialComplex ℝ E} {N J S₀ S₁ : Set E}
    (hN : IsCommonAnnularDerivedNeighborhood K N J S₀ S₁)
    (h : E ≃ₜ E) : HasImageDerivedNeighborhoodSurfaceTraces K h N J S₀ S₁ := by
  obtain ⟨R, L, P₀, P₁, hRfin, hLfin, hP₀fin, hP₁fin, hRK, hLspace,
    hP₀space, hP₁space, hP₀R, hP₁R, hLP₀, hLP₁, -, -, htrace₀,
    htrace₁, -, -⟩ := hN
  refine ⟨R, L, P₀, P₁, hRfin, hLfin, hP₀fin, hP₁fin, hRK, hLspace,
    hP₀space, hP₁space, hP₀R, hP₁R, hLP₀, hLP₁, ?_, ?_⟩
  · rw [← Set.image_inter h.injective, htrace₀]
  · rw [← Set.image_inter h.injective, htrace₁]

theorem IsNestedCommonAnnularDerivedNeighborhood.exists_image_open_nesting
    {K : Geometry.SimplicialComplex ℝ E} {A B J S₀ S₁ : Set E}
    (hAB : IsNestedCommonAnnularDerivedNeighborhood K A B J S₀ S₁)
    (h : E ≃ₜ E) :
    ∃ O : Set E, IsOpen O ∧ h '' J ⊆ O ∧
      h '' B ⊆ O ∩ h '' K.space ∧ O ∩ h '' K.space ⊆ h '' A := by
  obtain ⟨-, -, O, hO, hJO, hBO, hOA⟩ := hAB
  refine ⟨h '' O, h.isOpenMap O hO, image_mono hJO, ?_, ?_⟩
  · rw [← Set.image_inter h.injective]
    exact image_mono hBO
  · rw [← Set.image_inter h.injective]
    exact image_mono hOA

open Classical in
theorem exists_perturbation_radius_of_pairwise_disjoint_nested_common_neighborhoods
    {ι : Type*} [Finite ι] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (A B J S₀ S₁ : ι → Set E)
    {U : Set E} (hU : IsOpen U)
    (hAB : ∀ i, IsNestedCommonAnnularDerivedNeighborhood K
      (A i) (B i) (J i) (S₀ i) (S₁ i))
    (hAU : ∀ i, A i ⊆ U)
    (hdis : Pairwise fun i j => Disjoint (A i) (A j)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ g : ι → E → E,
        (∀ i x, x ∈ A i → dist (g i x) x < δ) →
        (∀ i, g i '' A i ⊆ U) ∧
        Pairwise (fun i j => Disjoint (g i '' A i) (g j '' A j)) ∧
        Pairwise fun i j => Disjoint (g i '' B i) (g j '' B j) := by
  exact
    exists_perturbation_radius_preserving_containment_pairwise_disjoint
        A B (fun i => (hAB i).1.isPolyhedron.isCompact) hU hAU
        (fun i => (hAB i).inner_subset_outer) hdis

end DifferentialGeometry.Topology.PiecewiseLinear

/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSubcomplexComplement
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldRelativeTopology

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem IsCombinatorialManifold.exists_annulus_complement
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) {J : Set F} (hJ : IsPLSphere 1 J)
    {a b : ℝ} (hab : a < b) {W : Set E} {ρ : F × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc a b) W) (hWK : W ⊆ K.space) :
    ∃ A R : Geometry.SimplicialComplex ℝ E, A.faces.Finite ∧ R.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 2 A ∧ IsCombinatorialManifoldWithBoundary 2 R ∧
      A.space = W ∧ R.space = closure (K.space \ W) ∧
      (boundaryComplex 2 A).space = ρ '' (J ×ˢ {a, b}) ∧
      (boundaryComplex 2 R).space = ρ '' (J ×ˢ {a, b}) ∧
      A.space ∩ R.space = ρ '' (J ×ˢ {a, b}) ∧ A.space ∪ R.space = K.space := by
  obtain ⟨A, hAfin, hA, -, hAspace, hAbd⟩ := hρ.exists_annulus_complex hJ hab
  let _ : Finite A.faces := hAfin.to_subtype
  have hAK : A.space ⊆ K.space := hAspace.subset.trans hWK
  obtain ⟨R, hRfin, hR, hRspace, hRbd⟩ :=
    hK.exists_isCombinatorialManifoldWithBoundary_closure_sdiff_two hA hAK
  have hKbd : (boundaryComplex 2 K).space = ∅ := by
    rw [Geometry.SimplicialComplex.space, hK.boundaryComplex_faces_eq_empty K]
    simp
  have hinter : A.space ∩ R.space = ρ '' (J ×ˢ {a, b}) := by
    rw [hRspace, ← hAbd]
    exact inter_closure_sdiff_eq_boundaryComplex_of_disjoint_boundary K A
      hK.isCombinatorialManifoldWithBoundary hA hAK (by rw [hKbd]; exact disjoint_empty _)
  have hcover : A.space ∪ R.space = K.space := by
    rw [hRspace]
    apply Subset.antisymm
    · exact union_subset hAK (closure_minimal sdiff_subset (isPolyhedron_space K).isClosed)
    · intro x hx
      by_cases hxA : x ∈ A.space
      · exact Or.inl hxA
      · exact Or.inr (subset_closure ⟨hx, hxA⟩)
  exact ⟨A, R, hAfin, hRfin, hA, hR, hAspace, by rwa [hAspace] at hRspace,
    hAbd, hRbd.trans hAbd, hinter, hcover⟩

end DifferentialGeometry.Topology.PiecewiseLinear

/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralManifold
import DifferentialGeometry.Topology.PiecewiseLinear.PieceInclusion

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem PLPieceIn.exists_restrict_of_isPolyhedralManifoldWithBoundary
    {m : ℕ} {Y N : Set X} (P : PLPieceIn E n X Y)
    (hN : IsPolyhedralManifoldWithBoundary (n := n) m N) (hNY : N ⊆ Y) :
    ∃ S : PLPieceIn E n X N,
      S.complex.space = P.complex.space ∩ P.map ⁻¹' N ∧ S.map = P.map ∧
        IsCombinatorialManifoldWithBoundary m S.complex := by
  obtain ⟨T, hT⟩ := hN
  let _ : Finite T.piece.complex.faces := T.piece.finite_faces.to_subtype
  have hg := T.piece.isPLHomeomorphOn_transition_of_subset P hNY
  have hQ : IsPolyhedron (P.complex.space ∩ P.map ⁻¹' N) := by
    rw [← hg.image_eq]
    exact T.piece.isPolyhedron_space.image_of_isPiecewiseAffineOn
      hg.isPiecewiseAffineOn hg.bijOn.injOn
  obtain ⟨S, hSspace, hSmap⟩ := P.exists_restrict_of_isPolyhedron hQ inter_subset_left
  let _ : Finite S.complex.faces := S.finite_faces.to_subtype
  have hS : IsCombinatorialManifoldWithBoundary m S.complex := by
    apply hT.of_isPLHomeomorphOn (f := Function.invFunOn P.map P.complex.space ∘ T.piece.map)
    rw [hSspace]
    exact hg
  have himage : P.map '' (P.complex.space ∩ P.map ⁻¹' N) = N := by
    apply Subset.antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact hy.2
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := P.bijOn.surjOn (hNY hx)
      exact ⟨y, ⟨hy, hx⟩, rfl⟩
  have h : ∃ S : PLPieceIn E n X (P.map '' (P.complex.space ∩ P.map ⁻¹' N)),
      S.complex.space = P.complex.space ∩ P.map ⁻¹' N ∧ S.map = P.map ∧
        IsCombinatorialManifoldWithBoundary m S.complex := ⟨S, hSspace, hSmap, hS⟩
  rwa [himage] at h

end DifferentialGeometry.Topology.PiecewiseLinear

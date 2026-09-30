/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Cell.Coordinates
import DifferentialGeometry.Topology.Handle.Manifold
import DifferentialGeometry.Topology.Handle.SmoothStage
import DifferentialGeometry.Topology.Manifold.ClosedBall
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedron

open Set Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem isSmoothHandleStage_adjunction_zero
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [CompactSpace M]
    (ψ : {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 4) | z.val ∈ (∅ : Set (Fin 4 → ℝ))} → M) :
    IsSmoothHandleStage (AdjunctionSpace (Subtype.val : _ → Convexity.StdSimplex.coordinateSet ℝ (Fin 4)) ψ)
      (adjunctionLower ψ '' (𝓡∂ 3).boundary M ∪
        adjunctionCell Subtype.val ψ '' {z | z.val ∈ stdSimplexBoundary 3}) := by
  let q : AdjunctionSpace (Subtype.val : _ → Convexity.StdSimplex.coordinateSet ℝ (Fin 4)) ψ ≃ₜ
      (Convexity.StdSimplex.coordinateSet ℝ (Fin 4) ⊕ M) :=
    { toFun := Quot.lift id (by
        intro x y hxy
        rcases hxy with ⟨z, _⟩
        exact (Set.notMem_empty _ z.property).elim)
      invFun := adjunctionMk _ ψ
      left_inv := by
        intro x
        refine Quot.inductionOn x ?_
        intro y
        rfl
      right_inv := by
        intro x
        rfl
      continuous_toFun := continuous_adjunction_lift _ _ (by
        intro x y hxy
        rcases hxy with ⟨z, _⟩
        exact (Set.notMem_empty _ z.property).elim) continuous_id
      continuous_invFun := continuous_adjunctionMk _ _ }
  let c := DifferentialGeometry.Cell.stdSimplexClosedCellHomeomorph 3
  let e := q.trans (Homeomorph.sumCongr c (Homeomorph.refl M))
  let _ : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
    DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2
  let _ : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
    DifferentialGeometry.Topology.Handle.closedCellIsManifold 2
  refine ⟨ClosedCell 3 ⊕ M, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, e, ?_⟩
  have hq_lower (x : M) : q (adjunctionLower ψ x) = Sum.inr x := rfl
  have hq_cell (x : Convexity.StdSimplex.coordinateSet ℝ (Fin 4)) : q (adjunctionCell Subtype.val ψ x) = Sum.inl x := rfl
  have he_lower (x : M) : e (adjunctionLower ψ x) = Sum.inr x := by
    change (Homeomorph.sumCongr c (Homeomorph.refl M)) (q (adjunctionLower ψ x)) = _
    rw [hq_lower x]
    rfl
  have he_cell (x : Convexity.StdSimplex.coordinateSet ℝ (Fin 4)) :
      e (adjunctionCell Subtype.val ψ x) = Sum.inl (c x) := by
    change (Homeomorph.sumCongr c (Homeomorph.refl M))
      (q (adjunctionCell Subtype.val ψ x)) = _
    rw [hq_cell x]
    rfl
  have hc_boundary (x : Convexity.StdSimplex.coordinateSet ℝ (Fin 4)) :
      ‖((c x : ClosedCell 3).val : EuclideanSpace ℝ (Fin 3))‖ = 1 ↔
        x.val ∈ stdSimplexBoundary 3 := by
    change ‖((DifferentialGeometry.Simplex.stdSimplexNormedBallHomeomorph
      (EuclideanSpace.equiv (Fin 3) ℝ).symm x).val : EuclideanSpace ℝ (Fin 3))‖ = 1 ↔ _
    simpa [stdSimplexBoundary, DifferentialGeometry.Simplex.boundary] using
      (DifferentialGeometry.Simplex.stdSimplexNormedBallHomeomorph_mem_sphere_iff
        (e := (EuclideanSpace.equiv (Fin 3) ℝ).symm) x)
  have h_lower : e '' (adjunctionLower ψ '' (𝓡∂ 3).boundary M) =
      Sum.inr '' (𝓡∂ 3).boundary M := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, he_lower z⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨adjunctionLower ψ y, ⟨y, hy, rfl⟩, he_lower y⟩
  have h_cell : e '' (adjunctionCell Subtype.val ψ '' {z | z.val ∈ stdSimplexBoundary 3}) =
      Sum.inl '' {z : ClosedCell 3 | ‖z.val‖ = 1} := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨c z, (hc_boundary z).mpr hz, he_cell z⟩
    · rintro ⟨y, hy, rfl⟩
      let z := c.symm y
      have hcz : c z = y := by
        dsimp [z]
        exact c.apply_symm_apply y
      have hz : z.val ∈ stdSimplexBoundary 3 := (hc_boundary z).mp (by
        rw [hcz]
        exact hy)
      exact ⟨adjunctionCell Subtype.val ψ z, ⟨z, hz, rfl⟩, by
        simpa [hcz] using he_cell z⟩
  rw [Set.image_union, h_lower, h_cell]
  rw [ModelWithCorners.boundary_disjointUnion]
  rw [DifferentialGeometry.Topology.Manifold.closedCell_boundary_eq_sphere 2]
  exact Set.union_comm _ _

end DifferentialGeometry.Topology.PiecewiseLinear

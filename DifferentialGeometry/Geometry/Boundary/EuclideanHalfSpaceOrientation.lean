import DifferentialGeometry.Geometry.Boundary.EuclideanHalfSpaceInstance
import DifferentialGeometry.Analysis.Calculus.LocalExtrema

noncomputable section

open Set Function Topology Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

variable {n : Nat} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

local notation "J" => modelWithCornersEuclideanHalfSpace n

theorem inwardCoordAt_head_pos_euclideanHalfSpace
    (alpha y : BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M)
    (hy : (y : M) ∈ (chartAt (EuclideanHalfSpace n) (alpha : M)).source) :
    0 < (tangentSpaceModelContinuousLinearEquiv
      (I := modelWithCornersEuclideanHalfSpace n) (y : M)
        (inwardCoordAt (M := M) alpha y)) 0 := by
  let e : EuclideanSpace Real (Fin n) := EuclideanSpace.single 0 1
  let phi : EuclideanSpace Real (Fin n) →L[Real] Real := EuclideanSpace.proj 0
  let T := tangentCoordChange J (alpha : M) (y : M) (y : M)
  let f := (extChartAt J (y : M)) ∘ (extChartAt J (alpha : M)).symm
  let z := extChartAt J (alpha : M) (y : M)
  have hys : (y : M) ∈ (extChartAt J (alpha : M)).source := by
    rwa [extChartAt_source]
  have hyy : (y : M) ∈ (extChartAt J (y : M)).source := mem_extChartAt_source (y : M)
  have hrange : Set.range J = {w | 0 ≤ phi w} := range_modelWithCornersEuclideanHalfSpace n
  have hz : phi z = 0 := by
    have h := BoundaryManifold.extChart_mem_frontier_of_mem_source (I := J) hy
    rw [EuclideanHalfSpaceInstance.frontier_range_modelWithCornersEuclideanHalfSpace_eq] at h
    exact h
  have hfz : phi (f z) = 0 := by
    change phi (extChartAt J (y : M) ((extChartAt J (alpha : M)).symm
      (extChartAt J (alpha : M) (y : M)))) = 0
    rw [(extChartAt J (alpha : M)).left_inv hys]
    have h : extChartAt J (y : M) (y : M) ∈ frontier (Set.range J) := y.property
    rw [EuclideanHalfSpaceInstance.frontier_range_modelWithCornersEuclideanHalfSpace_eq] at h
    exact h
  have hmin : IsLocalMinOn (phi ∘ f) {w | 0 ≤ phi w} z := by
    apply Filter.Eventually.of_forall
    intro w
    change phi (f z) ≤ phi (f w)
    rw [hfz]
    exact (chartAt (EuclideanHalfSpace n) (y : M) ((extChartAt J (alpha : M)).symm w)).property
  have hderiv : HasFDerivWithinAt (phi ∘ f) (phi.comp T) {w | 0 ≤ phi w} z := by
    rw [← hrange]
    exact phi.hasFDerivAt.comp_hasFDerivWithinAt z
      (hasFDerivWithinAt_tangentCoordChange ⟨hys, hyy⟩)
  have hne : phi.comp T ≠ 0 := by
    intro hzero
    have hcomp : T (tangentCoordChange J (y : M) (alpha : M) (y : M) e) = e := by
      exact (tangentCoordChange_comp ⟨⟨hyy, hys⟩, hyy⟩).trans (tangentCoordChange_self hyy)
    have h := congrArg (fun L : EuclideanSpace Real (Fin n) →L[Real] Real =>
      L (tangentCoordChange J (y : M) (alpha : M) (y : M) e)) hzero
    change phi (T (tangentCoordChange J (y : M) (alpha : M) (y : M) e)) = 0 at h
    rw [hcomp] at h
    simp [phi, e] at h
  have hpos := hmin.hasFDerivWithinAt_pos_of_halfSpace phi hz hderiv hne
    (show 0 < phi e by simp [phi, e])
  have hin : inwardCoordAt (M := M) alpha y = T e := by
    unfold inwardCoordAt
    rw [← Trivialization.symmL_apply (R := Real)
      (e := trivializationAt (EuclideanSpace Real (Fin n)) (TangentSpace J) (alpha : M)) hy]
    rw [TangentBundle.symmL_trivializationAt_eq_core hy]
    rfl
  rw [hin]
  exact hpos

instance instHasOrientableBoundaryEuclideanHalfSpace : HasOrientableBoundary (I := J) M where
  inwardCoord_chart_consistent := by
    intro alpha0 alpha1 y hy0 hy1
    let e := tangentSpaceModelContinuousLinearEquiv (I := J) (y : M)
    let v0 := inwardCoordAt (M := M) alpha0 y
    let v1 := inwardCoordAt (M := M) alpha1 y
    let a := e v0 0
    let b := e v1 0
    have ha : 0 < a := inwardCoordAt_head_pos_euclideanHalfSpace alpha0 y hy0
    have hb : 0 < b := inwardCoordAt_head_pos_euclideanHalfSpace alpha1 y hy1
    refine ⟨a / b, div_pos ha hb, ?_⟩
    have h0 := sub_head_smul_inwardCoord_mem_range_boundaryInclusionMfderiv y v0
    have h1 := sub_head_smul_inwardCoord_mem_range_boundaryInclusionMfderiv y v1
    let R := LinearMap.range (boundaryInclusionMfderiv (M := M) y).toLinearMap
    have hR : (v0 - a • inwardCoord y) - (a / b) • (v1 - b • inwardCoord y) ∈ R :=
      R.sub_mem h0 (R.smul_mem (a / b) h1)
    rw [smul_sub, smul_smul, div_mul_cancel₀ _ hb.ne'] at hR
    have heq : v0 - a • inwardCoord y - ((a / b) • v1 - a • inwardCoord y) =
        v0 - (a / b) • v1 := by abel
    rw [heq] at hR
    exact hR

theorem EuclideanHalfSpaceInstance.instHasOrientableBoundary_self_EuclideanHalfSpace
    (n : ℕ) [NeZero n] : HasOrientableBoundary
      (I := modelWithCornersEuclideanHalfSpace n) (EuclideanHalfSpace n) :=
  instHasOrientableBoundaryEuclideanHalfSpace

end DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

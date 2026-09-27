import DifferentialGeometry.Geometry.Curvature.Naturality.OpenRestriction
import DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorConeMetric

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem metricAlgebraicCurvatureTensorAt_restrictOpen_mem_curvatureOperatorNonnegativeCone_iff
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    (x : U) :
    metricAlgebraicCurvatureTensorAt (I := I) (M := U) (g.restrictOpen U) x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := U) ↔
    metricAlgebraicCurvatureTensorAt (I := I) (M := M) g (x : M) ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hRm (X Y Z W : TangentSpace I x) :
      metricRm04StandardAt (I := I) (M := U) (g.restrictOpen (I := I) U) x X Y Z W =
        metricRm04StandardAt (I := I) (M := M) g (x : M) X Y Z W := by
    exact (metricRm04StandardAt_restrictOpen (I := I) g U x X Y Z W).trans (by
      rw [mfderiv_subtype_val_apply, mfderiv_subtype_val_apply,
        mfderiv_subtype_val_apply, mfderiv_subtype_val_apply])
  constructor
  · intro hU
    rw [metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff] at hU ⊢
    intro n c v w
    have h := hU n c v w
    calc
      0 ≤ ∑ i, ∑ j, c i * c j *
          metricRm04StandardAt (I := I) (M := U) (g.restrictOpen (I := I) U) x
            (v i) (w i) (w j) (v j) := h
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact congrArg (fun a : ℝ => c i * c j * a)
          (hRm (v i) (w i) (w j) (v j))
  · intro hM
    rw [metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff] at hM ⊢
    intro n c v w
    have h := hM n c v w
    calc
      0 ≤ ∑ i, ∑ j, c i * c j *
          metricRm04StandardAt (I := I) (M := M) g (x : M)
            (v i) (w i) (w j) (v j) := h
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact (congrArg (fun a : ℝ => c i * c j * a)
          (hRm (v i) (w i) (w j) (v j))).symm

end DifferentialGeometry.Geometry.Curvature

end

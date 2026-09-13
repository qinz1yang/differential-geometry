import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.NullSectionalRankRigidity
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorRank

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [T2Space M]

theorem finrank_curvatureOperatorImageAt_ne_two_of_null_sectional_of_ricciReactionDefect_eq_zero
    (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank ℝ (TangentSpace I x) = 3)
    (hcone : metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hdefect : ricciReactionDefectAt (I := I) g x = 0)
    {a b : TangentSpace I x}
    (hgram : 0 < g.inner x a a * g.inner x b b - (g.inner x a b) ^ 2)
    (hsec : metricRm04StandardAt (I := I) (M := M) g x a b b a = 0) :
    Module.finrank ℝ (curvatureOperatorImageAt (I := I) g x
      ⟨metricRm04 (I := I) g x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩) ≠ 2 := by
  have h := metricCurvatureOperatorRankAt_eq_zero_or_one_of_null_sectional
    (I := I) (M := M) g x hdim hcone hdefect hgram hsec
  rw [metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank
    (I := I) (M := M) g x hdim] at h
  have hsub : (⟨metricRm04At (I := I) (M := M) g x,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x) =
      ⟨metricRm04 (I := I) g x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩ :=
    Subtype.ext (metricRm04_apply (I := I) (M := M) g x).symm
  rw [← hsub]
  omega

end DifferentialGeometry.Geometry.Curvature.DimensionThree

end

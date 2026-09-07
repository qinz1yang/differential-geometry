import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.BoundaryContribution.GreenWithBoundary
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.BoundaryContribution.WeightedStokes

open Bundle Manifold MeasureTheory
open scoped Manifold ContDiff

namespace DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

theorem boundaryFaceSum_eq_surface_integral
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    (X : Cₛ^∞⟮(modelWithCornersEuclideanHalfSpace n);
        EuclideanSpace ℝ (Fin n),
        (TangentSpace (modelWithCornersEuclideanHalfSpace n) : M → Type _)⟯) :
    boundaryFaceSum (I := modelWithCornersEuclideanHalfSpace n) g X =
      ∫ x : (modelWithCornersEuclideanHalfSpace n).boundary M,
        g.inner x.val
          (outwardNormal
              (I := modelWithCornersEuclideanHalfSpace n) (M := M) g x :
            TangentSpace _ x.val)
          (X x.val)
        ∂(surfaceMeasure
          (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) := by
  rw [← integral_divergence_with_boundary_eq_boundaryFaceSum]
  exact integral_divergence_g_with_boundary_eq_surfaceMeasure_flux g X

end DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

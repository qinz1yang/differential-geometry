import DifferentialGeometry.Topology.Manifold.OrientationCoverDeck
import DifferentialGeometry.Geometry.Metric.CoveringPullback



noncomputable section
open Bundle Manifold
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Topology.Manifold

namespace Poincare.Geometry.Riemannian

variable {n : ℕ} {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]


def tangentOrientationMetric (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hdim : Module.finrank ℝ E = n) :
    letI := tangentOrientationChartedSpace (M := M) hdim
    letI := tangentOrientation_isManifold (M := M) hdim
    SmoothRiemannianMetric 𝓘(ℝ, E) (tangentOrientationCover (M := M) hdim) := by
  letI := tangentOrientationChartedSpace (M := M) hdim
  letI := tangentOrientation_isManifold (M := M) hdim
  letI := tangentOrientationCover_t2Space (M := M) hdim
  exact localPullMetric g (tangentOrientationProjection hdim)
    (tangentOrientationProjection_isLocalDiffeomorph hdim)

theorem tangentOrientationMetric_inner (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hdim : Module.finrank ℝ E = n) :
    letI := tangentOrientationChartedSpace (M := M) hdim
    letI := tangentOrientation_isManifold (M := M) hdim
    ∀ z : tangentOrientationCover (M := M) hdim, ∀ v w : TangentSpace 𝓘(ℝ, E) z,
      (tangentOrientationMetric g hdim).inner z v w =
        g.inner (tangentOrientationProjection hdim z)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (tangentOrientationProjection hdim) z v)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (tangentOrientationProjection hdim) z w) := by
  let := tangentOrientationChartedSpace (M := M) hdim
  let := tangentOrientation_isManifold (M := M) hdim
  let := tangentOrientationCover_t2Space (M := M) hdim
  exact localPullMetric_inner g (tangentOrientationProjection hdim)
    (tangentOrientationProjection_isLocalDiffeomorph hdim)


theorem tangentOrientationDeck_isometry (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hdim : Module.finrank ℝ E = n) :
    letI := tangentOrientationChartedSpace (M := M) hdim
    letI := tangentOrientation_isManifold (M := M) hdim
    ∀ z : tangentOrientationCover (M := M) hdim, ∀ v w : TangentSpace 𝓘(ℝ, E) z,
      (tangentOrientationMetric g hdim).inner (tangentOrientationDeck hdim z)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (tangentOrientationDeck hdim) z v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (tangentOrientationDeck hdim) z w) =
      (tangentOrientationMetric g hdim).inner z v w := by
  let := tangentOrientationChartedSpace (M := M) hdim
  let := tangentOrientation_isManifold (M := M) hdim
  let := tangentOrientationCover_t2Space (M := M) hdim
  exact localPullMetric_deck_isometry g (tangentOrientationProjection hdim)
    (tangentOrientationProjection_isLocalDiffeomorph hdim)
    (tangentOrientationDeckDiffeomorph hdim) (tangentOrientationDeck_projects hdim)

end Poincare.Geometry.Riemannian

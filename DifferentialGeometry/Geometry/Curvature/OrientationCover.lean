import DifferentialGeometry.Geometry.Curvature.LocalPullback
import DifferentialGeometry.Geometry.Metric.OrientationCover



noncomputable section
open Bundle Manifold
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Topology.Manifold
open Poincare.Geometry.Riemannian

namespace Poincare.Geometry

variable {n : ℕ} {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

theorem HasPositiveSectionalCurvature.tangentOrientationMetric
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} (hg : HasPositiveSectionalCurvature g)
    (hdim : Module.finrank ℝ E = n) :
    letI := tangentOrientationChartedSpace (M := M) hdim
    letI := tangentOrientation_isManifold (M := M) hdim
    HasPositiveSectionalCurvature (tangentOrientationMetric g hdim) := by
  let := tangentOrientationChartedSpace (M := M) hdim
  let := tangentOrientation_isManifold (M := M) hdim
  let := tangentOrientationCover_t2Space (M := M) hdim
  let := tangentOrientationCover_compactSpace (M := M) hdim
  exact hg.localPull (tangentOrientationProjection hdim)
    (tangentOrientationProjection_isLocalDiffeomorph hdim)

omit [CompactSpace M] in
theorem tangentOrientationMetric_sectional_quotient [SecondCountableTopology M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hdim : Module.finrank ℝ E = n) :
    letI := tangentOrientationChartedSpace (M := M) hdim
    letI := tangentOrientation_isManifold (M := M) hdim
    ∀ (z : tangentOrientationCover (M := M) hdim) (v w : TangentSpace 𝓘(ℝ, E) z),
      let h := tangentOrientationMetric g hdim
      let p := tangentOrientationProjection (M := M) hdim
      let D := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) p z
      DifferentialGeometry.Geometry.Curvature.metricRm04StandardAt h z v w w v /
          (h.inner z v v * h.inner z w w - h.inner z v w ^ 2) =
        DifferentialGeometry.Geometry.Curvature.metricRm04StandardAt g (p z) (D v) (D w) (D w) (D v) /
          (g.inner (p z) (D v) (D v) * g.inner (p z) (D w) (D w) -
            g.inner (p z) (D v) (D w) ^ 2) := by
  let := tangentOrientationChartedSpace (M := M) hdim
  let := tangentOrientation_isManifold (M := M) hdim
  let := tangentOrientationCover_t2Space (M := M) hdim
  let := tangentOrientationCover_secondCountable (M := M) hdim
  let := ChartedSpace.locallyCompactSpace E M
  let := ChartedSpace.locallyCompactSpace E (tangentOrientationCover (M := M) hdim)
  intro z v w
  exact sectional_quotient_localPull g (tangentOrientationProjection hdim)
    (tangentOrientationProjection_isLocalDiffeomorph hdim) z v w

end Poincare.Geometry

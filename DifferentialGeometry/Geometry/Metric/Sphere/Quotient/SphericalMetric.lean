import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.SpaceForm
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Metric.CompletenessPullback

namespace GC.Geometry
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff
set_option autoImplicit false
universe u v
variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] [T2Space M]

noncomputable def sphericalMetric (S : SphericalSpaceFormQuotientModel (𝓡 3) M) :
    SmoothRiemannianMetric (𝓡 3) M :=
  Diffeomorph.pullbackMetricCross S.quotient.gQuot S.equiv

theorem sphericalMetric_inner (S : SphericalSpaceFormQuotientModel (𝓡 3) M)
    (x : M) (v w : TangentSpace (𝓡 3) x) :
    (sphericalMetric S).inner x v w =
      S.quotient.gQuot.inner (S.equiv x)
        (mfderiv (𝓡 3) (𝓡 3) S.equiv x v) (mfderiv (𝓡 3) (𝓡 3) S.equiv x w) :=
  Diffeomorph.pullbackMetricCross_inner S.quotient.gQuot S.equiv x v w

theorem sphericalMetric_sectional_one (S : SphericalSpaceFormQuotientModel (𝓡 3) M)
    (x : M) (v w : TangentSpace (𝓡 3) x) :
    metricRm04StandardAt (sphericalMetric S) x v w w v =
      (sphericalMetric S).inner x v v * (sphericalMetric S).inner x w w -
        (sphericalMetric S).inner x v w * (sphericalMetric S).inner x v w := by
  unfold sphericalMetric
  rw [metricRm04Standard_pullbackCross, S.quotient.gQuot_sectional_one,
    Diffeomorph.pullbackMetricCross_inner, Diffeomorph.pullbackMetricCross_inner,
    Diffeomorph.pullbackMetricCross_inner]

theorem sphericalMetric_complete [CompactSpace M]
    (S : SphericalSpaceFormQuotientModel (𝓡 3) M) :
    RiemannianMetricComplete (sphericalMetric S) :=
  RiemannianMetricComplete.of_compact (sphericalMetric S)

theorem complete_spherical_metric_on_actual_carrier [CompactSpace M]
    (S : SphericalSpaceFormQuotientModel (𝓡 3) M) :
    ∃ g : SmoothRiemannianMetric (𝓡 3) M, RiemannianMetricComplete g ∧
      ∀ (x : M) (v w : TangentSpace (𝓡 3) x),
        metricRm04StandardAt g x v w w v =
          g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w :=
  ⟨sphericalMetric S, sphericalMetric_complete S, sphericalMetric_sectional_one S⟩

theorem complete_round_metric_pullback [SigmaCompactSpace M]
    {N : Type v} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ N] [T2Space N] [SigmaCompactSpace N]
    (g : SmoothRiemannianMetric (𝓡 3) N) (hg : RiemannianMetricComplete g)
    (hsec : ∀ (x : N) (v w : TangentSpace (𝓡 3) x),
      metricRm04StandardAt g x v w w v =
        g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w)
    (f : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ N) :
    RiemannianMetricComplete (Diffeomorph.pullbackMetricCross g f) ∧
      ∀ (x : M) (v w : TangentSpace (𝓡 3) x),
        metricRm04StandardAt (Diffeomorph.pullbackMetricCross g f) x v w w v =
          (Diffeomorph.pullbackMetricCross g f).inner x v v *
            (Diffeomorph.pullbackMetricCross g f).inner x w w -
          (Diffeomorph.pullbackMetricCross g f).inner x v w *
            (Diffeomorph.pullbackMetricCross g f).inner x v w := by
  refine ⟨DifferentialGeometry.Geometry.Metric.riemannianMetricComplete_pullbackMetricCross hg f, ?_⟩
  intro x v w
  rw [metricRm04Standard_pullbackCross, hsec,
    Diffeomorph.pullbackMetricCross_inner, Diffeomorph.pullbackMetricCross_inner,
    Diffeomorph.pullbackMetricCross_inner]

end GC.Geometry

import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.SphericalMetric
import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.SpaceFormCovering

namespace GC.Geometry
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff
set_option autoImplicit false
universe u

theorem actual_group_quotient_complete (G : SphericalSpaceFormGroup) :
    RiemannianMetricComplete
      (sphericalMetric (sphericalSpaceFormQuotientModelOfSphericalSpaceFormGroup G)) :=
  sphericalMetric_complete _

noncomputable def orientedSphericalMetric
    (M : ClosedOrientedManifold.{u} 3) (G : SphericalSpaceFormGroup)
    (f : ClosedOrientedManifold.OrientedDiffeomorph M G.manifold.toClosedOrientedManifold) :
    SmoothRiemannianMetric (𝓡 3) M.Carrier :=
  Diffeomorph.pullbackMetricCross
    (sphericalMetric (sphericalSpaceFormQuotientModelOfSphericalSpaceFormGroup G)) f.1

theorem oriented_carrier_metric_inner
    (M : ClosedOrientedManifold.{u} 3) (G : SphericalSpaceFormGroup)
    (f : ClosedOrientedManifold.OrientedDiffeomorph M G.manifold.toClosedOrientedManifold)
    (x : M.Carrier) (v w : TangentSpace (𝓡 3) x) :
    (orientedSphericalMetric M G f).inner x v w =
      (sphericalMetric (sphericalSpaceFormQuotientModelOfSphericalSpaceFormGroup G)).inner
        (f.1 x) (mfderiv (𝓡 3) (𝓡 3) f.1 x v) (mfderiv (𝓡 3) (𝓡 3) f.1 x w) :=
  Diffeomorph.pullbackMetricCross_inner _ f.1 x v w

theorem complete_spherical_metric_from_oriented_model
    (M : ClosedOrientedManifold.{u} 3) (G : SphericalSpaceFormGroup)
    (f : ClosedOrientedManifold.OrientedDiffeomorph M G.manifold.toClosedOrientedManifold) :
    ∃ g : SmoothRiemannianMetric (𝓡 3) M.Carrier, RiemannianMetricComplete g ∧
      ∀ (x : M.Carrier) (v w : TangentSpace (𝓡 3) x),
        metricRm04StandardAt g x v w w v =
          g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w :=
  ⟨orientedSphericalMetric M G f,
    complete_round_metric_pullback _ (actual_group_quotient_complete G)
      (sphericalMetric_sectional_one _) f.1⟩

theorem complete_spherical_metric_with_nontrivial_piOne :
    ∃ (M : ConnectedClosedOrientedManifold.{0} 3)
      (g : SmoothRiemannianMetric (𝓡 3) M.Carrier),
      RiemannianMetricComplete g ∧
      (∀ (x : M.Carrier) (v w : TangentSpace (𝓡 3) x),
        metricRm04StandardAt g x v w w v =
          g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w) ∧
      ∀ p : M.Carrier, ¬ Subsingleton (FundamentalGroup M.Carrier p) := by
  let S := sphericalSpaceFormQuotientModelOfSphericalSpaceFormGroup
    SphericalSpaceFormGroup.antipodal
  exact ⟨SphericalSpaceFormGroup.antipodal.manifold, sphericalMetric S,
    sphericalMetric_complete S, sphericalMetric_sectional_one S,
    SphericalSpaceFormGroup.not_subsingleton_fundamentalGroup_antipodal⟩

theorem complete_spherical_metric_of_positive_space_form
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (h : ∃ g : SmoothRiemannianMetric (𝓡 3) M.Carrier,
      ∃ κ : ℝ, 0 < κ ∧ ∀ x (v w : TangentSpace (𝓡 3) x),
        LinearIndependent ℝ ![v, w] → Riemannian.sectionalCurvature g x v w = κ) :
    ∃ g : SmoothRiemannianMetric (𝓡 3) M.Carrier, RiemannianMetricComplete g ∧
      ∀ (x : M.Carrier) (v w : TangentSpace (𝓡 3) x),
        metricRm04StandardAt g x v w w v =
          g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨G, ⟨f⟩⟩ := exists_orientedDiffeomorph_sphericalSpaceForm_of_constantPositiveSectionalCurvature M g
    ((constantPositiveSectionalCurvatureMetric_iff g).mpr hg)
  exact complete_spherical_metric_from_oriented_model M.toClosedOrientedManifold G f

end GC.Geometry

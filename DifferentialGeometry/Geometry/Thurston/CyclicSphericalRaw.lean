import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.LensLift
import DifferentialGeometry.Geometry.Thurston.ElementaryModels
import DifferentialGeometry.Topology.ThreeManifold.SphericalSpaceFormOrientationClosure

/-!
Concrete orthogonal conjugates of the standard lens actions have actual lifted spherical metrics
and Raw presentations. This family transport does not assume a cyclic classification theorem.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Topology
open GC.Geometry GC.Endpoint GC.Seifert
open scoped Manifold ContDiff

universe u

namespace GC.GraphManifold

attribute [local instance] uliftChartedSpace isManifold_ulift

def sphericalGroupLiftStructure (G : SphericalSpaceFormGroup) :
    GC.Geometry.GeometricStructure (𝓡 3) G.manifold.ulift.{0, u}.Carrier where
  model := .spherical
  metric := Diffeomorph.pullbackMetricCross
    (sphericalMetric (sphericalSpaceFormQuotientModelOfSphericalSpaceFormGroup G))
    (uliftDiffeomorph.{0, u} (𝓡 3) G.manifold.Carrier).symm
  complete := ((sphericalMetric_complete_model_atlas
    (sphericalSpaceFormQuotientModelOfSphericalSpaceFormGroup G)).pullback
      (uliftDiffeomorph.{0, u} (𝓡 3) G.manifold.Carrier).symm).1
  atlas := ((sphericalMetric_complete_model_atlas
    (sphericalSpaceFormQuotientModelOfSphericalSpaceFormGroup G)).pullback
      (uliftDiffeomorph.{0, u} (𝓡 3) G.manifold.Carrier).symm).2
  hyperbolic_finite_volume h := by cases h

theorem sphericalGroupLiftStructure_model (G : SphericalSpaceFormGroup) :
    (sphericalGroupLiftStructure.{u} G).model = .spherical := rfl

theorem sphericalGroupLift_boundary (G : SphericalSpaceFormGroup) :
    (NoCuts.carrier G.manifold.ulift.{0, u}).model.boundary
      (NoCuts.carrier G.manifold.ulift.{0, u}).Carrier = ∅ :=
  closedCarrier_boundary_eq_empty _

section Lens

variable (p : ℕ) [NeZero p] (q : ℤ) (hpq : IsCoprime (p : ℤ) q)
  (φ : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))

def conjugateLensLiftDiffeomorph :
    (lensSpaceLift.{u} p q hpq).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (conjSphericalSpaceFormGroup (lensSpaceFormGroup p q hpq) φ).manifold.ulift.{0, u}.Carrier :=
  ((uliftDiffeomorph.{0, u} (𝓡 3) (lensSpaceFormGroup p q hpq).manifold.Carrier).symm.trans
    (conjOrbitDiffeomorph (lensSpaceFormGroup p q hpq) φ)).trans
      (uliftDiffeomorph.{0, u} (𝓡 3)
        (conjSphericalSpaceFormGroup (lensSpaceFormGroup p q hpq) φ).manifold.Carrier)

theorem exists_rawGraphPresentation_conjugateLensLift :
    ∃ R : RawGraphPresentation
      (NoCuts.carrier
        (conjSphericalSpaceFormGroup (lensSpaceFormGroup p q hpq) φ).manifold.ulift.{0, u}),
      R.components.count = 2 ∧ R.pairing.count = 1 ∧ R.externalCount = 0 := by
  obtain ⟨R, he, hc, ht, hx⟩ := exists_rawGraphPresentation_of_carrierDiffeomorph
    (W' := NoCuts.carrier
      (conjSphericalSpaceFormGroup (lensSpaceFormGroup p q hpq) φ).manifold.ulift.{0, u})
    (lensSpaceLiftRawGraphPresentation.{u} p q hpq) (conjugateLensLiftDiffeomorph p q hpq φ)
  obtain ⟨hc₀, ht₀, he₀⟩ := lensSpaceLiftRawGraphPresentation_counts.{u} p q hpq
  exact ⟨R, hc.trans hc₀, ht.trans ht₀, he.trans he₀⟩

theorem rawGraphPresentation_of_sphericalSpaceForm_lensConjugate :
    Nonempty (RawGraphPresentation
      (NoCuts.carrier
        (conjSphericalSpaceFormGroup (lensSpaceFormGroup p q hpq) φ).manifold.ulift.{0, u})) := by
  obtain ⟨R, hR⟩ := exists_rawGraphPresentation_conjugateLensLift.{u} p q hpq φ
  exact ⟨R⟩

end Lens

end GC.GraphManifold

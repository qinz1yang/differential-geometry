import DifferentialGeometry.Geometry.Thurston.QuaternionPrismRawRecognition_X127_R5b
import DifferentialGeometry.Topology.ThreeManifold.SphericalSpaceFormOrientationClosure
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.CarrierDiffeomorphTransport

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Manifold ContDiff

attribute [local instance] uliftChartedSpace isManifold_ulift

universe u

namespace GC.Geometry.QuaternionPrismConjugateRawX127

open GC.Geometry.QuaternionPrismX127R3
open GC.Geometry.QuaternionPrismCircleBundleRawX127

def prismConjugateLiftDiffeomorph_X127 (n : ℕ) [NeZero n]
    (φ : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) :
    (spaceForm_X127 n).manifold.ulift.{0, u}.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (conjSphericalSpaceFormGroup (spaceForm_X127 n) φ).manifold.ulift.{0, u}.Carrier :=
  ((uliftDiffeomorph.{0, u} (𝓡 3) (spaceForm_X127 n).manifold.Carrier).symm.trans
    (conjOrbitDiffeomorph (spaceForm_X127 n) φ)).trans
      (uliftDiffeomorph.{0, u} (𝓡 3)
        (conjSphericalSpaceFormGroup (spaceForm_X127 n) φ).manifold.Carrier)

theorem nonempty_rawGraphPresentation_conjugatePrism_X127 (n : ℕ) [NeZero n]
    (φ : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) :
    Nonempty (RawGraphPresentation (NoCuts.carrier
      (conjSphericalSpaceFormGroup (spaceForm_X127 n) φ).manifold.ulift.{0, u})) :=
by
  obtain ⟨R⟩ := prismHopfRawPresentation_ulift_X127 n
  exact nonempty_rawGraphPresentation_of_carrierDiffeomorph R
    (prismConjugateLiftDiffeomorph_X127 n φ)

end GC.Geometry.QuaternionPrismConjugateRawX127

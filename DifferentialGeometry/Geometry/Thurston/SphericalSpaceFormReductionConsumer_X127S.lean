import DifferentialGeometry.Geometry.Thurston.SphericalSpaceFormReduction_X127S
import DifferentialGeometry.Geometry.Thurston.CyclicSphericalRaw

/-!
Consumer of the X127-S reduction: the hypotheses of the reduction are satisfied by the actual
closed spherical-model carriers `S³/Γ` (actual spherical structure `sphericalGroupLiftStructure`),
and for the conjugate prism groups the whole chain reduction followed by the known Raw families
produces a raw graph presentation of the carrier.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.Geometry GC.Geometry.SphericalSpaceFormReductionX127S
open GC.Geometry.QuaternionPrismX127R3
open scoped Manifold ContDiff

attribute [local instance] uliftChartedSpace isManifold_ulift

universe u

namespace GC.Geometry.SphericalSpaceFormReductionConsumerX127S

theorem reduction_on_spaceForm_carrier_X127S (H : SphericalSpaceFormGroup) :
    ∃ H' : SphericalSpaceFormGroup,
      Nonempty ((NoCuts.carrier H.manifold.ulift.{0, u}).Carrier ≃ₘ⟮
        (NoCuts.carrier H.manifold.ulift.{0, u}).model, 𝓡 3⟯ H'.manifold.Carrier) :=
  exists_sphericalSpaceForm_diffeomorph_of_sphericalStructure_X127S
    (NoCuts.carrier H.manifold.ulift.{0, u}) (sphericalGroupLift_boundary.{u} H)
    (sphericalGroupLiftStructure.{u} H) (sphericalGroupLiftStructure_model.{u} H)

theorem prismCarrier_raw_via_reduction_X127S (n : ℕ) [NeZero n]
    (φ : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) :
    Nonempty (RawGraphPresentation (NoCuts.carrier
      (conjSphericalSpaceFormGroup (spaceForm_X127 n) φ).manifold.ulift.{0, u})) :=
  nonempty_rawGraphPresentation_of_diffeomorph_spaceForm_known_X127S.{u}
    (NoCuts.carrier
      (conjSphericalSpaceFormGroup (spaceForm_X127 n) φ).manifold.ulift.{0, u})
    (conjSphericalSpaceFormGroup (spaceForm_X127 n) φ)
    (Or.inr ⟨n, inferInstance, φ, rfl⟩)
    (uliftDiffeomorph.{0, u} (𝓡 3)
      (conjSphericalSpaceFormGroup (spaceForm_X127 n) φ).manifold.Carrier).symm

theorem cyclicCarrier_raw_via_reduction_X127S (H : SphericalSpaceFormGroup)
    (hcyc : IsCyclic H.group) :
    Nonempty (RawGraphPresentation (NoCuts.carrier H.manifold.ulift.{0, u})) :=
  nonempty_rawGraphPresentation_of_diffeomorph_spaceForm_known_X127S.{u}
    (NoCuts.carrier H.manifold.ulift.{0, u}) H (Or.inl hcyc)
    (uliftDiffeomorph.{0, u} (𝓡 3) H.manifold.Carrier).symm

end GC.Geometry.SphericalSpaceFormReductionConsumerX127S

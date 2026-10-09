import DifferentialGeometry.Topology.ThreeManifold.SphericalSpaceFormOrientationClosure

/-!
# PORT567 compatibility names: orientation closure of spherical space forms

The later layout states the integration-layout results `sphericalSpaceFormOrientationClosure_holds`
and `factorOrientationClosure_holds` (whose statements are the `Prop`s
`sphericalSpaceFormOrientationClosure` and `factorOrientationClosure`) as the named theorems
`SphericalSpaceFormGroup.exists_orientedDiffeomorph_opposite` and `isStandardFactor_opposite`.
-/

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

theorem SphericalSpaceFormGroup.exists_orientedDiffeomorph_opposite
    (G : SphericalSpaceFormGroup) :
    ∃ G' : SphericalSpaceFormGroup,
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        G.manifold.opposite.toClosedOrientedManifold G'.manifold.toClosedOrientedManifold) :=
  sphericalSpaceFormOrientationClosure_holds G

theorem isStandardFactor_opposite (X : ConnectedClosedOrientedManifold.{u} 3)
    (hX : isStandardFactor X) : isStandardFactor X.opposite :=
  factorOrientationClosure_holds X hX

end DifferentialGeometry.Topology

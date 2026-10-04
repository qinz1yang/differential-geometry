import DifferentialGeometry.Topology.ThreeManifold.PrimeDecomposition.SphereTube
import DifferentialGeometry.Topology.ThreeManifold.PrimeDecomposition.BallRecognition

/-!
# Prime closed oriented 3-manifolds are irreducible or `S² × S¹`

The three smooth inputs of `isIrreducible_or_orientedDiffeomorph_sphereTwoTimesCircle_of_isPrime`
are proved in `SphereTube`, `CutCapExistence` and `BallRecognition`; this file records the
unconditional statement (Hatcher, *Notes on basic 3-manifold topology*, Prop. 1.4).
-/

set_option autoImplicit false

open DifferentialGeometry DifferentialGeometry.Topology

namespace GC.Endpoint

universe u

theorem isIrreducible_or_sphereTwoTimesCircle_of_isPrime
    {M : ConnectedClosedOrientedManifold.{u} 3} (hM : IsPrime M) :
    IsIrreducible M ∨
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph M.toClosedOrientedManifold
        sphereTwoTimesCircleLift.ulift.{0, u}.toClosedOrientedManifold) ∨
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph M.toClosedOrientedManifold
        sphereTwoTimesCircleLift.ulift.{0, u}.opposite.toClosedOrientedManifold) :=
  isIrreducible_or_orientedDiffeomorph_sphereTwoTimesCircle_of_isPrime sphereTubeExtension
    sphereSystemCapping capSideBallRecognition hM

end GC.Endpoint

import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Finite
import DifferentialGeometry.Topology.Manifold.Orientation

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff
namespace GC.Endpoint
universe u

def IsPrime (P : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  ∀ A B : ConnectedClosedOrientedManifold.{u} 3,
    Nonempty (P.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (connectedSum A B).Carrier) →
      Nonempty (A.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ standardThreeSphereLift.{u}.Carrier) ∨
      Nonempty (B.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ standardThreeSphereLift.{u}.Carrier)

structure PrimeDecomposition (M : ConnectedClosedOrientedManifold.{u} 3) where
  factors : List (ConnectedClosedOrientedManifold.{u} 3)
  factors_nonempty : factors ≠ []
  prime : ∀ P ∈ factors, IsPrime P
  reconstruction : ClosedOrientedManifold.OrientedDiffeomorph
    (finiteConnectedSum factors).toClosedOrientedManifold M.toClosedOrientedManifold

theorem PrimeDecomposition.factor_index_nonempty
    {M : ConnectedClosedOrientedManifold.{u} 3} (P : PrimeDecomposition M) :
    Nonempty (Fin P.factors.length) :=
  Fin.pos_iff_nonempty.mp (List.length_pos_iff.mpr P.factors_nonempty)

def PrimeDecomposition.transport {M N : ConnectedClosedOrientedManifold.{u} 3}
    (P : PrimeDecomposition M)
    (f : ClosedOrientedManifold.OrientedDiffeomorph M.toClosedOrientedManifold
      N.toClosedOrientedManifold) : PrimeDecomposition N where
  factors := P.factors
  factors_nonempty := P.factors_nonempty
  prime := P.prime
  reconstruction := P.reconstruction.trans f

end GC.Endpoint

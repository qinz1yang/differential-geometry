import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RawLiftAlongUL
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.LensLift

/-!
# Consumers of `RawGraphPresentation.liftAlong_UL` (lane S-ULIFT, G1)

The lift along the ULift diffeomorphism of a closed oriented manifold, applied to an arbitrary raw
presentation and to the lens space presentation (a presentation with two components and one
gluing torus), at universe `1`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff

namespace GC.GraphManifold

/-- Raw presentations of closed manifolds transport from universe `0` to every universe. -/
example (M : ConnectedClosedOrientedManifold.{0} 3) (G : RawGraphPresentation (NoCuts.carrier M)) :
    Nonempty (RawGraphPresentation (NoCuts.carrier M.ulift.{0, 1})) :=
  nonempty_rawGraphPresentation_transport_universe
    (W₀ := NoCuts.carrier M) (W := NoCuts.carrier M.ulift.{0, 1})
    (ClosedOrientedManifold.uliftDiffeomorph M.toClosedOrientedManifold)
    (ClosedOrientedManifold.uliftDiffeomorph_preservesOrientation M.toClosedOrientedManifold)
    ⟨G⟩

/-- A concrete inhabitant: the lens space presentation lifted to universe `1` has two components,
one gluing torus and no external torus. -/
example (p : ℕ) [NeZero p] (q : ℤ) (hpq : IsCoprime (p : ℤ) q) :
    let M := (GC.Seifert.lensSpaceFormGroup p q hpq).manifold
    let G := (lensSpaceRawGraphPresentation p q hpq).liftAlong_UL
      (W := NoCuts.carrier M.ulift.{0, 1})
      (ClosedOrientedManifold.uliftDiffeomorph M.toClosedOrientedManifold)
      (ClosedOrientedManifold.uliftDiffeomorph_preservesOrientation M.toClosedOrientedManifold)
    G.components.count = 2 ∧ G.pairing.count = 1 ∧ G.externalCount = 0 :=
  ⟨rfl, rfl, rfl⟩

end GC.GraphManifold

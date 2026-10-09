import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.Center
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.StandardPrimes

/-!
# Prime manifolds from central elements of the fundamental group

A closed oriented `3`-manifold whose fundamental group has a nontrivial central element is prime,
because such a group is freely indecomposable. It applies to a closed Seifert manifold only once
the class of a regular fibre is shown to be nontrivial and central; this fails in general, e.g.
for `RP³ # RP³`, whose fundamental group `ℤ/2 ∗ ℤ/2` is infinite with trivial centre.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology

universe u

namespace GC.Endpoint

theorem isPrime_of_center_nontrivial (P : ConnectedClosedOrientedManifold.{u} 3) (p : P.Carrier)
    (z : FundamentalGroup P.Carrier p) (hz : z ≠ 1) (hc : ∀ x, x * z = z * x) : IsPrime P :=
  isPrime_of_freelyIndecomposable P p (GC.Group.freelyIndecomposable_of_center_nontrivial _ z hz hc)

end GC.Endpoint

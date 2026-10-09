import DifferentialGeometry.Topology.ThreeManifold.Geometrization.SphereExample
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.FiniteLaws

/-!
# Transport of primality and prime decompositions

Primality of a closed connected oriented `3`-manifold only depends on its smooth carrier, so it is
invariant under arbitrary diffeomorphisms and under orientation reversal. A prime decomposition of
`M` induces one of `M.opposite` with the reversed factors, a prime manifold has the one-factor
decomposition, and in particular the standard `3`-sphere is prime with decomposition `[S³]`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff

namespace GC.Endpoint

universe u v

theorem isPrime_of_diffeomorph {P Q : ConnectedClosedOrientedManifold.{u} 3}
    (f : P.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ Q.Carrier) (hP : IsPrime P) : IsPrime Q := by
  intro A B hd
  obtain ⟨d⟩ := hd
  exact hP A B ⟨f.trans d⟩

theorem isPrime_iff_of_diffeomorph {P Q : ConnectedClosedOrientedManifold.{u} 3}
    (f : P.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ Q.Carrier) : IsPrime P ↔ IsPrime Q :=
  ⟨isPrime_of_diffeomorph f, isPrime_of_diffeomorph f.symm⟩

theorem isPrime_opposite_iff (P : ConnectedClosedOrientedManifold.{u} 3) :
    IsPrime P.opposite ↔ IsPrime P :=
  isPrime_iff_of_diffeomorph (Diffeomorph.refl (𝓡 3) P.Carrier ∞)

private def orientedDiffeomorphOpposite {n : ℕ} {X : ClosedOrientedManifold.{u} n}
    {Y : ClosedOrientedManifold.{v} n} (f : ClosedOrientedManifold.OrientedDiffeomorph X Y) :
    ClosedOrientedManifold.OrientedDiffeomorph X.opposite Y.opposite :=
  ⟨f.1, Diffeomorph.preservesOrientation_opposite f.2⟩

def PrimeDecomposition.opposite {M : ConnectedClosedOrientedManifold.{u} 3}
    (D : PrimeDecomposition M) : PrimeDecomposition M.opposite where
  factors := D.factors.map ConnectedClosedOrientedManifold.opposite
  factors_nonempty := by
    simpa only [ne_eq, List.map_eq_nil_iff] using D.factors_nonempty
  prime P hP := by
    obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hP
    exact (isPrime_opposite_iff Q).mpr (D.prime Q hQ)
  reconstruction := (finiteConnectedSum_opposite D.factors).some.symm.trans
    (orientedDiffeomorphOpposite D.reconstruction)

theorem PrimeDecomposition.opposite_factors {M : ConnectedClosedOrientedManifold.{u} 3}
    (D : PrimeDecomposition M) :
    D.opposite.factors = D.factors.map ConnectedClosedOrientedManifold.opposite :=
  rfl

def PrimeDecomposition.ofIsPrime (P : ConnectedClosedOrientedManifold.{u} 3)
    (hP : IsPrime P) : PrimeDecomposition P where
  factors := [P]
  factors_nonempty := List.cons_ne_nil P []
  prime Q hQ := by
    rw [List.mem_singleton.mp hQ]
    exact hP
  reconstruction := ClosedOrientedManifold.OrientedDiffeomorph.refl P.toClosedOrientedManifold

theorem PrimeDecomposition.ofIsPrime_factors (P : ConnectedClosedOrientedManifold.{u} 3)
    (hP : IsPrime P) : (PrimeDecomposition.ofIsPrime P hP).factors = [P] :=
  rfl

theorem isPrime_standardThreeSphereLift : IsPrime standardThreeSphereLift.{u} := by
  have : SimplyConnectedSpace standardThreeSphere.Carrier :=
    inferInstanceAs (SimplyConnectedSpace SphereThree)
  have : SimplyConnectedSpace standardThreeSphereLift.{u}.Carrier :=
    Homeomorph.ulift.toHomotopyEquiv.simplyConnectedSpace
  exact isPrime_of_simplyConnected _

def standardThreeSphereLiftPrimeDecomposition :
    PrimeDecomposition standardThreeSphereLift.{u} :=
  PrimeDecomposition.ofIsPrime _ isPrime_standardThreeSphereLift

theorem standardThreeSphereLiftPrimeDecomposition_factors :
    standardThreeSphereLiftPrimeDecomposition.{u}.factors = [standardThreeSphereLift.{u}] :=
  rfl

end GC.Endpoint

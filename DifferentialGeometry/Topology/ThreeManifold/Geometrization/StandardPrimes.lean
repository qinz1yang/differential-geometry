import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.Commutative
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.SphereExample
import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.FiniteFreeFactors
import DifferentialGeometry.Topology.VanKampen.FiniteConnectedSumFreeProduct
import DifferentialGeometry.Topology.ThreeManifold.StandardFactors

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff
universe u v w

namespace GC.Endpoint

theorem isPrime_of_freelyIndecomposable (P : ConnectedClosedOrientedManifold.{u} 3)
    (p : P.Carrier) (hp : GC.Group.FreelyIndecomposable (FundamentalGroup P.Carrier p)) :
    IsPrime P := by
  intro A B hd
  obtain ⟨d⟩ := hd
  let e := (fundamentalGroupMulEquivOfHomotopyEquiv d.toHomeomorph.toHomotopyEquiv
    p (d p) rfl).trans
    ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
      (d p) (chosenPoint (connectedSum A B))).trans
        (fundamentalGroup_connectedSum_freeProduct A B).some)
  rcases hp _ _ ⟨e⟩ with hA | hB
  · let : SimplyConnectedSpace A.Carrier :=
      (VanKampen.simplyConnectedSpace_iff_fundamentalGroup_subsingleton
        A.Carrier (chosenPoint A)).mpr hA
    obtain ⟨f⟩ := DifferentialGeometry.Topology.smooth_poincare_conjecture A.Carrier
    exact Or.inl ⟨f.trans standardThreeSphereLiftDiffeomorph⟩
  · let : SimplyConnectedSpace B.Carrier :=
      (VanKampen.simplyConnectedSpace_iff_fundamentalGroup_subsingleton
        B.Carrier (chosenPoint B)).mpr hB
    obtain ⟨f⟩ := DifferentialGeometry.Topology.smooth_poincare_conjecture B.Carrier
    exact Or.inr ⟨f.trans standardThreeSphereLiftDiffeomorph⟩

theorem isPrime_of_finite_fundamentalGroup (P : ConnectedClosedOrientedManifold.{u} 3)
    (p : P.Carrier) [Finite (FundamentalGroup P.Carrier p)] : IsPrime P :=
  isPrime_of_freelyIndecomposable P p (GC.Group.finite_freelyIndecomposable _)

theorem isPrime_of_commutative_fundamentalGroup (P : ConnectedClosedOrientedManifold.{u} 3)
    (p : P.Carrier) (hc : ∀ a b : FundamentalGroup P.Carrier p, a * b = b * a) :
    IsPrime P :=
  isPrime_of_freelyIndecomposable P p (GC.Group.commutative_freelyIndecomposable _ hc)

theorem isPrime_of_isStandardFactor (P : ConnectedClosedOrientedManifold.{u} 3)
    (h : isStandardFactor P) : IsPrime P := by
  let p := chosenPoint P
  rcases h with ⟨G, ⟨f⟩⟩ | ⟨f, _hf⟩
  · let e := (fundamentalGroupMulEquivOfHomotopyEquiv f.val.toHomeomorph.toHomotopyEquiv
      p (f.val p) rfl).trans (G.fundamentalGroupManifoldEquiv (f.val p))
    let : Finite (FundamentalGroup P.Carrier p) := Finite.of_equiv G.group e.symm.toEquiv
    exact isPrime_of_finite_fundamentalGroup P p
  · let e := (fundamentalGroupMulEquivOfHomotopyEquiv f.toHomeomorph.toHomotopyEquiv
      p (f p) rfl).trans (exists_fundamentalGroupMulEquivInt_sphereTwoTimesCircle (f p)).some
    apply isPrime_of_commutative_fundamentalGroup P p
    intro a b
    apply e.injective
    simpa only [map_mul] using mul_comm (e a) (e b)

end GC.Endpoint

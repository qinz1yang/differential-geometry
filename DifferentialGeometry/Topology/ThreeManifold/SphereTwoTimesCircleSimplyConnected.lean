import DifferentialGeometry.Topology.ThreeManifold.SphereTwoTimesCircleLift
import DifferentialGeometry.Topology.Manifold.ULift
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Topology

universe u

theorem not_simplyConnectedSpace_sphereTwoTimesCircle :
    ¬ SimplyConnectedSpace SphereTwoTimesCircle := by
  intro h
  let := h
  let p : SphereTwoTimesCircle := Classical.choice inferInstance
  obtain ⟨e⟩ := exists_fundamentalGroupMulEquivInt_sphereTwoTimesCircle p
  have hZ : Subsingleton (Multiplicative ℤ) := e.symm.injective.subsingleton
  exact Int.zero_ne_one (Multiplicative.ofAdd.injective
    (hZ.elim (Multiplicative.ofAdd (0 : ℤ)) (Multiplicative.ofAdd (1 : ℤ))))

theorem not_simplyConnectedSpace_sphereTwoTimesCircleLift :
    ¬ SimplyConnectedSpace sphereTwoTimesCircleLift.Carrier := by
  intro h
  let H := sphereTwoTimesCircleModelCopy.equiv.toHomeomorph.toHomotopyEquiv
  exact not_simplyConnectedSpace_sphereTwoTimesCircle (H.simplyConnectedSpace_iff.mpr h)

theorem not_simplyConnectedSpace_sphereTwoTimesCircleLift_ulift :
    ¬ SimplyConnectedSpace (sphereTwoTimesCircleLift.ulift.{0, u}).Carrier := by
  intro h
  let H := (ClosedOrientedManifold.uliftDiffeomorph.{0, u}
    sphereTwoTimesCircleLift.toClosedOrientedManifold).toHomeomorph.toHomotopyEquiv
  exact not_simplyConnectedSpace_sphereTwoTimesCircleLift (H.simplyConnectedSpace_iff.mpr h)

end DifferentialGeometry.Topology

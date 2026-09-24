import DifferentialGeometry.Topology.ThreeManifold.PoincareStandard
import DifferentialGeometry.Topology.ThreeManifold.SphereTwoTimesCircleLift

noncomputable section

namespace DifferentialGeometry.Topology

universe u

theorem isStandardFactor_sphereTwoTimesCircleLift :
    isStandardFactor sphereTwoTimesCircleLift :=
  isStandardFactor_of_isSphereTwoTimesCircleFactor
    isSphereTwoTimesCircleFactor_sphereTwoTimesCircleLift

theorem isPoincareStandard_sphereTwoTimesCircleLift :
    isPoincareStandard sphereTwoTimesCircleLift.Carrier :=
  isPoincareStandard_of_standard_factor sphereTwoTimesCircleLift
    isStandardFactor_sphereTwoTimesCircleLift

theorem isPoincareStandard_finiteConnectedSum_sphereTwoTimesCircleLift :
    isPoincareStandard (finiteConnectedSum [sphereTwoTimesCircleLift]).Carrier := by
  refine isPoincareStandard_finite_sum [sphereTwoTimesCircleLift] ?_
  intro F hF
  rw [List.mem_singleton] at hF
  subst hF
  exact isStandardFactor_sphereTwoTimesCircleLift

theorem nonempty_standardThreeSphereLift : Nonempty standardThreeSphereLift.Carrier :=
  inferInstance

theorem nonempty_sphereTwoTimesCircleLift : Nonempty sphereTwoTimesCircleLift.Carrier :=
  inferInstance

theorem nonempty_finiteConnectedSum
    (L : List (ConnectedClosedOrientedManifold.{u} 3)) :
    Nonempty (finiteConnectedSum L).Carrier :=
  inferInstance

end DifferentialGeometry.Topology

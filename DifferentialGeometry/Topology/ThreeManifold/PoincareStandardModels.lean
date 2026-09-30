import DifferentialGeometry.Topology.ThreeManifold.PoincareStandard
import DifferentialGeometry.Topology.ThreeManifold.SphereTwoTimesCircle.SmoothModel

noncomputable section

namespace DifferentialGeometry.Topology

universe u

theorem isStandardFactor_sphereTwoTimesCircleLift :
    isStandardFactor sphereTwoTimesCircleLift :=
  isStandardFactor_of_isSphereTwoTimesCircleFactor
    isSphereTwoTimesCircleFactor_sphereTwoTimesCircleLift

theorem isStandardConnectedSum_sphereTwoTimesCircleLift :
    isStandardConnectedSum sphereTwoTimesCircleLift.Carrier :=
  isStandardConnectedSum_of_standard_factor sphereTwoTimesCircleLift
    isStandardFactor_sphereTwoTimesCircleLift

theorem isStandardConnectedSum_finiteConnectedSum_sphereTwoTimesCircleLift :
    isStandardConnectedSum (finiteConnectedSum [sphereTwoTimesCircleLift]).Carrier := by
  refine isStandardConnectedSum_finite_sum [sphereTwoTimesCircleLift] ?_
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

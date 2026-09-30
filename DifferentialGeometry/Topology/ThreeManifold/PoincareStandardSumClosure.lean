import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardFactorOrientation
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardModels
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedLawsAssembly
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.ChoiceIndependence

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Topology

universe u

theorem isPoincareStandard_finiteConnectedSum
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (hL : ∀ F ∈ L, isPoincareStandard F.Carrier) :
    isPoincareStandard (finiteConnectedSum L).Carrier :=
  isPoincareStandard_of_isOrientedPoincareStandard
    (isOrientedPoincareStandard_finiteConnectedSum L fun F hF =>
      isOrientedPoincareStandard_of_isPoincareStandard F (hL F hF))

theorem isPoincareStandard_connectedSum {M : ConnectedClosedOrientedManifold.{u} 3}
    {N : ConnectedClosedOrientedManifold.{u} 3}
    (hM : isPoincareStandard M.Carrier) (hN : isPoincareStandard N.Carrier) :
    isPoincareStandard (connectedSum M N).Carrier := by
  refine isPoincareStandard_finiteConnectedSum [M, N] ?_
  intro F hF
  rcases List.mem_cons.mp hF with rfl | hF
  · exact hM
  · rw [List.mem_singleton] at hF
    subst hF
    exact hN

theorem nonempty_smoothConnectedSum_sphere_sphereTwoTimesCircle :
    Nonempty (SmoothConnectedSum (orientedBallChart standardThreeSphereLift.{0})
      (orientedBallChart sphereTwoTimesCircleLift) boundaryAttachment) :=
  ⟨smoothConnectedSum standardThreeSphereLift.{0} sphereTwoTimesCircleLift
    (orientedBallChart standardThreeSphereLift.{0})
    (orientedBallChart sphereTwoTimesCircleLift) boundaryAttachment⟩

theorem isPoincareStandard_connectedSum_sphere_sphereTwoTimesCircle :
    isPoincareStandard
      (connectedSum standardThreeSphereLift.{0} sphereTwoTimesCircleLift).Carrier :=
  isPoincareStandard_connectedSum isPoincareStandard_sphere
    isPoincareStandard_sphereTwoTimesCircleLift

theorem isOrientedPoincareStandard_sphereTwoTimesCircleLift :
    isOrientedPoincareStandard sphereTwoTimesCircleLift.toClosedOrientedManifold :=
  isOrientedPoincareStandard_of_standard_factor sphereTwoTimesCircleLift
    isStandardFactor_sphereTwoTimesCircleLift

theorem nonempty_orientedDiffeomorph_connectedSum_sphere_sphereTwoTimesCircle :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum standardThreeSphereLift.{0} sphereTwoTimesCircleLift).toClosedOrientedManifold
      sphereTwoTimesCircleLift.toClosedOrientedManifold) :=
  connectedSum_sphere_left_of_binaryConnectedSumLaws binaryConnectedSumLaws_holds
    sphereTwoTimesCircleLift


end DifferentialGeometry.Topology

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

theorem isPoincareStandard_smoothConnectedSum
    (M N : ConnectedClosedOrientedManifold.{u} 3)
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold)
    (hM : isPoincareStandard M.Carrier) (hN : isPoincareStandard N.Carrier) :
    isPoincareStandard
      (smoothConnectedSum M N c d boundaryAttachment).toConnectedClosedOrientedManifold.Carrier := by
  obtain ⟨e⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_charts
    c (orientedBallChart M) d (orientedBallChart N) boundaryAttachment
  exact isPoincareStandard_of_diffeomorph e.val
    (isPoincareStandard_connectedSum hM hN)

end DifferentialGeometry.Topology

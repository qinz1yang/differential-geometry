import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardFactorOrientation
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardModels
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.FiniteLaws
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.ChoiceIndependence

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Topology

universe u

theorem isStandardConnectedSum_finiteConnectedSum
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (hL : ∀ F ∈ L, isStandardConnectedSum F.Carrier) :
    isStandardConnectedSum (finiteConnectedSum L).Carrier :=
  isStandardConnectedSum_of_isOrientedStandardConnectedSum
    (isOrientedStandardConnectedSum_finiteConnectedSum L fun F hF =>
      isOrientedStandardConnectedSum_of_isStandardConnectedSum F (hL F hF))

theorem isStandardConnectedSum_connectedSum {M : ConnectedClosedOrientedManifold.{u} 3}
    {N : ConnectedClosedOrientedManifold.{u} 3}
    (hM : isStandardConnectedSum M.Carrier) (hN : isStandardConnectedSum N.Carrier) :
    isStandardConnectedSum (connectedSum M N).Carrier := by
  refine isStandardConnectedSum_finiteConnectedSum [M, N] ?_
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

theorem isStandardConnectedSum_connectedSum_sphere_sphereTwoTimesCircle :
    isStandardConnectedSum
      (connectedSum standardThreeSphereLift.{0} sphereTwoTimesCircleLift).Carrier :=
  isStandardConnectedSum_connectedSum isStandardConnectedSum_sphere
    isStandardConnectedSum_sphereTwoTimesCircleLift

theorem isOrientedStandardConnectedSum_sphereTwoTimesCircleLift :
    isOrientedStandardConnectedSum sphereTwoTimesCircleLift.toClosedOrientedManifold :=
  isOrientedStandardConnectedSum_of_standard_factor sphereTwoTimesCircleLift
    isStandardFactor_sphereTwoTimesCircleLift

theorem nonempty_orientedDiffeomorph_connectedSum_sphere_sphereTwoTimesCircle :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum standardThreeSphereLift.{0} sphereTwoTimesCircleLift).toClosedOrientedManifold
      sphereTwoTimesCircleLift.toClosedOrientedManifold) :=
  connectedSum_sphere_left
    sphereTwoTimesCircleLift


end DifferentialGeometry.Topology

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

theorem isStandardConnectedSum_smoothConnectedSum
    (M N : ConnectedClosedOrientedManifold.{u} 3)
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold)
    (hM : isStandardConnectedSum M.Carrier) (hN : isStandardConnectedSum N.Carrier) :
    isStandardConnectedSum
      (smoothConnectedSum M N c d boundaryAttachment).toConnectedClosedOrientedManifold.Carrier := by
  obtain ⟨e⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_charts
    c (orientedBallChart M) d (orientedBallChart N) boundaryAttachment
  exact isStandardConnectedSum_of_diffeomorph e.val
    (isStandardConnectedSum_connectedSum hM hN)

end DifferentialGeometry.Topology

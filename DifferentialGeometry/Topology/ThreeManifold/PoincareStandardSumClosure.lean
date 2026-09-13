import DifferentialGeometry.Topology.ThreeManifold.SphericalSpaceFormOrientationClosure
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardModels
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedLawsAssembly

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Topology

universe u

theorem isPoincareStandard_connectedSum {M : ConnectedClosedOrientedManifold.{u} 3}
    {N : ConnectedClosedOrientedManifold.{u} 3}
    (hM : isPoincareStandard M.Carrier) (hN : isPoincareStandard N.Carrier) :
    isPoincareStandard (connectedSum M N).Carrier := by
  refine poincareStandardSumClosed_holds [M, N] ?_
  intro F hF
  rcases List.mem_cons.mp hF with rfl | hF
  · exact hM
  · rw [List.mem_singleton] at hF
    subst hF
    exact hN

theorem isOrientedPoincareStandardSumClosed_holds :
    isOrientedPoincareStandardSumClosed.{u} :=
  isOrientedPoincareStandardSumClosed_of_connectedSumLaws connectedSumLaws_holds

theorem nonempty_smoothConnectedSum_sphere_sphereTwoTimesCircle :
    Nonempty (SmoothConnectedSum (orientedBallChart standardThreeSphereLift.{0})
      (orientedBallChart sphereTwoTimesCircleLift) boundaryAttachment) :=
  exists_smooth_connected_sum standardThreeSphereLift.{0} sphereTwoTimesCircleLift
    (orientedBallChart standardThreeSphereLift.{0})
    (orientedBallChart sphereTwoTimesCircleLift) boundaryAttachment

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

theorem SphericalCutCapTransition.componentwise_isPoincareStandard_of_localReconstruction
    {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)
    (h : E.localReconstruction) (hctrl : E.poincareControlled)
    (hnext : ∀ C : ConnectedComponents Q.Carrier, isPoincareStandard (Q.component C).Carrier) :
    ∀ C : ConnectedComponents M.Carrier, isPoincareStandard (M.component C).Carrier :=
  E.componentwise_isPoincareStandard h hctrl hnext poincareStandardSumClosed_holds

theorem FiniteCutCapTrace.componentwise_isPoincareStandard_of_localReconstruction
    (T : FiniteCutCapTrace.{u})
    (h : ∀ i : Fin T.eventCount, (T.transition i).localReconstruction)
    (hctrl : T.poincareControlled) (hext : T.extinct) :
    ∀ i : Fin (T.eventCount + 1), ∀ C : ConnectedComponents (T.stage i).Carrier,
      isPoincareStandard ((T.stage i).component C).Carrier :=
  T.componentwise_isPoincareStandard h hctrl hext poincareStandardSumClosed_holds

theorem FiniteCutCapTrace.isPoincareStandard_of_initialIdentification_of_localReconstruction
    (T : FiniteCutCapTrace.{u})
    (h : ∀ i : Fin T.eventCount, (T.transition i).localReconstruction)
    (hctrl : T.poincareControlled) (hext : T.extinct)
    (M : ClosedOrientedManifold.{u} 3) [ConnectedSpace M.Carrier]
    (Φ : T.InitialIdentification M) : isPoincareStandard M.Carrier :=
  T.isPoincareStandard_of_initialIdentification h hctrl hext
    poincareStandardSumClosed_holds M Φ

end DifferentialGeometry.Topology

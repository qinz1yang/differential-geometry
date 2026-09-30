import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Finite
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedLaws
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.AssociativeFlattening
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OppositeSumOrientation
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedCongruence

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Topology

universe u v

theorem finiteConnectedSum_append (L K : List (ConnectedClosedOrientedManifold.{u} 3)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum (L ++ K)).toClosedOrientedManifold
      (connectedSum (finiteConnectedSum L) (finiteConnectedSum K)).toClosedOrientedManifold) :=
  finiteConnectedSum_append_of_unit_assoc_transport
    connectedSum_sphere_right connectedSum_sphere_left connectedSum_assoc
    (fun X _ _ h => h.elim fun f =>
      nonempty_orientedDiffeomorph_connectedSum_of_orientedDiffeomorph
        (ClosedOrientedManifold.OrientedDiffeomorph.refl X.toClosedOrientedManifold) f) L K

theorem finiteConnectedSum_perm {L L' : List (ConnectedClosedOrientedManifold.{u} 3)}
    (hp : L.Perm L') :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum L).toClosedOrientedManifold
      (finiteConnectedSum L').toClosedOrientedManifold) :=
  finiteConnectedSum_perm_of_comm_assoc_transport connectedSum_comm connectedSum_assoc
    (fun _ _ Y h => h.elim fun f =>
      nonempty_orientedDiffeomorph_connectedSum_of_orientedDiffeomorph f
        (ClosedOrientedManifold.OrientedDiffeomorph.refl Y.toClosedOrientedManifold))
    (fun X _ _ h => h.elim fun f =>
      nonempty_orientedDiffeomorph_connectedSum_of_orientedDiffeomorph
        (ClosedOrientedManifold.OrientedDiffeomorph.refl X.toClosedOrientedManifold) f) hp

theorem finiteConnectedSum_congr
    {L : List (ConnectedClosedOrientedManifold.{u} 3)}
    {K : List (ConnectedClosedOrientedManifold.{v} 3)}
    (hf : List.Forall₂ (fun (M : ConnectedClosedOrientedManifold.{u} 3)
      (N : ConnectedClosedOrientedManifold.{v} 3) =>
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          M.toClosedOrientedManifold N.toClosedOrientedManifold)) L K) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum L).toClosedOrientedManifold
      (finiteConnectedSum K).toClosedOrientedManifold) :=
  finiteConnectedSum_congr_of_binary_transport
    (fun _ _ _ _ hM hN => hM.elim fun f => hN.elim fun g =>
      nonempty_orientedDiffeomorph_connectedSum_of_orientedDiffeomorph f g) hf

theorem finiteConnectedSum_opposite (L : List (ConnectedClosedOrientedManifold.{u} 3)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum L).opposite.toClosedOrientedManifold
      (finiteConnectedSum
        (L.map ConnectedClosedOrientedManifold.opposite)).toClosedOrientedManifold) :=
  finiteConnectedSum_opposite_of_binary_transport connectedSum_opposite
    (fun X _ _ h => h.elim fun f =>
      nonempty_orientedDiffeomorph_connectedSum_of_orientedDiffeomorph
        (ClosedOrientedManifold.OrientedDiffeomorph.refl X.toClosedOrientedManifold) f)
    standardThreeSphereLift_orientationReversing_diffeomorph L

end DifferentialGeometry.Topology

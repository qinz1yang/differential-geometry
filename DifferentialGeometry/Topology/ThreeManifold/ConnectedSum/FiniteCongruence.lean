import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.FiniteLaws
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedLawsAssembly

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Topology

universe u

theorem finiteConnectedSum_orientedDiffeomorph_of_forall₂
    {L K : List (ConnectedClosedOrientedManifold.{u} 3)}
    (hf : List.Forall₂ (fun (M N : ConnectedClosedOrientedManifold.{u} 3) =>
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        M.toClosedOrientedManifold N.toClosedOrientedManifold)) L K) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum L).toClosedOrientedManifold
      (finiteConnectedSum K).toClosedOrientedManifold) :=
  finiteConnectedSum_congr_of_connectedSumLaws connectedSumLaws_holds hf

theorem finiteConnectedSum_append_orientedDiffeomorph
    (L K : List (ConnectedClosedOrientedManifold.{u} 3)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum (L ++ K)).toClosedOrientedManifold
      (connectedSum (finiteConnectedSum L) (finiteConnectedSum K)).toClosedOrientedManifold) :=
  finiteConnectedSum_append_of_connectedSumLaws connectedSumLaws_holds L K

theorem finiteConnectedSum_perm_orientedDiffeomorph
    {L K : List (ConnectedClosedOrientedManifold.{u} 3)} (hp : L.Perm K) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum L).toClosedOrientedManifold
      (finiteConnectedSum K).toClosedOrientedManifold) :=
  finiteConnectedSum_perm_of_connectedSumLaws connectedSumLaws_holds hp

theorem finiteConnectedSum_unique
    (f : List (ConnectedClosedOrientedManifold.{u} 3) → ConnectedClosedOrientedManifold.{u} 3)
    (h0 : f [] = standardThreeSphereLift.{u})
    (h1 : ∀ M : ConnectedClosedOrientedManifold.{u} 3, f [M] = M)
    (h2 : ∀ (M N : ConnectedClosedOrientedManifold.{u} 3)
      (L : List (ConnectedClosedOrientedManifold.{u} 3)),
      f (M :: N :: L) = connectedSum M (f (N :: L))) :
    f = finiteConnectedSum := by
  funext L
  induction L with
  | nil => exact h0
  | cons M t ih =>
      cases t with
      | nil => exact h1 M
      | cons N L =>
          rw [h2 M N L, ih]
          rfl

end DifferentialGeometry.Topology

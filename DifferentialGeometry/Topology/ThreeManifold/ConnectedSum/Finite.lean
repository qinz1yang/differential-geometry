import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Construction
import DifferentialGeometry.Topology.ThreeManifold.StandardSphere

noncomputable section

namespace DifferentialGeometry.Topology

universe u v

def finiteConnectedSum : List (ConnectedClosedOrientedManifold.{u} 3) →
    ConnectedClosedOrientedManifold.{u} 3
  | [] => standardThreeSphereLift
  | [M] => M
  | M :: N :: L => connectedSum M (finiteConnectedSum (N :: L))

@[simp]
theorem finiteConnectedSum_nil :
    finiteConnectedSum ([] : List (ConnectedClosedOrientedManifold.{u} 3)) =
      standardThreeSphereLift := rfl

@[simp]
theorem finiteConnectedSum_singleton (M : ConnectedClosedOrientedManifold.{u} 3) :
    finiteConnectedSum [M] = M := rfl

@[simp]
theorem finiteConnectedSum_cons_cons (M N : ConnectedClosedOrientedManifold.{u} 3)
    (L : List (ConnectedClosedOrientedManifold.{u} 3)) :
    finiteConnectedSum (M :: N :: L) = connectedSum M (finiteConnectedSum (N :: L)) := rfl

theorem connectedSum_sphere_right (M : ConnectedClosedOrientedManifold.{u} 3) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum M standardThreeSphereLift.{u}).toClosedOrientedManifold
      M.toClosedOrientedManifold) := by
  sorry

theorem connectedSum_sphere_left (M : ConnectedClosedOrientedManifold.{u} 3) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum standardThreeSphereLift.{u} M).toClosedOrientedManifold
      M.toClosedOrientedManifold) := by
  sorry

theorem finiteConnectedSum_append (L K : List (ConnectedClosedOrientedManifold.{u} 3)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum (L ++ K)).toClosedOrientedManifold
      (connectedSum (finiteConnectedSum L) (finiteConnectedSum K)).toClosedOrientedManifold) := by
  sorry

theorem finiteConnectedSum_perm {L K : List (ConnectedClosedOrientedManifold.{u} 3)}
    (h : L.Perm K) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum L).toClosedOrientedManifold
      (finiteConnectedSum K).toClosedOrientedManifold) := by
  sorry

theorem finiteConnectedSum_congr {L : List (ConnectedClosedOrientedManifold.{u} 3)}
    {K : List (ConnectedClosedOrientedManifold.{v} 3)}
    (h : List.Forall₂ (fun (M : ConnectedClosedOrientedManifold.{u} 3)
      (N : ConnectedClosedOrientedManifold.{v} 3) =>
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          M.toClosedOrientedManifold N.toClosedOrientedManifold)) L K) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum L).toClosedOrientedManifold
      (finiteConnectedSum K).toClosedOrientedManifold) := by
  sorry

theorem finiteConnectedSum_opposite (L : List (ConnectedClosedOrientedManifold.{u} 3)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum L).opposite.toClosedOrientedManifold
      (finiteConnectedSum (L.map ConnectedClosedOrientedManifold.opposite)).toClosedOrientedManifold) := by
  sorry

end DifferentialGeometry.Topology

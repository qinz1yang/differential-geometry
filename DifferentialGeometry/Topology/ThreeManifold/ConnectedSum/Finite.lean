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

end DifferentialGeometry.Topology

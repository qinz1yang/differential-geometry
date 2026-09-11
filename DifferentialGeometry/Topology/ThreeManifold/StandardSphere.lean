import DifferentialGeometry.Topology.Manifold.ClosedOriented
import DifferentialGeometry.Topology.Manifold.SphereOrientation
import DifferentialGeometry.Topology.Manifold.ULift
import Mathlib.Analysis.Normed.Module.Connected

noncomputable section

open Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

def standardThreeSphere : ConnectedClosedOrientedManifold.{0} 3 where
  Carrier := sphere (0 : EuclideanSpace ℝ (Fin 4)) 1
  orientation := sphereOrientation 3 (by decide)
  connected := isConnected_iff_connectedSpace.mp
    (isConnected_sphere
      (Module.one_lt_rank_of_one_lt_finrank (by simp))
      (0 : EuclideanSpace ℝ (Fin 4)) (by norm_num))

@[simp]
theorem standardThreeSphere_carrier :
    standardThreeSphere.Carrier = sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 := rfl

def standardThreeSphereLift : ConnectedClosedOrientedManifold.{u} 3 :=
  ConnectedClosedOrientedManifold.ulift.{0, u} standardThreeSphere

@[simp]
theorem standardThreeSphereLift_carrier :
    standardThreeSphereLift.{u}.Carrier =
      ULift.{u} (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := rfl

def standardThreeSphereLiftDiffeomorph :
    standardThreeSphere.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ standardThreeSphereLift.{u}.Carrier :=
  ClosedOrientedManifold.uliftDiffeomorph standardThreeSphere.toClosedOrientedManifold

theorem standardThreeSphereLiftDiffeomorph_preservesOrientation :
    standardThreeSphereLiftDiffeomorph.{u}.preservesOrientation
      standardThreeSphere.orientation standardThreeSphereLift.{u}.orientation :=
  ClosedOrientedManifold.uliftDiffeomorph_preservesOrientation
    standardThreeSphere.toClosedOrientedManifold

end DifferentialGeometry.Topology

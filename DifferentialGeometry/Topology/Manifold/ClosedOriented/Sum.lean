import DifferentialGeometry.Topology.Manifold.ClosedOriented
import DifferentialGeometry.Topology.Manifold.Orientation.Sum

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.ClosedOrientedManifold

universe u

variable {n : ℕ}

def sum (X Y : ClosedOrientedManifold.{u} n) : ClosedOrientedManifold.{u} n where
  Carrier := X.Carrier ⊕ Y.Carrier
  orientation := ManifoldOrientation.sum X.orientation Y.orientation

@[simp] theorem sum_carrier (X Y : ClosedOrientedManifold.{u} n) :
    (sum X Y).Carrier = (X.Carrier ⊕ Y.Carrier : Type u) := rfl

@[simp] theorem sum_orientation (X Y : ClosedOrientedManifold.{u} n) :
    (sum X Y).orientation = ManifoldOrientation.sum X.orientation Y.orientation := rfl

end DifferentialGeometry.Topology.ClosedOrientedManifold

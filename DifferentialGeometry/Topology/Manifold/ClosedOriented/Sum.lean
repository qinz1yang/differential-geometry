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

@[simp] theorem sum_orientation_inl (Q D : ClosedOrientedManifold.{u} n)
    (q : Q.Carrier) :
    (Q.sum D).orientation.orientation (Sum.inl q) = Q.orientation.orientation q := rfl

@[simp] theorem sum_orientation_inr (Q D : ClosedOrientedManifold.{u} n)
    (d : D.Carrier) :
    (Q.sum D).orientation.orientation (Sum.inr d) = D.orientation.orientation d := rfl

theorem sum_orientation_apply (Q D : ClosedOrientedManifold.{u} n)
    (x : Q.Carrier ⊕ D.Carrier) :
    (Q.sum D).orientation.orientation x =
      match x with
      | Sum.inl q => Q.orientation.orientation q
      | Sum.inr d => D.orientation.orientation d := by
  cases x <;> rfl

end DifferentialGeometry.Topology.ClosedOrientedManifold

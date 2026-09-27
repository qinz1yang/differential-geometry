import DifferentialGeometry.Topology.Manifold.Sigma
import DifferentialGeometry.Topology.Manifold.Components
import Mathlib.Geometry.Manifold.Instances.Real

noncomputable section
open Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

section Union

variable {ι : Type u} [Fintype ι]

def closedOrientedUnion (M : ι → ClosedOrientedManifold.{u} 3) : ClosedOrientedManifold.{u} 3 where
  Carrier := Σ i, (M i).Carrier
  orientation := manifoldOrientationUnion (M := fun i => (M i).Carrier) (I := 𝓡 3)
    (show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 by norm_num)
    (fun i => (M i).orientation)

theorem closedOrientedUnion_carrier (M : ι → ClosedOrientedManifold.{u} 3) :
    (closedOrientedUnion M).Carrier = (Σ i, (M i).Carrier) := rfl

theorem closedOrientedUnion_orientation (M : ι → ClosedOrientedManifold.{u} 3) (i : ι)
    (y : (M i).Carrier) :
    (closedOrientedUnion M).orientation.orientation (⟨i, y⟩ : Σ j, (M j).Carrier) =
      (M i).orientation.orientation y := rfl


end Union

end DifferentialGeometry.Topology

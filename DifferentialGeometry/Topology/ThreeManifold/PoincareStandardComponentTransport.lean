import DifferentialGeometry.Topology.Manifold.ComponentDiffeomorph
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandard

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.ClosedOrientedManifold

universe u
variable {M N : ClosedOrientedManifold.{u} 3}

theorem componentwise_isPoincareStandard_iff_of_diffeomorph
    (e : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ N.Carrier) :
    (∀ C : ConnectedComponents M.Carrier, isPoincareStandard (M.component C).Carrier) ↔
      ∀ C : ConnectedComponents N.Carrier, isPoincareStandard (N.component C).Carrier := by
  constructor
  · intro h C
    exact isPoincareStandard_of_diffeomorph (diffeomorphComponent e.symm C) (h _)
  · intro h C
    exact isPoincareStandard_of_diffeomorph (diffeomorphComponent e C) (h _)

end DifferentialGeometry.Topology.ClosedOrientedManifold

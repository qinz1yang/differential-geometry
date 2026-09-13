import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Commutative
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SphereCapFillingIsometry

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

theorem nonempty_diffeomorph_connectedSum_sphere_left_unit
    (X : ConnectedClosedOrientedManifold.{u} 3) :
    Nonempty ((connectedSum standardThreeSphereLift.{u} X).toClosedOrientedManifold.Carrier
      ≃ₘ⟮𝓡 3, 𝓡 3⟯ X.toClosedOrientedManifold.Carrier) :=
  (nonempty_diffeomorph_connectedSum_comm standardThreeSphereLift.{u} X).elim fun e₁ =>
    (nonempty_diffeomorph_connectedSum_sphere_right_unit X).elim fun e₂ => ⟨e₁.trans e₂⟩

end DifferentialGeometry.Topology

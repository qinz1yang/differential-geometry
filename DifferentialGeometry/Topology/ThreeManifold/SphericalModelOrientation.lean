import DifferentialGeometry.Topology.ThreeManifold.SphericalSpaceFormOrientationClosure
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardComponentwise

set_option autoImplicit false
noncomputable section
open Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

theorem exists_oriented_spherical_model_of_diffeomorph
    (M : ConnectedClosedOrientedManifold.{u} 3) (G : SphericalSpaceFormGroup)
    (e : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ G.manifold.Carrier) :
    ∃ (H : SphericalSpaceFormGroup)
      (τ : G.manifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ H.manifold.Carrier)
      (f : ClosedOrientedManifold.OrientedDiffeomorph M.toClosedOrientedManifold H.manifold.toClosedOrientedManifold),
      f.1 = e.trans τ ∧
      ((H = G ∧ HEq τ (Diffeomorph.refl (𝓡 3) G.manifold.Carrier ∞)) ∨
        τ.preservesOrientation G.manifold.orientation.opposite H.manifold.orientation) ∧
      isStandardFactor M := by
  rcases Diffeomorph.preservesOrientation_or_preservesOrientation_opposite e M.orientation G.manifold.orientation with h | h
  · let f : ClosedOrientedManifold.OrientedDiffeomorph M.toClosedOrientedManifold G.manifold.toClosedOrientedManifold := ⟨e,h⟩
    refine ⟨G,Diffeomorph.refl (𝓡 3) G.manifold.Carrier ∞,f,?_,Or.inl ⟨rfl,HEq.rfl⟩,?_⟩
    · rfl
    · exact Or.inl ⟨G,⟨f⟩⟩
  · obtain ⟨H,⟨τ,hτ⟩⟩ := sphericalSpaceFormOrientationClosure_holds G
    let f : ClosedOrientedManifold.OrientedDiffeomorph M.toClosedOrientedManifold H.manifold.toClosedOrientedManifold :=
      ⟨e.trans τ,Diffeomorph.preservesOrientation_trans h hτ⟩
    exact ⟨H,τ,f,rfl,Or.inr hτ,Or.inl ⟨H,⟨f⟩⟩⟩

end DifferentialGeometry.Topology

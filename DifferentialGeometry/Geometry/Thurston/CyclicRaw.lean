import DifferentialGeometry.Geometry.Thurston.CyclicFibre

/-!
# Cyclic affine deck recognition on the original carrier model

The original empty-boundary carrier is recharted by its actual closed-model diffeomorphism.
The same affine action and covering fibres produce the constructed whole torus fibre there.
Its raw graph presentation is transported back along that diffeomorphism to the same original
carrier, in any universe and for either original model kind. This is the cyclic case only.
-/

set_option autoImplicit false

noncomputable section

open Set Module Function DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint Manifold
open scoped Manifold ContDiff

namespace GC.GraphManifold.FlatTorus

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
open DifferentialGeometry.Geometry.FlatSurface

theorem rawGraphPresentation_of_cyclicAffineCover
    (W : CompactCarrier.{u}) [instW : ConnectedSpace W.Carrier]
    (hboundary : W.model.boundary W.Carrier = ∅)
    (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3)) (p : E3 → W.Carrier)
    (hp : IsLocalDiffeomorph (𝓡 3) W.model ∞ p) (hs : Surjective p)
    (hrel : ∀ x y, p x = p y ↔ ∃ γ : G, γ.val x = y) {R : ℝ}
    (hdisc : ∀ B : ℝ, Set.Finite {a : G | ‖a.val 0‖ ≤ B})
    (hcov : ∀ x : E3, ∃ k : G, ‖x - k.val 0‖ ≤ R)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hdet : ∀ γ : G,
      0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearEquiv.toLinearMap)
    (hcyclic : IsCyclic (affineLinearHom.comp G.subtype).range) :
    Nonempty (RawGraphPresentation W) := by
  obtain ⟨Q, d, _hdo⟩ := Assembly.exists_closedModel_of_boundary_eq_empty W hboundary
  have hp' : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (d ∘ p) := by
    intro x
    exact (hp x).comp (𝓡 3) Q.Carrier (d.isLocalDiffeomorph (p x))
  have hs' : Surjective (d ∘ p) := d.surjective.comp hs
  have hr' (x y : E3) : (d ∘ p) x = (d ∘ p) y ↔ ∃ γ : G, γ.val x = y :=
    d.injective.eq_iff.trans (hrel x y)
  obtain ⟨_ell, _F, _f, _hel, _hprim, _hF, _hdF, _he, _hr, _hFp, hRaw⟩ :=
    exists_torusFibre_of_cyclicDeck Q G (d ∘ p) hp' hs' hr' hdisc hcov hfree hdet hcyclic
  obtain ⟨A⟩ := hRaw
  exact nonempty_rawGraphPresentation_of_carrierDiffeomorph A d.symm

end GC.GraphManifold.FlatTorus

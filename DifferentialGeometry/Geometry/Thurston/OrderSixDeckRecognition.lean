import DifferentialGeometry.Geometry.Exponential.Flat.OrderSixHolonomy
import DifferentialGeometry.Geometry.Thurston.OrderThreeDeckRecognition

/-!
An actual order-six inverse-normalizer affine cover produces a raw graph presentation on
the same original empty-boundary carrier. Its actual square gives the proved order-three
branch, without assuming an axis, cyclic holonomy, fibre or Raw presentation.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff

namespace GC.GraphManifold.FlatTorus

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
open DifferentialGeometry.Geometry.FlatSurface

theorem rawGraphPresentation_of_orderSixNormalizerDeck
    (W : CompactCarrier.{u}) [instW : ConnectedSpace W.Carrier]
    (hboundary : W.model.boundary W.Carrier = ∅)
    (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3)) (p : E3 → W.Carrier)
    (hp : IsLocalDiffeomorph (𝓡 3) W.model ∞ p) (hs : Function.Surjective p)
    (hrel : ∀ x y, p x = p y ↔ ∃ γ : G, γ.val x = y) {R : ℝ}
    (hdisc : ∀ B : ℝ, Set.Finite {a : G | ‖a.val 0‖ ≤ B})
    (hcov : ∀ x : E3, ∃ k : G, ‖x - k.val 0‖ ≤ R)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hdet : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap)
    (g : G) (ho : orderOf g.val.linearIsometryEquiv = 6)
    (hc : ∀ γ : G, γ.val.linearIsometryEquiv * g.val.linearIsometryEquiv *
      γ.val.linearIsometryEquiv⁻¹ = g.val.linearIsometryEquiv ∨
      γ.val.linearIsometryEquiv * g.val.linearIsometryEquiv *
        γ.val.linearIsometryEquiv⁻¹ = g.val.linearIsometryEquiv⁻¹) :
    Nonempty (RawGraphPresentation W) := by
  obtain ⟨h3, hn⟩ := orderSix_square_cube_nontrivial g.val.linearIsometryEquiv ho
  have hsq : (g ^ 2).val.linearIsometryEquiv = g.val.linearIsometryEquiv ^ 2 :=
    map_pow (affineLinearHom.comp G.subtype) g 2
  have h3' : (g ^ 2).val.linearIsometryEquiv ^ 3 = 1 := by rw [hsq]; exact h3
  have hn' : (g ^ 2).val.linearIsometryEquiv ≠ 1 := by rw [hsq]; exact hn
  have hcs (γ : G) : γ.val.linearIsometryEquiv * (g ^ 2).val.linearIsometryEquiv *
      γ.val.linearIsometryEquiv⁻¹ = (g ^ 2).val.linearIsometryEquiv ∨
      γ.val.linearIsometryEquiv * (g ^ 2).val.linearIsometryEquiv *
        γ.val.linearIsometryEquiv⁻¹ = (g ^ 2).val.linearIsometryEquiv⁻¹ := by
    rw [hsq]
    exact inverseNormalizer_square γ.val.linearIsometryEquiv g.val.linearIsometryEquiv (hc γ)
  exact rawGraphPresentation_of_orderThreeNormalizerDeck W hboundary G p hp hs hrel
    hdisc hcov hfree hdet (g ^ 2) h3' hn' hcs

end GC.GraphManifold.FlatTorus

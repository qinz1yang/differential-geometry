import DifferentialGeometry.Geometry.Exponential.Flat.SixElementHolonomy
import DifferentialGeometry.Geometry.Thurston.CyclicRaw

/-!
An actual affine cover with six-element holonomy produces a raw graph presentation on
its same original empty-boundary carrier. The actual lattice, normal order-three subgroup,
inverse-normalizer relations and cyclic holonomy are constructed internally before the
frozen cyclic fibre reconstruction; no axis, cyclic, fibre or Raw output is assumed.
-/

set_option autoImplicit false

noncomputable section

open Set Module DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff

namespace GC.GraphManifold.FlatTorus

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
open DifferentialGeometry.Geometry.FlatSurface

theorem rawGraphPresentation_of_sixElementDeck
    (W : CompactCarrier.{u}) [instW : ConnectedSpace W.Carrier]
    (hboundary : W.model.boundary W.Carrier = ∅)
    (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3)) (p : E3 → W.Carrier)
    (hp : IsLocalDiffeomorph (𝓡 3) W.model ∞ p) (hs : Function.Surjective p)
    (hrel : ∀ x y, p x = p y ↔ ∃ γ : G, γ.val x = y) {R : ℝ}
    (hdisc : ∀ B : ℝ, Set.Finite {a : G | ‖a.val 0‖ ≤ B})
    (hcov : ∀ x : E3, ∃ k : G, ‖x - k.val 0‖ ≤ R)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hdet : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap)
    (hc : Nat.card (affineLinearHom.comp G.subtype).range = 6) :
    Nonempty (RawGraphPresentation W) := by
  obtain ⟨b, hb, hf⟩ := exists_bieberbach_lattice G hdisc hcov hfree
  let instQuotient : Finite (G ⧸ affineTranslationKernel G) := hf
  let instLinear : Finite (affineLinearHom.comp G.subtype).range :=
    Finite.of_equiv (G ⧸ affineTranslationKernel G)
      (QuotientGroup.quotientKerEquivRange (affineLinearHom.comp G.subtype)).toEquiv
  have hdim : finrank ℝ E3 = 3 := by simp
  let e : Fin (finrank ℝ E3) ≃ Fin 3 := Equiv.cast (congrArg Fin hdim)
  have hb' : Submodule.span ℤ (range (b.reindex e)) = affineTranslationModule G := by
    rw [b.range_reindex e]
    exact hb
  have hcyclic := affineFree_card_six_holonomy_isCyclic G (b.reindex e)
    hb' hfree hdet hc
  exact rawGraphPresentation_of_cyclicAffineCover W hboundary G p hp hs hrel
    hdisc hcov hfree hdet hcyclic

end GC.GraphManifold.FlatTorus

import DifferentialGeometry.Geometry.Exponential.Flat.CentralDeckAxis
import DifferentialGeometry.Geometry.Thurston.InvariantAxisRecognition

/-!
A nonidentity central motion in the actual free affine deck group constructs a common fixed
axis and hence a raw graph presentation on the same covered oriented closed manifold.
No axis, coordinate, fibre, cyclic classification or raw presentation is assumed.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff

namespace GC.GraphManifold.FlatTorus

local notation "E3" => EuclideanSpace ℝ (Fin 3)
open DifferentialGeometry.Geometry.FlatSurface

theorem rawGraphPresentation_of_centralDeck (Q : ConnectedClosedOrientedManifold 3)
    (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3)) (p : E3 → Q.Carrier)
    (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p) (hs : Function.Surjective p)
    (hrel : ∀ x y, p x = p y ↔ ∃ γ : G, γ.val x = y) {R : ℝ}
    (hdisc : ∀ B : ℝ, Set.Finite {a : G | ‖a.val 0‖ ≤ B})
    (hcov : ∀ x : E3, ∃ k : G, ‖x - k.val 0‖ ≤ R)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hdet : ∀ γ : G,
      0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearEquiv.toLinearMap)
    (g : G) (hg : g ≠ 1) (hc : g ∈ Subgroup.center G) :
    Nonempty (RawGraphPresentation (NoCuts.carrier Q)) := by
  obtain ⟨q, hq, hfix⟩ := exists_centralDeck_fixedVector G hfree g hg hc
  exact rawGraphPresentation_of_invariantAxisDeck Q G p hp hs hrel hdisc hcov
    hfree hdet q hq hfix

end GC.GraphManifold.FlatTorus

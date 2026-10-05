import DifferentialGeometry.Geometry.Exponential.Flat.FlatDeckLattice
import DifferentialGeometry.Geometry.Exponential.Flat.TorusDeckSmooth
import DifferentialGeometry.Geometry.Exponential.Flat.AffineDeckOrientation

/-!
# The same flat manifold as its actual finite affine torus quotient

The original Euclidean geometric structure supplies an isometric universal covering. Its
actual deck group produces a full translation lattice and finite quotient. The free affine
isometric torus action uses the canonical smooth quotient atlas, and the resulting whole
diffeomorphism retains the original covering square. Actual deck linear parts have positive
determinant because they cover the same orientation on the original manifold. The basis need
not be rectangular, and no comparison with a standard product metric is asserted.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open GC.GraphManifold.FlatTorus
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.FlatSurface

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_euclidean_finiteTorusQuotient (P : ConnectedClosedOrientedManifold.{u} 3)
    (g : GC.Geometry.GeometricStructure (𝓡 3) P.Carrier) (hg : g.model = .euclidean) :
    ∃ p : E3 → P.Carrier, IsCoveringMap p ∧ Function.Surjective p ∧
      IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p ∧
      ∃ hIso : ∀ γ : coveringDeckGroup p, Isometry (γ.1 : E3 → E3),
      let G := isometricDeckAffineGroup p hIso
      ∃ b : Module.Basis (Fin 3) ℝ E3,
      ∃ hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G,
      ∃ hf : Finite (G ⧸ affineTranslationKernel G),
      ∃ hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, (γ : E3 ≃ᵃⁱ[ℝ] E3) x ≠ x,
      letI _instCharts := finiteTorusDeckCharts G b hb hf hfree
      ∃ e : P.Carrier ≃ₘ⟮𝓡 3, addTripleModel⟯ finiteTorusDeckQuotient G b hb,
        (∀ x, e (p x) = Quotient.mk'' (periodicTriple b x)) ∧
        ∀ γ : G, 0 < LinearMap.det
          (γ : E3 ≃ᵃⁱ[ℝ] E3).linearIsometryEquiv.toLinearEquiv.toLinearMap := by
  obtain ⟨p, hp, hs, hl, hIso, b, hb, hf, hrel⟩ := exists_euclideanDeckLattice P g hg
  have hfree := isometricDeckAffineGroup_free p hIso hp
  obtain ⟨e, he⟩ := exists_finiteTorusDeckDiffeomorph
    (isometricDeckAffineGroup p hIso) b hb hf hfree p hl hp hs hrel
  exact ⟨p, hp, hs, hl, hIso, b, hb, hf, hfree, e, he,
    isometricDeckAffineGroup_det_pos P.orientation p hl hIso⟩

end DifferentialGeometry.Geometry.FlatSurface

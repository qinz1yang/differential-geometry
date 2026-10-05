import DifferentialGeometry.Geometry.Exponential.Flat.EuclideanDeckCover
import DifferentialGeometry.Geometry.Exponential.Flat.IsometricDeckAction
import DifferentialGeometry.Geometry.Exponential.Flat.Bieberbach

/-!
# The actual translation lattice of the original flat manifold

The normalized covering of the original Euclidean geometric structure produces its affine
isometric deck group. Its actual covering supplies freeness, discreteness and cocompactness,
so the proved first Bieberbach theorem supplies a full lattice and finite quotient.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open Module Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.FlatSurface

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_euclideanDeckLattice (P : ConnectedClosedOrientedManifold.{u} 3)
    (g : GC.Geometry.GeometricStructure (𝓡 3) P.Carrier) (hg : g.model = .euclidean) :
    ∃ p : E3 → P.Carrier,
      IsCoveringMap p ∧ Function.Surjective p ∧ IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p ∧
      ∃ hIso : ∀ γ : coveringDeckGroup p, Isometry (γ.1 : E3 → E3),
      let G := isometricDeckAffineGroup p hIso
      ∃ b : Basis (Fin 3) ℝ E3,
        Submodule.span ℤ (range b) = affineTranslationModule G ∧
        Finite (G ⧸ affineTranslationKernel G) ∧
        ∀ x y, p x = p y ↔ ∃ γ : G, (γ : E3 ≃ᵃⁱ[ℝ] E3) x = y := by
  obtain ⟨p, hp, hs, hl, hIso⟩ := exists_isometricCover_of_euclidean P g hg
  let G := isometricDeckAffineGroup p hIso
  have hd := isometricDeckAffineGroup_bounded_finite p hIso hp hs
  obtain ⟨R, hc⟩ := isometricDeckAffineGroup_orbit_net p hIso hp hs
  have hfree := isometricDeckAffineGroup_free p hIso hp
  obtain ⟨b, hb, hf⟩ := exists_bieberbach_lattice G hd hc hfree
  have hdim : Module.finrank ℝ E3 = 3 := by simp
  let e : Fin (Module.finrank ℝ E3) ≃ Fin 3 := Equiv.cast (congrArg Fin hdim)
  have hb' : Submodule.span ℤ (range (b.reindex e)) = affineTranslationModule G := by
    rw [b.range_reindex e]
    exact hb
  exact ⟨p, hp, hs, hl, hIso, b.reindex e, hb', hf,
    fun x y => isometricDeckAffineGroup_fibres hIso hp⟩

end DifferentialGeometry.Geometry.FlatSurface

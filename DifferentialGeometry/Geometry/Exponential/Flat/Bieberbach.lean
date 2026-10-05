import DifferentialGeometry.Geometry.Exponential.Flat.TranslationLattice
import DifferentialGeometry.Geometry.Exponential.Flat.RotationRestriction

/-!
# The first Bieberbach theorem for actual free Euclidean actions

A discrete cocompact free affine Euclidean group has a full translation lattice and finite
quotient by that actual translation subgroup. The full span follows from the proved small
rotation restriction and is then used by the lattice construction. Neither a lattice nor a
finite-index assumption is supplied.
-/

set_option autoImplicit false

noncomputable section

open Module Set

namespace DifferentialGeometry.Geometry.FlatSurface

variable {V : Type*} [instV : NormedAddCommGroup V]
  [instInner : InnerProductSpace ℝ V] [instFD : FiniteDimensional ℝ V]

theorem exists_bieberbach_lattice (G : Subgroup (V ≃ᵃⁱ[ℝ] V)) {R : ℝ}
    (hdisc : ∀ B : ℝ, Set.Finite {a : G | ‖(a : V ≃ᵃⁱ[ℝ] V) 0‖ ≤ B})
    (hcov : ∀ x : V, ∃ k : G, ‖x - (k : V ≃ᵃⁱ[ℝ] V) 0‖ ≤ R)
    (hfree : ∀ a : G, a ≠ 1 → ∀ x : V, (a : V ≃ᵃⁱ[ℝ] V) x ≠ x) :
    ∃ b : Basis (Fin (finrank ℝ V)) ℝ V,
      Submodule.span ℤ (Set.range b) = affineTranslationModule G ∧
        Finite (G ⧸ affineTranslationKernel G) := by
  have hspan := affineTranslationModule_span_eq_top G hdisc hcov hfree
  obtain ⟨b, hb⟩ := exists_affineTranslation_lattice G hdisc hspan
  exact ⟨b, hb, finite_affineTranslation_quotient G hdisc hspan⟩

end DifferentialGeometry.Geometry.FlatSurface

import DifferentialGeometry.Geometry.Exponential.Flat.InvariantAxisCoordinate
import DifferentialGeometry.Geometry.Thurston.CyclicFibre

/-!
A free oriented cocompact affine three-dimensional deck action with a common nonzero fixed
vector yields a raw presentation of its original covered manifold. Its integer coordinate,
primitive character and whole embedded torus fibre are constructed from the actual group.
The rotation group need not be presented as cyclic, and no fibre or Raw object is supplied.
-/

set_option autoImplicit false

noncomputable section

open Set Module Function DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint Manifold
open scoped Manifold ContDiff

namespace GC.GraphManifold.FlatTorus

local notation "E3" => EuclideanSpace ℝ (Fin 3)
open DifferentialGeometry.Geometry.FlatSurface

theorem rawGraphPresentation_of_invariantAxisDeck (Q : ConnectedClosedOrientedManifold 3)
    (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3)) (p : E3 → Q.Carrier)
    (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p) (hs : Surjective p)
    (hrel : ∀ x y, p x = p y ↔ ∃ γ : G, γ.val x = y) {R : ℝ}
    (hdisc : ∀ B : ℝ, Set.Finite {a : G | ‖a.val 0‖ ≤ B})
    (hcov : ∀ x : E3, ∃ k : G, ‖x - k.val 0‖ ≤ R)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hdet : ∀ γ : G,
      0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearEquiv.toLinearMap)
    (q : E3) (hq : q ≠ 0) (hfix : ∀ γ : G, γ.val.linearIsometryEquiv q = q) :
    Nonempty (RawGraphPresentation (NoCuts.carrier Q)) := by
  obtain ⟨b, hb, hfinite⟩ := exists_bieberbach_lattice G hdisc hcov hfree
  let instQuotient : Finite (G ⧸ affineTranslationKernel G) := hfinite
  let instLinear : Finite (affineLinearHom.comp G.subtype).range :=
    Finite.of_equiv (G ⧸ affineTranslationKernel G)
      (QuotientGroup.quotientKerEquivRange (affineLinearHom.comp G.subtype)).toEquiv
  obtain ⟨ell, hel, hlin, hint, hintL⟩ :=
    exists_invariantAxis_integerCovector G b hb q hq hfix
  obtain ⟨a, ha, honto, hker, hinc, hprimitive⟩ :=
    exists_primitive_deck_covector G ell hel hlin hint
      (affineTranslationModule_span_eq_top G hdisc hcov hfree)
  have hscaled (γ : G) (v : E3) :
      (a • ell) (γ.val.linearIsometryEquiv v) = (a • ell) v := by
    simp only [smul_apply, smul_eq_mul, hlin]
  have hzero (γ : G) (hz : (a • ell) (γ.val 0) = 0) (x : E3) :
      γ.val x = x + γ.val 0 := by
    by_cases he : γ = 1
    · simp [he]
    · exact affine_translation_of_zero_coordinate (by simp) (a • ell) honto γ.val
        (hscaled γ) hz (hdet γ) (hfree γ he) x
  have hcoords (i : Fin (finrank ℝ E3)) : ∃ m : ℤ, (a • ell) (b i) = m := by
    have hbi : b i ∈ affineTranslationModule G := hb ▸ Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨m, hm⟩ := hinc ⟨AffineIsometryEquiv.constVAdd ℝ E3 (b i), hbi⟩
    change (a • ell) (b i + 0) = m at hm
    exact ⟨m, by simpa only [add_zero] using hm⟩
  obtain ⟨c, hc⟩ := exists_integerHyperplane_basis (by simp) b (a • ell) honto hcoords
  have hplane : Submodule.span ℤ (range c) =
      ZLattice.comap ℝ (affineTranslationModule G) (a • ell).toLinearMap.ker.subtype := by
    rw [← hb]
    exact hc
  obtain ⟨F, f, hF, hdF, he, hr, hvalue⟩ :=
    exists_torusFibre_of_primitiveDeckCoordinate Q G p hp hs hrel (a • ell)
      honto hscaled hinc hprimitive hzero c hplane
  exact Assembly.exists_rawGraphPresentation_of_torusBundle (NoCuts.carrier Q)
    (closedCarrier_boundary_eq_empty Q) F hF hdF f he hr

end GC.GraphManifold.FlatTorus

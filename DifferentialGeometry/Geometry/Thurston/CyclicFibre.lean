import DifferentialGeometry.Geometry.Thurston.PlaneFibre
import DifferentialGeometry.Geometry.Thurston.PrimitiveDeck

/-!
# Whole torus fibres of actual cyclic affine deck covers

The ordinary free cocompact deck action supplies its actual lattice and invariant coordinate.
Its integer character is normalized primitively, and the kernel plane descends through the
same covering to the entire embedded torus level. This gives a raw presentation of the same
closed carrier in the cyclic case, without assuming a coordinate, fibre or torus bundle.
-/

set_option autoImplicit false

noncomputable section

open Set Module Function DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint Manifold
open scoped Manifold ContDiff

namespace GC.GraphManifold.FlatTorus

local notation "E3" => EuclideanSpace ℝ (Fin 3)
open DifferentialGeometry.Geometry.FlatSurface

theorem exists_torusFibre_of_cyclicDeck (Q : ConnectedClosedOrientedManifold 3)
    (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3)) (p : E3 → Q.Carrier)
    (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p) (hs : Surjective p)
    (hrel : ∀ x y, p x = p y ↔ ∃ γ : G, γ.val x = y) {R : ℝ}
    (hdisc : ∀ B : ℝ, Set.Finite {a : G | ‖a.val 0‖ ≤ B})
    (hcov : ∀ x : E3, ∃ k : G, ‖x - k.val 0‖ ≤ R)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hdet : ∀ γ : G,
      0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearEquiv.toLinearMap)
    (hcyclic : IsCyclic (affineLinearHom.comp G.subtype).range) :
    ∃ (ell : E3 →L[ℝ] ℝ) (F : Q.Carrier → Circle) (f : Torus → Q.Carrier),
      Surjective ell ∧ (∀ m : ℤ, ∃ γ : G, ell (γ.val 0) = m) ∧
      ContMDiff (𝓡 3) (𝓡 1) ∞ F ∧ (∀ z, Surjective (mfderiv (𝓡 3) (𝓡 1) F z)) ∧
      IsSmoothEmbedding torusModel (𝓡 3) ∞ f ∧ range f = F ⁻¹' {1} ∧
      (∀ x, F (p x) = AddCircle.diffeomorphCircle (ell x : AddCircle (1 : ℝ))) ∧
      Nonempty (RawGraphPresentation (NoCuts.carrier Q)) := by
  obtain ⟨ell, hel, hlin, hint, hk⟩ := exists_cyclicDeck_planeCoordinate
    (by simp) G hdisc hcov hfree hdet hcyclic
  obtain ⟨a, ha, hel', _hker, hint', hprim⟩ := exists_primitive_deck_covector G ell hel hlin
    hint (affineTranslationModule_span_eq_top G hdisc hcov hfree)
  let ell' := a • ell
  have hlin' (γ : G) (v : E3) : ell' (γ.val.linearIsometryEquiv v) = ell' v := by
    change a * ell (γ.val.linearIsometryEquiv v) = a * ell v
    rw [hlin]
  have hk' (γ : G) (hz : ell' (γ.val 0) = 0) (x : E3) :
      γ.val x = x + γ.val 0 := by
    have hz' : ell (γ.val 0) = 0 := by
      change a * ell (γ.val 0) = 0 at hz
      exact (mul_eq_zero.mp hz).resolve_left ha
    exact hk γ hz' x
  obtain ⟨b, hb, _hf⟩ := exists_bieberbach_lattice G hdisc hcov hfree
  have hintb (i : Fin (finrank ℝ E3)) : ∃ m : ℤ, ell' (b i) = m := by
    have hbi : b i ∈ affineTranslationModule G := by
      rw [← hb]
      exact Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨m, hm⟩ := hint' ⟨AffineIsometryEquiv.constVAdd ℝ E3 (b i), hbi⟩
    exact ⟨m, by simpa [ell'] using hm⟩
  obtain ⟨c, hc⟩ := exists_integerHyperplane_basis (by simp) b ell' hel' hintb
  rw [hb] at hc
  obtain ⟨F, f, hF, hdF, he, hr, hFp⟩ :=
    exists_torusFibre_of_primitiveDeckCoordinate Q G p hp hs hrel ell' hel' hlin' hint'
      hprim hk' c hc
  refine ⟨ell', F, f, hel', hprim, hF, hdF, he, hr, hFp, ?_⟩
  exact Assembly.exists_rawGraphPresentation_of_torusBundle (NoCuts.carrier Q)
    (closedCarrier_boundary_eq_empty Q) F hF hdF f he hr

end GC.GraphManifold.FlatTorus

import DifferentialGeometry.Geometry.Thurston.FlatTorusCoords
import Mathlib.Analysis.Normed.Affine.Isometry

/-!
# Actual circle submersions descended from affine deck coordinates

An onto smooth local diffeomorphism with actual affine orbit fibres descends a real linear
coordinate when the coordinate is invariant under the actual linear parts and all translation
increments are integers. The descended map is smooth, onto and has surjective differential;
its pointwise equation retains the original cover and coordinate. This is a structural deck
recognition tier, without a torus fibre or raw presentation assumption.
-/

set_option autoImplicit false

noncomputable section

open Function DifferentialGeometry GC.Endpoint Manifold
open scoped Manifold ContDiff

namespace GC.GraphManifold.FlatTorus

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "A1" => AddCircle (1 : ℝ)

theorem exists_circleSubmersion_of_affineDeckCoordinate (W : CompactCarrier.{u})
    (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3)) (p : E3 → W.Carrier)
    (hp : IsLocalDiffeomorph (𝓡 3) W.model ∞ p) (hs : Surjective p)
    (hrel : ∀ x y, p x = p y ↔ ∃ γ : G, (γ.val : E3 → E3) x = y)
    (ell : E3 →L[ℝ] ℝ) (hell : Surjective ell)
    (hlin : ∀ γ : G, ∀ v, ell (γ.val.linearIsometryEquiv v) = ell v)
    (hint : ∀ γ : G, ∃ m : ℤ, ell (γ.val 0) = m) :
    ∃ F : W.Carrier → Circle, ContMDiff W.model (𝓡 1) ∞ F ∧ Surjective F ∧
      (∀ z, Surjective (mfderiv W.model (𝓡 1) F z)) ∧
      ∀ x, F (p x) = AddCircle.diffeomorphCircle (ell x : A1) := by
  let d : ℝ → Circle := fun t => AddCircle.diffeomorphCircle (t : A1)
  have hd : IsLocalDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ∞ d := by
    intro t
    exact (AddCircle.isLocalDiffeomorph_coe t).comp (𝓡 1) Circle
      (AddCircle.diffeomorphCircle.isLocalDiffeomorph (t : A1))
  let q : E3 → Circle := d ∘ ell
  have hq : ContMDiff (𝓡 3) (𝓡 1) ∞ q := hd.contMDiff.comp ell.contDiff.contMDiff
  have hqi (γ : G) (x : E3) : q (γ.val x) = q x := by
    obtain ⟨m, hm⟩ := hint γ
    have ha : γ.val x = γ.val.linearIsometryEquiv x + γ.val 0 := by
      simpa only [vadd_eq_add, add_zero] using γ.val.map_vadd (0 : E3) x
    have hm0 : ((m : ℝ) : A1) = 0 := by
      rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff]
      exact ⟨m, by simp⟩
    change AddCircle.diffeomorphCircle (ell (γ.val x) : A1) = _
    rw [ha, map_add, hlin, hm, AddCircle.coe_add, hm0, add_zero]
    rfl
  let F : W.Carrier → Circle := q ∘ surjInv hs
  have hF : ∀ x, F (p x) = q x := by
    intro x
    obtain ⟨γ, hγ⟩ := (hrel _ _).mp (surjInv_eq hs (p x))
    exact (hqi γ _).symm.trans (congrArg q hγ)
  have hFs : ContMDiff W.model (𝓡 1) ∞ F := by
    apply hp.contMDiff_of_comp_of_surjective hs
    have he : F ∘ p = q := funext hF
    rw [he]
    exact hq
  have hqs : Surjective q := by
    intro z
    obtain ⟨a, rfl⟩ := AddCircle.diffeomorphCircle.surjective z
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective a
    obtain ⟨x, hx⟩ := hell t
    exact ⟨x, congrArg d hx⟩
  have helsmooth : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ell := ell.contDiff.contMDiff
  have hqd : ∀ x, Surjective (mfderiv (𝓡 3) (𝓡 1) q x) := by
    intro x
    change Surjective (mfderiv (𝓡 3) (𝓡 1) (d ∘ ell) x)
    rw [mfderiv_comp x (hd.contMDiff.mdifferentiableAt (by simp))
      (helsmooth.mdifferentiableAt (by simp)), mfderiv_eq_fderiv,
      ell.hasFDerivAt.fderiv]
    exact ((hd (ell x)).mfderivToContinuousLinearEquiv (by simp)).surjective.comp hell
  refine ⟨F, hFs, ?_, ?_, hF⟩
  · intro z
    obtain ⟨x, hx⟩ := hqs z
    exact ⟨p x, (hF x).trans hx⟩
  · intro z
    obtain ⟨x, rfl⟩ := hs z
    have he : F ∘ p = q := funext hF
    have h := hqd x
    rw [← he, mfderiv_comp x (hFs.mdifferentiableAt (by simp))
      (hp.contMDiff.mdifferentiableAt (by simp))] at h
    exact Surjective.of_comp h

end GC.GraphManifold.FlatTorus

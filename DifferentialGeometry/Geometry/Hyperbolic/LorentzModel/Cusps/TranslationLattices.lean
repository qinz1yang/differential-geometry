/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Horosphere.AffineMaps
import Mathlib.Algebra.Module.ZLattice.Basic

noncomputable section

open DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.TranslationLattices

open Hyperbolic HyperbolicAction HyperbolicBoundary MobiusBoundary
open Horospherical HoroballMaps
open Module

variable {m : ℕ}

theorem exists_linear_extension (D D' : Submodule ℤ (Horizontal m))
    [DiscreteTopology D] [DiscreteTopology D'] [IsZLattice ℝ D] [IsZLattice ℝ D']
    (f : D ≃+ D') :
    ∃ L : Horizontal m ≃L[ℝ] Horizontal m, ∀ u : D, L u = (f u : Horizontal m) := by
  let b := Free.chooseBasis ℤ D
  let b' := b.map f.toIntLinearEquiv
  let e : Horizontal m ≃ₗ[ℝ] Horizontal m :=
    (b.ofZLatticeBasis ℝ D).equiv (b'.ofZLatticeBasis ℝ D') (Equiv.refl _)
  have he : (e.toLinearMap.restrictScalars ℤ).comp D.subtype
      = D'.subtype.comp f.toIntLinearEquiv.toLinearMap := by
    apply b.ext
    intro i
    change e (b i : Horizontal m) = (f (b i) : Horizontal m)
    have h := Basis.equiv_apply (b.ofZLatticeBasis ℝ D) i (b'.ofZLatticeBasis ℝ D')
      (Equiv.refl _)
    simpa only [Basis.ofZLatticeBasis_apply, Equiv.refl_apply, b',
      Basis.map_apply, AddEquiv.coe_toIntLinearEquiv] using h
  exact ⟨e.toContinuousLinearEquiv, fun u => LinearMap.congr_fun he u⟩

local instance : MulAction (PO (m + 1) 1) (HUpper (m + 1)) :=
  poMulAction (by omega)

def translation (u : Horizontal m) : PO (m + 1) 1 :=
  QuotientGroup.mk' _ (transLor (fun i => u i))

theorem translation_smul_ofCoords (u x : Horizontal m) (h : ℝ) (hh : 0 < h) :
    translation u • ofCoords x h hh = ofCoords (x + u) h hh :=
  trans_po_smul_ofCoords u x h hh

theorem translation_smul (u : Horizontal m) (X : HUpper (m + 1)) :
    translation u • X = ofCoords (horizontal X + u) (height X) (height_pos X) := by
  conv_lhs => rw [← ofCoords_horizontal_height X]
  exact translation_smul_ofCoords _ _ _ _

private theorem eq_of_smul_eq {g h : PO (m + 1) 1}
    (heq : ∀ X : HUpper (m + 1), g • X = h • X) : g = h := by
  have h1 : h⁻¹ * g = 1 := HyperbolicFaithful.po_smul_eq_one (by omega) (fun X => by
    change (h⁻¹ * g) • X = X
    rw [mul_smul, heq X, inv_smul_smul])
  exact (inv_mul_eq_one.mp h1).symm

@[simp] theorem translation_zero : translation (0 : Horizontal m) = 1 := by
  apply eq_of_smul_eq
  intro X
  rw [translation_smul, add_zero, ofCoords_horizontal_height, one_smul]

theorem translation_add (u v : Horizontal m) :
    translation (u + v) = translation u * translation v := by
  apply eq_of_smul_eq
  intro X
  rw [mul_smul, translation_smul v X, translation_smul_ofCoords, translation_smul]
  congr 1
  abel

theorem translation_injective : Function.Injective (translation (m := m)) := by
  intro u v huv
  have h := congrArg (fun g : PO (m + 1) 1 =>
    horizontal (g • ofCoords (0 : Horizontal m) 1 zero_lt_one)) huv
  simpa only [translation_smul_ofCoords, horizontal_ofCoords, zero_add] using h

def translationHom : Multiplicative (Horizontal m) →* PO (m + 1) 1 where
  toFun u := translation u.toAdd
  map_one' := translation_zero
  map_mul' u v := translation_add u.toAdd v.toAdd

def latticeHom (D : Submodule ℤ (Horizontal m)) : Multiplicative D →* PO (m + 1) 1 :=
  translationHom.comp (AddMonoidHom.toMultiplicative D.subtype.toAddMonoidHom)

theorem latticeHom_injective (D : Submodule ℤ (Horizontal m)) :
    Function.Injective (latticeHom D) := by
  intro u v h
  have he : (u.toAdd : Horizontal m) = (v.toAdd : Horizontal m) := translation_injective h
  have h' : u.toAdd = v.toAdd := Subtype.ext he
  exact congrArg Multiplicative.ofAdd h'

def latticeGroup (D : Submodule ℤ (Horizontal m)) : Subgroup (PO (m + 1) 1) :=
  (latticeHom D).range

def latticeEquiv (D : Submodule ℤ (Horizontal m)) : Multiplicative D ≃* latticeGroup D :=
  MonoidHom.ofInjective (latticeHom_injective D)

@[simp] theorem latticeEquiv_coe (D : Submodule ℤ (Horizontal m)) (u : Multiplicative D) :
    (latticeEquiv D u : PO (m + 1) 1) = translation (u.toAdd : Horizontal m) := rfl

def inducedIso (D D' : Submodule ℤ (Horizontal m)) (f : D ≃+ D') :
    latticeGroup D ≃* latticeGroup D' :=
  ((latticeEquiv D).symm.trans (AddEquiv.toMultiplicative f)).trans (latticeEquiv D')

@[simp] theorem inducedIso_latticeEquiv (D D' : Submodule ℤ (Horizontal m)) (f : D ≃+ D')
    (u : Multiplicative D) :
    inducedIso D D' f (latticeEquiv D u)
      = latticeEquiv D' (Multiplicative.ofAdd (f u.toAdd)) := by
  simp [inducedIso]

theorem affine_isFEquivariant (D D' : Submodule ℤ (Horizontal m)) (f : D ≃+ D')
    (L : Horizontal m ≃L[ℝ] Horizontal m)
    (hL : ∀ u : D, L u = (f u : Horizontal m)) (b : Horizontal m) :
    PseudoIsometry.IsFEquivariant (inducedIso D D' f) (by omega) (affine L b) := by
  intro γ X
  obtain ⟨u, rfl⟩ := (latticeEquiv D).surjective γ
  change affine L b ((latticeEquiv D u : PO (m + 1) 1) • X)
    = (inducedIso D D' f (latticeEquiv D u) : PO (m + 1) 1) • affine L b X
  rw [inducedIso_latticeEquiv, latticeEquiv_coe, latticeEquiv_coe]
  have h := affine_translation_equivariant L b (u.toAdd : Horizontal m) X
  rw [hL u.toAdd] at h
  exact h

theorem affineBoundaryHomeomorph_equivariant (D D' : Submodule ℤ (Horizontal m))
    (f : D ≃+ D') (L : Horizontal m ≃L[ℝ] Horizontal m)
    (hL : ∀ u : D, L u = (f u : Horizontal m)) (b : Horizontal m)
    (γ : latticeGroup D) (ξ : BoundaryH (m + 1)) :
    affineBoundaryHomeomorph L b
        ((poBoundaryMulAction (by omega : 1 ≤ m + 1)).smul (γ : PO (m + 1) 1) ξ)
      = (poBoundaryMulAction (by omega : 1 ≤ m + 1)).smul
          (inducedIso D D' f γ : PO (m + 1) 1) (affineBoundaryHomeomorph L b ξ) := by
  unfold affineBoundaryHomeomorph
  simp only [BoundaryHomeomorph.bExtHomeomorph_apply]
  exact BoundaryExtension.bExt_equivariant (affine_isPseudoIsometry L b)
    (BoundaryHomeomorph.gromovCauchy_image_ray (affine_isPseudoIsometry L b) (by omega))
    (by omega) (affine_isFEquivariant D D' f L hL b) γ ξ

theorem exists_equivariant_horoball_map (D D' : Submodule ℤ (Horizontal m))
    [DiscreteTopology D] [DiscreteTopology D'] [IsZLattice ℝ D] [IsZLattice ℝ D']
    (f : D ≃+ D') :
    ∃ (Φ : HUpper (m + 1) ≃ HUpper (m + 1)) (C C' : ℝ)
        (φ : BoundaryH (m + 1) ≃ₜ BoundaryH (m + 1)),
      PseudoIsometry.IsPseudoIsometry 1 C Φ
      ∧ PseudoIsometry.IsPseudoIsometry 1 C' Φ.symm
      ∧ PseudoIsometry.IsFEquivariant (inducedIso D D' f) (by omega) Φ
      ∧ PseudoIsometry.IsFEquivariant (inducedIso D D' f).symm (by omega) Φ.symm
      ∧ (∀ c, Φ '' Busemann.horoball ptInfty c = Busemann.horoball ptInfty c)
      ∧ (∀ ξ, BoundaryTopology.ConvergesToBoundary
          (fun k : ℕ => Φ (BoundaryTopology.geodesicRay ξ (k : ℝ))) (φ ξ))
      ∧ (∀ (γ : latticeGroup D) (ξ : BoundaryH (m + 1)),
          φ ((poBoundaryMulAction (by omega : 1 ≤ m + 1)).smul (γ : PO (m + 1) 1) ξ)
            = (poBoundaryMulAction (by omega : 1 ≤ m + 1)).smul
                (inducedIso D D' f γ : PO (m + 1) 1) (φ ξ)) := by
  obtain ⟨L, hL⟩ := exists_linear_extension D D' f
  have hFE : PseudoIsometry.IsFEquivariant (inducedIso D D' f) (by omega) (affineEquiv L 0) :=
    affine_isFEquivariant D D' f L hL 0
  refine ⟨affineEquiv L 0, Real.log (2 * distortion L), Real.log (2 * distortion L.symm),
    affineBoundaryHomeomorph L 0, affine_isPseudoIsometry L 0, ?_,
    hFE, ?_, affine_image_horoball L 0,
    affineBoundaryHomeomorph_converges L 0, affineBoundaryHomeomorph_equivariant D D' f L hL 0⟩
  · exact affine_isPseudoIsometry L.symm (-L.symm 0)
  · intro γ X
    apply (affineEquiv L 0).injective
    rw [(affineEquiv L 0).apply_symm_apply]
    have h := hFE ((inducedIso D D' f).symm γ) ((affineEquiv L 0).symm X)
    rw [(inducedIso D D' f).apply_symm_apply, (affineEquiv L 0).apply_symm_apply] at h
    exact h.symm

end DifferentialGeometry.TranslationLattices

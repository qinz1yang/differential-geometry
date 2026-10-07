/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Affine.Crystallographic.CocompactActions
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.ParabolicRegions
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.TranslationLattices

noncomputable section

open Set
open DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.HorosphereGroups

open Hyperbolic HyperbolicAction HyperbolicBoundary Horospherical
open BusemannCocycle MobiusBoundary DifferentialGeometry.CrystallographicActions

variable {m : ℕ}

local instance : MulAction (PO (m + 1) 1) (HUpper (m + 1)) :=
  poMulAction (by omega)

variable (Γ : Subgroup (PO (m + 1) 1))
    (hfix : ∀ γ : Γ,
      (poBoundaryMulAction (by omega)).smul (γ : PO (m + 1) 1) ptInfty = ptInfty ∧
      poConfFactor (by omega) (γ : PO (m + 1) 1) ptInfty = 1)

def affineMap (γ : Γ) : Horizontal m ≃ᵃⁱ[ℝ] Horizontal m :=
  Classical.choose (exists_affineIsometry_of_po_fix_scale_one γ (hfix γ).1 (hfix γ).2)

theorem affineMap_spec (γ : Γ) (x : Horizontal m) (h : ℝ) (hh : 0 < h) :
    (γ : PO (m + 1) 1) • ofCoords x h hh =
      ofCoords (affineMap Γ hfix γ x) h hh :=
  Classical.choose_spec (exists_affineIsometry_of_po_fix_scale_one γ (hfix γ).1 (hfix γ).2)
    x h hh

def affineAction : Γ →* (Horizontal m ≃ᵃⁱ[ℝ] Horizontal m) where
  toFun := affineMap Γ hfix
  map_one' := by
    apply AffineIsometryEquiv.ext
    intro x
    have h := congrArg horizontal (affineMap_spec Γ hfix 1 x 1 zero_lt_one)
    simpa only [Subgroup.coe_one, one_smul, horizontal_ofCoords,
      AffineIsometryEquiv.coe_one, id_eq] using h.symm
  map_mul' γ δ := by
    apply AffineIsometryEquiv.ext
    intro x
    have h := affineMap_spec Γ hfix (γ * δ) x 1 zero_lt_one
    have h' : ((γ * δ : Γ) : PO (m + 1) 1) • ofCoords x 1 zero_lt_one =
        ofCoords (affineMap Γ hfix γ (affineMap Γ hfix δ x)) 1 zero_lt_one := by
      rw [Subgroup.coe_mul, mul_smul, affineMap_spec Γ hfix δ, affineMap_spec Γ hfix γ]
    have he := congrArg horizontal (h.symm.trans h')
    simpa only [horizontal_ofCoords, AffineIsometryEquiv.coe_mul, Function.comp_apply] using he

theorem affineAction_spec (γ : Γ) (x : Horizontal m) (h : ℝ) (hh : 0 < h) :
    (γ : PO (m + 1) 1) • ofCoords x h hh =
      ofCoords (affineAction Γ hfix γ x) h hh :=
  affineMap_spec Γ hfix γ x h hh

theorem eq_of_coords_action_eq (g h : PO (m + 1) 1)
    (he : ∀ (x : Horizontal m) (t : ℝ) (ht : 0 < t),
      (poMulAction (by omega : 1 ≤ m + 1)).smul g (ofCoords x t ht) =
        (poMulAction (by omega : 1 ≤ m + 1)).smul h (ofCoords x t ht)) : g = h := by
  let := poMulAction (by omega : 1 ≤ m + 1)
  have hpoint : ∀ X : HUpper (m + 1), g • X = h • X := by
    intro X
    change (poMulAction (by omega : 1 ≤ m + 1)).smul g X =
      (poMulAction (by omega : 1 ≤ m + 1)).smul h X
    have hX := he (horizontal X) (height X) (height_pos X)
    rw [ofCoords_horizontal_height] at hX
    exact hX
  have hk : h⁻¹ * g = 1 := HyperbolicFaithful.po_smul_eq_one (by omega) (fun X => by
    change (h⁻¹ * g) • X = X
    rw [mul_smul, hpoint, inv_smul_smul])
  exact (inv_mul_eq_one.mp hk).symm

theorem affineAction_injective : Function.Injective (affineAction Γ hfix) := by
  let := poMulAction (by omega : 1 ≤ m + 1)
  intro γ δ he
  apply Subtype.ext
  apply eq_of_coords_action_eq
  intro x h hh
  change (γ : PO (m + 1) 1) • ofCoords x h hh =
    (δ : PO (m + 1) 1) • ofCoords x h hh
  rw [affineAction_spec Γ hfix γ, affineAction_spec Γ hfix δ]
  exact congrArg (fun y : Horizontal m => ofCoords y h hh)
    (congrArg (fun a : Horizontal m ≃ᵃⁱ[ℝ] Horizontal m => a x) he)

theorem finite_affine_displacement (hΓ : IsDiscrete (SetLike.coe Γ)) (B : ℝ) :
    {γ : Γ | ‖affineAction Γ hfix γ 0‖ ≤ B}.Finite := by
  let p := ofCoords (0 : Horizontal m) 1 zero_lt_one
  apply (BoundaryStabilizer.finite_setOf_displacement_le (by omega) Γ hΓ p
    (Real.arcosh (1 + B ^ 2 / 2))).subset
  intro γ hγ
  change dist ((γ : PO (m + 1) 1) • p) p ≤ _
  have hsq : ‖affineAction Γ hfix γ 0‖ ^ 2 ≤ B ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hγ)).mpr hγ
  have he : Real.cosh (dist ((γ : PO (m + 1) 1) • p) p) =
      1 + ‖affineAction Γ hfix γ 0‖ ^ 2 / 2 := by
    change Real.cosh (dist ((γ : PO (m + 1) 1) • ofCoords 0 1 zero_lt_one)
      (ofCoords 0 1 zero_lt_one)) = _
    rw [affineAction_spec Γ hfix γ, cosh_dist_ofCoords]
    simp only [sub_zero, one_pow, mul_one]
    ring
  calc
    _ = Real.arcosh (Real.cosh (dist ((γ : PO (m + 1) 1) • p) p)) :=
      (Real.arcosh_cosh dist_nonneg).symm
    _ ≤ _ := (Real.arcosh_le_arcosh (Real.cosh_pos _) (by positivity)).mpr (by
      rw [he]
      linarith)

theorem translationKernel_finiteIndex
    (hco : CoboundedOrbit (affineAction Γ hfix)) (hvirt : Group.IsVirtuallyNilpotent Γ) :
    (linearPart.comp (affineAction Γ hfix)).ker.FiniteIndex :=
  finiteIndex_linear_kernel (affineAction Γ hfix) (affineAction_injective Γ hfix) hco hvirt

theorem finite_holonomy
    (hco : CoboundedOrbit (affineAction Γ hfix)) (hvirt : Group.IsVirtuallyNilpotent Γ) :
    Finite (linearPart.comp (affineAction Γ hfix)).range :=
  finite_linear_range (affineAction Γ hfix) (affineAction_injective Γ hfix) hco hvirt

theorem translationModule_discrete (hΓ : IsDiscrete (SetLike.coe Γ)) :
    DiscreteTopology (translationModule (affineAction Γ hfix)) :=
  discrete_translationModule (affineAction Γ hfix) (finite_affine_displacement Γ hfix hΓ)

theorem translationModule_full
    (hco : CoboundedOrbit (affineAction Γ hfix)) (hvirt : Group.IsVirtuallyNilpotent Γ)
    [DiscreteTopology (translationModule (affineAction Γ hfix))] :
    IsZLattice ℝ (translationModule (affineAction Γ hfix)) :=
  isZLattice_translationModule (affineAction Γ hfix) (affineAction_injective Γ hfix) hco hvirt

theorem translationEquiv_coe
    (u : Multiplicative (translationModule (affineAction Γ hfix))) :
    (((translationEquiv (affineAction Γ hfix) (affineAction_injective Γ hfix) u :
        (linearPart.comp (affineAction Γ hfix)).ker) : Γ) : PO (m + 1) 1) =
      TranslationLattices.translation (u.toAdd : Horizontal m) := by
  let e := translationEquiv (affineAction Γ hfix) (affineAction_injective Γ hfix)
  apply eq_of_coords_action_eq
  intro x h hh
  change (((e u : Γ) : PO (m + 1) 1)) • ofCoords x h hh =
    TranslationLattices.translation (u.toAdd : Horizontal m) • ofCoords x h hh
  rw [affineAction_spec Γ hfix (e u : Γ), TranslationLattices.translation_smul_ofCoords]
  exact congrArg (fun y : Horizontal m => ofCoords y h hh)
    (translationEquiv_apply (affineAction Γ hfix) (affineAction_injective Γ hfix) u x)

theorem translationKernel_map_eq_latticeGroup :
    (linearPart.comp (affineAction Γ hfix)).ker.map Γ.subtype =
      TranslationLattices.latticeGroup (translationModule (affineAction Γ hfix)) := by
  let e := translationEquiv (affineAction Γ hfix) (affineAction_injective Γ hfix)
  apply le_antisymm
  · rintro g ⟨γ, hγ, rfl⟩
    let a : (linearPart.comp (affineAction Γ hfix)).ker := ⟨γ, hγ⟩
    obtain ⟨u, hu⟩ := e.surjective a
    refine ⟨u, ?_⟩
    have he := translationEquiv_coe Γ hfix u
    change ((e u : Γ) : PO (m + 1) 1) = _ at he
    rw [hu] at he
    exact he.symm
  · rintro g ⟨u, rfl⟩
    exact ⟨(e u : Γ), (e u).property, translationEquiv_coe Γ hfix u⟩

theorem exists_full_translation_lattice (hΓ : IsDiscrete (SetLike.coe Γ))
    (hco : CoboundedOrbit (affineAction Γ hfix)) (hvirt : Group.IsVirtuallyNilpotent Γ) :
    ∃ (D : Submodule ℤ (Horizontal m)) (hD : DiscreteTopology D),
      letI := hD
      IsZLattice ℝ D ∧ TranslationLattices.latticeGroup D ≤ Γ ∧
        ((TranslationLattices.latticeGroup D).subgroupOf Γ).FiniteIndex := by
  let D := translationModule (affineAction Γ hfix)
  let hD : DiscreteTopology D := translationModule_discrete Γ hfix hΓ
  refine ⟨D, hD, translationModule_full Γ hfix hco hvirt, ?_, ?_⟩
  · rw [← translationKernel_map_eq_latticeGroup Γ hfix]
    rintro g ⟨γ, _, rfl⟩
    exact γ.property
  · rw [← translationKernel_map_eq_latticeGroup Γ hfix]
    change (((linearPart.comp (affineAction Γ hfix)).ker.map Γ.subtype).comap Γ.subtype).FiniteIndex
    rw [Subgroup.comap_map_eq_self_of_injective Γ.subtype_injective]
    exact translationKernel_finiteIndex Γ hfix hco hvirt

theorem fg_of_cobounded (hΓ : IsDiscrete (SetLike.coe Γ))
    (hco : CoboundedOrbit (affineAction Γ hfix)) : Group.FG Γ :=
  DifferentialGeometry.CrystallographicActions.fg_of_coboundedOrbit (affineAction Γ hfix) hco
    (finite_affine_displacement Γ hfix hΓ)

theorem virtuallyNilpotent_of_cobounded (hΓ : IsDiscrete (SetLike.coe Γ))
    (hco : CoboundedOrbit (affineAction Γ hfix)) : Group.IsVirtuallyNilpotent Γ := by
  let := fg_of_cobounded Γ hfix hΓ hco
  exact ParabolicRegions.virtuallyNilpotent_of_fg_horospherical (by omega) Γ hΓ ptInfty hfix

theorem exists_full_translation_lattice_of_cobounded (hΓ : IsDiscrete (SetLike.coe Γ))
    (hco : CoboundedOrbit (affineAction Γ hfix)) :
    ∃ (D : Submodule ℤ (Horizontal m)) (hD : DiscreteTopology D),
      let := hD
      IsZLattice ℝ D ∧ TranslationLattices.latticeGroup D ≤ Γ ∧
        ((TranslationLattices.latticeGroup D).subgroupOf Γ).FiniteIndex :=
  exists_full_translation_lattice Γ hfix hΓ hco (virtuallyNilpotent_of_cobounded Γ hfix hΓ hco)

end DifferentialGeometry.HorosphereGroups

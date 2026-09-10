/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

set_option autoImplicit false

open CategoryTheory

universe u v

namespace Poincare.Topology

noncomputable def fundamentalGroupChangeBasepoint
    {X : Type u} [TopologicalSpace X] {z m : X} (β : Path z m) :
    FundamentalGroup X m ≃* FundamentalGroup X z where
  toFun g := (Path.Homotopic.Quotient.trans ⟦β⟧ g).trans
    (Path.Homotopic.Quotient.symm ⟦β⟧)
  invFun h := (Path.Homotopic.Quotient.trans
    (Path.Homotopic.Quotient.symm ⟦β⟧) h).trans ⟦β⟧
  left_inv g := by
    simp only [Path.Homotopic.Quotient.mk''_eq_mk,
      Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
      Path.Homotopic.Quotient.trans_refl]
    rw [← Path.Homotopic.Quotient.trans_assoc]
    simp only [Path.Homotopic.Quotient.symm_trans,
      Path.Homotopic.Quotient.refl_trans]
  right_inv h := by
    simp only [Path.Homotopic.Quotient.mk''_eq_mk,
      Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
      Path.Homotopic.Quotient.trans_refl]
    rw [← Path.Homotopic.Quotient.trans_assoc]
    simp only [Path.Homotopic.Quotient.trans_symm,
      Path.Homotopic.Quotient.refl_trans]
  map_mul' g h := by
    simp only [FundamentalGroup.mul_def]
    simp only [Path.Homotopic.Quotient.mk''_eq_mk,
      Path.Homotopic.Quotient.trans_assoc]
    apply congrArg (Path.Homotopic.Quotient.trans
      (⟦β⟧ : Path.Homotopic.Quotient z m))
    apply congrArg (Path.Homotopic.Quotient.trans h)
    symm
    rw [← Path.Homotopic.Quotient.trans_assoc]
    simp only [Path.Homotopic.Quotient.symm_trans,
      Path.Homotopic.Quotient.refl_trans]

theorem fundamentalGroupChangeBasepoint_apply
    {X : Type u} [TopologicalSpace X] {z m : X} (β : Path z m)
    (g : FundamentalGroup X m) :
    fundamentalGroupChangeBasepoint β g =
      (Path.Homotopic.Quotient.trans ⟦β⟧ g).trans
        (Path.Homotopic.Quotient.symm ⟦β⟧) := by
  rfl

noncomputable def connectorLoop
    {X : Type u} [TopologicalSpace X] {z m : X} (β β' : Path z m) :
    FundamentalGroup X z :=
  Path.Homotopic.Quotient.trans ⟦β'⟧
    (Path.Homotopic.Quotient.symm ⟦β⟧)

theorem fundamentalGroupChangeBasepoint_connector
    {X : Type u} [TopologicalSpace X] {z m : X} (β β' : Path z m)
    (g : FundamentalGroup X m) :
    fundamentalGroupChangeBasepoint β' g =
      MulAut.conj (connectorLoop β β')⁻¹ (fundamentalGroupChangeBasepoint β g) := by
  let b : FundamentalGroupoid.mk z ⟶ FundamentalGroupoid.mk m := ⟦β⟧
  let b' : FundamentalGroupoid.mk z ⟶ FundamentalGroupoid.mk m := ⟦β'⟧
  let h : FundamentalGroup X z := CategoryTheory.End.of (b' ≫ Groupoid.inv b)
  have hcat :
      (b' ≫ g) ≫ Groupoid.inv b' =
        CategoryTheory.End.asHom h ≫ ((b ≫ g) ≫ Groupoid.inv b) ≫
          Groupoid.inv (CategoryTheory.End.asHom h) := by
    dsimp only [h, b, b', CategoryTheory.End.asHom, CategoryTheory.End.of]
    simp
  rw [fundamentalGroupChangeBasepoint_apply, fundamentalGroupChangeBasepoint_apply]
  rw [MulAut.conj_apply]
  rw [inv_inv]
  simp only [FundamentalGroup.mul_def, FundamentalGroup.inv_def]
  change (b' ≫ g) ≫ Groupoid.inv b' =
    CategoryTheory.End.asHom h ≫ ((b ≫ g) ≫ Groupoid.inv b) ≫
      Groupoid.inv (CategoryTheory.End.asHom h)
  exact hcat

noncomputable def transportedFundamentalGroupHom
    {X : Type u} [TopologicalSpace X] {z m : X} {G : Type v} [Group G]
    (φ : FundamentalGroup X z →* G) (β : Path z m) :
    FundamentalGroup X m →* G :=
  φ.comp (fundamentalGroupChangeBasepoint β).toMonoidHom

theorem transportedFundamentalGroupHom_apply
    {X : Type u} [TopologicalSpace X] {z m : X} {G : Type v} [Group G]
    (φ : FundamentalGroup X z →* G) (β : Path z m)
    (g : FundamentalGroup X m) :
    transportedFundamentalGroupHom φ β g = φ (fundamentalGroupChangeBasepoint β g) := by
  rfl

theorem transportedFundamentalGroupHom_connector
    {X : Type u} [TopologicalSpace X] {z m : X} {G : Type v} [Group G]
    (φ : FundamentalGroup X z →* G) (β β' : Path z m) :
    transportedFundamentalGroupHom φ β' =
      (MulAut.conj (φ (connectorLoop β β'))⁻¹).toMonoidHom.comp
        (transportedFundamentalGroupHom φ β) := by
  ext g
  simp only [transportedFundamentalGroupHom_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom]
  rw [fundamentalGroupChangeBasepoint_connector β β' g]
  simp only [MulAut.conj_inv_apply, map_mul, map_inv]

end Poincare.Topology

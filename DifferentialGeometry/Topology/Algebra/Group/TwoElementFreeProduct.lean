/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.Coprod.Basic
import DifferentialGeometry.Topology.Algebra.Group.FreeProduct

set_option autoImplicit false

open Function

namespace DifferentialGeometry.Algebra.Group


abbrev TwoElementGroup := Multiplicative (ZMod 2)


noncomputable def dihedralReflectionHom (i : ZMod 0) :
    TwoElementGroup →* DihedralGroup 0 :=
  AddMonoidHom.toMultiplicativeLeft <| ZMod.lift 2 ⟨
    zmultiplesHom (Additive (DihedralGroup 0)) (Additive.ofMul (DihedralGroup.sr i)), by
      change Additive.ofMul ((DihedralGroup.sr i) ^ (2 : ℕ)) = 0
      rw [pow_two, DihedralGroup.sr_mul_self]
      rfl⟩


@[simp]
theorem dihedralReflectionHom_generator (i : ZMod 0) :
    dihedralReflectionHom i (Multiplicative.ofAdd (1 : ZMod 2)) = DihedralGroup.sr i := by
  simp only [dihedralReflectionHom, AddMonoidHom.coe_toMultiplicativeLeft,
    Function.comp_apply]
  change Additive.toMul (ZMod.lift 2 _ (1 : ZMod 2)) = DihedralGroup.sr i
  rw [show (1 : ZMod 2) = Int.castAddHom (ZMod 2) 1 by simp,
    ZMod.lift_castAddHom]
  simp [zmultiplesHom_apply]

noncomputable def twoElementCoprodToDihedral :
    Monoid.Coprod TwoElementGroup TwoElementGroup →* DihedralGroup 0 :=
  Monoid.Coprod.lift (dihedralReflectionHom 0) (dihedralReflectionHom 1)


@[simp]
theorem twoElementCoprodToDihedral_left_generator :
    twoElementCoprodToDihedral
        (Monoid.Coprod.inl (Multiplicative.ofAdd (1 : ZMod 2))) =
      (DihedralGroup.sr (0 : ZMod 0) : DihedralGroup 0) := by
  simp [twoElementCoprodToDihedral]


@[simp]
theorem twoElementCoprodToDihedral_right_generator :
    twoElementCoprodToDihedral
        (Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ZMod 2))) =
      (DihedralGroup.sr (1 : ZMod 0) : DihedralGroup 0) := by
  simp [twoElementCoprodToDihedral]


def alternatingWord : ℤ → Monoid.Coprod TwoElementGroup TwoElementGroup := fun n =>
  (Monoid.Coprod.inl (Multiplicative.ofAdd (1 : ZMod 2)) *
    Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ZMod 2))) ^ n


theorem twoElementCoprodToDihedral_alternatingWord (n : ℤ) :
    twoElementCoprodToDihedral (alternatingWord n) =
      (DihedralGroup.r (n : ZMod 0) : DihedralGroup 0) := by
  change twoElementCoprodToDihedral
      ((Monoid.Coprod.inl (Multiplicative.ofAdd (1 : ZMod 2)) *
        Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ZMod 2))) ^ n) = _
  calc
    _ = ((DihedralGroup.r 1 : DihedralGroup 0) ^ n) := by
      rw [map_zpow]
      simp
    _ = DihedralGroup.r (n : ZMod 0) := DihedralGroup.r_one_zpow n


theorem alternatingWord_injective : Function.Injective alternatingWord := by
  intro m n h
  have hmap := congrArg twoElementCoprodToDihedral h
  rw [twoElementCoprodToDihedral_alternatingWord,
    twoElementCoprodToDihedral_alternatingWord] at hmap
  injection hmap with hmn


instance twoElementCoprodInfinite :
    Infinite (Monoid.Coprod TwoElementGroup TwoElementGroup) :=
  Infinite.of_injective alternatingWord alternatingWord_injective

end DifferentialGeometry.Algebra.Group

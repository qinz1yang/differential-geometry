/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Analysis.Normed.Module.Ball.Action
import DifferentialGeometry.Topology.Algebra.Group.TwoElementFreeProduct
import DifferentialGeometry.Topology.FundamentalGroup.SphericalQuotient

set_option autoImplicit false

open Metric

namespace DifferentialGeometry.Topology

open DifferentialGeometry.Algebra.Group


noncomputable def antipodalScalar : sphere (0 : ℝ) 1 :=
  ⟨-1, by simp⟩

@[simp]
theorem antipodalScalar_coe : (antipodalScalar : ℝ) = -1 := rfl


noncomputable def twoElementAntipodalScalarHom :
    TwoElementGroup →* sphere (0 : ℝ) 1 :=
  AddMonoidHom.toMultiplicativeLeft <| ZMod.lift 2 ⟨
    zmultiplesHom (Additive (sphere (0 : ℝ) 1)) (Additive.ofMul antipodalScalar), by
      change Additive.ofMul (antipodalScalar ^ (2 : ℕ)) = 0
      apply Additive.toMul.injective
      apply Subtype.ext
      norm_num [antipodalScalar]⟩

@[simp]
theorem twoElementAntipodalScalarHom_generator :
    twoElementAntipodalScalarHom (Multiplicative.ofAdd (1 : ZMod 2)) = antipodalScalar := by
  simp only [twoElementAntipodalScalarHom, AddMonoidHom.coe_toMultiplicativeLeft,
    Function.comp_apply]
  change Additive.toMul (ZMod.lift 2 _ (1 : ZMod 2)) = antipodalScalar
  rw [show (1 : ZMod 2) = Int.castAddHom (ZMod 2) 1 by simp,
    ZMod.lift_castAddHom]
  simp [zmultiplesHom_apply]


theorem twoElementAntipodalScalarHom_injective :
    Function.Injective twoElementAntipodalScalarHom := by
  have hzmod : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by
    intro z
    by_cases hz : z = 0
    · exact Or.inl hz
    · right
      apply (ZMod.val_eq_one (by norm_num) z).mp
      have hpos : 0 < z.val := ZMod.val_pos.mpr hz
      have hlt : z.val < 2 := z.val_lt
      omega
  intro g h hgh
  rcases hzmod (Multiplicative.toAdd g) with hg | hg <;>
    rcases hzmod (Multiplicative.toAdd h) with hh | hh
  · have hg' : g = 1 := by simpa using congrArg Multiplicative.ofAdd hg
    have hh' : h = 1 := by simpa using congrArg Multiplicative.ofAdd hh
    rw [hg', hh']
  · have hg' : g = 1 := by simpa using congrArg Multiplicative.ofAdd hg
    have hh' : h = Multiplicative.ofAdd (1 : ZMod 2) :=
      by simpa using congrArg Multiplicative.ofAdd hh
    rw [hg', hh'] at hgh
    have := congrArg Subtype.val hgh
    norm_num [antipodalScalar] at this
  · have hg' : g = Multiplicative.ofAdd (1 : ZMod 2) :=
      by simpa using congrArg Multiplicative.ofAdd hg
    have hh' : h = 1 := by simpa using congrArg Multiplicative.ofAdd hh
    rw [hg', hh'] at hgh
    have := congrArg Subtype.val hgh
    norm_num [antipodalScalar] at this
  · simpa using congrArg Multiplicative.ofAdd (hg.trans hh.symm)


noncomputable instance twoElementAntipodalMulAction : MulAction TwoElementGroup SphereThree :=
  MulAction.compHom SphereThree twoElementAntipodalScalarHom


@[simp]
theorem twoElementAntipodal_generator_smul (x : SphereThree) :
    Multiplicative.ofAdd (1 : ZMod 2) • x = -x := by
  apply Subtype.ext
  change ((twoElementAntipodalScalarHom (Multiplicative.ofAdd (1 : ZMod 2)) : ℝ) •
    (x : EuclideanSpace ℝ (Fin 4))) = _
  rw [twoElementAntipodalScalarHom_generator]
  simp

noncomputable instance twoElementAntipodalContinuousConstSMul :
    ContinuousConstSMul TwoElementGroup SphereThree :=
  ⟨fun g ↦ continuous_const_smul (twoElementAntipodalScalarHom g)⟩


noncomputable instance twoElementAntipodalIsCancelSMul :
    IsCancelSMul TwoElementGroup SphereThree where
  right_cancel' g h x hsmul := by
    apply twoElementAntipodalScalarHom_injective
    apply Subtype.ext
    have hx0 : (x : EuclideanSpace ℝ (Fin 4)) ≠ 0 := by
      intro hx
      have hxnorm := mem_sphere_zero_iff_norm.mp x.property
      simp [hx] at hxnorm
    have hzero :
        (((twoElementAntipodalScalarHom g : ℝ) -
            (twoElementAntipodalScalarHom h : ℝ)) •
          (x : EuclideanSpace ℝ (Fin 4))) = 0 := by
      rw [sub_smul, sub_eq_zero]
      exact congrArg Subtype.val hsmul
    exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hx0)


abbrev RealProjectiveThree := MulActionOrbitQuotient TwoElementGroup SphereThree


noncomputable def realProjectiveThreeBasepoint : RealProjectiveThree :=
  Quotient.mk (MulAction.orbitRel TwoElementGroup SphereThree) sphereThreeNorth


noncomputable def fundamentalGroupRealProjectiveThreeEquivTwoElement :
    FundamentalGroup RealProjectiveThree realProjectiveThreeBasepoint ≃* TwoElementGroup :=
  fundamentalGroupFiniteFreeSphereThreeQuotientEquiv

end DifferentialGeometry.Topology

/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

set_option autoImplicit false

open CategoryTheory

universe u v

namespace DifferentialGeometry.Topology.VanKampen

structure CommSqRetract {C : Type u} [Category.{v} C]
    {Z' X' Y' P' Z X Y P : C}
    (f' : Z' ⟶ X') (g' : Z' ⟶ Y') (inl' : X' ⟶ P') (inr' : Y' ⟶ P')
    (f : Z ⟶ X) (g : Z ⟶ Y) (inl : X ⟶ P) (inr : Y ⟶ P) where
  small : CommSq f' g' inl' inr'
  iZ : Z' ⟶ Z
  iX : X' ⟶ X
  iY : Y' ⟶ Y
  iP : P' ⟶ P
  rZ : Z ⟶ Z'
  rX : X ⟶ X'
  rY : Y ⟶ Y'
  rP : P ⟶ P'
  retract_z : iZ ≫ rZ = 𝟙 Z'
  retract_x : iX ≫ rX = 𝟙 X'
  retract_y : iY ≫ rY = 𝟙 Y'
  retract_p : iP ≫ rP = 𝟙 P'
  i_top : iZ ≫ f = f' ≫ iX
  i_left : iZ ≫ g = g' ≫ iY
  i_right : iX ≫ inl = inl' ≫ iP
  i_bottom : iY ≫ inr = inr' ≫ iP
  r_top : f ≫ rX = rZ ≫ f'
  r_left : g ≫ rY = rZ ≫ g'
  r_right : inl ≫ rP = rX ≫ inl'
  r_bottom : inr ≫ rP = rY ≫ inr'

theorem CommSqRetract.isPushout {C : Type u} [Category.{v} C]
    {Z' X' Y' P' Z X Y P : C}
    {f' : Z' ⟶ X'} {g' : Z' ⟶ Y'} {inl' : X' ⟶ P'} {inr' : Y' ⟶ P'}
    {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
    (R : CommSqRetract f' g' inl' inr' f g inl inr)
    (h : IsPushout f g inl inr) : IsPushout f' g' inl' inr' := by
  apply IsPushout.mk' R.small.w
  · intro T d e hd he
    rw [← Category.id_comp d, ← R.retract_p, Category.assoc]
    rw [← Category.id_comp e, ← R.retract_p, Category.assoc]
    congr 1
    apply h.hom_ext
    · calc
        inl ≫ (R.rP ≫ d) = (inl ≫ R.rP) ≫ d := by simp
        _ = (R.rX ≫ inl') ≫ d := by rw [R.r_right]
        _ = R.rX ≫ (inl' ≫ d) := by simp
        _ = R.rX ≫ (inl' ≫ e) := by rw [hd]
        _ = (R.rX ≫ inl') ≫ e := by simp
        _ = (inl ≫ R.rP) ≫ e := by rw [R.r_right]
        _ = inl ≫ (R.rP ≫ e) := by simp
    · calc
        inr ≫ (R.rP ≫ d) = (inr ≫ R.rP) ≫ d := by simp
        _ = (R.rY ≫ inr') ≫ d := by rw [R.r_bottom]
        _ = R.rY ≫ (inr' ≫ d) := by simp
        _ = R.rY ≫ (inr' ≫ e) := by rw [he]
        _ = (R.rY ≫ inr') ≫ e := by simp
        _ = (inr ≫ R.rP) ≫ e := by rw [R.r_bottom]
        _ = inr ≫ (R.rP ≫ e) := by simp
  · intro T a b hab
    have hcompat : f ≫ (R.rX ≫ a) = g ≫ (R.rY ≫ b) := by
      calc
        f ≫ (R.rX ≫ a) = (f ≫ R.rX) ≫ a := by simp
        _ = (R.rZ ≫ f') ≫ a := by rw [R.r_top]
        _ = R.rZ ≫ (f' ≫ a) := by simp
        _ = R.rZ ≫ (g' ≫ b) := by rw [hab]
        _ = (R.rZ ≫ g') ≫ b := by simp
        _ = (g ≫ R.rY) ≫ b := by rw [R.r_left]
        _ = g ≫ (R.rY ≫ b) := by simp
    let d : P ⟶ T := h.desc (R.rX ≫ a) (R.rY ≫ b) hcompat
    refine ⟨R.iP ≫ d, ?_, ?_⟩
    · calc
        inl' ≫ (R.iP ≫ d) = (inl' ≫ R.iP) ≫ d := by simp
        _ = (R.iX ≫ inl) ≫ d := by rw [R.i_right]
        _ = R.iX ≫ (inl ≫ d) := by simp
        _ = R.iX ≫ (R.rX ≫ a) := by rw [h.inl_desc]
        _ = (R.iX ≫ R.rX) ≫ a := by simp
        _ = a := by rw [R.retract_x]; simp
    · calc
        inr' ≫ (R.iP ≫ d) = (inr' ≫ R.iP) ≫ d := by simp
        _ = (R.iY ≫ inr) ≫ d := by rw [R.i_bottom]
        _ = R.iY ≫ (inr ≫ d) := by simp
        _ = R.iY ≫ (R.rY ≫ b) := by rw [h.inr_desc]
        _ = (R.iY ≫ R.rY) ≫ b := by simp
        _ = b := by rw [R.retract_y]; simp

end DifferentialGeometry.Topology.VanKampen

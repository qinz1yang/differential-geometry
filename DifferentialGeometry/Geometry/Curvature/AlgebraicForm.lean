import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Algebraic curvature forms

This file records the small polarization argument saying that an algebraic
curvature form is determined by its sectional diagonal.  It is independent of
manifolds and curvature realizations.
-/

noncomputable section

namespace DifferentialGeometry.Integral.Connection

variable {V : Type*} [AddCommGroup V] [Module Real V]

/-- A real quadrilinear curvature form, presented by first-slot linearity and
the three standard curvature identities.  The remaining slot linearities
follow from these identities. -/
structure IsAlgCurvForm (B : V → V → V → V → Real) : Prop where
  add_left : ∀ x₁ x₂ y z w, B (x₁ + x₂) y z w = B x₁ y z w + B x₂ y z w
  smul_left : ∀ (a : Real) x y z w, B (a • x) y z w = a * B x y z w
  anti_first : ∀ x y z w, B x y z w = -B y x z w
  anti_last : ∀ x y z w, B x y z w = -B x y w z
  bianchi : ∀ x y z w, B x y z w + B y z x w + B z x y w = 0

namespace IsAlgCurvForm

variable {B B' : V → V → V → V → Real}

/-- Algebraic curvature forms are symmetric under swapping the two pairs. -/
theorem pair_swap (hB : IsAlgCurvForm B) (x y z w : V) :
    B x y z w = B z w x y := by
  have h1 := hB.bianchi y z x w
  have h2 := hB.bianchi z x w y
  have h3 := hB.bianchi x w y z
  have h4 := hB.bianchi w y z x
  have a1 := hB.anti_last y z x w
  have a2 := hB.anti_last z x y w
  have a3 := hB.anti_last x w z y
  have a4 := hB.anti_last w y z x
  have a5 := hB.anti_last x y z w
  have a6 := hB.anti_last w z x y
  have b1 := hB.anti_first y x w z
  have b2 := hB.anti_first z w y x
  have b3 := hB.anti_first w z x y
  linarith

/-- Additivity in the second slot. -/
theorem add_two (hB : IsAlgCurvForm B) (x y₁ y₂ z w : V) :
    B x (y₁ + y₂) z w = B x y₁ z w + B x y₂ z w := by
  rw [hB.anti_first x (y₁ + y₂), hB.add_left,
    hB.anti_first y₁ x, hB.anti_first y₂ x]
  ring

/-- Additivity in the third slot. -/
theorem add_three (hB : IsAlgCurvForm B) (x y z₁ z₂ w : V) :
    B x y (z₁ + z₂) w = B x y z₁ w + B x y z₂ w := by
  rw [hB.pair_swap x y (z₁ + z₂) w, hB.add_left,
    hB.pair_swap z₁ w x y, hB.pair_swap z₂ w x y]

/-- Additivity in the fourth slot. -/
theorem add_four (hB : IsAlgCurvForm B) (x y z w₁ w₂ : V) :
    B x y z (w₁ + w₂) = B x y z w₁ + B x y z w₂ := by
  rw [hB.anti_last x y z (w₁ + w₂), hB.add_three,
    hB.anti_last x y w₁ z, hB.anti_last x y w₂ z]
  ring

/-- The difference of two algebraic curvature forms is an algebraic curvature
form. -/
theorem sub (hB : IsAlgCurvForm B) (hB' : IsAlgCurvForm B') :
    IsAlgCurvForm (fun x y z w => B x y z w - B' x y z w) where
  add_left x₁ x₂ y z w := by
    rw [hB.add_left, hB'.add_left]
    ring
  smul_left a x y z w := by
    rw [hB.smul_left, hB'.smul_left]
    ring
  anti_first x y z w := by
    rw [hB.anti_first, hB'.anti_first]
    ring
  anti_last x y z w := by
    rw [hB.anti_last, hB'.anti_last]
    ring
  bianchi x y z w := by
    have h := hB.bianchi x y z w
    have h' := hB'.bianchi x y z w
    linarith

/-- A scalar multiple of an algebraic curvature form is one. -/
theorem smul (hB : IsAlgCurvForm B) (c : Real) :
    IsAlgCurvForm (fun x y z w => c * B x y z w) where
  add_left x₁ x₂ y z w := by
    rw [hB.add_left]
    ring
  smul_left a x y z w := by
    rw [hB.smul_left]
    ring
  anti_first x y z w := by
    rw [hB.anti_first]
    ring
  anti_last x y z w := by
    rw [hB.anti_last]
    ring
  bianchi x y z w := by
    have h := hB.bianchi x y z w
    calc
      c * B x y z w + c * B y z x w + c * B z x y w =
          c * (B x y z w + B y z x w + B z x y w) := by ring
      _ = 0 := by rw [h, mul_zero]

/-- An algebraic curvature form whose sectional diagonal vanishes is zero. -/
theorem zero_of_diag (hB : IsAlgCurvForm B)
    (hdiag : ∀ x y, B x y x y = 0) :
    ∀ x y z w, B x y z w = 0 := by
  have hthree : ∀ x y z, B x y z y = 0 := by
    intro x y z
    have h := hdiag (x + z) y
    rw [hB.add_left, hB.add_three, hB.add_three, hdiag x y,
      hdiag z y, hB.pair_swap z y x y] at h
    linarith
  have hcyc : ∀ x y z w, B x y z w = B y z x w := by
    intro x y z w
    have h := hthree x (y + w) z
    rw [hB.add_two, hB.add_four, hB.add_four, hthree x y z,
      hthree x w z] at h
    have hswap : B x w z y = -B y z x w := by
      rw [hB.pair_swap x w z y, hB.anti_first z y x w]
    linarith
  intro x y z w
  have h := hB.bianchi x y z w
  have h1 := hcyc x y z w
  have h2 := hcyc y z x w
  linarith

/-- Two algebraic curvature forms with the same sectional diagonal agree. -/
theorem ext (hB : IsAlgCurvForm B) (hB' : IsAlgCurvForm B')
    (hdiag : ∀ x y, B x y x y = B' x y x y) :
    ∀ x y z w, B x y z w = B' x y z w := by
  have hsub := hB.sub hB'
  have hzero : ∀ x y,
      (fun a b c d => B a b c d - B' a b c d) x y x y = 0 := by
    intro x y
    change B x y x y - B' x y x y = 0
    rw [hdiag x y, sub_self]
  intro x y z w
  have h := hsub.zero_of_diag hzero x y z w
  linarith

end IsAlgCurvForm

end DifferentialGeometry.Integral.Connection

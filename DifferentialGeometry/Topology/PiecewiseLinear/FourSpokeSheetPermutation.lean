/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FourSpokeLabels

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

def fourSpokeSheetPerm (b : Bool) : Equiv.Perm (Fin 4) :=
  if b then fourSpokeFlipPerm else Equiv.refl _

theorem fourSpokeLabel_sheetPerm (b : Bool) (i : Fin 4) :
    fourSpokeLabel (fourSpokeSheetPerm b i) =
      (Bool.xor (fourSpokeLabel i).1 b, (fourSpokeLabel i).2) := by
  cases b <;> fin_cases i <;> rfl

theorem fourSpokeSheetPerm_add_two (b : Bool) (i : Fin 4) :
    fourSpokeSheetPerm b (i + 2) = fourSpokeSheetPerm b i + 2 := by
  cases b <;> fin_cases i <;> rfl

theorem fourSpoke_separated_sheetPerm {X : Type*} [TopologicalSpace X]
    {S : Set X} {T : Fin 4 → Set X}
    (hsep : ∀ i : Fin 4, ∀ U ⊆ S \ (T i ∪ T (i + 2)), IsPreconnected U →
      (U ∩ T (i + 1)).Nonempty → (U ∩ T (i + 3)).Nonempty → False) (b : Bool) :
    ∀ i : Fin 4,
      ∀ U ⊆ S \ (T (fourSpokeSheetPerm b i) ∪ T (fourSpokeSheetPerm b (i + 2))),
        IsPreconnected U → (U ∩ T (fourSpokeSheetPerm b (i + 1))).Nonempty →
        (U ∩ T (fourSpokeSheetPerm b (i + 3))).Nonempty → False := by
  cases b
  · exact hsep
  · have h₁ : ∀ i : Fin 4, fourSpokeFlipPerm (i + 1) = fourSpokeFlipPerm i + 3 := by decide
    have h₂ : ∀ i : Fin 4, fourSpokeFlipPerm (i + 2) = fourSpokeFlipPerm i + 2 := by decide
    have h₃ : ∀ i : Fin 4, fourSpokeFlipPerm (i + 3) = fourSpokeFlipPerm i + 1 := by decide
    intro i U hU hconn hp hn
    simp only [fourSpokeSheetPerm, ite_true, h₁, h₂, h₃] at hU hp hn
    exact hsep (fourSpokeFlipPerm i) U hU hconn hn hp

end DifferentialGeometry.Topology.PiecewiseLinear

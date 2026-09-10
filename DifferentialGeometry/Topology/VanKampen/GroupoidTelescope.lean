/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.CategoryTheory.ComposableArrows.Basic
import Mathlib.CategoryTheory.Groupoid

set_option autoImplicit false

open CategoryTheory

universe u v

namespace Poincare.Topology.VanKampen

theorem groupoid_telescope {C : Type u} [Groupoid.{v} C] {n : ℕ}
    {R S : ComposableArrows C n} (α : R ⟶ S) :
    S.hom = inv (ComposableArrows.app' α 0 (hi := Nat.zero_le n)) ≫ R.hom ≫
      ComposableArrows.app' α n (hi := le_rfl) := by
  calc
    S.hom = inv (ComposableArrows.app' α 0 (hi := Nat.zero_le n)) ≫
        ComposableArrows.app' α 0 (hi := Nat.zero_le n) ≫ S.hom := by
      rw [IsIso.inv_hom_id_assoc]
    _ = inv (ComposableArrows.app' α 0 (hi := Nat.zero_le n)) ≫
        (R.hom ≫ ComposableArrows.app' α n (hi := le_rfl)) := by
      rw [ComposableArrows.naturality' α 0 n]
    _ = inv (ComposableArrows.app' α 0 (hi := Nat.zero_le n)) ≫ R.hom ≫
        ComposableArrows.app' α n (hi := le_rfl) := by
      rfl

section Regression

example {C : Type u} [Groupoid.{v} C] {R S : ComposableArrows C 0} (α : R ⟶ S) :
    S.hom = inv (ComposableArrows.app' α 0 (hi := le_rfl)) ≫ R.hom ≫
      ComposableArrows.app' α 0 (hi := le_rfl) :=
  groupoid_telescope α

example {C : Type u} [Groupoid.{v} C] {R S : ComposableArrows C 1} (α : R ⟶ S) :
    S.hom = inv (ComposableArrows.app' α 0 (hi := by omega)) ≫ R.hom ≫
      ComposableArrows.app' α 1 (hi := le_rfl) :=
  groupoid_telescope α

end Regression

end Poincare.Topology.VanKampen

import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
A finite action in which every nonidentity fixes exactly two points, and every point has a
nonidentity stabilizer, has at most three orbits. Actual fixed-point/stabilizer incidence
counting and Burnside's lemma give this bound without a supplied orbit classification.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.FlatSurface

theorem finite_twoFixed_orbits_le_three (G X : Type*) [instG : Group G]
    [instFG : Finite G] [instFX : Finite X] [instAction : MulAction G X]
    (htwo : ∀ g : G, g ≠ 1 → Nat.card (MulAction.fixedBy X g) = 2)
    (hnontrivial : ∀ x : X, ∃ g : G, g ≠ 1 ∧ g • x = x) :
    Nat.card (Quotient (MulAction.orbitRel G X)) ≤ 3 := by
  classical
  let instFintypeG : Fintype G := Fintype.ofFinite G
  let instFintypeX : Fintype X := Fintype.ofFinite X
  let instFixed (g : G) : Fintype (MulAction.fixedBy X g) := Fintype.ofFinite _
  let instStabilizer (x : X) : Fintype (MulAction.stabilizer G x) := Fintype.ofFinite _
  let instOrbits : Fintype (Quotient (MulAction.orbitRel G X)) := Fintype.ofFinite _
  let e : (Σ g : G, MulAction.fixedBy X g) ≃ (Σ x : X, MulAction.stabilizer G x) :=
    { toFun := fun ⟨g, x⟩ => ⟨x.val, ⟨g, x.property⟩⟩
      invFun := fun ⟨x, g⟩ => ⟨g.val, ⟨x, g.property⟩⟩
      left_inv := by intro ⟨g, ⟨x, hx⟩⟩; rfl
      right_inv := by intro ⟨x, ⟨g, hg⟩⟩; rfl }
  have hcount : (∑ g : G, Fintype.card (MulAction.fixedBy X g)) =
      ∑ x : X, Fintype.card (MulAction.stabilizer G x) := by
    rw [← Fintype.card_sigma, ← Fintype.card_sigma]
    exact Fintype.card_congr e
  let eone : MulAction.fixedBy X (1 : G) ≃ X :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, one_smul G x⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  have hone : Fintype.card (MulAction.fixedBy X (1 : G)) = Fintype.card X :=
    Fintype.card_congr eone
  have hrest : (∑ g ∈ Finset.univ.erase (1 : G), Fintype.card (MulAction.fixedBy X g)) =
      2 * (Fintype.card G - 1) := by
    calc
      _ = ∑ g ∈ Finset.univ.erase (1 : G), 2 := by
        apply Finset.sum_congr rfl
        intro g hg
        simpa only [Nat.card_eq_fintype_card] using htwo g (Finset.ne_of_mem_erase hg)
      _ = _ := by simp [Finset.card_erase_of_mem, Nat.mul_comm]
  have htotal : (∑ g : G, Fintype.card (MulAction.fixedBy X g)) =
      Fintype.card X + 2 * (Fintype.card G - 1) := by
    have he := Finset.sum_erase_add Finset.univ
      (fun g : G => Fintype.card (MulAction.fixedBy X g)) (Finset.mem_univ (1 : G))
    rw [hrest, hone] at he
    exact he.symm.trans (Nat.add_comm _ _)
  have hstab (x : X) : 2 ≤ Fintype.card (MulAction.stabilizer G x) := by
    obtain ⟨g, hg, hfix⟩ := hnontrivial x
    let instNontrivial : Nontrivial (MulAction.stabilizer G x) :=
      ⟨⟨⟨g, hfix⟩, 1, by intro he; exact hg (congrArg Subtype.val he)⟩⟩
    exact Fintype.one_lt_card
  have hlower : 2 * Fintype.card X ≤ ∑ x : X, Fintype.card (MulAction.stabilizer G x) := by
    calc
      _ = ∑ x : X, 2 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (by intro x hx; exact hstab x)
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X
  have heq : Fintype.card (Quotient (MulAction.orbitRel G X)) * Fintype.card G =
      Fintype.card X + 2 * (Fintype.card G - 1) := hburn.symm.trans htotal
  rw [← hcount, hburn] at hlower
  have hgpos : 0 < Fintype.card G := Fintype.card_pos
  rw [Nat.card_eq_fintype_card]
  by_contra hn
  have hlarge : 4 * Fintype.card G ≤
      Fintype.card (Quotient (MulAction.orbitRel G X)) * Fintype.card G :=
    Nat.mul_le_mul_right _ (by omega)
  omega

end DifferentialGeometry.Geometry.FlatSurface

import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index

/-!
Actual finite-action orbit cardinal sums and the exact two-fixed-point Burnside equation
retain the whole orbit and stabilizer data. They provide numerical pole signatures without
an assumed group or orbit classification.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.FlatSurface

theorem finite_twoFixed_orbit_card_eq (G X : Type*) [instG : Group G]
    [instFG : Finite G] [instFX : Finite X] [instAction : MulAction G X]
    (htwo : ∀ g : G, g ≠ 1 → Nat.card (MulAction.fixedBy X g) = 2) :
    Nat.card (Quotient (MulAction.orbitRel G X)) * Nat.card G =
      Nat.card X + 2 * (Nat.card G - 1) := by
  classical
  let instFintypeG : Fintype G := Fintype.ofFinite G
  let instFintypeX : Fintype X := Fintype.ofFinite X
  let instFixed (g : G) : Fintype (MulAction.fixedBy X g) := Fintype.ofFinite _
  let instOrbits : Fintype (Quotient (MulAction.orbitRel G X)) := Fintype.ofFinite _
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
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X
  simpa only [Nat.card_eq_fintype_card] using hburn.symm.trans htotal

theorem finite_orbit_sum_card (G X : Type*) [instG : Group G] [instFX : Finite X]
    [instAction : MulAction G X] [instOrbits : Fintype (Quotient (MulAction.orbitRel G X))] :
    Nat.card X = ∑ w : Quotient (MulAction.orbitRel G X), Nat.card (MulAction.orbit G w.out) := by
  classical
  let instFintypeX : Fintype X := Fintype.ofFinite X
  let instOrbit (x : X) : Fintype (MulAction.orbit G x) := Fintype.ofFinite _
  simp only [Nat.card_eq_fintype_card]
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (MulAction.selfEquivSigmaOrbits G X)

end DifferentialGeometry.Geometry.FlatSurface

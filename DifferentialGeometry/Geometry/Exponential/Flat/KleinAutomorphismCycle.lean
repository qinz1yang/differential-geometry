import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-!
A nontrivial cubic automorphism of an actual four-element group cycles its three nonidentity
members. The cycle exhausts the group by a faithful four-label enumeration and cardinality.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.FlatSurface

theorem four_group_automorphism_cycle {K : Type*} [instG : Group K] [instF : Fintype K]
    (hc : Fintype.card K = 4) (T : MulAut K) (hT : T ^ 3 = 1)
    (a : K) (ha : T a ≠ a) :
    ∀ {x : K}, x ≠ 1 ↔ x = a ∨ x = T a ∨ x = T (T a) := by
  classical
  have h3 : T (T (T a)) = a := by
    have he := congrArg (fun f : MulAut K => f a) hT
    exact he
  have ha1 : a ≠ 1 := by intro he; simp only [he, map_one] at ha; exact ha rfl
  have ht1 : T a ≠ 1 := by
    intro he
    exact ha1 (T.injective (he.trans T.map_one.symm))
  have htt1 : T (T a) ≠ 1 := by
    intro he
    exact ht1 (T.injective (he.trans T.map_one.symm))
  have htta : T (T a) ≠ a := by
    intro he
    have hh := congrArg T he
    rw [h3] at hh
    exact ha hh.symm
  let f : Fin 4 → K := ![1, a, T a, T (T a)]
  have hf : Function.Injective f := by
    intro i j he
    fin_cases i <;> fin_cases j <;> norm_num [f] at he ⊢ <;>
      first
      | exact ha he
      | exact ha he.symm
      | exact ha1 he
      | exact ha1 he.symm
      | exact ht1 he
      | exact ht1 he.symm
      | exact htt1 he
      | exact htt1 he.symm
      | exact htta he
      | exact htta he.symm
  have hs : Function.Surjective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, by simpa using hc.symm⟩ |>.2
  intro x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := hs x
    fin_cases i
    · change 1 = x at hi
      exact False.elim (hx hi.symm)
    · exact Or.inl hi.symm
    · exact Or.inr (Or.inl hi.symm)
    · exact Or.inr (Or.inr hi.symm)
  · rintro (rfl | rfl | rfl)
    · exact ha1
    · exact ht1
    · exact htt1

end DifferentialGeometry.Geometry.FlatSurface

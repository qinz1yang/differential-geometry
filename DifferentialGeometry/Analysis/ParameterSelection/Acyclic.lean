import Mathlib.Order.WellFoundedSet
import Mathlib.Logic.Relation
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace WellFounded

variable {ι : Type*} {r : ι → ι → Prop}

theorem exists_assignment (hr : WellFounded r) {A : ι → Type*}
    (D : ∀ i, Set (A i))
    (P : ∀ i, (∀ j, r j i → A j) → A i → Prop)
    (h : ∀ i, ∀ v : ∀ j, r j i → A j,
      (∀ j hj, v j hj ∈ D j) → ∃ x ∈ D i, P i v x) :
    ∃ f : ∀ i, A i, (∀ i, f i ∈ D i) ∧ ∀ i, P i (fun j _ => f j) (f i) := by
  classical
  let F (i : ι) (v : ∀ j, r j i → {x : A j // x ∈ D j}) : {x : A i // x ∈ D i} :=
    ⟨(h i (fun j hj => (v j hj).val) (fun j hj => (v j hj).property)).choose,
      (h i (fun j hj => (v j hj).val) (fun j hj => (v j hj).property)).choose_spec.1⟩
  let f := hr.fix F
  refine ⟨fun i => (f i).val, fun i => (f i).property, fun i => ?_⟩
  have heq : f i = F i (fun j _ => f j) := hr.fix_eq F i
  change P i (fun j _ => (f j).val) (f i).val
  conv_rhs => rw [heq]
  exact (h i (fun j _ => (f j).val) (fun j _ => (f j).property)).choose_spec.2

end WellFounded

namespace Relation

theorem wellFounded_of_finite_acyclic {ι : Type*} [Finite ι] {r : ι → ι → Prop}
    (h : ∀ i, ¬ TransGen r i i) : WellFounded r := by
  let : Std.Irrefl (TransGen r) := ⟨h⟩
  let : IsStrictOrder ι (TransGen r) := {}
  have hw : WellFounded (TransGen r) :=
    Set.wellFoundedOn_univ.mp (Set.toFinite (Set.univ : Set ι)).wellFoundedOn
  exact hw.mono (fun _ _ => TransGen.single)

end Relation

namespace Finset

theorem exists_pos_lt_bounds {ι : Type*} (s : Finset ι) (b : ι → ℝ)
    (hb : ∀ i ∈ s, 0 < b i) : ∃ x : ℝ, 0 < x ∧ ∀ i ∈ s, x < b i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨x, hx, hxb⟩ := ih (fun j hj => hb j (mem_insert_of_mem hj))
    refine ⟨min x (b i / 2), lt_min hx (by linarith [hb i (mem_insert_self i s)]), ?_⟩
    intro j hj
    rcases mem_insert.mp hj with hji | hj
    · subst j
      exact (min_le_right _ _).trans_lt (by linarith [hb i (mem_insert_self i s)])
    · exact (min_le_left _ _).trans_lt (hxb j hj)

theorem exists_gt_bounds {ι : Type*} (s : Finset ι) (b : ι → ℝ) :
    ∃ x : ℝ, ∀ i ∈ s, b i < x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨x, hx⟩ := ih
    refine ⟨max x (b i + 1), ?_⟩
    intro j hj
    rcases mem_insert.mp hj with hji | hj
    · subst j
      exact (by linarith : b i < b i + 1).trans_le (le_max_right _ _)
    · exact (hx j hj).trans_le (le_max_left _ _)

end Finset

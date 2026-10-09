import DifferentialGeometry.Analysis.ParameterSelection.Acyclic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity

/-!
# Finite acyclic parameter selection (FC46)

Finitely many positive parameters ordered by an acyclic relation `r` (`r j i`: `j` is chosen before `i`).
At each node, once the predecessor values are fixed, the admissible set either contains every positive number
below finitely many positive upper bounds, or every positive number above finitely many lower bounds, or is a
supplied set with a positive element.  Then all constraints have a simultaneous positive solution.
-/

set_option autoImplicit false

open Set

namespace DifferentialGeometry.Analysis.ParameterSelection

/-- The admissible set of a node with finitely many positive strict upper bounds has a positive element. -/
theorem exists_pos_mem_of_upper_bounds {A : Set ℝ} (U : Finset ℝ) (hU : ∀ b ∈ U, 0 < b)
    (hA : {x | 0 < x ∧ ∀ b ∈ U, x < b} ⊆ A) : (A ∩ Ioi 0).Nonempty := by
  obtain ⟨x, hx, hxb⟩ := U.exists_pos_lt_bounds id hU
  exact ⟨x, hA ⟨hx, hxb⟩, hx⟩

/-- The admissible set of a node with finitely many finite lower bounds has a positive element. -/
theorem exists_pos_mem_of_lower_bounds {A : Set ℝ} (L : Finset ℝ)
    (hA : {x | ∀ b ∈ L, b < x} ⊆ A) : (A ∩ Ioi 0).Nonempty := by
  obtain ⟨x, hx⟩ := (insert 0 L).exists_gt_bounds id
  exact ⟨x, hA fun b hb => hx b (Finset.mem_insert_of_mem hb), hx 0 (Finset.mem_insert_self 0 L)⟩

/-- **FC46.** Finite acyclic parameter selection: upper-bound nodes, lower-bound nodes and nodes with a supplied
nonempty admissible set (for every positive predecessor tuple) have a simultaneous positive assignment. -/
theorem exists_positive_parameters_of_acyclic {ι : Type*} [Finite ι] {r : ι → ι → Prop}
    (hr : ∀ i, ¬ Relation.TransGen r i i) (A : ∀ i, (∀ j, r j i → ℝ) → Set ℝ)
    (hA : ∀ i (v : ∀ j, r j i → ℝ), (∀ j hj, 0 < v j hj) →
      (∃ U : Finset ℝ, (∀ b ∈ U, 0 < b) ∧ {x | 0 < x ∧ ∀ b ∈ U, x < b} ⊆ A i v) ∨
      (∃ L : Finset ℝ, {x | ∀ b ∈ L, b < x} ⊆ A i v) ∨ (A i v ∩ Ioi 0).Nonempty) :
    ∃ f : ι → ℝ, (∀ i, 0 < f i) ∧ ∀ i, f i ∈ A i (fun j _ => f j) := by
  have hwf : WellFounded r := Relation.wellFounded_of_finite_acyclic hr
  obtain ⟨f, hpos, hf⟩ := hwf.exists_assignment (A := fun _ => ℝ) (fun _ => Ioi 0)
    (fun i v x => x ∈ A i v) (fun i v hv => by
      have hne : (A i v ∩ Ioi 0).Nonempty := by
        rcases hA i v hv with ⟨U, hU, hUA⟩ | ⟨L, hLA⟩ | hne
        · exact exists_pos_mem_of_upper_bounds U hU hUA
        · exact exists_pos_mem_of_lower_bounds L hLA
        · exact hne
      obtain ⟨x, hxA, hx⟩ := hne
      exact ⟨x, hx, hxA⟩)
  exact ⟨f, hpos, hf⟩

/-- Consumer: a three-parameter chain `c₃ ≺ Δ ≺ Λ` of the register's shape
(`c₃ < 1/1000`; `Δ > 100` and `Δ > 1/c₃`; `Λ < 1/(10⁶ Δ)` and `Λ < c₃`). -/
theorem exists_chain_parameters :
    ∃ f : Fin 3 → ℝ, (∀ i, 0 < f i) ∧ f 0 < 1 / 1000 ∧ 100 < f 1 ∧ 1 / f 0 < f 1 ∧
      f 2 < 1 / (1000000 * f 1) ∧ f 2 < f 0 := by
  let r : Fin 3 → Fin 3 → Prop := fun j i => j < i
  have hr : ∀ i, ¬ Relation.TransGen r i i := by
    intro i h
    have : ∀ a b, Relation.TransGen r a b → a < b := fun a b hab =>
      Relation.TransGen.trans_induction_on hab (fun h => h) (fun _ _ h₁ h₂ => h₁.trans h₂)
    exact lt_irrefl i (this i i h)
  let A : ∀ i, (∀ j, r j i → ℝ) → Set ℝ := fun i v =>
    if h2 : i = 2 then
      {x | x < 1 / (1000000 * v 1 (by subst h2; decide)) ∧ x < v 0 (by subst h2; decide)}
    else if h1 : i = 1 then
      {x | 100 < x ∧ 1 / v 0 (by subst h1; decide) < x}
    else {x | x < 1 / 1000}
  obtain ⟨f, hpos, hf⟩ := exists_positive_parameters_of_acyclic hr A (by
    intro i v hv
    fin_cases i
    · refine Or.inl ⟨{1 / 1000}, by simp, fun x hx => ?_⟩
      simpa [A] using hx.2 (1 / 1000) (by simp)
    · refine Or.inr (Or.inl ⟨{100, 1 / v 0 (by decide)}, fun x hx => ?_⟩)
      simp only [A, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceDIte, mem_ofPred_eq]
      exact ⟨hx 100 (by simp), hx _ (by simp)⟩
    · have h1 := hv 1 (by decide)
      have h0 := hv 0 (by decide)
      refine Or.inl ⟨{1 / (1000000 * v 1 (by decide)), v 0 (by decide)}, ?_, fun x hx => ?_⟩
      · intro b hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl
        · positivity
        · exact h0
      · simp only [A, Fin.reduceFinMk, Fin.isValue, ↓reduceDIte, mem_ofPred_eq]
        exact ⟨hx.2 _ (by simp), hx.2 _ (by simp)⟩)
  have h0 := hf 0
  have h1 := hf 1
  have h2 := hf 2
  simp only [A, Fin.isValue, Fin.reduceEq, ↓reduceDIte, mem_ofPred_eq] at h0 h1 h2
  exact ⟨f, hpos, h0, h1.1, h1.2, h2.1, h2.2⟩

end DifferentialGeometry.Analysis.ParameterSelection

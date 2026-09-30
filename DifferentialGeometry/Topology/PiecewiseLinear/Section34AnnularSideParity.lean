import DifferentialGeometry.Topology.PiecewiseLinear.Section34AlternatingPathMatchings
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Set.Lattice.Bounded
import Mathlib.Data.Set.Lattice.Disjoint
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Data.Set.Lattice.Order

namespace Bool

theorem alternating_eq_ite_mod_two {n : ℕ} {s : ℕ → Bool}
    (hstep : ∀ i, i + 1 < n → s (i + 1) = !s i) {i : ℕ} (hi : i < n) :
    s i = if i % 2 = 0 then s 0 else !s 0 := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [hstep i hi, ih (by omega)]
    by_cases h : i % 2 = 0
    · have hnext : (i + 1) % 2 ≠ 0 := by omega
      simp [h, hnext]
    · have hnext : (i + 1) % 2 = 0 := by omega
      simp [h, hnext]

theorem alternating_eq_iff_mod_two_eq {n : ℕ} {s : ℕ → Bool}
    (hstep : ∀ i, i + 1 < n → s (i + 1) = !s i) {i j : ℕ}
    (hi : i < n) (hj : j < n) : s i = s j ↔ i % 2 = j % 2 := by
  rw [alternating_eq_ite_mod_two hstep hi, alternating_eq_ite_mod_two hstep hj]
  by_cases hpar : i % 2 = j % 2
  · simp only [hpar]
  have hcases : (i % 2 = 0 ∧ j % 2 ≠ 0) ∨ (i % 2 ≠ 0 ∧ j % 2 = 0) := by omega
  rcases hcases with ⟨hi₀, hj₀⟩ | ⟨hi₀, hj₀⟩
  · rw [ite_eq_left hi₀, ite_eq_right hj₀]
    exact iff_of_false (not_ne_self (s 0)).symm hpar
  · rw [ite_eq_right hi₀, ite_eq_left hj₀]
    exact iff_of_false (not_ne_self (s 0)) hpar

end Bool

namespace Fin

theorem alternatingNeighbor_lower_index {n : ℕ} (c : Fin 2) (i : Fin n)
    (hi : alternatingNeighbor c i ≠ i) :
    min i.val (alternatingNeighbor c i).val < n - 1 ∧
      min i.val (alternatingNeighbor c i).val % 2 = c.val := by
  have hj := (alternatingNeighbor c i).isLt
  have h := (alternatingNeighbor_eq_and_ne_iff c i (alternatingNeighbor c i)).mp
    ⟨rfl, hi.symm⟩
  rcases h with ⟨hpar, hsucc⟩ | ⟨hpar, hsucc⟩
  · rw [min_eq_left (by omega)]
    exact ⟨by omega, hpar⟩
  · rw [min_eq_right (by omega)]
    exact ⟨by omega, hpar⟩

theorem alternatingNeighbor_sides_eq {n : ℕ} {s : ℕ → Bool}
    (hstep : ∀ i, i + 1 < n - 1 → s (i + 1) = !s i)
    (c : Fin 2) (i j : Fin n) (hi : alternatingNeighbor c i ≠ i)
    (hj : alternatingNeighbor c j ≠ j) :
    s (min i.val (alternatingNeighbor c i).val) =
      s (min j.val (alternatingNeighbor c j).val) := by
  have hi' := alternatingNeighbor_lower_index c i hi
  have hj' := alternatingNeighbor_lower_index c j hj
  exact (Bool.alternating_eq_iff_mod_two_eq hstep hi'.1 hj'.1).mpr (hi'.2.trans hj'.2.symm)

end Fin

namespace Set

theorem same_side_of_local_alternation {X : Type*} {A B : Set X} {O : ℕ → Set X}
    {n : ℕ} (hdis : Disjoint A B) (hne : ∀ i, i < n → (O i).Nonempty)
    (hside : ∀ i, i < n → O i ⊆ A ∨ O i ⊆ B)
    (hstep : ∀ i, i + 1 < n →
      (O i ⊆ A ∧ O (i + 1) ⊆ B) ∨ (O i ⊆ B ∧ O (i + 1) ⊆ A))
    {i j : ℕ} (hi : i < n) (hj : j < n) (hpar : i % 2 = j % 2) :
    (O i ⊆ A ∧ O j ⊆ A) ∨ (O i ⊆ B ∧ O j ⊆ B) := by
  classical
  let s (k : ℕ) : Bool := decide (O k ⊆ A)
  have hnot (k : ℕ) (hk : k < n) (hkB : O k ⊆ B) : ¬ O k ⊆ A := by
    intro hkA
    obtain ⟨x, hx⟩ := hne k hk
    exact disjoint_left.mp hdis (hkA hx) (hkB hx)
  have hnext (k : ℕ) (hk : k + 1 < n) : s (k + 1) = !s k := by
    rcases hstep k hk with ⟨hkA, hkB⟩ | ⟨hkB, hkA⟩
    · simp [s, hkA, hnot (k + 1) hk hkB]
    · simp [s, hkA, hnot k (by omega) hkB]
  have heq := (Bool.alternating_eq_iff_mod_two_eq hnext hi hj).mpr hpar
  by_cases hiA : O i ⊆ A
  · have hjA : O j ⊆ A := by
      have hs : s j = true := heq.symm.trans (by simp [s, hiA])
      simpa [s] using hs
    exact Or.inl ⟨hiA, hjA⟩
  · have hjA : ¬ O j ⊆ A := by
      have hs : s j = false := heq.symm.trans (by simp [s, hiA])
      simpa [s] using hs
    exact Or.inr ⟨(hside i hi).resolve_left hiA, (hside j hj).resolve_left hjA⟩

theorem same_side_alternatingNeighbor {X : Type*} {A B : Set X} {O : ℕ → Set X}
    {n : ℕ} (hdis : Disjoint A B) (hne : ∀ i, i < n - 1 → (O i).Nonempty)
    (hside : ∀ i, i < n - 1 → O i ⊆ A ∨ O i ⊆ B)
    (hstep : ∀ i, i + 1 < n - 1 →
      (O i ⊆ A ∧ O (i + 1) ⊆ B) ∨ (O i ⊆ B ∧ O (i + 1) ⊆ A))
    (c : Fin 2) (i j : Fin n) (hi : Fin.alternatingNeighbor c i ≠ i)
    (hj : Fin.alternatingNeighbor c j ≠ j) :
    (O (min i.val (Fin.alternatingNeighbor c i).val) ⊆ A ∧
        O (min j.val (Fin.alternatingNeighbor c j).val) ⊆ A) ∨
      (O (min i.val (Fin.alternatingNeighbor c i).val) ⊆ B ∧
        O (min j.val (Fin.alternatingNeighbor c j).val) ⊆ B) := by
  have hi' := Fin.alternatingNeighbor_lower_index c i hi
  have hj' := Fin.alternatingNeighbor_lower_index c j hj
  exact same_side_of_local_alternation hdis hne hside hstep hi'.1 hj'.1
    (hi'.2.trans hj'.2.symm)

end Set

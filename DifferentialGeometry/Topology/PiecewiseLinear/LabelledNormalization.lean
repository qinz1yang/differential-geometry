/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Basic.Countable.Defs
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Pairing
import Mathlib.Order.Lattice.Nat
import Mathlib.Logic.Function.Basic

open Function

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_forall_not_legal_of_forall_exists_move {ι α β : Type*} [Countable ι]
    [DecidableEq ι] {r : ι → α → ℕ} {Legal : ι → (ι → α) → Prop} {Inv : β → (ι → α) → Prop}
    {nbr : ι → Finset ι} {dep : β → Finset ι} {C₀ : ι → α}
    (hlegal : ∀ (i : ι) (C C' : ι → α), (∀ j ∈ nbr i, C j = C' j) → (Legal i C ↔ Legal i C'))
    (hdep : ∀ (b : β) (C C' : ι → α), (∀ j ∈ dep b, C j = C' j) → (Inv b C ↔ Inv b C'))
    (hC₀ : ∀ b, Inv b C₀)
    (hmove : ∀ (C : ι → α) (i : ι), (∀ b, Inv b C) → Legal i C →
      ∃ a : α, r i a < r i (C i) ∧ ∀ b, Inv b (Function.update C i a)) :
    ∃ (D : ℕ → ι → α) (Cinf : ι → α), D 0 = C₀ ∧
      (∀ n : ℕ, D (n + 1) = D n ∨ ∃ i : ι, Legal i (D n) ∧
        r i (D (n + 1) i) < r i (D n i) ∧ ∀ j : ι, j ≠ i → D (n + 1) j = D n j) ∧
      (∀ i : ι, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → D n i = Cinf i) ∧
      (∀ i : ι, ¬ Legal i Cinf) ∧ ∀ b : β, Inv b Cinf := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨fun _ => C₀, C₀, rfl, fun _ => Or.inl rfl, fun i => isEmptyElim i,
      fun i => isEmptyElim i, hC₀⟩
  obtain ⟨σ, hσ⟩ := exists_surjective_nat ι
  have hmove' : ∀ (C : ι → α) (i : ι), ∃ a : α, (∀ b, Inv b C) → Legal i C →
      r i a < r i (C i) ∧ ∀ b, Inv b (Function.update C i a) := by
    intro C i
    by_cases h : (∀ b, Inv b C) ∧ Legal i C
    · obtain ⟨a, ha⟩ := hmove C i h.1 h.2
      exact ⟨a, fun _ _ => ha⟩
    · exact ⟨C i, fun h₁ h₂ => absurd ⟨h₁, h₂⟩ h⟩
  choose pick hpick using hmove'
  let e : ℕ → ι := fun k => σ (Nat.unpair k).1
  let step : ℕ → (ι → α) → (ι → α) := fun k C =>
    if Legal (e k) C then Function.update C (e k) (pick C (e k)) else C
  let D : ℕ → ι → α := fun n => Nat.rec (motive := fun _ => ι → α) C₀ (fun k Ck => step k Ck) n
  have hD0 : D 0 = C₀ := rfl
  have hDs : ∀ k : ℕ, D (k + 1) = step k (D k) := fun _ => rfl
  have hstep : ∀ (k : ℕ) (C : ι → α), step k C =
      if Legal (e k) C then Function.update C (e k) (pick C (e k)) else C := fun _ _ => rfl
  have hfair : ∀ (i : ι) (N : ℕ), ∃ m : ℕ, N ≤ m ∧ e m = i := by
    intro i N
    obtain ⟨k, rfl⟩ := hσ i
    exact ⟨Nat.pair k N, Nat.right_le_pair k N, by simp only [e, Nat.unpair_pair]⟩
  have hDinv : ∀ n : ℕ, ∀ b, Inv b (D n) := by
    intro n
    induction n with
    | zero => exact hC₀
    | succ k ih =>
      rw [hDs, hstep]
      by_cases h : Legal (e k) (D k)
      · rw [ite_eq_left h]
        exact (hpick (D k) (e k) ih h).2
      · rw [ite_eq_right h]
        exact ih
  have hmovestep : ∀ k : ℕ, Legal (e k) (D k) →
      D (k + 1) = Function.update (D k) (e k) (pick (D k) (e k)) := by
    intro k h
    rw [hDs, hstep, ite_eq_left h]
  have hfix : ∀ k : ℕ, ¬ Legal (e k) (D k) → D (k + 1) = D k := by
    intro k h
    rw [hDs, hstep, ite_eq_right h]
  have hpoint : ∀ (k : ℕ) (i : ι), D (k + 1) i = D k i ∨ r i (D (k + 1) i) < r i (D k i) := by
    intro k i
    by_cases h : Legal (e k) (D k)
    · have hEq := hmovestep k h
      by_cases hik : i = e k
      · refine Or.inr ?_
        rw [hik, hEq, Function.update_self]
        exact (hpick (D k) (e k) (hDinv k) h).1
      · exact Or.inl (by rw [hEq, Function.update_of_ne hik])
    · exact Or.inl (by rw [hfix k h])
  have hanti : ∀ i : ι, Antitone fun n : ℕ => r i (D n i) := by
    intro i
    refine antitone_nat_of_succ_le fun n => ?_
    rcases hpoint n i with h | h
    · exact le_of_eq (by rw [h])
    · exact le_of_lt h
  have hstab : ∀ i : ι, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → D n i = D N i := by
    intro i
    have hne : (Set.range fun n : ℕ => r i (D n i)).Nonempty := ⟨_, 0, rfl⟩
    obtain ⟨N, hN⟩ := Nat.sInf_mem hne
    have hmin : ∀ n : ℕ, r i (D N i) ≤ r i (D n i) := by
      intro n
      calc r i (D N i) = sInf (Set.range fun n : ℕ => r i (D n i)) := hN
        _ ≤ r i (D n i) := Nat.sInf_le ⟨n, rfl⟩
    have hconst : ∀ n : ℕ, N ≤ n → r i (D n i) = r i (D N i) :=
      fun n hn => le_antisymm (hanti i hn) (hmin n)
    refine ⟨N, fun n hn => ?_⟩
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ m hm ih =>
      rcases hpoint m i with h | h
      · rw [h, ih]
      · exact absurd h (by
          rw [hconst (m + 1) (Nat.le_succ_of_le hm), hconst m hm]; exact lt_irrefl _)
  choose N hN using hstab
  refine ⟨D, fun i => D (N i) i, hD0, ?_, fun i => ⟨N i, fun n hn => hN i n hn⟩, ?_, ?_⟩
  · intro n
    by_cases h : Legal (e n) (D n)
    · have hEq := hmovestep n h
      refine Or.inr ⟨e n, h, ?_, fun j hj => by rw [hEq, Function.update_of_ne hj]⟩
      rw [hEq, Function.update_self]
      exact (hpick (D n) (e n) (hDinv n) h).1
    · exact Or.inl (hfix n h)
  · intro i hleg
    obtain ⟨m, hmM, hem⟩ := hfair i ((insert i (nbr i)).sup N)
    have hagree : ∀ j ∈ nbr i, D m j = D (N j) j := fun j hj =>
      hN j m (le_trans (Finset.le_sup (Finset.mem_insert_of_mem hj)) hmM)
    have hlegm : Legal i (D m) := (hlegal i (D m) (fun j => D (N j) j) hagree).mpr hleg
    have hmi : N i ≤ m := le_trans (Finset.le_sup (Finset.mem_insert_self i (nbr i))) hmM
    have hL : Legal (e m) (D m) := by rw [hem]; exact hlegm
    have hEq := hmovestep m hL
    rw [hem] at hEq
    have h1 : r i (D (m + 1) i) < r i (D m i) := by
      rw [hEq, Function.update_self]
      exact (hpick (D m) i (hDinv m) hlegm).1
    rw [hN i (m + 1) (Nat.le_succ_of_le hmi), hN i m hmi] at h1
    exact lt_irrefl _ h1
  · intro b
    have hagree : ∀ j ∈ dep b, D ((dep b).sup N) j = D (N j) j :=
      fun j hj => hN j _ (Finset.le_sup hj)
    exact (hdep b (D ((dep b).sup N)) (fun j => D (N j) j) hagree).mp (hDinv _ b)

end DifferentialGeometry.Topology.PiecewiseLinear

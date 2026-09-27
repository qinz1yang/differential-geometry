import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Nth

open Set

theorem Set.Finite.exists_strictMono_enumeration_fiber {I : Type*} {label : ℕ → I}
    (hfinite : (range label).Finite) :
    ∃ i : I, ∃ s : ℕ → ℕ, StrictMono s ∧
      (∀ n, label (s n) = i) ∧
      (∀ m, label m = i ↔ ∃ n, s n = m) ∧
      (∀ m, label m = i → s 0 ≤ m) ∧
      ∀ n m, s n < m → m < s (n + 1) → label m ≠ i := by
  let _ : Finite (range label) := hfinite.to_subtype
  obtain ⟨i, hi⟩ :=
    Finite.exists_infinite_fiber (fun n => (⟨label n, mem_range_self n⟩ : range label))
  have hinfinite : (Set.ofPred (fun m => label m = i.val)).Infinite := by
    have he : (fun n => (⟨label n, mem_range_self n⟩ : range label)) ⁻¹' {i} =
        Set.ofPred (fun m => label m = i.val) := by
      ext m
      simp only [mem_preimage, mem_singleton_iff, Subtype.ext_iff, mem_ofPred]
    rw [← he]
    exact Set.infinite_coe_iff.mp hi
  let s := Nat.nth (fun m => label m = i.val)
  have hmono : StrictMono s := Nat.nth_strictMono hinfinite
  have hmem (n : ℕ) : label (s n) = i.val := Nat.nth_mem_of_infinite hinfinite n
  have hcover (m : ℕ) : label m = i.val ↔ ∃ n, s n = m := by
    change m ∈ Set.ofPred (fun m => label m = i.val) ↔ m ∈ range s
    rw [Nat.range_nth_of_infinite hinfinite]
  refine ⟨i.val, s, hmono, hmem, hcover, ?_, ?_⟩
  · intro m hm
    obtain ⟨n, rfl⟩ := (hcover m).mp hm
    exact hmono.monotone (Nat.zero_le n)
  · intro n m hnm hms hm
    exact hnm.not_ge (Nat.le_nth_of_lt_nth_succ hms hm)

theorem Finite.exists_strictMono_enumeration_fiber {I : Type*} [Finite I] (label : ℕ → I) :
    ∃ i : I, ∃ s : ℕ → ℕ, StrictMono s ∧
      (∀ n, label (s n) = i) ∧
      (∀ m, label m = i ↔ ∃ n, s n = m) ∧
      (∀ m, label m = i → s 0 ≤ m) ∧
      ∀ n m, s n < m → m < s (n + 1) → label m ≠ i :=
  (Set.toFinite (range label)).exists_strictMono_enumeration_fiber

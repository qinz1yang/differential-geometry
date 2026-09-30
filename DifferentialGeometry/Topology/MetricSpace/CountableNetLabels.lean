import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Basic.Countable.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Positivity

open Filter

namespace Metric

universe u

variable {X : ℕ → Type u} [∀ n, MetricSpace (X n)]

private noncomputable def paddedEnumeration {Y : Type u} (p : Y) (S : Finset Y)
    (N : ℕ) : Fin (N + 1) → Y := by
  classical
  exact fun a => if h : a.val < S.card then
    (S.equivFin.symm ⟨a.val, h⟩).val else p

private theorem paddedEnumeration_mem_or_eq {Y : Type u} (p : Y) (S : Finset Y)
    (N : ℕ) (a : Fin (N + 1)) :
    paddedEnumeration p S N a ∈ S ∨ paddedEnumeration p S N a = p := by
  classical
  unfold paddedEnumeration
  split_ifs
  · exact Or.inl (Subtype.property _)
  · exact Or.inr rfl

private theorem exists_paddedEnumeration_eq {Y : Type u} (p : Y) (S : Finset Y)
    {N : ℕ} (hcard : S.card ≤ N) {y : Y} (hy : y ∈ S) :
    ∃ a : Fin (N + 1), paddedEnumeration p S N a = y := by
  classical
  let b := S.equivFin ⟨y, hy⟩
  let a : Fin (N + 1) := ⟨b.val, lt_of_lt_of_le b.isLt (Nat.le_succ_of_le hcard)⟩
  refine ⟨a, ?_⟩
  have ha : a.val < S.card := b.isLt
  simp only [paddedEnumeration, dite_eq_left ha]
  exact congrArg Subtype.val (S.equivFin.symm_apply_apply ⟨y, hy⟩)

theorem exists_countable_ball_net_labels_of_eventual_nets (p : ∀ n, X n)
    (hnets : ∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η → ∃ N I : ℕ, ∀ n : ℕ, I ≤ n →
      ∃ S : Finset (X n), S.card ≤ N ∧
        (∀ y ∈ S, dist y (p n) ≤ R) ∧
        ∀ x : X n, dist x (p n) ≤ R → ∃ y ∈ S, dist x y ≤ η) :
    ∃ N : ℕ → ℕ,
      let L := Option (Σ m : ℕ, Fin (N m + 1))
      ∃ (x : ∀ n, L → X n) (C : L → ℝ) (F : ℕ → Finset L),
        (∀ n, x n none = p n) ∧
        (∀ n a, dist (x n a) (x n none) ≤ C a) ∧
        (∀ m, none ∈ F m) ∧
        ∀ m : ℕ, ∀ᶠ n in atTop, ∀ y : X n,
          dist y (x n none) ≤ (m : ℝ) + 1 →
            ∃ a ∈ F m, dist y (x n a) ≤ ((m : ℝ) + 1)⁻¹ := by
  classical
  have hscales : ∀ m : ℕ, ∃ N I : ℕ, ∀ n : ℕ, I ≤ n →
      ∃ S : Finset (X n), S.card ≤ N ∧
        (∀ y ∈ S, dist y (p n) ≤ (m : ℝ) + 1) ∧
        ∀ x : X n, dist x (p n) ≤ (m : ℝ) + 1 →
          ∃ y ∈ S, dist x y ≤ ((m : ℝ) + 1)⁻¹ := by
    intro m
    exact hnets ((m : ℝ) + 1) (by positivity) (((m : ℝ) + 1)⁻¹) (by positivity)
  choose N I hNI using hscales
  have hsets : ∀ m n : ℕ, ∃ S : Finset (X n), S.card ≤ N m ∧
      (∀ y ∈ S, dist y (p n) ≤ (m : ℝ) + 1) ∧
      (I m ≤ n → ∀ x : X n, dist x (p n) ≤ (m : ℝ) + 1 →
        ∃ y ∈ S, dist x y ≤ ((m : ℝ) + 1)⁻¹) := by
    intro m n
    by_cases h : I m ≤ n
    · obtain ⟨S, hcard, hrad, hnet⟩ := hNI m n h
      exact ⟨S, hcard, hrad, fun _ => hnet⟩
    · exact ⟨∅, by simp, by simp, fun h' => (h h').elim⟩
  choose S hS using hsets
  let L := Option (Σ m : ℕ, Fin (N m + 1))
  let x : ∀ n, L → X n := fun n a =>
    match a with
    | none => p n
    | some ⟨m, b⟩ => paddedEnumeration (p n) (S m n) (N m) b
  let C : L → ℝ := fun a =>
    match a with
    | none => 0
    | some ⟨m, _⟩ => (m : ℝ) + 1
  let F : ℕ → Finset L := fun m =>
    insert none (Finset.univ.image (fun b : Fin (N m + 1) => some ⟨m, b⟩))
  refine ⟨N, x, C, F, fun _ => rfl, ?_, ?_, ?_⟩
  · intro n a
    cases a with
    | none => simp [x, C]
    | some a =>
      obtain ⟨m, b⟩ := a
      change dist (paddedEnumeration (p n) (S m n) (N m) b) (p n) ≤ (m : ℝ) + 1
      rcases paddedEnumeration_mem_or_eq (p n) (S m n) (N m) b with hb | hb
      · exact (hS m n).2.1 _ hb
      · rw [hb, dist_self]
        positivity
  · intro m
    exact Finset.mem_insert_self _ _
  · intro m
    refine eventually_atTop.mpr ⟨I m, fun n hn y hy => ?_⟩
    obtain ⟨z, hz, hdist⟩ := (hS m n).2.2 hn y hy
    obtain ⟨b, hb⟩ := exists_paddedEnumeration_eq (p n) (S m n) (hS m n).1 hz
    refine ⟨some ⟨m, b⟩, Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨b, Finset.mem_univ _, rfl⟩), ?_⟩
    change dist y (paddedEnumeration (p n) (S m n) (N m) b) ≤ ((m : ℝ) + 1)⁻¹
    simpa only [hb] using hdist

end Metric

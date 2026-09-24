import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open Set

namespace Metric

variable {X : Type*} [PseudoMetricSpace X] {s : Set X}

theorem totallyBounded_of_finset_card_le
    (h : ∀ eps > 0, ∃ N : ℕ, ∀ A : Finset X,
      (A : Set X) ⊆ s → (A : Set X).Pairwise (fun x y => eps ≤ dist x y) → A.card ≤ N) :
    TotallyBounded s := by
  classical
  rw [totallyBounded_iff]
  intro eps heps
  obtain ⟨N, hN⟩ := h eps heps
  by_contra hcover
  have hchoose (A : Finset X) : ∃ x ∈ s, ∀ y ∈ A, eps ≤ dist x y := by
    have hnot : ¬ s ⊆ ⋃ y ∈ (A : Set X), ball y eps :=
      fun hh => hcover ⟨A, A.finite_toSet, hh⟩
    simp only [subset_def, mem_iUnion, mem_ball, not_forall,
      not_exists, not_lt] at hnot
    obtain ⟨x, hx, hxy⟩ := hnot
    exact ⟨x, hx, fun y hy => hxy y hy⟩
  have hsets : ∀ n : ℕ, ∃ A : Finset X, (A : Set X) ⊆ s ∧ A.card = n ∧
      (A : Set X).Pairwise (fun x y => eps ≤ dist x y) := by
    intro n
    induction n with
    | zero =>
      exact ⟨∅, by simpa only [Finset.coe_empty] using (empty_subset s), rfl,
        by simpa only [Finset.coe_empty] using (pairwise_empty (fun x y : X => eps ≤ dist x y))⟩
    | succ n ih =>
      obtain ⟨A, hAs, hcard, hpair⟩ := ih
      obtain ⟨x, hxs, hx⟩ := hchoose A
      have hxA : x ∉ A := by
        intro hxA
        have hh := hx x hxA
        rw [dist_self] at hh
        exact (not_le.mpr heps) hh
      refine ⟨insert x A, ?_, by simp only [Finset.card_insert_of_notMem hxA, hcard], ?_⟩
      · simpa only [Finset.coe_insert] using insert_subset hxs hAs
      · rw [Finset.coe_insert]
        exact Set.pairwise_insert.mpr ⟨hpair, fun y hy _ => ⟨hx y hy,
          by rw [dist_comm]; exact hx y hy⟩⟩
  obtain ⟨A, hAs, hcard, hpair⟩ := hsets (N + 1)
  have hle := hN A hAs hpair
  rw [hcard] at hle
  exact Nat.not_succ_le_self N hle


theorem totallyBounded_univ_iff_finset_net {α : Type*} [PseudoMetricSpace α] :
    TotallyBounded (univ : Set α) ↔
      ∀ ε > 0, ∃ t : Finset α, ∀ x : α, ∃ y ∈ t, dist x y < ε := by
  constructor
  · intro h ε hε
    obtain ⟨t, ht, hcov⟩ := Metric.totallyBounded_iff.mp h (ε / 2) (half_pos hε)
    refine ⟨ht.toFinset, fun x => ?_⟩
    obtain ⟨y, hy⟩ := mem_iUnion.mp (hcov (mem_univ x))
    obtain ⟨hyt, hxy⟩ := mem_iUnion.mp hy
    exact ⟨y, ht.mem_toFinset.mpr hyt, by
      rw [Metric.mem_ball] at hxy
      linarith⟩
  · intro h
    rw [Metric.totallyBounded_iff]
    intro ε hε
    obtain ⟨t, ht⟩ := h ε hε
    refine ⟨(t : Set α), t.finite_toSet, fun x _ => ?_⟩
    obtain ⟨y, hyt, hxy⟩ := ht x
    exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨by simpa using hyt,
      by rw [Metric.mem_ball]; exact hxy⟩⟩

theorem compactSpace_completion_of_totallyBounded {α : Type*} [PseudoMetricSpace α]
    (h : TotallyBounded (univ : Set α)) :
    CompactSpace (UniformSpace.Completion α) := by
  have htb : TotallyBounded (univ : Set (UniformSpace.Completion α)) := by
    rw [Metric.totallyBounded_iff] at h ⊢
    intro ε hε
    obtain ⟨t, ht, hcov⟩ := h (ε / 2) (half_pos hε)
    refine ⟨(fun x : α => (x : UniformSpace.Completion α)) '' t, ht.image _, ?_⟩
    intro z _
    obtain ⟨x, hx⟩ :=
      (UniformSpace.Completion.denseRange_coe (α := α)).exists_dist_lt z (half_pos hε)
    obtain ⟨y, hy⟩ := mem_iUnion.mp (hcov (mem_univ x))
    obtain ⟨hyt, hxy⟩ := mem_iUnion.mp hy
    refine mem_iUnion.mpr ⟨(y : UniformSpace.Completion α), mem_iUnion.mpr
      ⟨⟨y, hyt, rfl⟩, ?_⟩⟩
    rw [Metric.mem_ball] at hxy ⊢
    have htri := dist_triangle z (x : UniformSpace.Completion α)
      (y : UniformSpace.Completion α)
    rw [UniformSpace.Completion.dist_eq] at htri
    linarith
  exact isCompact_univ_iff.mp
    (isCompact_iff_totallyBounded_isComplete.mpr ⟨htb, isComplete_univ⟩)

end Metric

/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.NeighborhoodCycle

open Set Fin.NatCast

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem val_sub_natCast_of_le {m j k : ℕ} (hjk : j ≤ k) (hk : k ≤ m) (a : Fin (m + 1)) :
    ((a + (k : Fin (m + 1))) - (a + (j : Fin (m + 1)))).val = k - j := by
  rw [add_sub_add_left_eq_sub, Fin.val_sub, Fin.val_natCast, Fin.val_natCast,
    Nat.mod_eq_of_lt (by omega : j < m + 1), Nat.mod_eq_of_lt (by omega : k < m + 1),
    show m + 1 - j + k = k - j + (m + 1) by omega, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

theorem val_sub_natCast_of_lt {m j k : ℕ} (hjk : j < k) (hk : k ≤ m) (a : Fin (m + 1)) :
    ((a + (j : Fin (m + 1))) - (a + (k : Fin (m + 1)))).val = m + 1 - (k - j) := by
  rw [← neg_sub, Fin.val_neg', val_sub_natCast_of_le hjk.le hk]
  exact Nat.mod_eq_of_lt (by omega)

theorem exists_faceChain_of_isCombinatorialManifold_one (L : Geometry.SimplicialComplex ℝ E)
    [Finite L.faces] (hL : IsCombinatorialManifold 1 L) (hconn : IsConnected L.space)
    {s₀ : Finset E} (hs₀ : s₀ ∈ L.faces) :
    ∃ (m : ℕ) (s : ℕ → Finset E), 2 ≤ m ∧ s 0 = s₀ ∧ (∀ k, s k ∈ L.faces) ∧
      (∀ k < m, s k ≠ s (k + 1) ∧ (s k ⊆ s (k + 1) ∨ s (k + 1) ⊆ s k)) ∧
      (s m ≠ s 0 ∧ (s m ⊆ s 0 ∨ s 0 ⊆ s m)) ∧ (∀ j k, j < k → k ≤ m → s j ≠ s k) ∧
      (∀ j k, j + 1 < k → k ≤ m → (j ≠ 0 ∨ k ≠ m) → ¬(s j ⊆ s k ∨ s k ⊆ s j)) ∧
      ∀ t ∈ L.faces, ∃ k ≤ m, s k = t := by
  obtain ⟨n, hn, e, hadj⟩ := exists_cyclic_face_order L hL hconn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set a : Fin (m + 1) := e.symm ⟨s₀, hs₀⟩ with ha
  have hadj' : ∀ u v : Fin (m + 1), ((u - v).val = 1 ∨ (v - u).val = 1) →
      e u ≠ e v ∧ ((e u).val ⊆ (e v).val ∨ (e v).val ⊆ (e u).val) :=
    fun u v h => (hadj u v).mp (SimpleGraph.cycleGraph_adj'.mpr h)
  have hne : ∀ j k, j < k → k ≤ m →
      (e (a + (j : Fin (m + 1)))).val ≠ (e (a + (k : Fin (m + 1)))).val := by
    intro j k hjk hk h
    have h' := e.injective (Subtype.ext h)
    have hv := val_sub_natCast_of_le hjk.le hk a
    rw [h', sub_self, Fin.val_zero] at hv
    omega
  refine ⟨m, fun k => (e (a + (k : Fin (m + 1)))).val, by omega, ?_, fun k => (e _).2, ?_, ?_,
    fun j k hjk hk => hne j k hjk hk, ?_, ?_⟩
  · change (e (a + ((0 : ℕ) : Fin (m + 1)))).val = s₀
    rw [Nat.cast_zero, add_zero, ha, e.apply_symm_apply]
  · intro k hk
    obtain ⟨h1, h2⟩ := hadj' (a + ((k + 1 : ℕ) : Fin (m + 1))) (a + (k : Fin (m + 1)))
      (Or.inl (by rw [val_sub_natCast_of_le (Nat.le_succ k) hk]; omega))
    exact ⟨fun h => h1 (Subtype.ext h.symm), h2.symm⟩
  · obtain ⟨h1, h2⟩ := hadj' (a + ((0 : ℕ) : Fin (m + 1))) (a + (m : Fin (m + 1)))
      (Or.inl (by rw [val_sub_natCast_of_lt (by omega) le_rfl]; omega))
    exact ⟨fun h => h1 (Subtype.ext h.symm), h2.symm⟩
  · intro j k hjk hk hjm hcomp
    have hd := (hadj (a + (j : Fin (m + 1))) (a + (k : Fin (m + 1)))).mpr
      ⟨fun h => hne j k (by omega) hk (congrArg Subtype.val h), hcomp⟩
    rw [SimpleGraph.cycleGraph_adj', val_sub_natCast_of_lt (by omega) hk,
      val_sub_natCast_of_le (by omega) hk] at hd
    omega
  · intro t ht
    refine ⟨(e.symm ⟨t, ht⟩ - a).val, by omega, ?_⟩
    change (e (a + (((e.symm ⟨t, ht⟩ - a).val : ℕ) : Fin (m + 1)))).val = t
    rw [Fin.cast_val_eq_self, add_sub_cancel, e.apply_symm_apply]

end DifferentialGeometry.Topology.PiecewiseLinear

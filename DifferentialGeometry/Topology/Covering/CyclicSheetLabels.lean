/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Covering.CyclicSections

open Set

namespace DifferentialGeometry.Topology.Covering

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem exists_cyclic_two_section_labels
    {p : X → Y} (hnosec : ¬∃ σ : C(Y, X), Function.RightInverse σ p)
    {m : ℕ} (C : ℕ → Set Y) (s : ℕ → Bool → Y → X)
    (hclosed : ∀ k ≤ m, IsClosed (C k)) (hcover : ⋃ k ≤ m, C k = univ)
    (hcont : ∀ k ≤ m, ∀ b, ContinuousOn (s k b) (C k))
    (hsec : ∀ k ≤ m, ∀ b y, y ∈ C k → p (s k b y) = y)
    (hne : ∀ k ≤ m, ∀ y ∈ C k, s k false y ≠ s k true y)
    (hfib : ∀ k ≤ m, ∀ y ∈ C k, ∀ x, p x = y → x = s k false y ∨ x = s k true y)
    (q : ℕ → Y) (hq : ∀ k < m, q k ∈ C k ∩ C (k + 1))
    (hadj : ∀ k < m, C k ∩ C (k + 1) ⊆ {q k})
    (hfar : ∀ j k, j + 1 < k → k ≤ m → (j ≠ 0 ∨ k ≠ m) → Disjoint (C j) (C k))
    {z : Y} (hz : z ∈ C 0 ∩ C m) (hseam : C 0 ∩ C m ⊆ {z}) (b₀ : Bool) :
    ∃ b : ℕ → Bool, b 0 = b₀ ∧
      (∀ k < m, ∀ a : Bool,
        EqOn (s k (Bool.xor a (b k))) (s (k + 1) (Bool.xor a (b (k + 1))))
          (C k ∩ C (k + 1))) ∧
      ∀ a : Bool, s m (Bool.xor a (b m)) z = s 0 (Bool.xor (!a) (b 0)) z := by
  classical
  let b : ℕ → Bool := Nat.rec b₀ (fun k prev =>
    if s k prev (q k) = s (k + 1) false (q k) then false else true)
  have hb0 : b 0 = b₀ := rfl
  have hbnext : ∀ k < m, s k (b k) (q k) = s (k + 1) (b (k + 1)) (q k) := by
    intro k hk
    have hkp : k + 1 ≤ m := hk
    have hchoice := hfib (k + 1) hkp (q k) (hq k hk).2 (s k (b k) (q k))
      (hsec k hk.le (b k) (q k) (hq k hk).1)
    change s k (b k) (q k) = s (k + 1)
      (if s k (b k) (q k) = s (k + 1) false (q k) then false else true) (q k)
    split_ifs with h
    · exact h
    · exact hchoice.resolve_left h
  have hnot : ∀ k ≤ m, ∀ y ∈ C k, ∀ b : Bool, s k (!b) y ≠ s k b y := by
    intro k hk y hy b
    cases b
    · exact (hne k hk y hy).symm
    · exact hne k hk y hy
  have hother : ∀ j k, j ≤ m → k ≤ m → ∀ y ∈ C j ∩ C k, ∀ a b : Bool,
      s j a y = s k b y → s j (!a) y = s k (!b) y := by
    intro j k hj hk y hy a b heq
    have hf := hfib k hk y hy.2 (s j (!a) y) (hsec j hj (!a) y hy.1)
    cases b
    · rcases hf with h | h
      · exact (hnot j hj y hy.1 a (h.trans heq.symm)).elim
      · exact h
    · rcases hf with h | h
      · exact h
      · exact (hnot j hj y hy.1 a (h.trans heq.symm)).elim
  have hmatch : ∀ k < m, EqOn (s k (b k)) (s (k + 1) (b (k + 1)))
      (C k ∩ C (k + 1)) := by
    intro k hk y hy
    have hyq : y = q k := hadj k hk hy
    rw [hyq]
    exact hbnext k hk
  have hclosedne : s m (b m) z ≠ s 0 (b 0) z :=
    ne_at_seam_of_no_section_of_cyclic_closed_cover hnosec C (fun k => s k (b k))
      hclosed hcover (fun k hk => hcont k hk (b k))
      (fun k hk y hy => hsec k hk (b k) y hy) hmatch hfar hseam
  have hclose : s m (b m) z = s 0 (!(b 0)) z := by
    have hf := hfib 0 (Nat.zero_le m) z hz.1 (s m (b m) z)
      (hsec m le_rfl (b m) z hz.2)
    cases hb : b 0
    · simp only [hb, Bool.not_false] at hclosedne ⊢
      exact hf.resolve_left hclosedne
    · simp only [hb, Bool.not_true] at hclosedne ⊢
      exact hf.resolve_right hclosedne
  refine ⟨b, hb0, ?_, ?_⟩
  · intro k hk a y hy
    cases a
    · simpa only [Bool.false_xor] using hmatch k hk hy
    · simpa only [Bool.true_xor] using
        hother k (k + 1) hk.le hk y hy (b k) (b (k + 1)) (hmatch k hk hy)
  · intro a
    cases a
    · simpa only [Bool.false_xor, Bool.not_false, Bool.true_xor] using hclose
    · have h := hother m 0 le_rfl (Nat.zero_le m) z ⟨hz.2, hz.1⟩
        (b m) (!(b 0)) hclose
      simpa only [Bool.true_xor, Bool.not_true, Bool.false_xor, Bool.not_not] using h

end DifferentialGeometry.Topology.Covering

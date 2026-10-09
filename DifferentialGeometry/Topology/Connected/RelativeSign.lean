/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.IntermediateValue

open Set Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {O : Set X} {u v : X → ℝ}

theorem forall_pos_or_forall_neg_of_isPreconnected {S : Set X} {f : X → ℝ}
    (hS : IsPreconnected S) (hf : ContinuousOn f S) (hne : ∀ w ∈ S, f w ≠ 0) :
    (∀ w ∈ S, 0 < f w) ∨ ∀ w ∈ S, f w < 0 := by
  by_cases hall : ∀ w ∈ S, 0 < f w
  · exact Or.inl hall
  · refine Or.inr fun b hbS => ?_
    obtain ⟨a, haS, hfa⟩ : ∃ a ∈ S, f a ≤ 0 := by
      by_contra hcon
      exact hall fun w hw => not_le.mp fun h => hcon ⟨w, hw, h⟩
    by_contra hfb
    obtain ⟨z, hzS, hz⟩ := hS.intermediate_value haS hbS hf ⟨hfa, not_lt.mp hfb⟩
    exact hne z hzS hz

omit [TopologicalSpace X] in
theorem exists_sign_of_forall_mul_nonneg_or_forall_mul_nonpos
    (h : (∀ z ∈ O, 0 ≤ u z * v z) ∨ ∀ z ∈ O, u z * v z ≤ 0) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ z ∈ O, 0 ≤ σ * u z * v z := by
  rcases h with h | h
  · exact ⟨1, Or.inl rfl, fun z hz => by simpa using h z hz⟩
  · exact ⟨-1, Or.inr rfl, fun z hz => by simpa using h z hz⟩

theorem exists_sign_mul_nonneg_of_mul_ne_zero (hO : IsPreconnected O) (hu : ContinuousOn u O)
    (hv : ContinuousOn v O) (hne : ∀ z ∈ O, u z * v z ≠ 0) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ z ∈ O, 0 ≤ σ * u z * v z := by
  refine exists_sign_of_forall_mul_nonneg_or_forall_mul_nonpos ?_
  rcases forall_pos_or_forall_neg_of_isPreconnected hO (hu.mul hv) hne with h | h
  · exact Or.inl fun z hz => (h z hz).le
  · exact Or.inr fun z hz => (h z hz).le

theorem exists_isOpen_forall_mul_nonneg_or_nonpos_of_mul_ne_zero {z : X}
    (hu : ContinuousOn u O) (hv : ContinuousOn v O) (hz : z ∈ O) (hne : u z * v z ≠ 0) :
    ∃ W : Set X, IsOpen W ∧ z ∈ W ∧
      ((∀ w ∈ W ∩ O, 0 ≤ u w * v w) ∨ ∀ w ∈ W ∩ O, u w * v w ≤ 0) := by
  have hprod : ContinuousOn (fun w => u w * v w) O := hu.mul hv
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmem : (fun w => u w * v w) ⁻¹' Iio 0 ∈ 𝓝[O] z :=
      (hprod z hz).preimage_mem_nhdsWithin (Iio_mem_nhds hlt)
    obtain ⟨W, hW, hzW, hsub⟩ := mem_nhdsWithin.mp hmem
    exact ⟨W, hW, hzW, Or.inr fun w hw => le_of_lt (hsub hw)⟩
  · have hmem : (fun w => u w * v w) ⁻¹' Ioi 0 ∈ 𝓝[O] z :=
      (hprod z hz).preimage_mem_nhdsWithin (Ioi_mem_nhds hgt)
    obtain ⟨W, hW, hzW, hsub⟩ := mem_nhdsWithin.mp hmem
    exact ⟨W, hW, hzW, Or.inl fun w hw => le_of_lt (hsub hw)⟩

theorem forall_mul_nonneg_or_nonpos_of_isPreconnected_sides {N : Set X}
    (hv : ContinuousOn v O) (hzero : ∀ z ∈ O, u z = 0 ↔ v z = 0)
    (hpos : IsPreconnected {w ∈ N ∩ O | 0 < u w})
    (hneg : IsPreconnected {w ∈ N ∩ O | u w < 0})
    (hvpos : ∃ w ∈ N ∩ O, 0 < v w) (hvneg : ∃ w ∈ N ∩ O, v w < 0) :
    (∀ w ∈ N ∩ O, 0 ≤ u w * v w) ∨ ∀ w ∈ N ∩ O, u w * v w ≤ 0 := by
  have hsubP : {w ∈ N ∩ O | 0 < u w} ⊆ O := fun _ hw => hw.1.2
  have hsubN : {w ∈ N ∩ O | u w < 0} ⊆ O := fun _ hw => hw.1.2
  have hneP : ∀ w ∈ {w ∈ N ∩ O | 0 < u w}, v w ≠ 0 := fun w hw h0 =>
    (ne_of_gt hw.2) ((hzero w hw.1.2).mpr h0)
  have hneN : ∀ w ∈ {w ∈ N ∩ O | u w < 0}, v w ≠ 0 := fun w hw h0 =>
    (ne_of_lt hw.2) ((hzero w hw.1.2).mpr h0)
  have hsplit : ∀ w ∈ N ∩ O, v w ≠ 0 → u w < 0 ∨ 0 < u w := fun w hw hvw =>
    lt_or_gt_of_ne (fun h0 => hvw ((hzero w hw.2).mp h0))
  have hvne : ∀ w ∈ N ∩ O, u w ≠ 0 → v w ≠ 0 := fun w hw h0 h1 =>
    h0 ((hzero w hw.2).mpr h1)
  rcases forall_pos_or_forall_neg_of_isPreconnected hpos (hv.mono hsubP) hneP with hP | hP
  · rcases forall_pos_or_forall_neg_of_isPreconnected hneg (hv.mono hsubN) hneN with hN | hN
    · exfalso
      obtain ⟨w, hw, hwv⟩ := hvneg
      rcases hsplit w hw (ne_of_lt hwv) with h | h
      · exact absurd (hN w ⟨hw, h⟩) (not_lt.mpr (le_of_lt hwv))
      · exact absurd (hP w ⟨hw, h⟩) (not_lt.mpr (le_of_lt hwv))
    · refine Or.inl fun w hw => ?_
      by_cases h0 : u w = 0
      · simp [h0]
      · rcases hsplit w hw (hvne w hw h0) with h | h
        · exact le_of_lt (mul_pos_of_neg_of_neg h (hN w ⟨hw, h⟩))
        · exact le_of_lt (mul_pos h (hP w ⟨hw, h⟩))
  · rcases forall_pos_or_forall_neg_of_isPreconnected hneg (hv.mono hsubN) hneN with hN | hN
    · refine Or.inr fun w hw => ?_
      by_cases h0 : u w = 0
      · simp [h0]
      · rcases hsplit w hw (hvne w hw h0) with h | h
        · exact le_of_lt (mul_neg_of_neg_of_pos h (hN w ⟨hw, h⟩))
        · exact le_of_lt (mul_neg_of_pos_of_neg h (hP w ⟨hw, h⟩))
    · exfalso
      obtain ⟨w, hw, hwv⟩ := hvpos
      rcases hsplit w hw (ne_of_gt hwv) with h | h
      · exact absurd (hN w ⟨hw, h⟩) (not_lt.mpr (le_of_lt hwv))
      · exact absurd (hP w ⟨hw, h⟩) (not_lt.mpr (le_of_lt hwv))

theorem forall_mul_nonneg_or_nonpos_of_locally_constant (hO : IsPreconnected O)
    (hdense : ∀ z ∈ O, ∀ W : Set X, IsOpen W → z ∈ W → ∃ w ∈ W ∩ O, u w * v w ≠ 0)
    (hloc : ∀ z ∈ O, ∃ W : Set X, IsOpen W ∧ z ∈ W ∧
      ((∀ w ∈ W ∩ O, 0 ≤ u w * v w) ∨ ∀ w ∈ W ∩ O, u w * v w ≤ 0)) :
    (∀ z ∈ O, 0 ≤ u z * v z) ∨ ∀ z ∈ O, u z * v z ≤ 0 := by
  obtain ⟨P, hP⟩ : ∃ P : Set X, ∀ x : X,
      x ∈ P ↔ ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ ∀ w ∈ W ∩ O, 0 ≤ u w * v w :=
    ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Set X, ∀ x : X,
      x ∈ Q ↔ ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ ∀ w ∈ W ∩ O, u w * v w ≤ 0 :=
    ⟨_, fun _ => Iff.rfl⟩
  have hPopen : IsOpen P := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨W, hW, hxW, hWle⟩ := (hP x).mp hx
    exact ⟨W, fun y hy => (hP y).mpr ⟨W, hW, hy, hWle⟩, hW, hxW⟩
  have hQopen : IsOpen Q := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨W, hW, hxW, hWle⟩ := (hQ x).mp hx
    exact ⟨W, fun y hy => (hQ y).mpr ⟨W, hW, hy, hWle⟩, hW, hxW⟩
  have hcover : O ⊆ P ∪ Q := by
    intro z hz
    obtain ⟨W, hW, hzW, h⟩ := hloc z hz
    rcases h with h | h
    · exact Or.inl ((hP z).mpr ⟨W, hW, hzW, h⟩)
    · exact Or.inr ((hQ z).mpr ⟨W, hW, hzW, h⟩)
  have hdisj : ¬(O ∩ (P ∩ Q)).Nonempty := by
    rintro ⟨z, hzO, hzP, hzQ⟩
    obtain ⟨W₁, hW₁, hz₁, h₁⟩ := (hP z).mp hzP
    obtain ⟨W₂, hW₂, hz₂, h₂⟩ := (hQ z).mp hzQ
    obtain ⟨w, hw, hwne⟩ := hdense z hzO (W₁ ∩ W₂) (hW₁.inter hW₂) ⟨hz₁, hz₂⟩
    exact hwne (le_antisymm (h₂ w ⟨hw.1.2, hw.2⟩) (h₁ w ⟨hw.1.1, hw.2⟩))
  by_cases hQne : (O ∩ Q).Nonempty
  · have hPne : ¬(O ∩ P).Nonempty := fun h => hdisj (hO P Q hPopen hQopen hcover h hQne)
    refine Or.inr fun z hz => ?_
    rcases hcover hz with h | h
    · exact absurd ⟨z, hz, h⟩ hPne
    · obtain ⟨W, _, hzW, hWle⟩ := (hQ z).mp h
      exact hWle z ⟨hzW, hz⟩
  · refine Or.inl fun z hz => ?_
    rcases hcover hz with h | h
    · obtain ⟨W, _, hzW, hWle⟩ := (hP z).mp h
      exact hWle z ⟨hzW, hz⟩
    · exact absurd ⟨z, hz, h⟩ hQne

theorem exists_sign_mul_nonneg (hO : IsPreconnected O) (hu : ContinuousOn u O)
    (hv : ContinuousOn v O) (hzero : ∀ z ∈ O, u z = 0 ↔ v z = 0)
    (hnd : ∀ z ∈ O, v z = 0 → ∀ N ∈ 𝓝[O] z, (∃ w ∈ N, 0 < v w) ∧ ∃ w ∈ N, v w < 0)
    (hside : ∀ z ∈ O, u z = 0 → ∃ N ∈ 𝓝[O] z,
      IsPreconnected {w ∈ N ∩ O | 0 < u w} ∧ IsPreconnected {w ∈ N ∩ O | u w < 0}) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ z ∈ O, 0 ≤ σ * u z * v z := by
  refine exists_sign_of_forall_mul_nonneg_or_forall_mul_nonpos ?_
  have hdense : ∀ z ∈ O, ∀ W : Set X, IsOpen W → z ∈ W → ∃ w ∈ W ∩ O, u w * v w ≠ 0 := by
    intro z hz W hW hzW
    by_cases h0 : u z * v z = 0
    · have hvz : v z = 0 := by
        rcases mul_eq_zero.mp h0 with h | h
        · exact (hzero z hz).mp h
        · exact h
      have hmem : W ∩ O ∈ 𝓝[O] z :=
        Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (hW.mem_nhds hzW)) self_mem_nhdsWithin
      obtain ⟨⟨w, hw, hwv⟩, -⟩ := hnd z hz hvz (W ∩ O) hmem
      refine ⟨w, hw, mul_ne_zero ?_ (ne_of_gt hwv)⟩
      exact fun h => (ne_of_gt hwv) ((hzero w hw.2).mp h)
    · exact ⟨z, ⟨hzW, hz⟩, h0⟩
  refine forall_mul_nonneg_or_nonpos_of_locally_constant hO hdense ?_
  intro z hz
  by_cases h0 : u z * v z = 0
  · have huz : u z = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · exact (hzero z hz).mpr h
    obtain ⟨N, hN, hpos, hneg⟩ := hside z hz huz
    have hmem : N ∩ O ∈ 𝓝[O] z := Filter.inter_mem hN self_mem_nhdsWithin
    obtain ⟨hvpos, hvneg⟩ := hnd z hz ((hzero z hz).mp huz) (N ∩ O) hmem
    have hmain := forall_mul_nonneg_or_nonpos_of_isPreconnected_sides hv hzero hpos hneg
      hvpos hvneg
    obtain ⟨W, hW, hzW, hsub⟩ := mem_nhdsWithin.mp hmem
    refine ⟨W, hW, hzW, ?_⟩
    rcases hmain with h | h
    · exact Or.inl fun w hw => h w (hsub hw)
    · exact Or.inr fun w hw => h w (hsub hw)
  · exact exists_isOpen_forall_mul_nonneg_or_nonpos_of_mul_ne_zero hu hv hz h0

theorem nonneg_iff_of_mul_nonneg {a b : ℝ} (hab : 0 ≤ a * b) (h0 : a = 0 ↔ b = 0) :
    0 ≤ b ↔ 0 ≤ a := by
  constructor
  · intro hb
    rcases eq_or_lt_of_le hb with h | h
    · exact le_of_eq (h0.mpr h.symm).symm
    · by_contra hc
      exact absurd hab (not_le.mpr (mul_neg_of_neg_of_pos (not_le.mp hc) h))
  · intro ha
    rcases eq_or_lt_of_le ha with h | h
    · exact le_of_eq (h0.mp h.symm).symm
    · by_contra hc
      exact absurd hab (not_le.mpr (mul_neg_of_pos_of_neg h (not_le.mp hc)))

theorem exists_sign_nonneg_iff (hO : IsPreconnected O) (hu : ContinuousOn u O)
    (hv : ContinuousOn v O) (hzero : ∀ z ∈ O, u z = 0 ↔ v z = 0)
    (hnd : ∀ z ∈ O, v z = 0 → ∀ N ∈ 𝓝[O] z, (∃ w ∈ N, 0 < v w) ∧ ∃ w ∈ N, v w < 0)
    (hside : ∀ z ∈ O, u z = 0 → ∃ N ∈ 𝓝[O] z,
      IsPreconnected {w ∈ N ∩ O | 0 < u w} ∧ IsPreconnected {w ∈ N ∩ O | u w < 0}) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ z ∈ O, (0 ≤ v z ↔ 0 ≤ σ * u z) := by
  obtain ⟨σ, hσ, h⟩ := exists_sign_mul_nonneg hO hu hv hzero hnd hside
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  refine ⟨σ, hσ, fun z hz => nonneg_iff_of_mul_nonneg (h z hz) ?_⟩
  rw [mul_eq_zero]
  constructor
  · rintro (h1 | h1)
    · exact absurd h1 hσ0
    · exact (hzero z hz).mp h1
  · exact fun h1 => Or.inr ((hzero z hz).mpr h1)

end DifferentialGeometry.Topology

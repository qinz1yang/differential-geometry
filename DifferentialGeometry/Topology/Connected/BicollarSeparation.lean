/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Connected.LocalSeparation
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue

open Set Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {N S W : Set X} {ρ : X × ℝ → X}

theorem exists_connected_pair_sdiff_of_bicollar (hS : IsConnected S)
    (hρ : ContinuousOn ρ (S ×ˢ Icc (-1 : ℝ) 1))
    (hbij : BijOn ρ (S ×ˢ Icc (-1 : ℝ) 1) W) (hzero : ∀ x ∈ S, ρ (x, 0) = x) :
    ∃ A B : Set X, IsConnected A ∧ IsConnected B ∧ Disjoint A B ∧
      A ∪ B = W \ S ∧ S ⊆ closure A ∧ S ⊆ closure B := by
  let A := ρ '' (S ×ˢ Ico (-1 : ℝ) 0)
  let B := ρ '' (S ×ˢ Ioc (0 : ℝ) 1)
  have hneg : S ×ˢ Ico (-1 : ℝ) 0 ⊆ S ×ˢ Icc (-1 : ℝ) 1 :=
    fun _ hx => ⟨hx.1, hx.2.1, hx.2.2.le.trans zero_le_one⟩
  have hpos : S ×ˢ Ioc (0 : ℝ) 1 ⊆ S ×ˢ Icc (-1 : ℝ) 1 :=
    fun _ hx => ⟨hx.1, (by norm_num : (-1 : ℝ) ≤ 0).trans hx.2.1.le, hx.2.2⟩
  have hA : IsConnected A :=
    (hS.prod (isConnected_Ico (by norm_num : (-1 : ℝ) < 0))).image ρ (hρ.mono hneg)
  have hB : IsConnected B :=
    (hS.prod (isConnected_Ioc (by norm_num : (0 : ℝ) < 1))).image ρ (hρ.mono hpos)
  have hnon (z : X × ℝ) (hz : z ∈ S ×ˢ Icc (-1 : ℝ) 1) (ht : z.2 ≠ 0) : ρ z ∉ S := by
    intro hzS
    have heq := hbij.injOn hz ⟨hzS, by norm_num, by norm_num⟩ (hzero (ρ z) hzS).symm
    exact ht (congrArg Prod.snd heq)
  have hdis : Disjoint A B := by
    apply disjoint_left.mpr
    rintro y ⟨z, hz, hzy⟩ ⟨w, hw, hwy⟩
    have heq := hbij.injOn (hneg hz) (hpos hw) (hzy.trans hwy.symm)
    have ht := congrArg Prod.snd heq
    linarith [hz.2.2, hw.2.1]
  have hcover : A ∪ B = W \ S := by
    apply Subset.antisymm
    · rintro y (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
      · exact ⟨hbij.mapsTo (hneg hz), hnon z (hneg hz) hz.2.2.ne⟩
      · exact ⟨hbij.mapsTo (hpos hz), hnon z (hpos hz) hz.2.1.ne'⟩
    · rintro y ⟨hyW, hyS⟩
      obtain ⟨z, hz, rfl⟩ := hbij.surjOn hyW
      have hz0 : z.2 ≠ 0 := by
        intro ht
        apply hyS
        rw [show z = (z.1, 0) from Prod.ext rfl ht, hzero z.1 hz.1]
        exact hz.1
      rcases lt_or_gt_of_ne hz0 with ht | ht
      · exact Or.inl ⟨z, ⟨hz.1, hz.2.1, ht⟩, rfl⟩
      · exact Or.inr ⟨z, ⟨hz.1, ht, hz.2.2⟩, rfl⟩
  refine ⟨A, B, hA, hB, hdis, hcover, ?_, ?_⟩
  · intro x hx
    have hcl : (x, (0 : ℝ)) ∈ closure (S ×ˢ Ico (-1 : ℝ) 0) := by
      rw [closure_prod_eq, closure_Ico (by norm_num : (-1 : ℝ) ≠ 0)]
      exact ⟨subset_closure hx, by norm_num, le_rfl⟩
    have h := ((hρ (x, 0) ⟨hx, by norm_num, by norm_num⟩).mono hneg).mem_closure_image hcl
    rwa [hzero x hx] at h
  · intro x hx
    have hcl : (x, (0 : ℝ)) ∈ closure (S ×ˢ Ioc (0 : ℝ) 1) := by
      rw [closure_prod_eq, closure_Ioc (by norm_num : (0 : ℝ) ≠ 1)]
      exact ⟨subset_closure hx, le_rfl, zero_le_one⟩
    have h := ((hρ (x, 0) ⟨hx, by norm_num, by norm_num⟩).mono hpos).mem_closure_image hcl
    rwa [hzero x hx] at h

private theorem local_separation_of_bicollar (hS : IsConnected S) (hWN : W ⊆ N)
    (hW : W ∈ 𝓝ˢ[N] S) (hρ : ContinuousOn ρ (S ×ˢ Icc (-1 : ℝ) 1))
    (hbij : BijOn ρ (S ×ˢ Icc (-1 : ℝ) 1) W) (hzero : ∀ x ∈ S, ρ (x, 0) = x) :
    ∀ p ∈ S, ∃ C ∈ 𝓝[N] p, C ⊆ N ∧
      ∃ A B : Set X, IsConnected A ∧ IsConnected B ∧ A ∪ B = C \ S ∧
        C ∩ S ⊆ closure A ∧ C ∩ S ⊆ closure B := by
  obtain ⟨A, B, hA, hB, _, hcover, hSA, hSB⟩ :=
    exists_connected_pair_sdiff_of_bicollar hS hρ hbij hzero
  obtain ⟨O, hO, hSO, hOW⟩ := mem_nhdsSetWithin.mp hW
  exact fun p hp => ⟨W, mem_nhdsWithin.mpr ⟨O, hO, hSO hp, hOW⟩, hWN,
    A, B, hA, hB, hcover, inter_subset_right.trans hSA, inter_subset_right.trans hSB⟩

theorem exists_connectedComponentIn_pair_sdiff_of_bicollar [LocallyConnectedSpace N]
    (hN : IsPreconnected N) (hS : IsConnected S) (hSclosed : IsClosed S) (hWN : W ⊆ N)
    (hW : W ∈ 𝓝ˢ[N] S) (hρ : ContinuousOn ρ (S ×ˢ Icc (-1 : ℝ) 1))
    (hbij : BijOn ρ (S ×ˢ Icc (-1 : ℝ) 1) W) (hzero : ∀ x ∈ S, ρ (x, 0) = x) :
    ∃ a ∈ N \ S, ∃ b ∈ N \ S, ∀ x ∈ N \ S,
      connectedComponentIn (N \ S) x = connectedComponentIn (N \ S) a ∨
      connectedComponentIn (N \ S) x = connectedComponentIn (N \ S) b := by
  have hSN : S ⊆ N := fun x hx =>
    hWN ((hzero x hx) ▸ hbij.mapsTo ⟨hx, by norm_num, by norm_num⟩)
  have hlocal := local_separation_of_bicollar hS hWN hW hρ hbij hzero
  obtain ⟨a, ha, b, hb, hpair⟩ := exists_connectedComponentIn_pair_of_local_separation hSN hS hlocal
  exact ⟨a, ha, b, hb, fun x hx => hpair x
    (inter_closure_connectedComponentIn_sdiff_nonempty hN hSclosed hSN hS.nonempty hx)⟩

theorem exists_connectedComponentIn_pair_sdiff_of_separating_bicollar [LocallyConnectedSpace N]
    (hN : IsPreconnected N) (hNclosed : IsClosed N) (hS : IsConnected S)
    (hSclosed : IsClosed S) (hWN : W ⊆ N) (hW : W ∈ 𝓝ˢ[N] S)
    (hρ : ContinuousOn ρ (S ×ˢ Icc (-1 : ℝ) 1))
    (hbij : BijOn ρ (S ×ˢ Icc (-1 : ℝ) 1) W) (hzero : ∀ x ∈ S, ρ (x, 0) = x)
    (hsep : ¬ IsPreconnected (N \ S)) :
    ∃ a ∈ N \ S, ∃ b ∈ N \ S,
      let A := connectedComponentIn (N \ S) a
      let B := connectedComponentIn (N \ S) b
      Disjoint A B ∧ A ∪ B = N \ S ∧ closure A ∪ closure B = N ∧ closure A ∩ closure B = S := by
  have hSN : S ⊆ N := fun x hx =>
    hWN ((hzero x hx) ▸ hbij.mapsTo ⟨hx, by norm_num, by norm_num⟩)
  exact exists_connectedComponentIn_pair_sdiff_of_local_separation hN hNclosed hS hSclosed hSN
    (local_separation_of_bicollar hS hWN hW hρ hbij hzero) hsep

end DifferentialGeometry.Topology

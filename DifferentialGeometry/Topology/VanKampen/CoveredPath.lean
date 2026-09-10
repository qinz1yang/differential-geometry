/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import DifferentialGeometry.Topology.VanKampen.Subdivision

set_option autoImplicit false

open Metric Set unitInterval
open scoped unitInterval

universe u

namespace Poincare.Topology.VanKampen

namespace Path

def IsCovered {X : Type u} [TopologicalSpace X] {a b : X} (p : _root_.Path a b)
    (U V : Set X) (n : ℕ) : Prop :=
  ∀ i : Fin n, range (standardSubpath p i) ⊆ U ∨ range (standardSubpath p i) ⊆ V

theorem dist_standardTime_le {n : ℕ} (hn : 0 < n) (i : Fin n) (t : I)
    (ht : t ∈ Icc (standardTime n i.castSucc) (standardTime n i.succ)) :
    dist (standardTime n i.castSucc) t ≤ 1 / (n : ℝ) := by
  rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonpos, neg_sub]
  · calc
      (t : ℝ) - standardTime n i.castSucc ≤
          standardTime n i.succ - standardTime n i.castSucc := by
        exact sub_le_sub_right (by exact_mod_cast ht.2) _
      _ = 1 / (n : ℝ) := standardTime_succ_sub_castSucc hn i
  · exact sub_nonpos.mpr (by exact_mod_cast ht.1)

theorem exists_isCovered {X : Type u} [TopologicalSpace X] {a b : X} (p : _root_.Path a b)
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ) :
    ∃ n : ℕ, 0 < n ∧ IsCovered p U V n := by
  let c : Bool → Set I := fun side ↦ p ⁻¹' if side then U else V
  have hc_open : ∀ side, IsOpen (c side) := by
    intro side
    cases side <;> simp [c, hU, hV, p.continuous.isOpen_preimage]
  have hc_cover : (univ : Set I) ⊆ ⋃ side, c side := by
    intro t _
    have ht : p t ∈ U ∪ V := by rw [hcover]; trivial
    rcases ht with htU | htV
    · exact mem_iUnion.mpr ⟨true, by simpa [c] using htU⟩
    · exact mem_iUnion.mpr ⟨false, by simpa [c] using htV⟩
  obtain ⟨δ, hδ, hball⟩ :=
    lebesgue_number_lemma_of_metric (s := (univ : Set I)) isCompact_univ hc_open hc_cover
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (K := ℝ) hδ
  let n := m + 1
  have hn : 0 < n := Nat.succ_pos m
  have hmesh : 1 / (n : ℝ) < δ := by simpa [n] using hm
  refine ⟨n, hn, ?_⟩
  intro i
  obtain ⟨side, hside⟩ := hball (standardTime n i.castSucc) (mem_univ _)
  have hinterval : Icc (standardTime n i.castSucc) (standardTime n i.succ) ⊆ c side := by
    intro t ht
    apply hside
    rw [mem_ball]
    simpa [dist_comm] using (dist_standardTime_le hn i t ht).trans_lt hmesh
  have hrange : range (standardSubpath p i) ⊆ if side then U else V := by
    rw [standardSubpath, _root_.Path.range_subpath_of_le _ _ _
      (standardTime_castSucc_le_succ hn i)]
    rintro _ ⟨t, ht, rfl⟩
    exact hinterval ht
  cases side
  · exact Or.inr hrange
  · exact Or.inl hrange

theorem IsCovered.mul {X : Type u} [TopologicalSpace X] {a b : X} {p : _root_.Path a b}
    {U V : Set X} {n k : ℕ} (h : IsCovered p U V n) (hn : 0 < n) (hk : 0 < k) :
    IsCovered p U V (n * k) := by
  intro j
  let i : Fin n := ⟨j / k, (Nat.div_lt_iff_lt_mul hk).mpr j.isLt⟩
  let r : Fin k := ⟨j % k, Nat.mod_lt j hk⟩
  have hj : refinedIndex i r = j := by
    apply Fin.ext
    simpa [refinedIndex, i, r, Nat.mul_comm] using Nat.div_add_mod j k
  rw [← hj]
  rcases h i with hiU | hiV
  · exact Or.inl ((range_standardSubpath_refined_subset p hn hk i r).trans hiU)
  · exact Or.inr ((range_standardSubpath_refined_subset p hn hk i r).trans hiV)

end Path

end Poincare.Topology.VanKampen

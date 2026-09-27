/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import DifferentialGeometry.Topology.VanKampen.CoveredPath

set_option autoImplicit false

open Metric Set unitInterval
open scoped unitInterval

universe u

namespace DifferentialGeometry.Topology.VanKampen

def IsCoveredGrid {X : Type u} [TopologicalSpace X] (H : C(I × I, X))
    (U V : Set X) (n : ℕ) : Prop :=
  ∀ i j : Fin n,
    H '' (Icc (standardTime n i.castSucc) (standardTime n i.succ) ×ˢ
      Icc (standardTime n j.castSucc) (standardTime n j.succ)) ⊆ U ∨
    H '' (Icc (standardTime n i.castSucc) (standardTime n i.succ) ×ˢ
      Icc (standardTime n j.castSucc) (standardTime n j.succ)) ⊆ V

theorem exists_coveredGrid {X : Type u} [TopologicalSpace X] (H : C(I × I, X))
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ) :
    ∃ n : ℕ, 0 < n ∧ IsCoveredGrid H U V n := by
  let c : Bool → Set (I × I) := fun side ↦ H ⁻¹' if side then U else V
  have hc_open : ∀ side, IsOpen (c side) := by
    intro side
    cases side <;> simp [c, hU, hV, H.continuous.isOpen_preimage]
  have hc_cover : (univ : Set (I × I)) ⊆ ⋃ side, c side := by
    intro z _
    have hz : H z ∈ U ∪ V := by rw [hcover]; trivial
    rcases hz with hzU | hzV
    · exact mem_iUnion.mpr ⟨true, by simpa [c] using hzU⟩
    · exact mem_iUnion.mpr ⟨false, by simpa [c] using hzV⟩
  obtain ⟨δ, hδ, hball⟩ :=
    lebesgue_number_lemma_of_metric (s := (univ : Set (I × I))) isCompact_univ hc_open hc_cover
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (K := ℝ) hδ
  let n := m + 1
  have hn : 0 < n := Nat.succ_pos m
  have hmesh : 1 / (n : ℝ) < δ := by simpa [n] using hm
  refine ⟨n, hn, ?_⟩
  intro i j
  let z₀ : I × I := (standardTime n i.castSucc, standardTime n j.castSucc)
  obtain ⟨side, hside⟩ := hball z₀ (mem_univ _)
  let cell := Icc (standardTime n i.castSucc) (standardTime n i.succ) ×ˢ
    Icc (standardTime n j.castSucc) (standardTime n j.succ)
  have hcell : cell ⊆ c side := by
    intro z hz
    apply hside
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    constructor
    · simpa [z₀, dist_comm] using
        (Path.dist_standardTime_le hn i z.1 hz.1).trans_lt hmesh
    · simpa [z₀, dist_comm] using
        (Path.dist_standardTime_le hn j z.2 hz.2).trans_lt hmesh
  have himage : H '' cell ⊆ if side then U else V := by
    rintro _ ⟨z, hz, rfl⟩
    exact hcell hz
  cases side
  · exact Or.inr himage
  · exact Or.inl himage

end DifferentialGeometry.Topology.VanKampen

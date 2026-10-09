/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLDiskArcGluing

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_isPLHomeomorphOn_union_biUnion_of_inter_eq_arc {Δ : Set F}
    {q : (Fin 3 → ℝ) → F} (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ) {ι : Type*}
    {Z α : ι → Set F} {r : ι → (Fin 3 → ℝ) → F} {γ : ι → ℝ → F}
    (hr : ∀ i, IsPLHomeomorphOn (r i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (Z i))
    (hγ : ∀ i, IsPLHomeomorphOn (γ i) (Icc 0 1) (α i)) (s : Finset ι)
    (hΔZ : ∀ i ∈ s, Δ ∩ Z i = α i) (hαΔ : ∀ i ∈ s, α i ⊆ q '' stdSimplexBoundary 2)
    (hαZ : ∀ i ∈ s, α i ⊆ r i '' stdSimplexBoundary 2)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (Z i) (Z j)) :
    ∃ q' : (Fin 3 → ℝ) → F, IsPLHomeomorphOn q' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (Δ ∪ ⋃ i ∈ s, Z i) ∧
      q' '' stdSimplexBoundary 2 = (q '' stdSimplexBoundary 2 ∪
        ⋃ i ∈ s, r i '' stdSimplexBoundary 2) \ ⋃ i ∈ s, (α i \ {γ i 0, γ i 1}) := by
  classical
  have hrZ : ∀ i, r i '' stdSimplexBoundary 2 ⊆ Z i := fun i => by
    rw [← (hr i).image_eq]
    exact image_mono fun x hx => hx.1
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨q, ?_, ?_⟩
    · simpa using hq
    · simp
  | @insert j s hjs ih =>
    obtain ⟨q₁, hq₁, hq₁b⟩ := ih (fun i hi => hΔZ i (Finset.mem_insert_of_mem hi))
      (fun i hi => hαΔ i (Finset.mem_insert_of_mem hi))
      (fun i hi => hαZ i (Finset.mem_insert_of_mem hi))
      (fun i hi k hk hik => hdisj i (Finset.mem_insert_of_mem hi) k (Finset.mem_insert_of_mem hk)
        hik)
    have hjmem : j ∈ insert j s := Finset.mem_insert_self j s
    have hαZi : ∀ i ∈ insert j s, α i ⊆ Z i := fun i hi => by
      rw [← hΔZ i hi]
      exact inter_subset_right
    have hjs' : ∀ i ∈ s, Disjoint (Z j) (Z i) := fun i hi =>
      hdisj j hjmem i (Finset.mem_insert_of_mem hi) fun h => hjs (h ▸ hi)
    have hinter : (Δ ∪ ⋃ i ∈ s, Z i) ∩ Z j = α j := by
      apply Subset.antisymm
      · rintro x ⟨hx | hx, hxj⟩
        · rw [← hΔZ j hjmem]
          exact ⟨hx, hxj⟩
        · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
          exact absurd hxi (Set.disjoint_left.mp (hjs' i hi) hxj)
      · intro x hx
        have hx' : x ∈ Δ ∩ Z j := (hΔZ j hjmem).symm ▸ hx
        exact ⟨Or.inl hx'.1, hx'.2⟩
    have hαq₁ : α j ⊆ q₁ '' stdSimplexBoundary 2 := by
      intro x hx
      rw [hq₁b]
      refine ⟨Or.inl (hαΔ j hjmem hx), fun hxU => ?_⟩
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxU
      exact Set.disjoint_left.mp (hjs' i hi) (hαZi j hjmem hx)
        (hαZi i (Finset.mem_insert_of_mem hi) hxi.1)
    obtain ⟨q₂, hq₂, hq₂b⟩ :=
      exists_isPLHomeomorphOn_union_of_inter_eq_arc hq₁ (hr j) (hγ j) hinter hαq₁ (hαZ j hjmem)
    have hset : Δ ∪ ⋃ i ∈ insert j s, Z i = (Δ ∪ ⋃ i ∈ s, Z i) ∪ Z j := by
      rw [Finset.set_biUnion_insert]
      ext x
      simp only [mem_union]
      tauto
    rw [hset]
    refine ⟨q₂, hq₂, ?_⟩
    rw [hq₂b, hq₁b, Finset.set_biUnion_insert, Finset.set_biUnion_insert]
    have hrj : ∀ i ∈ s, Disjoint (r j '' stdSimplexBoundary 2) (α i) := fun i hi =>
      Disjoint.mono (hrZ j) (hαZi i (Finset.mem_insert_of_mem hi)) (hjs' i hi)
    ext x
    constructor
    · rintro ⟨⟨hx, hxn⟩ | hx, hxj⟩
      · refine ⟨?_, ?_⟩
        · rcases hx with hx | hx
          · exact Or.inl hx
          · exact Or.inr (Or.inr hx)
        · rintro (h | h)
          · exact hxj h
          · exact hxn h
      · refine ⟨Or.inr (Or.inl hx), ?_⟩
        rintro (h | h)
        · exact hxj h
        · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp h
          exact Set.disjoint_left.mp (hrj i hi) hx hxi.1
    · rintro ⟨hx | hx | hx, hxn⟩
      · exact ⟨Or.inl ⟨Or.inl hx, fun h => hxn (Or.inr h)⟩, fun h => hxn (Or.inl h)⟩
      · exact ⟨Or.inr hx, fun h => hxn (Or.inl h)⟩
      · exact ⟨Or.inl ⟨Or.inr hx, fun h => hxn (Or.inr h)⟩, fun h => hxn (Or.inl h)⟩

end DifferentialGeometry.Topology.PiecewiseLinear

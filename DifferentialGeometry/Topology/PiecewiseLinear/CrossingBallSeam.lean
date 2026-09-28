/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BigonBoundaryCrossing
import DifferentialGeometry.Topology.PiecewiseLinear.CurveCrossingGeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem eventually_mem_frontier_iUnion_iff_pair
    {X ι : Type*} [TopologicalSpace X] [Finite ι] {B : ι → Set X}
    (hB : ∀ k, IsClosed (B k)) {i j : ι} {x : X}
    (hx : ∀ k, k ≠ i → k ≠ j → x ∉ B k) :
    ∀ᶠ y in 𝓝 x, y ∈ frontier (⋃ k, B k) ↔ y ∈ frontier (B i ∪ B j) := by
  let O := (⋃ k ∈ {k | k ≠ i ∧ k ≠ j}, B k)ᶜ
  have hO : IsOpen O :=
    ((Set.toFinite _).isClosed_biUnion fun k _ => hB k).isOpen_compl
  have hxO : x ∈ O := by
    intro hbad
    obtain ⟨k, ⟨hki, hkj⟩, hxk⟩ := mem_iUnion₂.mp hbad
    exact hx k hki hkj hxk
  have heq : (⋃ k, B k) ∩ O = (B i ∪ B j) ∩ O := by
    ext y
    constructor
    · rintro ⟨hy, hyO⟩
      obtain ⟨k, hyk⟩ := mem_iUnion.mp hy
      by_cases hki : k = i
      · exact ⟨Or.inl (hki ▸ hyk), hyO⟩
      by_cases hkj : k = j
      · exact ⟨Or.inr (hkj ▸ hyk), hyO⟩
      exact (hyO (mem_iUnion₂.mpr ⟨k, ⟨hki, hkj⟩, hyk⟩)).elim
    · rintro ⟨hy, hyO⟩
      exact ⟨hy.elim (fun h => mem_iUnion.mpr ⟨i, h⟩)
        (fun h => mem_iUnion.mpr ⟨j, h⟩), hyO⟩
  have hfr : frontier (⋃ k, B k) ∩ O = frontier (B i ∪ B j) ∩ O := by
    rw [← frontier_inter_open_inter hO, heq, frontier_inter_open_inter hO]
  filter_upwards [hO.mem_nhds hxO] with y hy
  exact ⟨fun h => (hfr.subset ⟨h, hy⟩).1, fun h => (hfr.symm.subset ⟨h, hy⟩).1⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem HasPLCurveCrossingOnAt.not_subset_of_ball_seam {A B J : Set E}
    (hA : IsClosed A) (hB : IsClosed B) (hS : IsPLSphere 2 (frontier B))
    {q : (Fin 3 → ℝ) → E}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (A ∩ B))
    (hDS : A ∩ B ⊆ frontier B) {x : E}
    (hc : HasPLCurveCrossingOnAt (frontier (A ∪ B)) J (q '' stdSimplexBoundary 2) x) :
    ¬ J ⊆ A := by
  intro hJA
  let Q := closure (frontier B \ (A ∩ B))
  have hQ : IsPLBall 2 Q := hS.isPLBall_closure_sdiff ⟨q, hq⟩ hDS
  obtain ⟨r, hr⟩ := hQ
  have hrJ : r '' stdSimplexBoundary 2 = q '' stdSimplexBoundary 2 := by
    rw [hS.image_stdSimplexBoundary_complement ⟨q, hq⟩ hDS hr, inter_comm]
    exact hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hq hDS
  have hQS : Q ⊆ frontier (A ∪ B) := by
    apply closure_minimal _ isClosed_frontier
    rintro y ⟨hyB, hyD⟩
    have hyA : y ∈ Aᶜ := fun hy => hyD ⟨hy, hB.frontier_subset hyB⟩
    have heq : (A ∪ B) ∩ Aᶜ = B ∩ Aᶜ := by
      ext z
      simp only [mem_inter_iff, mem_union, mem_compl_iff]
      tauto
    have hfr : frontier (A ∪ B) ∩ Aᶜ = frontier B ∩ Aᶜ := by
      rw [← frontier_inter_open_inter hA.isOpen_compl, heq,
        frontier_inter_open_inter hA.isOpen_compl]
    exact (hfr.symm.subset ⟨hyB, hyA⟩).1
  have hQA : Disjoint (Q \ r '' stdSimplexBoundary 2) A := by
    apply Set.disjoint_left.mpr
    rintro y ⟨hyQ, hyJ⟩ hyA
    have hyB : y ∈ B := hB.frontier_subset
      (closure_minimal sdiff_subset isClosed_frontier hyQ)
    apply hyJ
    rw [hrJ, ← hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hq hDS]
    exact ⟨⟨hyA, hyB⟩, hyQ⟩
  have hcl := hc.mem_closure_inter_diskInterior hr hQS
    (Filter.Eventually.of_forall fun y => by rw [hrJ])
  have hempty : J ∩ (Q \ r '' stdSimplexBoundary 2) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro y ⟨hyJ, hyQ⟩
    exact Set.disjoint_left.mp hQA hyQ (hJA hyJ)
  simp only [hempty, closure_empty, mem_empty_iff_false] at hcl

end DifferentialGeometry.Topology.PiecewiseLinear

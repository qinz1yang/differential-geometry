/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ChartImagePLCell
import DifferentialGeometry.Topology.PiecewiseLinear.CircleClosedCover
import DifferentialGeometry.Topology.PiecewiseLinear.CircleFourPoints
import DifferentialGeometry.Topology.PiecewiseLinear.FourArcSphere

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Chain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_isPLHomeomorphOn_Icc_biUnion_of_chain {A : ℕ → Set E} {γ : ℕ → ℝ → E} (n : ℕ)
    (hγ : ∀ i ≤ n, IsPLHomeomorphOn (γ i) (Icc 0 1) (A i))
    (hnext : ∀ i < n, γ (i + 1) 0 = γ i 1)
    (hadj : ∀ i < n, A i ∩ A (i + 1) = {γ i 1})
    (hfar : ∀ i j, j ≤ n → i + 1 < j → Disjoint (A i) (A j)) :
    ∃ l : ℝ → E, IsPLHomeomorphOn l (Icc 0 1) (⋃ i ∈ Finset.range (n + 1), A i) ∧
      l 0 = γ 0 0 ∧ l 1 = γ n 1 := by
  induction n with
  | zero =>
    refine ⟨γ 0, ?_, rfl, rfl⟩
    simpa using hγ 0 le_rfl
  | succ n ih =>
    obtain ⟨l, hl, hl0, hl1⟩ := ih (fun i hi => hγ i (by omega)) (fun i hi => hnext i (by omega))
      (fun i hi => hadj i (by omega)) (fun i j hj hij => hfar i j (by omega) hij)
    have hmeet : (⋃ i ∈ Finset.range (n + 1), A i) ∩ A (n + 1) = {l 1} := by
      rw [hl1, iUnion₂_inter]
      apply Subset.antisymm
      · refine iUnion₂_subset fun i hi => ?_
        have hi' : i < n + 1 := Finset.mem_range.mp hi
        by_cases hin : i = n
        · rw [hin, hadj n (by omega)]
        · rw [(hfar i (n + 1) le_rfl (by omega)).inter_eq]
          exact empty_subset _
      · rw [singleton_subset_iff]
        exact mem_iUnion₂.mpr ⟨n, Finset.mem_range.mpr (by omega),
          (hadj n (by omega)).symm.subset (mem_singleton _)⟩
    obtain ⟨l', hl', hl'0, -, hl'1⟩ := exists_isPLHomeomorphOn_Icc_concat hl (hγ (n + 1) le_rfl)
      (by rw [hnext n (by omega), hl1]) hmeet
    refine ⟨l', ?_, hl'0.trans hl0, hl'1⟩
    rw [Finset.range_add_one, Finset.set_biUnion_insert, union_comm]
    exact hl'

theorem isPLSphere_one_biUnion_of_cycle {A : ℕ → Set E} {γ : ℕ → ℝ → E} (n : ℕ)
    (hγ : ∀ i ≤ n + 2, IsPLHomeomorphOn (γ i) (Icc 0 1) (A i))
    (hnext : ∀ i < n + 2, γ (i + 1) 0 = γ i 1)
    (hclose : γ (n + 2) 1 = γ 0 0)
    (hadj : ∀ i < n + 2, A i ∩ A (i + 1) = {γ i 1})
    (hlast : A 0 ∩ A (n + 2) = {γ 0 0})
    (hfar : ∀ i j, j ≤ n + 2 → i + 1 < j → (i, j) ≠ (0, n + 2) → Disjoint (A i) (A j)) :
    IsPLSphere 1 (⋃ i ∈ Finset.range (n + 3), A i) := by
  obtain ⟨l, hl, hl0, hl1⟩ := exists_isPLHomeomorphOn_Icc_biUnion_of_chain (A := A) (γ := γ)
    (n + 1) (fun i hi => hγ i (by omega)) (fun i hi => hnext i (by omega))
    (fun i hi => hadj i (by omega))
    (fun i j hj hij => hfar i j (by omega) hij
      (fun h => by simp only [Prod.mk.injEq] at h; omega))
  have hδ := isPLHomeomorphOn_comp_one_sub (hγ (n + 2) le_rfl)
  have hδ0 : (fun x => γ (n + 2) (1 - x)) 0 = l 0 := by
    simp only [sub_zero]
    rw [hclose, hl0]
  have hδ1 : (fun x => γ (n + 2) (1 - x)) 1 = l 1 := by
    simp only [sub_self]
    rw [hnext (n + 1) (by omega), hl1]
  have hmeet : (⋃ i ∈ Finset.range (n + 2), A i) ∩ A (n + 2) = {l 0, l 1} := by
    rw [hl0, hl1, iUnion₂_inter]
    apply Subset.antisymm
    · refine iUnion₂_subset fun i hi => ?_
      have hi' : i < n + 2 := Finset.mem_range.mp hi
      by_cases hi0 : i = 0
      · rw [hi0, hlast]
        exact singleton_subset_iff.mpr (mem_insert _ _)
      by_cases hin : i = n + 1
      · rw [hin, hadj (n + 1) (by omega)]
        exact singleton_subset_iff.mpr (mem_insert_of_mem _ (mem_singleton _))
      · rw [(hfar i (n + 2) le_rfl (by omega)
          (fun h => by simp only [Prod.mk.injEq] at h; omega)).inter_eq]
        exact empty_subset _
    · rintro x (rfl | rfl)
      · exact mem_iUnion₂.mpr ⟨0, Finset.mem_range.mpr (by omega),
          hlast.symm.subset (mem_singleton _)⟩
      · exact mem_iUnion₂.mpr ⟨n + 1, Finset.mem_range.mpr (by omega),
          (hadj (n + 1) (by omega)).symm.subset (mem_singleton _)⟩
  have hS := isPLSphere_one_union_of_isPLHomeomorphOn_Icc hl hδ hδ0 hδ1 hmeet
  rw [Finset.range_add_one, Finset.set_biUnion_insert, union_comm]
  exact hS

end Chain

section Cell

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem isPLHomeomorphOn_lineMap_Icc_stdSimplex_two :
    IsPLHomeomorphOn (AffineMap.lineMap (k := ℝ) (![1, 0] : Fin 2 → ℝ) ![0, 1]) (Icc 0 1)
      (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) := by
  let L : ℝ →ᵃ[ℝ] (Fin 2 → ℝ) := AffineMap.lineMap ![1, 0] ![0, 1]
  have hL0 : ∀ t : ℝ, L t 0 = 1 - t := by
    intro t
    simp only [L, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Pi.add_apply,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    simp
    ring
  have hL1 : ∀ t : ℝ, L t 1 = t := by
    intro t
    simp only [L, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Pi.add_apply,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    simp
  have hLbij : BijOn L (Icc 0 1) (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) := by
    refine ⟨fun t ht => ⟨fun i => ?_, ?_⟩, fun s _ t _ hst => ?_, fun x hx => ?_⟩
    · fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, hL0]
        linarith [ht.2]
      · simp only [Fin.mk_one, Fin.isValue, hL1]
        exact ht.1
    · rw [Fin.sum_univ_two, hL0, hL1]
      ring
    · have := congrFun hst 1
      rwa [hL1, hL1] at this
    · refine ⟨x 1, ⟨hx.1 1, ?_⟩, ?_⟩
      · have hsum : x 0 + x 1 = 1 := by simpa [Fin.sum_univ_two] using hx.2
        linarith [hx.1 0]
      · funext j
        fin_cases j
        · simp only [Fin.zero_eta, Fin.isValue, hL0]
          have hsum : x 0 + x 1 = 1 := by simpa [Fin.sum_univ_two] using hx.2
          linarith
        · simp only [Fin.mk_one, Fin.isValue, hL1]
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
    ((isPiecewiseAffineOn_of_affine L isOpen_univ).mono_of_isPolyhedron
      isHPolytope_Icc.isPolyhedron (subset_univ _)) hLbij

theorem IsPLCellOn.exists_isPLHomeomorphOn_Icc {S B : Set E3} (h : IsPLCellOn 1 S B) :
    ∃ γ : ℝ → E3, IsPLHomeomorphOn γ (Icc 0 1) S ∧ B = {γ 0, γ 1} := by
  obtain ⟨q, hq, hB⟩ := h.exists_isPLHomeomorphOn_image_chart
    (StructureGroupoid.chart_mem_maximalAtlas (plGroupoid 3) (0 : E3))
    (by rw [chartAt_self_eq]; exact subset_univ S)
  simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, image_id] at hq hB
  subst hB
  refine ⟨q ∘ AffineMap.lineMap (k := ℝ) (![1, 0] : Fin 2 → ℝ) ![0, 1],
    isPLHomeomorphOn_lineMap_Icc_stdSimplex_two.trans hq, ?_⟩
  rw [stdSimplexBoundary_one_eq_pair, image_pair, Function.comp_apply, Function.comp_apply,
    AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one]

end Cell

end DifferentialGeometry.Topology.PiecewiseLinear

/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchTubeEdges

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem isPLSphere_one_tubeCellArc_union {i j : Fin 4} (hij : i ≠ j) :
    IsPLSphere 1 (tubeCellArc i ∪ tubeCellArc j) := by
  refine isPLSphere_one_union_of_isPLHomeomorphOn_Icc (isPLHomeomorphOn_tubeCellArc i)
    (isPLHomeomorphOn_tubeCellArc j) ?_ ?_ ?_
  · rw [tubeMeridianParam_zero, tubeMeridianParam_zero]
  · rw [tubeMeridianParam_one, tubeMeridianParam_one]
  · rw [tubeCellArc_inter hij, tubeMeridianParam_zero, tubeMeridianParam_one]

theorem tubeLeafCoord_add_two_self (k : Fin 4) :
    tubeLeafCoord k (fourSpokeModelLeaf (k + 2)) = -1 := by
  rw [fourSpokeModelLeaf_add_two, ← neg_one_smul ℝ (fourSpokeModelLeaf k), tubeLeafCoord_smul,
    tubeLeafCoord_self]
  norm_num

theorem notMem_tubeSector_of_add_two (k : Fin 4) (h : ℝ) :
    (fourSpokeModelLeaf (k + 2), h) ∉ tubeSector k := fun hp => by
  have h1 : 0 ≤ tubeLeafCoord k (fourSpokeModelLeaf (k + 2)) := hp.2.1
  rw [tubeLeafCoord_add_two_self] at h1
  norm_num at h1

theorem mem_tubeCellSphere_bounds {q : (ℝ × ℝ) × ℝ} (hq : q ∈ tubeCellSphere) :
    q.1 ∈ spliceSquare ∧ 0 ≤ q.2 ∧ q.2 ≤ 1 := by
  rcases mem_tubeCellSphere_iff.mp hq with ⟨hs, h | h⟩ | ⟨hb, h0, h1⟩
  · exact ⟨hs, by linarith, by linarith⟩
  · exact ⟨hs, by linarith, by linarith⟩
  · exact ⟨hb.1, h0, h1⟩

theorem tubeCellSphere_snd_eq_of_lt {q : (ℝ × ℝ) × ℝ} (hq : q ∈ tubeCellSphere)
    (h1 : -1 < q.1.1) (h2 : q.1.1 < 1) (h3 : -1 < q.1.2) (h4 : q.1.2 < 1) :
    q.2 = 0 ∨ q.2 = 1 := by
  rcases mem_tubeCellSphere_iff.mp hq with ⟨-, h⟩ | ⟨hb, -⟩
  · exact h
  · exfalso
    rcases hb.2 with h | h | h | h <;> linarith

theorem exists_tubeSector_param (k : Fin 4) :
    ∃ u : (Fin 3 → ℝ) → (ℝ × ℝ) × ℝ, IsPLHomeomorphOn u (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (tubeSector k) ∧
      u '' stdSimplexBoundary 2 = tubeCellArc k ∪ tubeCellArc (k + 1) := by
  have hO : IsOpen {p : (ℝ × ℝ) × ℝ | 0 < tubeLeafCoord k p.1 ∧ 0 < tubeLeafCoord (k + 1) p.1} :=
    (isOpen_lt continuous_const ((continuous_tubeLeafCoord k).comp continuous_fst)).inter
      (isOpen_lt continuous_const ((continuous_tubeLeafCoord (k + 1)).comp continuous_fst))
  have hc := tubeLeafCoord_leaf_combination k 1 (1 / 2)
  refine exists_param_of_sdiff_eq_inter_isOpen isPLSphere_tubeCellSphere
    (isPLSphere_one_tubeCellArc_union (fin_four_ne_add_one k))
    (union_subset (tubeCellArc_subset_tubeSector k) (tubeCellArc_add_one_subset_tubeSector k))
    (fun p hp => hp.1) (isClosed_tubeSector k) hO (tubeSector_sdiff k) ?_ ?_
  · rw [tubeSector_sdiff]
    refine ⟨((1 : ℝ) • fourSpokeModelLeaf k + (1 / 2 : ℝ) • fourSpokeModelLeaf (k + 1), 0),
      tubeEdge_subset_tubeCellSphere k (h := 0) (by norm_num)
        (mem_tubeEdge_iff.mpr ⟨1, 1 / 2, by norm_num, by norm_num, Or.inl rfl, rfl⟩), ?_, ?_⟩
    · change 0 < tubeLeafCoord k
        ((1 : ℝ) • fourSpokeModelLeaf k + (1 / 2 : ℝ) • fourSpokeModelLeaf (k + 1))
      rw [hc.1]
      norm_num
    · change 0 < tubeLeafCoord (k + 1)
        ((1 : ℝ) • fourSpokeModelLeaf k + (1 / 2 : ℝ) • fourSpokeModelLeaf (k + 1))
      rw [hc.2]
      norm_num
  · exact ⟨(fourSpokeModelLeaf (k + 2), 1 / 2),
      mem_tubeCellSphere_iff.mpr (Or.inr ⟨fourSpokeModelLeaf_mem_spliceSquareBoundary _,
        by norm_num, by norm_num⟩), notMem_tubeSector_of_add_two k _⟩

def tubeUpperArc (k : Fin 4) : Set ((ℝ × ℝ) × ℝ) :=
  tubeMeridianParam (fourSpokeModelLeaf k) '' Icc (1 / 4) 1

noncomputable def tubeUpperArcParam (k : Fin 4) (t : ℝ) : (ℝ × ℝ) × ℝ :=
  tubeMeridianParam (fourSpokeModelLeaf k) ((1 - 1 / 4) * t + 1 / 4)

theorem isPLHomeomorphOn_tubeUpperArcParam (k : Fin 4) :
    IsPLHomeomorphOn (tubeUpperArcParam k) (Icc 0 1) (tubeUpperArc k) :=
  isPLHomeomorphOn_comp_mul_add_Icc (isPLHomeomorphOn_tubeCellArc k) (by norm_num) (by norm_num)
    le_rfl

theorem tubeUpperArcParam_zero (k : Fin 4) :
    tubeUpperArcParam k 0 = (fourSpokeModelLeaf k, 0) := by
  rw [tubeUpperArcParam, show (1 - 1 / 4 : ℝ) * 0 + 1 / 4 = 1 / 4 by norm_num,
    tubeMeridianParam_quarter]

theorem tubeUpperArcParam_one (k : Fin 4) :
    tubeUpperArcParam k 1 = ((0 : ℝ × ℝ), (1 : ℝ)) := by
  rw [tubeUpperArcParam, show (1 - 1 / 4 : ℝ) * 1 + 1 / 4 = 1 by norm_num, tubeMeridianParam_one]

theorem tubeUpperArc_subset_tubeCellArc (k : Fin 4) : tubeUpperArc k ⊆ tubeCellArc k :=
  image_mono (Icc_subset_Icc (by norm_num) le_rfl)

def tubeUpperPart : Set ((ℝ × ℝ) × ℝ) :=
  spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1 ∪ spliceSquare ×ˢ ({1} : Set ℝ)

theorem isClosed_tubeUpperPart : IsClosed tubeUpperPart := by
  have hb : IsClosed spliceSquareBoundary := by
    rw [spliceSquareBoundary_eq_frontier]
    exact isClosed_frontier
  exact (hb.prod isClosed_Icc).union (isHPolytope_spliceSquare.1.isClosed.prod isClosed_singleton)

theorem mem_tubeUpperPart_of_pos {p : (ℝ × ℝ) × ℝ} (hp : p ∈ tubeCellSphere) (hz : 0 < p.2) :
    p ∈ tubeUpperPart := by
  rcases mem_tubeCellSphere_iff.mp hp with ⟨hq, hz' | hz'⟩ | ⟨hq, h0, h1⟩
  · exact absurd hz' hz.ne'
  · exact Or.inr ⟨hq, hz'⟩
  · exact Or.inl ⟨hq, h0, h1⟩

theorem mem_tubeUpperArc_of_mem_tubeCellArc {k : Fin 4} {p : (ℝ × ℝ) × ℝ}
    (hp : p ∈ tubeCellArc k) (hu : p ∈ tubeUpperPart) : p ∈ tubeUpperArc k := by
  obtain ⟨t, ht, rfl⟩ := hp
  rcases le_or_gt (1 / 4) t with h | h
  · exact ⟨t, ⟨h, ht.2⟩, rfl⟩
  · exfalso
    rw [tubeMeridianParam, tubeMeridianCoeff_of_le h.le, tubeMeridianHeight_of_le h.le] at hu
    rcases hu with ⟨hb, -⟩ | ⟨-, h1⟩
    · have := (smul_fourSpokeModelLeaf_mem_spliceSquareBoundary_iff k
        (by linarith [ht.1] : (0 : ℝ) ≤ 4 * t)).mp hb
      linarith
    · norm_num at h1

theorem tubeUpperArc_subset_tubeUpperPart (k : Fin 4) : tubeUpperArc k ⊆ tubeUpperPart := by
  rintro _ ⟨t, ⟨h1, h2⟩, rfl⟩
  rcases le_total t (3 / 4) with h | h
  · rw [tubeMeridianParam, tubeMeridianCoeff_of_mem h1 h, tubeMeridianHeight_of_mem h1 h,
      one_smul]
    exact Or.inl ⟨fourSpokeModelLeaf_mem_spliceSquareBoundary k, by linarith, by linarith⟩
  · rw [tubeMeridianParam, tubeMeridianHeight_of_ge h]
    exact Or.inr ⟨smul_mem_spliceSquare (fourSpokeModelLeaf_mem_spliceSquareBoundary k).1
      (tubeMeridianCoeff_mem ⟨by linarith, h2⟩), mem_singleton _⟩

theorem tubeEdge_subset_tubeUpperPart (k : Fin 4) {h : ℝ} (hh : h ∈ Icc (0 : ℝ) 1) :
    tubeEdge k h ⊆ tubeUpperPart := by
  intro p hp
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := mem_tubeEdge_iff.mp hp
  exact Or.inl ⟨leaf_combination_mem_spliceSquareBoundary k ha hb hab, hh⟩

theorem tubeEdge_inter_tubeUpperArc_add_one (k : Fin 4) :
    tubeEdge k 0 ∩ tubeUpperArc (k + 1) = {(fourSpokeModelLeaf (k + 1), (0 : ℝ))} := by
  apply Subset.antisymm
  · rintro p ⟨hpe, hpa⟩
    have hmem : p ∈ tubeEdge k 0 ∩ (tubeCellArc k ∪ tubeCellArc (k + 1)) :=
      ⟨hpe, Or.inr (tubeUpperArc_subset_tubeCellArc (k + 1) hpa)⟩
    rw [tubeEdge_inter_tubeCellArc k (Or.inl rfl)] at hmem
    rcases hmem with rfl | rfl
    · exfalso
      have h0 := ((mem_tubeCellArc_iff_tubeLeafCoord (k + 1)).mp
        (tubeUpperArc_subset_tubeCellArc (k + 1) hpa)).2.1
      rw [fin_four_add_one_add_one, tubeLeafCoord_add_two] at h0
      change -tubeLeafCoord k (fourSpokeModelLeaf k) = 0 at h0
      rw [tubeLeafCoord_self] at h0
      norm_num at h0
    · rfl
  · rintro p rfl
    exact ⟨⟨1, ⟨zero_le_one, le_rfl⟩, tubeEdgeParam_one k 0⟩,
      ⟨1 / 4, ⟨le_rfl, by norm_num⟩, tubeMeridianParam_quarter _⟩⟩

theorem tubeUpperArc_inter_tubeEdge (k : Fin 4) :
    tubeUpperArc k ∩ tubeEdge k 0 = {(fourSpokeModelLeaf k, (0 : ℝ))} := by
  apply Subset.antisymm
  · rintro p ⟨hpa, hpe⟩
    have hmem : p ∈ tubeEdge k 0 ∩ (tubeCellArc k ∪ tubeCellArc (k + 1)) :=
      ⟨hpe, Or.inl (tubeUpperArc_subset_tubeCellArc k hpa)⟩
    rw [tubeEdge_inter_tubeCellArc k (Or.inl rfl)] at hmem
    rcases hmem with rfl | rfl
    · rfl
    · exfalso
      have h0 := ((mem_tubeCellArc_iff_tubeLeafCoord k).mp
        (tubeUpperArc_subset_tubeCellArc k hpa)).2.1
      change tubeLeafCoord (k + 1) (fourSpokeModelLeaf (k + 1)) = 0 at h0
      rw [tubeLeafCoord_add_one_add_one] at h0
      norm_num at h0
  · rintro p rfl
    exact ⟨⟨1 / 4, ⟨le_rfl, by norm_num⟩, tubeMeridianParam_quarter _⟩,
      ⟨0, ⟨le_rfl, zero_le_one⟩, tubeEdgeParam_zero k 0⟩⟩

theorem tubeUpperArc_inter_tubeUpperArc_add_one (k : Fin 4) :
    tubeUpperArc k ∩ tubeUpperArc (k + 1) = {((0 : ℝ × ℝ), (1 : ℝ))} := by
  apply Subset.antisymm
  · rintro p ⟨hp, hq⟩
    have hmem : p ∈ tubeCellArc k ∩ tubeCellArc (k + 1) :=
      ⟨tubeUpperArc_subset_tubeCellArc k hp, tubeUpperArc_subset_tubeCellArc (k + 1) hq⟩
    rw [tubeCellArc_inter (fin_four_ne_add_one k)] at hmem
    rcases hmem with rfl | rfl
    · exfalso
      obtain ⟨t, ht, hte⟩ := hp
      have h0 : tubeMeridianParam (fourSpokeModelLeaf k) t =
          tubeMeridianParam (fourSpokeModelLeaf k) 0 := by
        rw [hte, tubeMeridianParam_zero]
      have := injOn_tubeMeridianParam (fourSpokeModelLeaf_ne_zero k)
        ⟨by linarith [ht.1], ht.2⟩ ⟨le_rfl, zero_le_one⟩ h0
      linarith [ht.1]
    · exact mem_singleton _
  · rintro p rfl
    exact ⟨⟨1, ⟨by norm_num, le_rfl⟩, tubeMeridianParam_one _⟩,
      ⟨1, ⟨by norm_num, le_rfl⟩, tubeMeridianParam_one _⟩⟩

theorem exists_tubeSectorUpper_boundary_param (k : Fin 4) :
    ∃ l : ℝ → (ℝ × ℝ) × ℝ, IsPLHomeomorphOn l (Icc 0 1) (tubeEdge k 0 ∪ tubeUpperArc (k + 1)) ∧
      l 0 = (fourSpokeModelLeaf k, 0) ∧ l 1 = ((0 : ℝ × ℝ), (1 : ℝ)) := by
  obtain ⟨l, hl, hl0, -, hl1⟩ := exists_isPLHomeomorphOn_Icc_concat
    (isPLHomeomorphOn_tubeEdgeParam k 0) (isPLHomeomorphOn_tubeUpperArcParam (k + 1))
    (by rw [tubeUpperArcParam_zero, tubeEdgeParam_one])
    (by rw [tubeEdgeParam_one]; exact tubeEdge_inter_tubeUpperArc_add_one k)
  exact ⟨l, hl, hl0.trans (tubeEdgeParam_zero k 0), hl1.trans (tubeUpperArcParam_one (k + 1))⟩

theorem isPLSphere_one_tubeSectorUpper_boundary (k : Fin 4) :
    IsPLSphere 1 (tubeUpperArc k ∪ (tubeEdge k 0 ∪ tubeUpperArc (k + 1))) := by
  obtain ⟨l, hl, hl0, hl1⟩ := exists_tubeSectorUpper_boundary_param k
  refine isPLSphere_one_union_of_isPLHomeomorphOn_Icc (isPLHomeomorphOn_tubeUpperArcParam k) hl
    (by rw [hl0, tubeUpperArcParam_zero]) (by rw [hl1, tubeUpperArcParam_one]) ?_
  rw [tubeUpperArcParam_zero, tubeUpperArcParam_one, inter_union_distrib_left,
    tubeUpperArc_inter_tubeEdge, tubeUpperArc_inter_tubeUpperArc_add_one, singleton_union]

def tubeSectorUpper (k : Fin 4) : Set ((ℝ × ℝ) × ℝ) := tubeSector k ∩ tubeUpperPart

def tubeSectorLower (k : Fin 4) : Set ((ℝ × ℝ) × ℝ) :=
  tubeSector k ∩ spliceSquare ×ˢ ({0} : Set ℝ)

theorem tubeSectorUpper_sdiff (k : Fin 4) :
    tubeSectorUpper k \ (tubeUpperArc k ∪ (tubeEdge k 0 ∪ tubeUpperArc (k + 1))) =
      tubeCellSphere ∩
        {p | 0 < tubeLeafCoord k p.1 ∧ 0 < tubeLeafCoord (k + 1) p.1 ∧ 0 < p.2} := by
  ext p
  constructor
  · rintro ⟨⟨⟨hS, h1, h2⟩, hU⟩, hJ⟩
    refine ⟨hS, ?_, ?_, ?_⟩
    · rcases h1.lt_or_eq with h1' | h1'
      · exact h1'
      · exfalso
        refine hJ (Or.inr (Or.inr (mem_tubeUpperArc_of_mem_tubeCellArc ?_ hU)))
        refine (mem_tubeCellArc_iff_tubeLeafCoord (k + 1)).mpr ⟨hS, ?_, h2⟩
        rw [fin_four_add_one_add_one, tubeLeafCoord_add_two, ← h1', neg_zero]
    · rcases h2.lt_or_eq with h2' | h2'
      · exact h2'
      · exfalso
        exact hJ (Or.inl (mem_tubeUpperArc_of_mem_tubeCellArc
          ((mem_tubeCellArc_iff_tubeLeafCoord k).mpr ⟨hS, h2'.symm, h1⟩) hU))
    · rcases hU with ⟨hq, hz0, -⟩ | ⟨-, hz⟩
      · rcases hz0.lt_or_eq with hz0' | hz0'
        · exact hz0'
        · exfalso
          refine hJ (Or.inr (Or.inl ?_))
          have hpe : p = (p.1, 0) := Prod.ext rfl hz0'.symm
          rw [hpe]
          exact mem_tubeEdge_of_mem_spliceSquareBoundary 0 hq h1 h2
      · rw [mem_singleton_iff] at hz
        rw [hz]
        norm_num
  · rintro ⟨hS, h1, h2, hz⟩
    refine ⟨⟨⟨hS, h1.le, h2.le⟩, mem_tubeUpperPart_of_pos hS hz⟩, ?_⟩
    rintro (hp | hp | hp)
    · have := ((mem_tubeCellArc_iff_tubeLeafCoord k).mp
        (tubeUpperArc_subset_tubeCellArc k hp)).2.1
      linarith
    · obtain ⟨a, b, -, -, -, rfl⟩ := mem_tubeEdge_iff.mp hp
      exact lt_irrefl _ hz
    · have := ((mem_tubeCellArc_iff_tubeLeafCoord (k + 1)).mp
        (tubeUpperArc_subset_tubeCellArc (k + 1) hp)).2.1
      rw [fin_four_add_one_add_one, tubeLeafCoord_add_two] at this
      linarith

theorem exists_tubeSectorUpper_param (k : Fin 4) :
    ∃ u : (Fin 3 → ℝ) → (ℝ × ℝ) × ℝ,
      IsPLHomeomorphOn u (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (tubeSectorUpper k) ∧
        u '' stdSimplexBoundary 2 = tubeUpperArc k ∪ (tubeEdge k 0 ∪ tubeUpperArc (k + 1)) := by
  have hO : IsOpen {p : (ℝ × ℝ) × ℝ |
      0 < tubeLeafCoord k p.1 ∧ 0 < tubeLeafCoord (k + 1) p.1 ∧ 0 < p.2} :=
    (isOpen_lt continuous_const ((continuous_tubeLeafCoord k).comp continuous_fst)).inter
      ((isOpen_lt continuous_const ((continuous_tubeLeafCoord (k + 1)).comp continuous_fst)).inter
        (isOpen_lt continuous_const continuous_snd))
  have hc := tubeLeafCoord_leaf_combination k 1 (1 / 2)
  have hJW : tubeUpperArc k ∪ (tubeEdge k 0 ∪ tubeUpperArc (k + 1)) ⊆ tubeSectorUpper k := by
    refine union_subset (fun p hp => ⟨tubeCellArc_subset_tubeSector k
      (tubeUpperArc_subset_tubeCellArc k hp), tubeUpperArc_subset_tubeUpperPart k hp⟩)
      (union_subset (fun p hp => ⟨tubeEdge_subset_tubeSector k (by norm_num) hp,
        tubeEdge_subset_tubeUpperPart k (by norm_num) hp⟩) (fun p hp =>
          ⟨tubeCellArc_add_one_subset_tubeSector k (tubeUpperArc_subset_tubeCellArc (k + 1) hp),
            tubeUpperArc_subset_tubeUpperPart (k + 1) hp⟩))
  refine exists_param_of_sdiff_eq_inter_isOpen isPLSphere_tubeCellSphere
    (isPLSphere_one_tubeSectorUpper_boundary k) hJW (fun p hp => hp.1.1)
    ((isClosed_tubeSector k).inter isClosed_tubeUpperPart) hO (tubeSectorUpper_sdiff k) ?_ ?_
  · rw [tubeSectorUpper_sdiff]
    refine ⟨((1 : ℝ) • fourSpokeModelLeaf k + (1 / 2 : ℝ) • fourSpokeModelLeaf (k + 1), 1 / 2),
      tubeEdge_subset_tubeCellSphere k (h := 1 / 2) (by norm_num)
        (mem_tubeEdge_iff.mpr ⟨1, 1 / 2, by norm_num, by norm_num, Or.inl rfl, rfl⟩), ?_, ?_,
          by norm_num⟩
    · change 0 < tubeLeafCoord k
        ((1 : ℝ) • fourSpokeModelLeaf k + (1 / 2 : ℝ) • fourSpokeModelLeaf (k + 1))
      rw [hc.1]
      norm_num
    · change 0 < tubeLeafCoord (k + 1)
        ((1 : ℝ) • fourSpokeModelLeaf k + (1 / 2 : ℝ) • fourSpokeModelLeaf (k + 1))
      rw [hc.2]
      norm_num
  · exact ⟨(fourSpokeModelLeaf (k + 2), 1 / 2),
      mem_tubeCellSphere_iff.mpr (Or.inr ⟨fourSpokeModelLeaf_mem_spliceSquareBoundary _,
        by norm_num, by norm_num⟩), fun hp => notMem_tubeSector_of_add_two k _ hp.1⟩

theorem tubeSectorLower_union_tubeSectorUpper (k : Fin 4) :
    tubeSectorLower k ∪ tubeSectorUpper k = tubeSector k := by
  apply Subset.antisymm (union_subset inter_subset_left inter_subset_left)
  intro p hp
  rcases mem_tubeCellSphere_iff.mp hp.1 with ⟨hq, hz | hz⟩ | ⟨hq, h0, h1⟩
  · exact Or.inl ⟨hp, hq, hz⟩
  · exact Or.inr ⟨hp, Or.inr ⟨hq, hz⟩⟩
  · exact Or.inr ⟨hp, Or.inl ⟨hq, h0, h1⟩⟩

theorem tubeSectorLower_inter_tubeSectorUpper (k : Fin 4) :
    tubeSectorLower k ∩ tubeSectorUpper k = tubeEdge k 0 := by
  apply Subset.antisymm
  · rintro p ⟨⟨hp, -, hz⟩, -, hU⟩
    rcases hU with ⟨hq, -⟩ | ⟨-, hz'⟩
    · have hpe : p = (p.1, 0) := Prod.ext rfl hz
      rw [hpe]
      exact mem_tubeEdge_of_mem_spliceSquareBoundary 0 hq hp.2.1 hp.2.2
    · exfalso
      rw [mem_singleton_iff] at hz hz'
      rw [hz] at hz'
      exact zero_ne_one hz'
  · intro p hp
    have hS := tubeEdge_subset_tubeSector k (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1) hp
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := mem_tubeEdge_iff.mp hp
    have hq := leaf_combination_mem_spliceSquareBoundary k ha hb hab
    exact ⟨⟨hS, hq.1, mem_singleton _⟩, hS, Or.inl ⟨hq, le_rfl, zero_le_one⟩⟩

theorem isPolyhedron_tubeSector (k : Fin 4) : IsPolyhedron (tubeSector k) := by
  obtain ⟨u, hu, -⟩ := exists_tubeSector_param k
  exact IsPLBall.isPolyhedron ⟨u, hu⟩

theorem isPolyhedron_tubeSectorLower (k : Fin 4) : IsPolyhedron (tubeSectorLower k) := by
  have hP := isPolyhedron_tubeSector k
  have hC : IsHPolytope (spliceSquare ×ˢ ({0} : Set ℝ)) := by
    rw [← Icc_self (0 : ℝ)]
    exact isHPolytope_spliceSquare.prod isHPolytope_Icc
  have hcomp : IsCompact (tubeSector k ∩ id ⁻¹' (spliceSquare ×ˢ ({0} : Set ℝ))) := by
    rw [preimage_id]
    exact hP.isCompact.inter_right hC.1.isClosed
  have h := isPolyhedron_inter_preimage_of_isCompact
    hP.isPLHomeomorphOn_id.isPiecewiseAffineOn hC hcomp
  rwa [preimage_id] at h

theorem isPolyhedron_tubeSectorUpper (k : Fin 4) : IsPolyhedron (tubeSectorUpper k) := by
  obtain ⟨u, hu, -⟩ := exists_tubeSectorUpper_param k
  exact IsPLBall.isPolyhedron ⟨u, hu⟩

theorem tubeEdge_one_subset_tubeSectorUpper (k : Fin 4) : tubeEdge k 1 ⊆ tubeSectorUpper k :=
  fun _ hp => ⟨tubeEdge_subset_tubeSector k (by norm_num) hp,
    tubeEdge_subset_tubeUpperPart k (by norm_num) hp⟩

theorem tubeEdge_one_inter_tubeSectorUpper_boundary (k : Fin 4) :
    tubeEdge k 1 ∩ (tubeUpperArc k ∪ (tubeEdge k 0 ∪ tubeUpperArc (k + 1))) =
      {(fourSpokeModelLeaf k, 1), (fourSpokeModelLeaf (k + 1), 1)} := by
  apply Subset.antisymm
  · rintro p ⟨hp, hJ⟩
    rw [← tubeEdge_inter_tubeCellArc k (Or.inr rfl)]
    refine ⟨hp, ?_⟩
    rcases hJ with hJ | hJ | hJ
    · exact Or.inl (tubeUpperArc_subset_tubeCellArc k hJ)
    · exfalso
      obtain ⟨a, b, -, -, -, rfl⟩ := mem_tubeEdge_iff.mp hJ
      obtain ⟨a', b', -, -, -, h⟩ := mem_tubeEdge_iff.mp hp
      exact zero_ne_one (congrArg Prod.snd h)
    · exact Or.inr (tubeUpperArc_subset_tubeCellArc (k + 1) hJ)
  · rintro p (rfl | rfl)
    · exact ⟨⟨0, ⟨le_rfl, zero_le_one⟩, tubeEdgeParam_zero k 1⟩,
        Or.inl ⟨3 / 4, ⟨by norm_num, by norm_num⟩, tubeMeridianParam_threeQuarter _⟩⟩
    · exact ⟨⟨1, ⟨zero_le_one, le_rfl⟩, tubeEdgeParam_one k 1⟩,
        Or.inr (Or.inr ⟨3 / 4, ⟨by norm_num, by norm_num⟩, tubeMeridianParam_threeQuarter _⟩)⟩

theorem subset_tubeSectorUpper_of_isPreconnected {k : Fin 4} {U : Set ((ℝ × ℝ) × ℝ)}
    (hU : U ⊆ tubeSector k \ tubeEdge k 0) (hconn : IsPreconnected U) {p : (ℝ × ℝ) × ℝ}
    (hpU : p ∈ U) (hp : 0 < p.2) : U ⊆ tubeSectorUpper k := by
  have c1 : Continuous fun q : (ℝ × ℝ) × ℝ => q.1.1 := continuous_fst.comp continuous_fst
  have c2 : Continuous fun q : (ℝ × ℝ) × ℝ => q.1.2 := continuous_snd.comp continuous_fst
  have hO₂ : IsOpen {q : (ℝ × ℝ) × ℝ |
      -1 < q.1.1 ∧ q.1.1 < 1 ∧ -1 < q.1.2 ∧ q.1.2 < 1 ∧ q.2 < 1 / 2} :=
    (isOpen_lt continuous_const c1).inter ((isOpen_lt c1 continuous_const).inter
      ((isOpen_lt continuous_const c2).inter ((isOpen_lt c2 continuous_const).inter
        (isOpen_lt continuous_snd continuous_const))))
  have hcover : U ⊆ {q : (ℝ × ℝ) × ℝ | 0 < q.2} ∪
      {q : (ℝ × ℝ) × ℝ | -1 < q.1.1 ∧ q.1.1 < 1 ∧ -1 < q.1.2 ∧ q.1.2 < 1 ∧ q.2 < 1 / 2} := by
    intro q hq
    obtain ⟨hqs, hqe⟩ := hU hq
    obtain ⟨hsq, hz0, -⟩ := mem_tubeCellSphere_bounds hqs.1
    rcases hz0.lt_or_eq with hz | hz
    · exact Or.inl hz
    · right
      have hnb : q.1 ∉ spliceSquareBoundary := fun hb => by
        have hqe' : q = (q.1, 0) := Prod.ext rfl hz.symm
        rw [hqe'] at hqe
        exact hqe (mem_tubeEdge_of_mem_spliceSquareBoundary 0 hb hqs.2.1 hqs.2.2)
      have hsq' := hsq
      rw [mem_spliceSquare] at hsq'
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hsq'
      have e1 : q.1.1 ≠ -1 := fun h => hnb ⟨hsq, Or.inl h⟩
      have e2 : q.1.1 ≠ 1 := fun h => hnb ⟨hsq, Or.inr (Or.inl h)⟩
      have e3 : q.1.2 ≠ -1 := fun h => hnb ⟨hsq, Or.inr (Or.inr (Or.inl h))⟩
      have e4 : q.1.2 ≠ 1 := fun h => hnb ⟨hsq, Or.inr (Or.inr (Or.inr h))⟩
      exact ⟨lt_of_le_of_ne h1 e1.symm, lt_of_le_of_ne h2 e2, lt_of_le_of_ne h3 e3.symm,
        lt_of_le_of_ne h4 e4, by linarith⟩
  have hdisj : U ∩ ({q : (ℝ × ℝ) × ℝ | 0 < q.2} ∩
      {q : (ℝ × ℝ) × ℝ | -1 < q.1.1 ∧ q.1.1 < 1 ∧ -1 < q.1.2 ∧ q.1.2 < 1 ∧ q.2 < 1 / 2}) =
        ∅ := by
    refine eq_empty_iff_forall_notMem.mpr fun q ⟨hq, hz, h1, h2, h3, h4, h5⟩ => ?_
    change 0 < q.2 at hz
    rcases tubeCellSphere_snd_eq_of_lt (hU hq).1.1 h1 h2 h3 h4 with h | h <;> linarith
  rcases isPreconnected_iff_subset_of_disjoint.mp hconn _ _
    (isOpen_lt continuous_const continuous_snd) hO₂ hcover hdisj with h | h
  · intro q hq
    exact ⟨(hU hq).1, mem_tubeUpperPart_of_pos (hU hq).1.1 (h hq)⟩
  · exfalso
    obtain ⟨h1, h2, h3, h4, h5⟩ := h hpU
    rcases tubeCellSphere_snd_eq_of_lt (hU hpU).1.1 h1 h2 h3 h4 with h | h <;> linarith

end DifferentialGeometry.Topology.PiecewiseLinear

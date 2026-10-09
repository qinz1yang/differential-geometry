/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ClosedBranchOrientability
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchTubeChain

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable def spliceSquareLoop (t : ℝ) : ℝ × ℝ :=
  if t ≤ 1 / 2 then upperSpliceArc (2 * t) else lowerSpliceArc (2 - 2 * t)

theorem spliceSquareLoop_of_le {t : ℝ} (ht : t ≤ 1 / 2) :
    spliceSquareLoop t = upperSpliceArc (2 * t) :=
  ite_eq_left ht

theorem spliceSquareLoop_of_ge {t : ℝ} (ht : 1 / 2 ≤ t) :
    spliceSquareLoop t = lowerSpliceArc (2 - 2 * t) := by
  rcases eq_or_lt_of_le ht with h | h
  · rw [← h, spliceSquareLoop_of_le le_rfl, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
      show (2 : ℝ) - 1 = 1 by norm_num, upperSpliceArc_one, lowerSpliceArc_one]
  · exact ite_eq_right (not_le.mpr h)

theorem continuousOn_spliceSquareLoop : ContinuousOn spliceSquareLoop (Icc 0 1) := by
  have hu := isPLHomeomorphOn_upperSpliceArc.isPiecewiseAffineOn.continuousOn
  have hl := isPLHomeomorphOn_lowerSpliceArc.isPiecewiseAffineOn.continuousOn
  have hc₁ : Continuous fun t : ℝ => 2 * t := continuous_const_mul 2
  have hc₂ : Continuous fun t : ℝ => 2 - 2 * t := continuous_const.sub (continuous_const_mul 2)
  have h₁ : ContinuousOn spliceSquareLoop (Icc 0 (1 / 2)) := by
    refine (hu.comp hc₁.continuousOn fun t (ht : t ∈ Icc (0 : ℝ) (1 / 2)) =>
      (⟨by linarith [ht.1], by linarith [ht.2]⟩ : 2 * t ∈ Icc (0 : ℝ) 1)).congr fun t ht => ?_
    exact spliceSquareLoop_of_le ht.2
  have h₂ : ContinuousOn spliceSquareLoop (Icc (1 / 2) 1) := by
    refine (hl.comp hc₂.continuousOn fun t (ht : t ∈ Icc (1 / 2 : ℝ) 1) =>
      (⟨by linarith [ht.2], by linarith [ht.1]⟩ : 2 - 2 * t ∈ Icc (0 : ℝ) 1)).congr
        fun t ht => ?_
    exact spliceSquareLoop_of_ge ht.1
  have h := h₁.union_of_isClosed h₂ isClosed_Icc isClosed_Icc
  rwa [Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)] at h

theorem spliceSquareLoop_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    spliceSquareLoop t ∈ spliceSquareBoundary := by
  rw [← upperSpliceBoundary_union_lowerSpliceBoundary]
  rcases le_total t (1 / 2) with h | h
  · rw [spliceSquareLoop_of_le h]
    exact Or.inl (bijOn_upperSpliceArc.mapsTo ⟨by linarith [ht.1], by linarith⟩)
  · rw [spliceSquareLoop_of_ge h]
    exact Or.inr (bijOn_lowerSpliceArc.mapsTo ⟨by linarith [ht.2], by linarith⟩)

theorem injOn_spliceSquareLoop : InjOn spliceSquareLoop (Ico 0 1) := by
  have hmemU : ∀ s ∈ Icc (0 : ℝ) 1, upperSpliceArc s ∈ upperSpliceBoundary :=
    fun s hs => bijOn_upperSpliceArc.mapsTo hs
  have hmemL : ∀ s ∈ Icc (0 : ℝ) 1, lowerSpliceArc s ∈ lowerSpliceBoundary :=
    fun s hs => bijOn_lowerSpliceArc.mapsTo hs
  have hcross : ∀ x y : ℝ, x ∈ Icc (0 : ℝ) (1 / 2) → y ∈ Ioo (1 / 2 : ℝ) 1 →
      upperSpliceArc (2 * x) ≠ lowerSpliceArc (2 - 2 * y) := by
    intro x y hx hy hxy
    have hx' : 2 * x ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hy' : 2 - 2 * y ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have hmem : upperSpliceArc (2 * x) ∈ upperSpliceBoundary ∩ lowerSpliceBoundary :=
      ⟨hmemU _ hx', hxy ▸ hmemL _ hy'⟩
    rw [upperSpliceBoundary_inter_lowerSpliceBoundary] at hmem
    rcases hmem with h | h
    · have := bijOn_lowerSpliceArc.injOn hy' ⟨le_rfl, zero_le_one⟩
        ((hxy.symm.trans h).trans lowerSpliceArc_zero.symm)
      linarith [hy.2]
    · have := bijOn_lowerSpliceArc.injOn hy' ⟨zero_le_one, le_rfl⟩
        ((hxy.symm.trans h).trans lowerSpliceArc_one.symm)
      linarith [hy.1]
  intro x hx y hy hxy
  rcases le_or_gt x (1 / 2) with hx2 | hx2 <;> rcases le_or_gt y (1 / 2) with hy2 | hy2
  · rw [spliceSquareLoop_of_le hx2, spliceSquareLoop_of_le hy2] at hxy
    have := bijOn_upperSpliceArc.injOn ⟨by linarith [hx.1], by linarith⟩
      ⟨by linarith [hy.1], by linarith⟩ hxy
    linarith
  · rw [spliceSquareLoop_of_le hx2, spliceSquareLoop_of_ge hy2.le] at hxy
    exact (hcross x y ⟨hx.1, hx2⟩ ⟨hy2, hy.2⟩ hxy).elim
  · rw [spliceSquareLoop_of_ge hx2.le, spliceSquareLoop_of_le hy2] at hxy
    exact (hcross y x ⟨hy.1, hy2⟩ ⟨hx2, hx.2⟩ hxy.symm).elim
  · rw [spliceSquareLoop_of_ge hx2.le, spliceSquareLoop_of_ge hy2.le] at hxy
    have := bijOn_lowerSpliceArc.injOn ⟨by linarith [hx.2], by linarith⟩
      ⟨by linarith [hy.2], by linarith⟩ hxy
    linarith

theorem surjOn_spliceSquareLoop : SurjOn spliceSquareLoop (Ico 0 1) spliceSquareBoundary := by
  intro p hp
  rw [← upperSpliceBoundary_union_lowerSpliceBoundary] at hp
  rcases hp with hp | hp
  · obtain ⟨s, hs, rfl⟩ := bijOn_upperSpliceArc.surjOn hp
    refine ⟨s / 2, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
    rw [spliceSquareLoop_of_le (by linarith [hs.2]), mul_div_cancel₀ s two_ne_zero]
  · obtain ⟨s, hs, rfl⟩ := bijOn_lowerSpliceArc.surjOn hp
    rcases eq_or_lt_of_le hs.1 with h | h
    · refine ⟨0, ⟨le_rfl, zero_lt_one⟩, ?_⟩
      rw [← h, spliceSquareLoop_of_le (by norm_num), mul_zero, upperSpliceArc_zero,
        lowerSpliceArc_zero]
    · refine ⟨1 - s / 2, ⟨by linarith [hs.2], by linarith⟩, ?_⟩
      rw [spliceSquareLoop_of_ge (by linarith [hs.2])]
      congr 1
      ring

noncomputable def spliceLeafTime : Fin 4 → ℝ
  | 0 => 0
  | 1 => 1 / 4
  | 2 => 1 / 2
  | 3 => 3 / 4

theorem spliceLeafTime_zero : spliceLeafTime 0 = 0 := rfl

theorem spliceLeafTime_one : spliceLeafTime 1 = 1 / 4 := rfl

theorem spliceLeafTime_two : spliceLeafTime 2 = 1 / 2 := rfl

theorem spliceLeafTime_three : spliceLeafTime 3 = 3 / 4 := rfl

theorem exists_spliceSquare_cyclic :
    ∃ (g : loopCircle → ℝ × ℝ) (v : Fin 4 → ℝ), Continuous g ∧
      BijOn g univ spliceSquareBoundary ∧ v 0 < v 1 ∧ v 1 < v 2 ∧ v 2 < v 3 ∧
        v 3 < v 0 + 1 ∧ ∀ i, fourSpokeModelLeaf i = g ((v i : ℝ) : loopCircle) := by
  have h01 : spliceSquareLoop 0 = spliceSquareLoop (0 + 1) := by
    rw [spliceSquareLoop_of_le (by norm_num), zero_add, spliceSquareLoop_of_ge (by norm_num),
      mul_zero, show (2 : ℝ) - 2 * 1 = 0 by norm_num, upperSpliceArc_zero, lowerSpliceArc_zero]
  have hcont : Continuous (AddCircle.liftIco (1 : ℝ) 0 spliceSquareLoop) :=
    AddCircle.liftIco_continuous h01 (by rw [zero_add]; exact continuousOn_spliceSquareLoop)
  have happ : ∀ x ∈ Ico (0 : ℝ) 1,
      AddCircle.liftIco (1 : ℝ) 0 spliceSquareLoop (x : loopCircle) = spliceSquareLoop x :=
    fun x hx => AddCircle.liftIco_coe_apply (by rwa [zero_add])
  have hval : ∀ z : loopCircle, AddCircle.liftIco (1 : ℝ) 0 spliceSquareLoop z =
      spliceSquareLoop (AddCircle.equivIco (1 : ℝ) 0 z : ℝ) := fun _ => rfl
  have hmemIco : ∀ z : loopCircle, (AddCircle.equivIco (1 : ℝ) 0 z : ℝ) ∈ Ico (0 : ℝ) 1 :=
    fun z => by simpa only [zero_add] using (AddCircle.equivIco (1 : ℝ) 0 z).2
  refine ⟨AddCircle.liftIco (1 : ℝ) 0 spliceSquareLoop, spliceLeafTime, hcont,
    ⟨fun z _ => ?_, fun z _ w _ hzw => ?_, fun p hp => ?_⟩, ?_, ?_, ?_, ?_, fun i => ?_⟩
  · rw [hval]
    exact spliceSquareLoop_mem (Ico_subset_Icc_self (hmemIco z))
  · rw [hval, hval] at hzw
    exact (AddCircle.equivIco (1 : ℝ) 0).injective
      (Subtype.ext (injOn_spliceSquareLoop (hmemIco z) (hmemIco w) hzw))
  · obtain ⟨x, hx, rfl⟩ := surjOn_spliceSquareLoop hp
    exact ⟨(x : loopCircle), mem_univ _, happ x hx⟩
  · rw [spliceLeafTime_zero, spliceLeafTime_one]
    norm_num
  · rw [spliceLeafTime_one, spliceLeafTime_two]
    norm_num
  · rw [spliceLeafTime_two, spliceLeafTime_three]
    norm_num
  · rw [spliceLeafTime_three, spliceLeafTime_zero]
    norm_num
  · rcases fourSpokeIndexCases i with rfl | rfl | rfl | rfl
    · rw [spliceLeafTime_zero, happ 0 ⟨le_rfl, zero_lt_one⟩,
        spliceSquareLoop_of_le (by norm_num), mul_zero, upperSpliceArc_zero]
      rfl
    · rw [spliceLeafTime_one, happ (1 / 4) ⟨by norm_num, by norm_num⟩,
        spliceSquareLoop_of_le (by norm_num), upperSpliceArc_of_mem (by norm_num) (by norm_num)]
      norm_num [fourSpokeModelLeaf]
    · rw [spliceLeafTime_two, happ (1 / 2) ⟨by norm_num, by norm_num⟩,
        spliceSquareLoop_of_le le_rfl, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
        upperSpliceArc_one]
      rfl
    · rw [spliceLeafTime_three, happ (3 / 4) ⟨by norm_num, by norm_num⟩,
        spliceSquareLoop_of_ge (by norm_num), lowerSpliceArc_of_mem (by norm_num) (by norm_num)]
      norm_num [fourSpokeModelLeaf]

theorem boundaryComplex_space_of_space_eq_spliceSquare
    (Pc : Geometry.SimplicialComplex ℝ (ℝ × ℝ)) [Finite Pc.faces] (hPc : Pc.space = spliceSquare) :
    (boundaryComplex 2 Pc).space = spliceSquareBoundary := by
  classical
  have hball : IsPLBall (1 + 1) Pc.space := by
    rw [hPc]
    exact isPLBall_spliceSquare
  rw [← frontier_space_eq_boundaryComplex_space_of_finrank (n := 1) (by simp) Pc
    hball.isCombinatorialManifoldWithBoundary, hPc, spliceSquareBoundary_eq_frontier]

end DifferentialGeometry.Topology.PiecewiseLinear

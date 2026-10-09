/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.HandleModelCharts

open Set Complex Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem mem_closedBall_zero_prod_iff {p : EuclideanSpace ℝ (Fin 2) × ℝ} :
    p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2) × ℝ) 1 ↔ ‖p.1‖ ≤ 1 ∧ |p.2| ≤ 1 := by
  rw [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff, Real.norm_eq_abs]

theorem ofReal_add_mul_I_mem_concaveQuadrant_iff (x y : ℝ) :
    (x : ℂ) + y * I ∈ concaveQuadrant ↔ 0 ≤ x ∨ 0 ≤ y := by
  simp [concaveQuadrant]

theorem norm_ofReal_add_mul_I_lt_one {x y : ℝ} (h : |x| + |y| < 1) : ‖(x : ℂ) + y * I‖ < 1 := by
  calc ‖(x : ℂ) + y * I‖ ≤ |((x : ℂ) + y * I).re| + |((x : ℂ) + y * I).im| :=
        norm_le_abs_re_add_abs_im _
    _ = |x| + |y| := by simp
    _ < 1 := h

def twoHandleCollar (a : ℝ) : Set (EuclideanSpace ℝ (Fin 2) × ℝ) :=
  {p | 1 ≤ ‖p.1‖ ∧ ‖p.1‖ < 1 + a ∧ |p.2| < 3 / 2}

def twoHandleInterior (a : ℝ) : Set (EuclideanSpace ℝ (Fin 2) × ℝ) :=
  {p | (‖p.1‖ < 1 + a ∧ |p.2| < 1) ∨ (1 < ‖p.1‖ ∧ ‖p.1‖ < 1 + a ∧ |p.2| < 3 / 2)}

def twoHandleFaceBottom : Set (EuclideanSpace ℝ (Fin 2) × ℝ) :=
  {p | ‖p.1‖ < 3 / 4 ∧ p.2 < 0}

def twoHandleFaceTop : Set (EuclideanSpace ℝ (Fin 2) × ℝ) :=
  {p | ‖p.1‖ < 3 / 4 ∧ 0 < p.2}

def twoHandleCornerDomain (a : ℝ) : Set (ℝ × ℝ) :=
  Ioo (-(1 / 2)) a ×ˢ Ioo (-(1 / 2)) (1 / 2)

def twoHandleBottomL (q : ℝ × ℝ) : ℝ × ℝ := (q.1 - 1, q.2 + 1)

def twoHandleBottomLinv (q : ℝ × ℝ) : ℝ × ℝ := (q.1 + 1, q.2 - 1)

def twoHandleTopL (q : ℝ × ℝ) : ℝ × ℝ := (q.1 - 1, 1 - q.2)

def twoHandleTopLinv (q : ℝ × ℝ) : ℝ × ℝ := (q.1 + 1, 1 - q.2)

def twoHandleRim : Set (EuclideanSpace ℝ (Fin 2) × ℝ) := {p | ‖p.1‖ = 1 ∧ |p.2| = 1}

noncomputable def twoHandleRimIndex (p : EuclideanSpace ℝ (Fin 2) × ℝ) : Fin 5 :=
  if p.2 < 0 then 3 else 4

def twoHandleChartSource (a : ℝ) : Fin 5 → Set (EuclideanSpace ℝ (Fin 2) × ℝ) :=
  ![twoHandleInterior a, twoHandleFaceBottom, twoHandleFaceTop,
    cornerModelSource twoHandleBottomL (twoHandleCornerDomain a),
    cornerModelSource twoHandleTopL (twoHandleCornerDomain a)]

def twoHandleChartTarget (a : ℝ) : Fin 5 → Set (EuclideanHalfSpace 3) :=
  ![slabChartTarget 1 2 (twoHandleInterior a), slabChartTarget 1 1 twoHandleFaceBottom,
    slabChartTarget (-1) 1 twoHandleFaceTop, cornerModelTarget (twoHandleCornerDomain a),
    cornerModelTarget (twoHandleCornerDomain a)]

noncomputable def twoHandleChartVec :
    Fin 5 → EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3) :=
  ![slabChartVec 1 2, slabChartVec 1 1, slabChartVec (-1) 1, cornerModelVec twoHandleBottomL,
    cornerModelVec twoHandleTopL]

noncomputable def twoHandleChartInv :
    Fin 5 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 2) × ℝ :=
  ![slabChartInv 1 2, slabChartInv 1 1, slabChartInv (-1) 1, cornerModelInv twoHandleBottomLinv,
    cornerModelInv twoHandleTopLinv]

theorem contDiff_twoHandleBottomL : ContDiff ℝ ∞ twoHandleBottomL :=
  (contDiff_fst.sub contDiff_const).prodMk (contDiff_snd.add contDiff_const)

theorem contDiff_twoHandleBottomLinv : ContDiff ℝ ∞ twoHandleBottomLinv :=
  (contDiff_fst.add contDiff_const).prodMk (contDiff_snd.sub contDiff_const)

theorem contDiff_twoHandleTopL : ContDiff ℝ ∞ twoHandleTopL :=
  (contDiff_fst.sub contDiff_const).prodMk (contDiff_const.sub contDiff_snd)

theorem contDiff_twoHandleTopLinv : ContDiff ℝ ∞ twoHandleTopLinv :=
  (contDiff_fst.add contDiff_const).prodMk (contDiff_const.sub contDiff_snd)

theorem twoHandleBottomL_Linv (q : ℝ × ℝ) : twoHandleBottomL (twoHandleBottomLinv q) = q := by
  simp [twoHandleBottomL, twoHandleBottomLinv]

theorem twoHandleBottomLinv_L (q : ℝ × ℝ) : twoHandleBottomLinv (twoHandleBottomL q) = q := by
  simp [twoHandleBottomL, twoHandleBottomLinv]

theorem twoHandleTopL_Linv (q : ℝ × ℝ) : twoHandleTopL (twoHandleTopLinv q) = q := by
  simp [twoHandleTopL, twoHandleTopLinv]

theorem twoHandleTopLinv_L (q : ℝ × ℝ) : twoHandleTopLinv (twoHandleTopL q) = q := by
  simp [twoHandleTopL, twoHandleTopLinv]

theorem twoHandleCornerDomain_norm_lt {a : ℝ} (ha2 : a ≤ 1 / 2) :
    ∀ q ∈ twoHandleCornerDomain a, ‖((q.1 : ℂ) + q.2 * I)‖ < 1 := by
  rintro q ⟨⟨h1, h2⟩, h3, h4⟩
  apply norm_ofReal_add_mul_I_lt_one
  have e1 : |q.1| < 1 / 2 := abs_lt.mpr ⟨h1, by linarith⟩
  have e2 : |q.2| < 1 / 2 := abs_lt.mpr ⟨h3, h4⟩
  linarith

theorem twoHandleCornerDomain_bottom_pos (a : ℝ) :
    ∀ q ∈ twoHandleCornerDomain a, 0 < (twoHandleBottomLinv q).1 := by
  rintro q ⟨⟨h1, -⟩, -⟩
  change 0 < q.1 + 1
  linarith

theorem twoHandleCornerDomain_top_pos (a : ℝ) :
    ∀ q ∈ twoHandleCornerDomain a, 0 < (twoHandleTopLinv q).1 := by
  rintro q ⟨⟨h1, -⟩, -⟩
  change 0 < q.1 + 1
  linarith

theorem isOpen_twoHandleCornerDomain (a : ℝ) : IsOpen (twoHandleCornerDomain a) :=
  isOpen_Ioo.prod isOpen_Ioo

theorem twoHandleInterior_mem_iff {a : ℝ} :
    ∀ p ∈ twoHandleInterior a, (p ∈ Metric.closedBall 0 1 ∪ twoHandleCollar a ↔
      0 ≤ 1 * p.2 + 2) := by
  intro p hp
  constructor
  · intro _
    rcases hp with ⟨-, h2⟩ | ⟨-, -, h3⟩
    · linarith [(abs_lt.mp h2).1]
    · linarith [(abs_lt.mp h3).1]
  · intro _
    rw [mem_union, mem_closedBall_zero_prod_iff]
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · by_cases hw : ‖p.1‖ ≤ 1
      · exact Or.inl ⟨hw, h2.le⟩
      · refine Or.inr ⟨(not_le.mp hw).le, h1, ?_⟩
        linarith
    · exact Or.inr ⟨h1.le, h2, h3⟩

theorem twoHandleFaceBottom_mem_iff (a : ℝ) :
    ∀ p ∈ twoHandleFaceBottom, (p ∈ Metric.closedBall 0 1 ∪ twoHandleCollar a ↔
      0 ≤ 1 * p.2 + 1) := by
  rintro p ⟨h1, h2⟩
  rw [mem_union, mem_closedBall_zero_prod_iff]
  constructor
  · rintro (⟨-, h3⟩ | ⟨h3, -⟩)
    · linarith [(abs_le.mp h3).1]
    · linarith
  · intro h3
    refine Or.inl ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩

theorem twoHandleFaceTop_mem_iff (a : ℝ) :
    ∀ p ∈ twoHandleFaceTop, (p ∈ Metric.closedBall 0 1 ∪ twoHandleCollar a ↔
      0 ≤ -1 * p.2 + 1) := by
  rintro p ⟨h1, h2⟩
  rw [mem_union, mem_closedBall_zero_prod_iff]
  constructor
  · rintro (⟨-, h3⟩ | ⟨h3, -⟩)
    · linarith [(abs_le.mp h3).2]
    · linarith
  · intro h3
    refine Or.inl ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩

theorem twoHandleBottom_mem_iff {a : ℝ} (ha2 : a ≤ 1 / 2) :
    ∀ p ∈ cornerModelSource twoHandleBottomL (twoHandleCornerDomain a),
      (p ∈ Metric.closedBall 0 1 ∪ twoHandleCollar a ↔
        ((twoHandleBottomL (‖p.1‖, p.2)).1 : ℂ) + (twoHandleBottomL (‖p.1‖, p.2)).2 * I ∈
          concaveQuadrant) := by
  rintro p ⟨-, ⟨h1, h2⟩, h3, h4⟩
  simp only [twoHandleBottomL] at h1 h2 h3 h4
  rw [ofReal_add_mul_I_mem_concaveQuadrant_iff, mem_union, mem_closedBall_zero_prod_iff]
  simp only [twoHandleBottomL]
  constructor
  · rintro (⟨-, h5⟩ | ⟨h5, -⟩)
    · right
      linarith [(abs_le.mp h5).1]
    · left
      linarith
  · rintro (h5 | h5)
    · exact Or.inr ⟨by linarith, by linarith, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
    · by_cases hw : ‖p.1‖ ≤ 1
      · exact Or.inl ⟨hw, abs_le.mpr ⟨by linarith, by linarith⟩⟩
      · exact Or.inr ⟨(not_le.mp hw).le, by linarith, abs_lt.mpr ⟨by linarith, by linarith⟩⟩

theorem twoHandleTop_mem_iff {a : ℝ} (ha2 : a ≤ 1 / 2) :
    ∀ p ∈ cornerModelSource twoHandleTopL (twoHandleCornerDomain a),
      (p ∈ Metric.closedBall 0 1 ∪ twoHandleCollar a ↔
        ((twoHandleTopL (‖p.1‖, p.2)).1 : ℂ) + (twoHandleTopL (‖p.1‖, p.2)).2 * I ∈
          concaveQuadrant) := by
  rintro p ⟨-, ⟨h1, h2⟩, h3, h4⟩
  simp only [twoHandleTopL] at h1 h2 h3 h4
  rw [ofReal_add_mul_I_mem_concaveQuadrant_iff, mem_union, mem_closedBall_zero_prod_iff]
  simp only [twoHandleTopL]
  constructor
  · rintro (⟨-, h5⟩ | ⟨h5, -⟩)
    · right
      linarith [(abs_le.mp h5).2]
    · left
      linarith
  · rintro (h5 | h5)
    · exact Or.inr ⟨by linarith, by linarith, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
    · by_cases hw : ‖p.1‖ ≤ 1
      · exact Or.inl ⟨hw, abs_le.mpr ⟨by linarith, by linarith⟩⟩
      · exact Or.inr ⟨(not_le.mp hw).le, by linarith, abs_lt.mpr ⟨by linarith, by linarith⟩⟩

theorem isOpen_twoHandleChartSource (a : ℝ) (j : Fin 5) : IsOpen (twoHandleChartSource a j) := by
  have hn : Continuous (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => ‖p.1‖) :=
    continuous_norm.comp continuous_fst
  have hs : Continuous (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => |p.2|) :=
    continuous_abs.comp continuous_snd
  fin_cases j
  · exact ((isOpen_lt hn continuous_const).inter (isOpen_lt hs continuous_const)).union
      ((isOpen_lt continuous_const hn).inter
        ((isOpen_lt hn continuous_const).inter (isOpen_lt hs continuous_const)))
  · exact (isOpen_lt hn continuous_const).inter (isOpen_lt continuous_snd continuous_const)
  · exact (isOpen_lt hn continuous_const).inter (isOpen_lt continuous_const continuous_snd)
  · exact isOpen_cornerModelSource contDiff_twoHandleBottomL.continuous
      (isOpen_twoHandleCornerDomain a)
  · exact isOpen_cornerModelSource contDiff_twoHandleTopL.continuous
      (isOpen_twoHandleCornerDomain a)

theorem isOpen_twoHandleChartTarget (a : ℝ) (j : Fin 5) : IsOpen (twoHandleChartTarget a j) := by
  fin_cases j
  · exact isOpen_slabChartTarget 1 2 (isOpen_twoHandleChartSource a 0)
  · exact isOpen_slabChartTarget 1 1 (isOpen_twoHandleChartSource a 1)
  · exact isOpen_slabChartTarget (-1) 1 (isOpen_twoHandleChartSource a 2)
  · exact isOpen_cornerModelTarget (isOpen_twoHandleCornerDomain a)
  · exact isOpen_cornerModelTarget (isOpen_twoHandleCornerDomain a)

theorem twoHandleChart_mem {a : ℝ} (ha2 : a ≤ 1 / 2) (j : Fin 5) :
    ∀ p ∈ twoHandleChartSource a j, p ∈ Metric.closedBall 0 1 ∪ twoHandleCollar a →
      0 ≤ twoHandleChartVec j p 0 ∧
        toHalfSpace (twoHandleChartVec j p) ∈ twoHandleChartTarget a j := by
  fin_cases j
  · exact slabChart_mem (by norm_num) twoHandleInterior_mem_iff
  · exact slabChart_mem (by norm_num) (twoHandleFaceBottom_mem_iff a)
  · exact slabChart_mem (by norm_num) (twoHandleFaceTop_mem_iff a)
  · exact cornerModel_mem (twoHandleCornerDomain_norm_lt ha2) (twoHandleBottom_mem_iff ha2)
  · exact cornerModel_mem (twoHandleCornerDomain_norm_lt ha2) (twoHandleTop_mem_iff ha2)

theorem twoHandleChart_inv_mem {a : ℝ} (ha2 : a ≤ 1 / 2) (j : Fin 5) :
    ∀ y ∈ twoHandleChartTarget a j, twoHandleChartInv j y.val ∈ twoHandleChartSource a j ∧
      twoHandleChartInv j y.val ∈ Metric.closedBall 0 1 ∪ twoHandleCollar a := by
  fin_cases j
  · exact slabChart_inv_mem (by norm_num) twoHandleInterior_mem_iff
  · exact slabChart_inv_mem (by norm_num) (twoHandleFaceBottom_mem_iff a)
  · exact slabChart_inv_mem (by norm_num) (twoHandleFaceTop_mem_iff a)
  · exact cornerModel_inv_mem twoHandleBottomL_Linv (twoHandleCornerDomain_bottom_pos a)
      (twoHandleBottom_mem_iff ha2)
  · exact cornerModel_inv_mem twoHandleTopL_Linv (twoHandleCornerDomain_top_pos a)
      (twoHandleTop_mem_iff ha2)

theorem twoHandleChart_left {a : ℝ} (ha2 : a ≤ 1 / 2) (j : Fin 5) :
    ∀ p ∈ twoHandleChartSource a j, p ∈ Metric.closedBall 0 1 ∪ twoHandleCollar a →
      twoHandleChartInv j (twoHandleChartVec j p) = p := by
  fin_cases j
  · exact fun p _ _ => slabChartInv_vec (by norm_num) 2 p
  · exact fun p _ _ => slabChartInv_vec (by norm_num) 1 p
  · exact fun p _ _ => slabChartInv_vec (by norm_num) 1 p
  · exact cornerModel_left twoHandleBottomLinv_L (twoHandleCornerDomain_norm_lt ha2)
      (twoHandleBottom_mem_iff ha2)
  · exact cornerModel_left twoHandleTopLinv_L (twoHandleCornerDomain_norm_lt ha2)
      (twoHandleTop_mem_iff ha2)

theorem twoHandleChart_right (a : ℝ) (j : Fin 5) :
    ∀ y ∈ twoHandleChartTarget a j, twoHandleChartVec j (twoHandleChartInv j y.val) = y.val := by
  fin_cases j
  · exact fun y _ => slabChartVec_inv (by norm_num) 2 y.val
  · exact fun y _ => slabChartVec_inv (by norm_num) 1 y.val
  · exact fun y _ => slabChartVec_inv (by norm_num) 1 y.val
  · exact cornerModel_right twoHandleBottomL_Linv (twoHandleCornerDomain_bottom_pos a)
  · exact cornerModel_right twoHandleTopL_Linv (twoHandleCornerDomain_top_pos a)

theorem continuousOn_twoHandleChartVec {a : ℝ} (ha2 : a ≤ 1 / 2) (j : Fin 5) :
    ContinuousOn (twoHandleChartVec j)
      (twoHandleChartSource a j ∩ (Metric.closedBall 0 1 ∪ twoHandleCollar a)) := by
  fin_cases j
  · exact (contDiff_slabChartVec 1 2).continuous.continuousOn
  · exact (contDiff_slabChartVec 1 1).continuous.continuousOn
  · exact (contDiff_slabChartVec (-1) 1).continuous.continuousOn
  · exact continuousOn_cornerModelVec contDiff_twoHandleBottomL.continuous
      (twoHandleBottom_mem_iff ha2)
  · exact continuousOn_cornerModelVec contDiff_twoHandleTopL.continuous
      (twoHandleTop_mem_iff ha2)

theorem continuousOn_twoHandleChartInv (a : ℝ) (j : Fin 5) :
    ContinuousOn (fun y : EuclideanHalfSpace 3 => twoHandleChartInv j y.val)
      (twoHandleChartTarget a j) := by
  fin_cases j
  · exact ((contDiff_slabChartInv 1 2).continuous.comp continuous_subtype_val).continuousOn
  · exact ((contDiff_slabChartInv 1 1).continuous.comp continuous_subtype_val).continuousOn
  · exact ((contDiff_slabChartInv (-1) 1).continuous.comp continuous_subtype_val).continuousOn
  · exact continuousOn_cornerModelInv contDiff_twoHandleBottomLinv.continuous _
  · exact continuousOn_cornerModelInv contDiff_twoHandleTopLinv.continuous _

theorem mem_twoHandleRim_of_eq_bottomLinv {p : EuclideanSpace ℝ (Fin 2) × ℝ}
    (h : (‖p.1‖, p.2) = twoHandleBottomLinv 0) : p ∈ twoHandleRim := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [twoHandleBottomLinv, Prod.fst_zero, Prod.snd_zero] at h1 h2
  refine ⟨by linarith, ?_⟩
  rw [h2]
  norm_num

theorem mem_twoHandleRim_of_eq_topLinv {p : EuclideanSpace ℝ (Fin 2) × ℝ}
    (h : (‖p.1‖, p.2) = twoHandleTopLinv 0) : p ∈ twoHandleRim := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [twoHandleTopLinv, Prod.fst_zero, Prod.snd_zero] at h1 h2
  refine ⟨by linarith, ?_⟩
  rw [h2]
  norm_num

theorem contMDiffAt_twoHandleChartInv (a : ℝ) (j : Fin 5) :
    ∀ y ∈ twoHandleChartTarget a j, twoHandleChartInv j y.val ∉ twoHandleRim →
      ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞
        (fun y : EuclideanHalfSpace 3 => twoHandleChartInv j y.val) y := by
  fin_cases j
  · exact fun y _ _ => contMDiffAt_slabChartInv 1 2 y
  · exact fun y _ _ => contMDiffAt_slabChartInv 1 1 y
  · exact fun y _ _ => contMDiffAt_slabChartInv (-1) 1 y
  · intro y hy hne
    exact contMDiffAt_cornerModelInv contDiff_twoHandleBottomLinv
      (twoHandleCornerDomain_bottom_pos a) y hy fun h => hne (mem_twoHandleRim_of_eq_bottomLinv h)
  · intro y hy hne
    exact contMDiffAt_cornerModelInv contDiff_twoHandleTopLinv
      (twoHandleCornerDomain_top_pos a) y hy fun h => hne (mem_twoHandleRim_of_eq_topLinv h)

theorem contDiffAt_twoHandleChartVec {a : ℝ} (ha2 : a ≤ 1 / 2) (j : Fin 5) :
    ∀ p ∈ twoHandleChartSource a j, p ∈ Metric.closedBall 0 1 ∪ twoHandleCollar a →
      p ∉ twoHandleRim → ContDiffAt ℝ ∞ (twoHandleChartVec j) p := by
  fin_cases j
  · exact fun p _ _ _ => (contDiff_slabChartVec 1 2).contDiffAt
  · exact fun p _ _ _ => (contDiff_slabChartVec 1 1).contDiffAt
  · exact fun p _ _ _ => (contDiff_slabChartVec (-1) 1).contDiffAt
  · intro p hp hW hne
    exact contDiffAt_cornerModelVec contDiff_twoHandleBottomL twoHandleBottomLinv_L
      (twoHandleBottom_mem_iff ha2) p hp hW fun h => hne (mem_twoHandleRim_of_eq_bottomLinv h)
  · intro p hp hW hne
    exact contDiffAt_cornerModelVec contDiff_twoHandleTopL twoHandleTopLinv_L
      (twoHandleTop_mem_iff ha2) p hp hW fun h => hne (mem_twoHandleRim_of_eq_topLinv h)

theorem twoHandleChart_rim (a : ℝ) (j : Fin 5) :
    ∀ p ∈ twoHandleChartSource a j, p ∈ twoHandleRim → j = twoHandleRimIndex p := by
  fin_cases j
  · rintro p (⟨-, h2⟩ | ⟨h1, -⟩) ⟨h3, h4⟩
    · rw [h4] at h2
      norm_num at h2
    · rw [h3] at h1
      norm_num at h1
  · rintro p ⟨h1, -⟩ ⟨h3, -⟩
    rw [h3] at h1
    norm_num at h1
  · rintro p ⟨h1, -⟩ ⟨h3, -⟩
    rw [h3] at h1
    norm_num at h1
  · rintro p ⟨-, -, -, h2⟩ -
    simp only [twoHandleBottomL] at h2
    have hs : p.2 < 0 := by linarith
    exact (ite_eq_left hs).symm
  · rintro p ⟨-, -, -, h1⟩ -
    simp only [twoHandleTopL] at h1
    have hs : ¬ p.2 < 0 := by linarith
    exact (ite_eq_right hs).symm

theorem twoHandleChart_cover {a : ℝ} (ha : 0 < a) {p : EuclideanSpace ℝ (Fin 2) × ℝ}
    (hp : p ∈ Metric.closedBall 0 1) : ∃ j, p ∈ twoHandleChartSource a j := by
  obtain ⟨hw, hs⟩ := mem_closedBall_zero_prod_iff.mp hp
  by_cases hs1 : |p.2| < 1
  · exact ⟨0, Or.inl ⟨by linarith, hs1⟩⟩
  have hs2 : |p.2| = 1 := le_antisymm hs (not_lt.mp hs1)
  rcases (abs_eq (zero_le_one' ℝ)).mp hs2 with h | h
  · by_cases hw3 : ‖p.1‖ < 3 / 4
    · exact ⟨2, hw3, by linarith⟩
    · have hne : p.1 ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hw3
        norm_num at hw3
      refine ⟨4, hne, ⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [twoHandleTopL, h] <;> linarith
  · by_cases hw3 : ‖p.1‖ < 3 / 4
    · exact ⟨1, hw3, by linarith⟩
    · have hne : p.1 ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hw3
        norm_num at hw3
      refine ⟨3, hne, ⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [twoHandleBottomL, h] <;> linarith

theorem twoHandleChart_zero_coord_eq_zero_iff {a : ℝ} (ha2 : a ≤ 1 / 2) (j : Fin 5) :
    ∀ p ∈ twoHandleChartSource a j, p ∈ Metric.closedBall 0 1 →
      (twoHandleChartVec j p 0 = 0 ↔ |p.2| = 1) := by
  fin_cases j
  · rintro p (⟨-, h2⟩ | ⟨h1, -⟩) hp
    · obtain ⟨h3, -⟩ := abs_lt.mp h2
      change 1 * p.2 + 2 = 0 ↔ _
      constructor
      · intro h
        linarith
      · intro h
        rw [h] at h2
        norm_num at h2
    · have := (mem_closedBall_zero_prod_iff.mp hp).1
      exfalso
      linarith
  · rintro p ⟨-, h2⟩ hp
    have h3 := (mem_closedBall_zero_prod_iff.mp hp).2
    change 1 * p.2 + 1 = 0 ↔ _
    rw [abs_of_neg h2]
    constructor <;> intro h <;> linarith
  · rintro p ⟨-, h2⟩ hp
    have h3 := (mem_closedBall_zero_prod_iff.mp hp).2
    change -1 * p.2 + 1 = 0 ↔ _
    rw [abs_of_pos h2]
    constructor <;> intro h <;> linarith
  · intro p hp hpb
    have hQ := (twoHandleBottom_mem_iff ha2 p hp).mp (Or.inl hpb)
    obtain ⟨hw, hs⟩ := mem_closedBall_zero_prod_iff.mp hpb
    obtain ⟨-, -, h3, h4⟩ := hp
    simp only [twoHandleBottomL] at h3 h4
    change cornerChartVec (twoHandleBottomL (‖p.1‖, p.2)).1 (twoHandleBottomL (‖p.1‖, p.2)).2
      (‖p.1‖⁻¹ • p.1) 0 = 0 ↔ _
    rw [cornerChartVec_zero_coord_eq_zero_iff hQ]
    simp only [twoHandleBottomL]
    obtain ⟨hs1, -⟩ := abs_le.mp hs
    rw [abs_of_neg (by linarith : p.2 < 0)]
    constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩) <;> linarith
    · intro h
      exact Or.inr ⟨by linarith, by linarith⟩
  · intro p hp hpb
    have hQ := (twoHandleTop_mem_iff ha2 p hp).mp (Or.inl hpb)
    obtain ⟨hw, hs⟩ := mem_closedBall_zero_prod_iff.mp hpb
    obtain ⟨-, -, h3, h4⟩ := hp
    simp only [twoHandleTopL] at h3 h4
    change cornerChartVec (twoHandleTopL (‖p.1‖, p.2)).1 (twoHandleTopL (‖p.1‖, p.2)).2
      (‖p.1‖⁻¹ • p.1) 0 = 0 ↔ _
    rw [cornerChartVec_zero_coord_eq_zero_iff hQ]
    simp only [twoHandleTopL]
    obtain ⟨-, hs2⟩ := abs_le.mp hs
    rw [abs_of_pos (by linarith : 0 < p.2)]
    constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩) <;> linarith
    · intro h
      exact Or.inr ⟨by linarith, by linarith⟩

theorem isSmoothHandleStage_adjunction_of_twoHandleCollar
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [CompactSpace M]
    {A P : Type} [TopologicalSpace A] [TopologicalSpace P] [CompactSpace A] [CompactSpace P]
    [T2Space P] {i : A → P} (hi : IsClosedEmbedding i) {ψ : A → M} (hψ : IsClosedEmbedding ψ)
    {Ext : P → EuclideanSpace ℝ (Fin 2) × ℝ} (hExt : IsClosedEmbedding Ext)
    (hExtr : range Ext = Metric.closedBall 0 1) (hExti : ∀ b, ‖(Ext b).1‖ = 1 ↔ b ∈ range i)
    {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) {V : Set M} (hV : IsOpen V)
    {θ : M → EuclideanSpace ℝ (Fin 2) × ℝ} {Θ : EuclideanSpace ℝ (Fin 2) × ℝ → M}
    (hθV : MapsTo θ V (twoHandleCollar a)) (hΘO : MapsTo Θ (twoHandleCollar a) V)
    (hΘθ : ∀ m ∈ V, Θ (θ m) = m) (hθΘ : ∀ p ∈ twoHandleCollar a, θ (Θ p) = p)
    (hΘi : ∀ z, Θ (Ext (i z)) = ψ z)
    (hθs : ContMDiffOn (𝓡∂ 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞ θ V)
    (hΘs : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) (𝓡∂ 3) ∞ Θ (twoHandleCollar a)) :
    IsSmoothHandleStage (AdjunctionSpace i ψ)
      (adjunctionLower ψ '' ((𝓡∂ 3).boundary M \ range ψ) ∪
        adjunctionCell i ψ '' {b | |(Ext b).2| = 1}) := by
  have hExtball : ∀ b, Ext b ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2) × ℝ) 1 :=
    fun b => hExtr ▸ mem_range_self b
  have hWeq : range Ext ∪ twoHandleCollar a = Metric.closedBall 0 1 ∪ twoHandleCollar a := by
    rw [hExtr]
  refine isSmoothHandleStage_adjunction_of_modelCharts hi hψ hExt ?_ ?_ ?_ hV hθV hΘO hΘθ hθΘ
    hΘi hθs hΘs (twoHandleChartSource a) (isOpen_twoHandleChartSource a)
    (twoHandleChartTarget a) (isOpen_twoHandleChartTarget a) twoHandleChartVec twoHandleChartInv
    ?_ ?_ ?_ (twoHandleChart_right a) ?_ (continuousOn_twoHandleChartInv a) (Rim := twoHandleRim)
    ?_ (contMDiffAt_twoHandleChartInv a) ?_ twoHandleRimIndex (twoHandleChart_rim a) ?_ ?_
  · rintro p hp ⟨b, rfl⟩
    have h1 : ‖(Ext b).1‖ = 1 :=
      le_antisymm (mem_closedBall_zero_prod_iff.mp (hExtball b)).1 hp.1
    obtain ⟨z, rfl⟩ := (hExti b).mp h1
    exact ⟨z, rfl⟩
  · intro z
    have h1 : ‖(Ext (i z)).1‖ = 1 := (hExti _).mpr ⟨z, rfl⟩
    have h2 := (mem_closedBall_zero_prod_iff.mp (hExtball (i z))).2
    exact ⟨h1.ge, by linarith, by linarith⟩
  · rw [hExtr]
    rintro p ⟨hpc, hpb⟩
    have hn : Continuous (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => ‖p.1‖) :=
      continuous_norm.comp continuous_fst
    have hs : Continuous (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => |p.2|) :=
      continuous_abs.comp continuous_snd
    have hcl : IsClosed {p : EuclideanSpace ℝ (Fin 2) × ℝ |
        1 ≤ ‖p.1‖ ∧ ‖p.1‖ ≤ 1 + a ∧ |p.2| ≤ 3 / 2} :=
      (isClosed_le continuous_const hn).inter
        ((isClosed_le hn continuous_const).inter (isClosed_le hs continuous_const))
    have hsub : closure (twoHandleCollar a) ⊆ {p : EuclideanSpace ℝ (Fin 2) × ℝ |
        1 ≤ ‖p.1‖ ∧ ‖p.1‖ ≤ 1 + a ∧ |p.2| ≤ 3 / 2} :=
      closure_minimal (fun q hq => ⟨hq.1, hq.2.1.le, hq.2.2.le⟩) hcl
    obtain ⟨h1, -, -⟩ := hsub hpc
    obtain ⟨h3, h4⟩ := mem_closedBall_zero_prod_iff.mp hpb
    exact ⟨h1, by linarith, by linarith⟩
  · rw [hWeq]
    exact twoHandleChart_mem ha2
  · rw [hWeq]
    exact twoHandleChart_inv_mem ha2
  · rw [hWeq]
    exact twoHandleChart_left ha2
  · rw [hWeq]
    exact continuousOn_twoHandleChartVec ha2
  · rw [hExtr]
    intro p hp
    exact mem_closedBall_zero_prod_iff.mpr ⟨hp.1.le, hp.2.le⟩
  · rw [hWeq]
    exact contDiffAt_twoHandleChartVec ha2
  · intro b
    exact twoHandleChart_cover ha (hExtball b)
  · intro j b hj
    exact twoHandleChart_zero_coord_eq_zero_iff ha2 j (Ext b) hj (hExtball b)

end DifferentialGeometry.Topology.PiecewiseLinear

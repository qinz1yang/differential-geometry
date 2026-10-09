/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.TwoHandleModelAttachment

open Set Complex Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

def oneHandleCollar (a : ℝ) : Set (EuclideanSpace ℝ (Fin 2) × ℝ) :=
  {p | ‖p.1‖ < 3 / 2 ∧ ((-1 - a < p.2 ∧ p.2 ≤ -1) ∨ (1 ≤ p.2 ∧ p.2 < 1 + a))}

def oneHandleInterior (a : ℝ) : Set (EuclideanSpace ℝ (Fin 2) × ℝ) :=
  {p | (‖p.1‖ < 1 ∧ |p.2| < 1 + a) ∨ (‖p.1‖ < 3 / 2 ∧ 1 < |p.2| ∧ |p.2| < 1 + a)}

def oneHandleCornerDomain (a : ℝ) : Set (ℝ × ℝ) :=
  Ioo (-(3 / 4)) (a / 2) ×ˢ Ioo (-(1 / 4)) (1 / 4)

noncomputable def oneHandleBottomL (q : ℝ × ℝ) : ℝ × ℝ := ((-1 - q.2) / 2, (1 - q.1) / 2)

def oneHandleBottomLinv (q : ℝ × ℝ) : ℝ × ℝ := (1 - 2 * q.2, -1 - 2 * q.1)

noncomputable def oneHandleTopL (q : ℝ × ℝ) : ℝ × ℝ := ((q.2 - 1) / 2, (1 - q.1) / 2)

def oneHandleTopLinv (q : ℝ × ℝ) : ℝ × ℝ := (1 - 2 * q.2, 1 + 2 * q.1)

noncomputable def oneHandleRimIndex (p : EuclideanSpace ℝ (Fin 2) × ℝ) : Fin 3 :=
  if p.2 < 0 then 1 else 2

def oneHandleChartSource (a : ℝ) : Fin 3 → Set (EuclideanSpace ℝ (Fin 2) × ℝ) :=
  ![oneHandleInterior a, cornerModelSource oneHandleBottomL (oneHandleCornerDomain a),
    cornerModelSource oneHandleTopL (oneHandleCornerDomain a)]

def oneHandleChartTarget (a : ℝ) : Fin 3 → Set (EuclideanHalfSpace 3) :=
  ![slabChartTarget 1 2 (oneHandleInterior a), cornerModelTarget (oneHandleCornerDomain a),
    cornerModelTarget (oneHandleCornerDomain a)]

noncomputable def oneHandleChartVec :
    Fin 3 → EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3) :=
  ![slabChartVec 1 2, cornerModelVec oneHandleBottomL, cornerModelVec oneHandleTopL]

noncomputable def oneHandleChartInv :
    Fin 3 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 2) × ℝ :=
  ![slabChartInv 1 2, cornerModelInv oneHandleBottomLinv, cornerModelInv oneHandleTopLinv]

theorem contDiff_oneHandleBottomL : ContDiff ℝ ∞ oneHandleBottomL :=
  ((contDiff_const.sub contDiff_snd).div_const 2).prodMk
    ((contDiff_const.sub contDiff_fst).div_const 2)

theorem contDiff_oneHandleBottomLinv : ContDiff ℝ ∞ oneHandleBottomLinv :=
  (contDiff_const.sub (contDiff_const.mul contDiff_snd)).prodMk
    (contDiff_const.sub (contDiff_const.mul contDiff_fst))

theorem contDiff_oneHandleTopL : ContDiff ℝ ∞ oneHandleTopL :=
  ((contDiff_snd.sub contDiff_const).div_const 2).prodMk
    ((contDiff_const.sub contDiff_fst).div_const 2)

theorem contDiff_oneHandleTopLinv : ContDiff ℝ ∞ oneHandleTopLinv :=
  (contDiff_const.sub (contDiff_const.mul contDiff_snd)).prodMk
    (contDiff_const.add (contDiff_const.mul contDiff_fst))

theorem oneHandleBottomL_Linv (q : ℝ × ℝ) : oneHandleBottomL (oneHandleBottomLinv q) = q := by
  simp only [oneHandleBottomL, oneHandleBottomLinv]
  ext <;> ring

theorem oneHandleBottomLinv_L (q : ℝ × ℝ) : oneHandleBottomLinv (oneHandleBottomL q) = q := by
  simp only [oneHandleBottomL, oneHandleBottomLinv]
  ext <;> ring

theorem oneHandleTopL_Linv (q : ℝ × ℝ) : oneHandleTopL (oneHandleTopLinv q) = q := by
  simp only [oneHandleTopL, oneHandleTopLinv]
  ext <;> ring

theorem oneHandleTopLinv_L (q : ℝ × ℝ) : oneHandleTopLinv (oneHandleTopL q) = q := by
  simp only [oneHandleTopL, oneHandleTopLinv]
  ext <;> ring

theorem oneHandleCornerDomain_norm_lt {a : ℝ} (ha2 : a ≤ 1 / 2) :
    ∀ q ∈ oneHandleCornerDomain a, ‖((q.1 : ℂ) + q.2 * I)‖ < 1 := by
  rintro q ⟨⟨h1, h2⟩, h3, h4⟩
  apply norm_ofReal_add_mul_I_lt_one
  have e1 : |q.1| < 3 / 4 := abs_lt.mpr ⟨h1, by linarith⟩
  have e2 : |q.2| < 1 / 4 := abs_lt.mpr ⟨h3, h4⟩
  linarith

theorem oneHandleCornerDomain_bottom_pos (a : ℝ) :
    ∀ q ∈ oneHandleCornerDomain a, 0 < (oneHandleBottomLinv q).1 := by
  rintro q ⟨-, -, h4⟩
  change 0 < 1 - 2 * q.2
  linarith

theorem oneHandleCornerDomain_top_pos (a : ℝ) :
    ∀ q ∈ oneHandleCornerDomain a, 0 < (oneHandleTopLinv q).1 := by
  rintro q ⟨-, -, h4⟩
  change 0 < 1 - 2 * q.2
  linarith

theorem isOpen_oneHandleCornerDomain (a : ℝ) : IsOpen (oneHandleCornerDomain a) :=
  isOpen_Ioo.prod isOpen_Ioo

theorem oneHandleInterior_mem_iff {a : ℝ} (ha2 : a ≤ 1 / 2) :
    ∀ p ∈ oneHandleInterior a, (p ∈ Metric.closedBall 0 1 ∪ oneHandleCollar a ↔
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
    · obtain ⟨h2a, h2b⟩ := abs_lt.mp h2
      by_cases hs : |p.2| ≤ 1
      · exact Or.inl ⟨h1.le, hs⟩
      · right
        refine ⟨by linarith, ?_⟩
        rcases lt_abs.mp (not_le.mp hs) with h | h
        · exact Or.inr ⟨h.le, h2b⟩
        · exact Or.inl ⟨by linarith, by linarith⟩
    · obtain ⟨h3a, h3b⟩ := abs_lt.mp h3
      right
      refine ⟨h1, ?_⟩
      rcases lt_abs.mp h2 with h | h
      · exact Or.inr ⟨h.le, h3b⟩
      · exact Or.inl ⟨by linarith, by linarith⟩

theorem oneHandleBottom_mem_iff {a : ℝ} (ha2 : a ≤ 1 / 2) :
    ∀ p ∈ cornerModelSource oneHandleBottomL (oneHandleCornerDomain a),
      (p ∈ Metric.closedBall 0 1 ∪ oneHandleCollar a ↔
        ((oneHandleBottomL (‖p.1‖, p.2)).1 : ℂ) + (oneHandleBottomL (‖p.1‖, p.2)).2 * I ∈
          concaveQuadrant) := by
  rintro p ⟨-, ⟨h1, h2⟩, h3, h4⟩
  simp only [oneHandleBottomL] at h1 h2 h3 h4
  rw [ofReal_add_mul_I_mem_concaveQuadrant_iff, mem_union, mem_closedBall_zero_prod_iff]
  simp only [oneHandleBottomL]
  constructor
  · rintro (⟨h5, -⟩ | ⟨-, ⟨-, h5⟩ | ⟨h5, -⟩⟩)
    · right
      linarith
    · left
      linarith
    · exfalso
      linarith
  · rintro (h5 | h5)
    · exact Or.inr ⟨by linarith, Or.inl ⟨by linarith, by linarith⟩⟩
    · by_cases hs : -1 ≤ p.2
      · exact Or.inl ⟨by linarith, abs_le.mpr ⟨hs, by linarith⟩⟩
      · exact Or.inr ⟨by linarith, Or.inl ⟨by linarith, by linarith⟩⟩

theorem oneHandleTop_mem_iff {a : ℝ} (ha2 : a ≤ 1 / 2) :
    ∀ p ∈ cornerModelSource oneHandleTopL (oneHandleCornerDomain a),
      (p ∈ Metric.closedBall 0 1 ∪ oneHandleCollar a ↔
        ((oneHandleTopL (‖p.1‖, p.2)).1 : ℂ) + (oneHandleTopL (‖p.1‖, p.2)).2 * I ∈
          concaveQuadrant) := by
  rintro p ⟨-, ⟨h1, h2⟩, h3, h4⟩
  simp only [oneHandleTopL] at h1 h2 h3 h4
  rw [ofReal_add_mul_I_mem_concaveQuadrant_iff, mem_union, mem_closedBall_zero_prod_iff]
  simp only [oneHandleTopL]
  constructor
  · rintro (⟨h5, -⟩ | ⟨-, ⟨-, h5⟩ | ⟨h5, -⟩⟩)
    · right
      linarith
    · exfalso
      linarith
    · left
      linarith
  · rintro (h5 | h5)
    · exact Or.inr ⟨by linarith, Or.inr ⟨by linarith, by linarith⟩⟩
    · by_cases hs : p.2 ≤ 1
      · exact Or.inl ⟨by linarith, abs_le.mpr ⟨by linarith, hs⟩⟩
      · exact Or.inr ⟨by linarith, Or.inr ⟨by linarith, by linarith⟩⟩

theorem isOpen_oneHandleChartSource (a : ℝ) (j : Fin 3) : IsOpen (oneHandleChartSource a j) := by
  have hn : Continuous (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => ‖p.1‖) :=
    continuous_norm.comp continuous_fst
  have hs : Continuous (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => |p.2|) :=
    continuous_abs.comp continuous_snd
  fin_cases j
  · exact ((isOpen_lt hn continuous_const).inter (isOpen_lt hs continuous_const)).union
      ((isOpen_lt hn continuous_const).inter
        ((isOpen_lt continuous_const hs).inter (isOpen_lt hs continuous_const)))
  · exact isOpen_cornerModelSource contDiff_oneHandleBottomL.continuous
      (isOpen_oneHandleCornerDomain a)
  · exact isOpen_cornerModelSource contDiff_oneHandleTopL.continuous
      (isOpen_oneHandleCornerDomain a)

theorem isOpen_oneHandleChartTarget (a : ℝ) (j : Fin 3) : IsOpen (oneHandleChartTarget a j) := by
  fin_cases j
  · exact isOpen_slabChartTarget 1 2 (isOpen_oneHandleChartSource a 0)
  · exact isOpen_cornerModelTarget (isOpen_oneHandleCornerDomain a)
  · exact isOpen_cornerModelTarget (isOpen_oneHandleCornerDomain a)

theorem oneHandleChart_mem {a : ℝ} (ha2 : a ≤ 1 / 2) (j : Fin 3) :
    ∀ p ∈ oneHandleChartSource a j, p ∈ Metric.closedBall 0 1 ∪ oneHandleCollar a →
      0 ≤ oneHandleChartVec j p 0 ∧
        toHalfSpace (oneHandleChartVec j p) ∈ oneHandleChartTarget a j := by
  fin_cases j
  · exact slabChart_mem (by norm_num) (oneHandleInterior_mem_iff ha2)
  · exact cornerModel_mem (oneHandleCornerDomain_norm_lt ha2) (oneHandleBottom_mem_iff ha2)
  · exact cornerModel_mem (oneHandleCornerDomain_norm_lt ha2) (oneHandleTop_mem_iff ha2)

theorem oneHandleChart_inv_mem {a : ℝ} (ha2 : a ≤ 1 / 2) (j : Fin 3) :
    ∀ y ∈ oneHandleChartTarget a j, oneHandleChartInv j y.val ∈ oneHandleChartSource a j ∧
      oneHandleChartInv j y.val ∈ Metric.closedBall 0 1 ∪ oneHandleCollar a := by
  fin_cases j
  · exact slabChart_inv_mem (by norm_num) (oneHandleInterior_mem_iff ha2)
  · exact cornerModel_inv_mem oneHandleBottomL_Linv (oneHandleCornerDomain_bottom_pos a)
      (oneHandleBottom_mem_iff ha2)
  · exact cornerModel_inv_mem oneHandleTopL_Linv (oneHandleCornerDomain_top_pos a)
      (oneHandleTop_mem_iff ha2)

theorem oneHandleChart_left {a : ℝ} (ha2 : a ≤ 1 / 2) (j : Fin 3) :
    ∀ p ∈ oneHandleChartSource a j, p ∈ Metric.closedBall 0 1 ∪ oneHandleCollar a →
      oneHandleChartInv j (oneHandleChartVec j p) = p := by
  fin_cases j
  · exact fun p _ _ => slabChartInv_vec (by norm_num) 2 p
  · exact cornerModel_left oneHandleBottomLinv_L (oneHandleCornerDomain_norm_lt ha2)
      (oneHandleBottom_mem_iff ha2)
  · exact cornerModel_left oneHandleTopLinv_L (oneHandleCornerDomain_norm_lt ha2)
      (oneHandleTop_mem_iff ha2)

theorem oneHandleChart_right (a : ℝ) (j : Fin 3) :
    ∀ y ∈ oneHandleChartTarget a j, oneHandleChartVec j (oneHandleChartInv j y.val) = y.val := by
  fin_cases j
  · exact fun y _ => slabChartVec_inv (by norm_num) 2 y.val
  · exact cornerModel_right oneHandleBottomL_Linv (oneHandleCornerDomain_bottom_pos a)
  · exact cornerModel_right oneHandleTopL_Linv (oneHandleCornerDomain_top_pos a)

theorem continuousOn_oneHandleChartVec {a : ℝ} (ha2 : a ≤ 1 / 2) (j : Fin 3) :
    ContinuousOn (oneHandleChartVec j)
      (oneHandleChartSource a j ∩ (Metric.closedBall 0 1 ∪ oneHandleCollar a)) := by
  fin_cases j
  · exact (contDiff_slabChartVec 1 2).continuous.continuousOn
  · exact continuousOn_cornerModelVec contDiff_oneHandleBottomL.continuous
      (oneHandleBottom_mem_iff ha2)
  · exact continuousOn_cornerModelVec contDiff_oneHandleTopL.continuous
      (oneHandleTop_mem_iff ha2)

theorem continuousOn_oneHandleChartInv (a : ℝ) (j : Fin 3) :
    ContinuousOn (fun y : EuclideanHalfSpace 3 => oneHandleChartInv j y.val)
      (oneHandleChartTarget a j) := by
  fin_cases j
  · exact ((contDiff_slabChartInv 1 2).continuous.comp continuous_subtype_val).continuousOn
  · exact continuousOn_cornerModelInv contDiff_oneHandleBottomLinv.continuous _
  · exact continuousOn_cornerModelInv contDiff_oneHandleTopLinv.continuous _

theorem mem_twoHandleRim_of_eq_oneHandleBottomLinv {p : EuclideanSpace ℝ (Fin 2) × ℝ}
    (h : (‖p.1‖, p.2) = oneHandleBottomLinv 0) : p ∈ twoHandleRim := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [oneHandleBottomLinv, Prod.fst_zero, Prod.snd_zero] at h1 h2
  refine ⟨by linarith, ?_⟩
  rw [h2]
  norm_num

theorem mem_twoHandleRim_of_eq_oneHandleTopLinv {p : EuclideanSpace ℝ (Fin 2) × ℝ}
    (h : (‖p.1‖, p.2) = oneHandleTopLinv 0) : p ∈ twoHandleRim := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [oneHandleTopLinv, Prod.fst_zero, Prod.snd_zero] at h1 h2
  refine ⟨by linarith, ?_⟩
  rw [h2]
  norm_num

theorem contMDiffAt_oneHandleChartInv (a : ℝ) (j : Fin 3) :
    ∀ y ∈ oneHandleChartTarget a j, oneHandleChartInv j y.val ∉ twoHandleRim →
      ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞
        (fun y : EuclideanHalfSpace 3 => oneHandleChartInv j y.val) y := by
  fin_cases j
  · exact fun y _ _ => contMDiffAt_slabChartInv 1 2 y
  · intro y hy hne
    exact contMDiffAt_cornerModelInv contDiff_oneHandleBottomLinv
      (oneHandleCornerDomain_bottom_pos a) y hy
      fun h => hne (mem_twoHandleRim_of_eq_oneHandleBottomLinv h)
  · intro y hy hne
    exact contMDiffAt_cornerModelInv contDiff_oneHandleTopLinv
      (oneHandleCornerDomain_top_pos a) y hy
      fun h => hne (mem_twoHandleRim_of_eq_oneHandleTopLinv h)

theorem contDiffAt_oneHandleChartVec {a : ℝ} (ha2 : a ≤ 1 / 2) (j : Fin 3) :
    ∀ p ∈ oneHandleChartSource a j, p ∈ Metric.closedBall 0 1 ∪ oneHandleCollar a →
      p ∉ twoHandleRim → ContDiffAt ℝ ∞ (oneHandleChartVec j) p := by
  fin_cases j
  · exact fun p _ _ _ => (contDiff_slabChartVec 1 2).contDiffAt
  · intro p hp hW hne
    exact contDiffAt_cornerModelVec contDiff_oneHandleBottomL oneHandleBottomLinv_L
      (oneHandleBottom_mem_iff ha2) p hp hW
      fun h => hne (mem_twoHandleRim_of_eq_oneHandleBottomLinv h)
  · intro p hp hW hne
    exact contDiffAt_cornerModelVec contDiff_oneHandleTopL oneHandleTopLinv_L
      (oneHandleTop_mem_iff ha2) p hp hW
      fun h => hne (mem_twoHandleRim_of_eq_oneHandleTopLinv h)

theorem oneHandleChart_rim (a : ℝ) (j : Fin 3) :
    ∀ p ∈ oneHandleChartSource a j, p ∈ twoHandleRim → j = oneHandleRimIndex p := by
  fin_cases j
  · rintro p (⟨h1, -⟩ | ⟨-, h2, -⟩) ⟨h3, h4⟩
    · rw [h3] at h1
      norm_num at h1
    · rw [h4] at h2
      norm_num at h2
  · rintro p ⟨-, ⟨h1, -⟩, -⟩ ⟨-, h4⟩
    simp only [oneHandleBottomL] at h1
    have hs : p.2 < 0 := by
      rcases (abs_eq zero_le_one).mp h4 with h | h <;> linarith
    exact (ite_eq_left hs).symm
  · rintro p ⟨-, ⟨h1, -⟩, -⟩ ⟨-, h4⟩
    simp only [oneHandleTopL] at h1
    have hs : ¬ p.2 < 0 := by
      rcases (abs_eq zero_le_one).mp h4 with h | h <;> intro hlt <;> linarith
    exact (ite_eq_right hs).symm

theorem oneHandleChart_cover {a : ℝ} (ha : 0 < a) {p : EuclideanSpace ℝ (Fin 2) × ℝ}
    (hp : p ∈ Metric.closedBall 0 1) : ∃ j, p ∈ oneHandleChartSource a j := by
  obtain ⟨hw, hs⟩ := mem_closedBall_zero_prod_iff.mp hp
  obtain ⟨hs1, hs2⟩ := abs_le.mp hs
  by_cases hw1 : ‖p.1‖ < 1
  · exact ⟨0, Or.inl ⟨hw1, by linarith⟩⟩
  have hw2 : ‖p.1‖ = 1 := le_antisymm hw (not_lt.mp hw1)
  have hne : p.1 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hw2
    norm_num at hw2
  by_cases hs3 : p.2 < 1 / 2
  · refine ⟨1, hne, ⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [oneHandleBottomL, hw2] <;> linarith
  · refine ⟨2, hne, ⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [oneHandleTopL, hw2] <;> linarith

theorem oneHandleChart_zero_coord_eq_zero_iff {a : ℝ} (ha2 : a ≤ 1 / 2) (j : Fin 3) :
    ∀ p ∈ oneHandleChartSource a j, p ∈ Metric.closedBall 0 1 →
      (oneHandleChartVec j p 0 = 0 ↔ ‖p.1‖ = 1) := by
  fin_cases j
  · rintro p (⟨h1, h2⟩ | ⟨-, h2, -⟩) hp
    · change 1 * p.2 + 2 = 0 ↔ _
      constructor
      · intro h
        exfalso
        have := (abs_le.mp (mem_closedBall_zero_prod_iff.mp hp).2).1
        linarith
      · intro h
        rw [h] at h1
        norm_num at h1
    · have := (mem_closedBall_zero_prod_iff.mp hp).2
      exfalso
      linarith
  · intro p hp hpb
    have hQ := (oneHandleBottom_mem_iff ha2 p hp).mp (Or.inl hpb)
    obtain ⟨hw, hs⟩ := mem_closedBall_zero_prod_iff.mp hpb
    obtain ⟨hs1, -⟩ := abs_le.mp hs
    change cornerChartVec (oneHandleBottomL (‖p.1‖, p.2)).1 (oneHandleBottomL (‖p.1‖, p.2)).2
      (‖p.1‖⁻¹ • p.1) 0 = 0 ↔ _
    rw [cornerChartVec_zero_coord_eq_zero_iff hQ]
    simp only [oneHandleBottomL]
    constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩) <;> linarith
    · intro h
      exact Or.inr ⟨by linarith, by linarith⟩
  · intro p hp hpb
    have hQ := (oneHandleTop_mem_iff ha2 p hp).mp (Or.inl hpb)
    obtain ⟨hw, hs⟩ := mem_closedBall_zero_prod_iff.mp hpb
    obtain ⟨-, hs2⟩ := abs_le.mp hs
    change cornerChartVec (oneHandleTopL (‖p.1‖, p.2)).1 (oneHandleTopL (‖p.1‖, p.2)).2
      (‖p.1‖⁻¹ • p.1) 0 = 0 ↔ _
    rw [cornerChartVec_zero_coord_eq_zero_iff hQ]
    simp only [oneHandleTopL]
    constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩) <;> linarith
    · intro h
      exact Or.inr ⟨by linarith, by linarith⟩

theorem isSmoothHandleStage_adjunction_of_oneHandleCollar
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [CompactSpace M]
    {A P : Type} [TopologicalSpace A] [TopologicalSpace P] [CompactSpace A] [CompactSpace P]
    [T2Space P] {i : A → P} (hi : IsClosedEmbedding i) {ψ : A → M} (hψ : IsClosedEmbedding ψ)
    {Ext : P → EuclideanSpace ℝ (Fin 2) × ℝ} (hExt : IsClosedEmbedding Ext)
    (hExtr : range Ext = Metric.closedBall 0 1) (hExti : ∀ b, |(Ext b).2| = 1 ↔ b ∈ range i)
    {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) {V : Set M} (hV : IsOpen V)
    {θ : M → EuclideanSpace ℝ (Fin 2) × ℝ} {Θ : EuclideanSpace ℝ (Fin 2) × ℝ → M}
    (hθV : MapsTo θ V (oneHandleCollar a)) (hΘO : MapsTo Θ (oneHandleCollar a) V)
    (hΘθ : ∀ m ∈ V, Θ (θ m) = m) (hθΘ : ∀ p ∈ oneHandleCollar a, θ (Θ p) = p)
    (hΘi : ∀ z, Θ (Ext (i z)) = ψ z)
    (hθs : ContMDiffOn (𝓡∂ 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞ θ V)
    (hΘs : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) (𝓡∂ 3) ∞ Θ (oneHandleCollar a)) :
    IsSmoothHandleStage (AdjunctionSpace i ψ)
      (adjunctionLower ψ '' ((𝓡∂ 3).boundary M \ range ψ) ∪
        adjunctionCell i ψ '' {b | ‖(Ext b).1‖ = 1}) := by
  have hExtball : ∀ b, Ext b ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2) × ℝ) 1 :=
    fun b => hExtr ▸ mem_range_self b
  have hWeq : range Ext ∪ oneHandleCollar a = Metric.closedBall 0 1 ∪ oneHandleCollar a := by
    rw [hExtr]
  refine isSmoothHandleStage_adjunction_of_modelCharts hi hψ hExt ?_ ?_ ?_ hV hθV hΘO hΘθ hθΘ
    hΘi hθs hΘs (oneHandleChartSource a) (isOpen_oneHandleChartSource a)
    (oneHandleChartTarget a) (isOpen_oneHandleChartTarget a) oneHandleChartVec oneHandleChartInv
    ?_ ?_ ?_ (oneHandleChart_right a) ?_ (continuousOn_oneHandleChartInv a) (Rim := twoHandleRim)
    ?_ (contMDiffAt_oneHandleChartInv a) ?_ oneHandleRimIndex (oneHandleChart_rim a) ?_ ?_
  · rintro p ⟨-, hp⟩ ⟨b, rfl⟩
    have h1 := (abs_le.mp (mem_closedBall_zero_prod_iff.mp (hExtball b)).2)
    have h2 : |(Ext b).2| = 1 := by
      rcases hp with ⟨-, h⟩ | ⟨h, -⟩
      · rw [abs_of_neg (by linarith)]
        linarith
      · rw [abs_of_pos (by linarith)]
        linarith
    obtain ⟨z, rfl⟩ := (hExti b).mp h2
    exact ⟨z, rfl⟩
  · intro z
    have h1 : |(Ext (i z)).2| = 1 := (hExti _).mpr ⟨z, rfl⟩
    have h2 := (mem_closedBall_zero_prod_iff.mp (hExtball (i z))).1
    refine ⟨by linarith, ?_⟩
    rcases (abs_eq zero_le_one).mp h1 with h | h
    · exact Or.inr ⟨h.ge, by linarith⟩
    · exact Or.inl ⟨by linarith, h.le⟩
  · rw [hExtr]
    rintro p ⟨hpc, hpb⟩
    have hn : Continuous (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => ‖p.1‖) :=
      continuous_norm.comp continuous_fst
    have hcl : IsClosed {p : EuclideanSpace ℝ (Fin 2) × ℝ | ‖p.1‖ ≤ 3 / 2 ∧
        ((-1 - a ≤ p.2 ∧ p.2 ≤ -1) ∨ (1 ≤ p.2 ∧ p.2 ≤ 1 + a))} :=
      (isClosed_le hn continuous_const).inter
        (((isClosed_le continuous_const continuous_snd).inter
          (isClosed_le continuous_snd continuous_const)).union
          ((isClosed_le continuous_const continuous_snd).inter
            (isClosed_le continuous_snd continuous_const)))
    have hsub : closure (oneHandleCollar a) ⊆ {p : EuclideanSpace ℝ (Fin 2) × ℝ |
        ‖p.1‖ ≤ 3 / 2 ∧ ((-1 - a ≤ p.2 ∧ p.2 ≤ -1) ∨ (1 ≤ p.2 ∧ p.2 ≤ 1 + a))} := by
      refine closure_minimal (fun q hq => ⟨hq.1.le, ?_⟩) hcl
      rcases hq.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1.le, h2⟩
      · exact Or.inr ⟨h1, h2.le⟩
    obtain ⟨-, h1⟩ := hsub hpc
    obtain ⟨h3, h4⟩ := mem_closedBall_zero_prod_iff.mp hpb
    obtain ⟨h4a, h4b⟩ := abs_le.mp h4
    refine ⟨by linarith, ?_⟩
    rcases h1 with ⟨-, h⟩ | ⟨h, -⟩
    · exact Or.inl ⟨by linarith, h⟩
    · exact Or.inr ⟨h, by linarith⟩
  · rw [hWeq]
    exact oneHandleChart_mem ha2
  · rw [hWeq]
    exact oneHandleChart_inv_mem ha2
  · rw [hWeq]
    exact oneHandleChart_left ha2
  · rw [hWeq]
    exact continuousOn_oneHandleChartVec ha2
  · rw [hExtr]
    intro p hp
    exact mem_closedBall_zero_prod_iff.mpr ⟨hp.1.le, hp.2.le⟩
  · rw [hWeq]
    exact contDiffAt_oneHandleChartVec ha2
  · intro b
    exact oneHandleChart_cover ha (hExtball b)
  · intro j b hj
    exact oneHandleChart_zero_coord_eq_zero_iff ha2 j (Ext b) hj (hExtball b)

end DifferentialGeometry.Topology.PiecewiseLinear

/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchTubeSectors

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem tubeLeafCoord_zero (q : ℝ × ℝ) : tubeLeafCoord 0 q = q.1 := by
  simp [tubeLeafCoord, fourSpokeModelLeaf]

theorem tubeLeafCoord_one (q : ℝ × ℝ) : tubeLeafCoord 1 q = q.2 := by
  simp [tubeLeafCoord, fourSpokeModelLeaf]

theorem tubeLeafCoord_two (q : ℝ × ℝ) : tubeLeafCoord 2 q = -q.1 := by
  simp [tubeLeafCoord, fourSpokeModelLeaf]

theorem tubeLeafCoord_three (q : ℝ × ℝ) : tubeLeafCoord 3 q = -q.2 := by
  simp [tubeLeafCoord, fourSpokeModelLeaf]

theorem tubeLeafCoord_zero_add_one (q : ℝ × ℝ) : tubeLeafCoord (0 + 1) q = q.2 := by
  rw [tubeLeafCoord_add_one]
  simp [fourSpokeModelLeaf]

theorem tubeLeafCoord_one_add_one (q : ℝ × ℝ) : tubeLeafCoord (1 + 1) q = -q.1 := by
  rw [tubeLeafCoord_add_one]
  simp [fourSpokeModelLeaf]

theorem tubeLeafCoord_two_add_one (q : ℝ × ℝ) : tubeLeafCoord (2 + 1) q = -q.2 := by
  rw [tubeLeafCoord_add_one]
  simp [fourSpokeModelLeaf]

theorem tubeLeafCoord_three_add_one (q : ℝ × ℝ) : tubeLeafCoord (3 + 1) q = q.1 := by
  rw [tubeLeafCoord_add_one]
  simp [fourSpokeModelLeaf]

theorem exists_tubeLeafCoord_pos_of_notMem {p : (ℝ × ℝ) × ℝ} (hp : p ∈ tubeCellSphere)
    (hn : ∀ k, p ∉ tubeCellArc k) :
    ∃ j : Fin 4, 0 < tubeLeafCoord j p.1 ∧ 0 < tubeLeafCoord (j + 1) p.1 := by
  have hx : p.1.1 ≠ 0 := fun h => by
    rcases mem_tubeCellArc_union_of_fst_eq_zero hp h with h' | h'
    · exact hn 1 h'
    · exact hn 3 h'
  have hy : p.1.2 ≠ 0 := fun h => by
    rcases mem_tubeCellArc_union_of_snd_eq_zero hp h with h' | h'
    · exact hn 0 h'
    · exact hn 2 h'
  rcases lt_or_gt_of_ne hx with hx' | hx' <;> rcases lt_or_gt_of_ne hy with hy' | hy'
  · exact ⟨2, by rw [tubeLeafCoord_two]; linarith, by rw [tubeLeafCoord_two_add_one]; linarith⟩
  · exact ⟨1, by rw [tubeLeafCoord_one]; linarith, by rw [tubeLeafCoord_one_add_one]; linarith⟩
  · exact ⟨3, by rw [tubeLeafCoord_three]; linarith,
      by rw [tubeLeafCoord_three_add_one]; linarith⟩
  · exact ⟨0, by rw [tubeLeafCoord_zero]; linarith, by rw [tubeLeafCoord_zero_add_one]; linarith⟩

theorem not_tubeLeafCoord_pos_pos_of_ne {j j' : Fin 4} (hjj : j ≠ j') (q : ℝ × ℝ) :
    ¬(0 < tubeLeafCoord j q ∧ 0 < tubeLeafCoord (j + 1) q ∧ 0 < tubeLeafCoord j' q ∧
      0 < tubeLeafCoord (j' + 1) q) := by
  rintro ⟨h1, h2, h3, h4⟩
  rcases fourSpokeIndexCases j with rfl | rfl | rfl | rfl <;>
    rcases fourSpokeIndexCases j' with rfl | rfl | rfl | rfl <;>
    simp only [tubeLeafCoord_zero, tubeLeafCoord_one, tubeLeafCoord_two, tubeLeafCoord_three,
      tubeLeafCoord_zero_add_one, tubeLeafCoord_one_add_one, tubeLeafCoord_two_add_one,
      tubeLeafCoord_three_add_one] at h1 h2 h3 h4 <;>
    first
    | exact absurd rfl hjj
    | linarith

theorem eq_or_eq_add_one_of_mem_tubeSector {m j : Fin 4} {h : ℝ}
    (hmem : (fourSpokeModelLeaf m, h) ∈ tubeSector j) : m = j ∨ m = j + 1 := by
  obtain ⟨-, h1, h2⟩ := hmem
  rcases fourSpokeIndexCases m with rfl | rfl | rfl | rfl <;>
    rcases fourSpokeIndexCases j with rfl | rfl | rfl | rfl <;>
    simp only [tubeLeafCoord_zero, tubeLeafCoord_one, tubeLeafCoord_two, tubeLeafCoord_three,
      tubeLeafCoord_zero_add_one, tubeLeafCoord_one_add_one, tubeLeafCoord_two_add_one,
      tubeLeafCoord_three_add_one, fourSpokeModelLeaf] at h1 h2 <;>
    first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | (exfalso; linarith)

noncomputable def tubeEdgeCoeffA (t : ℝ) : ℝ := if t ≤ 1 / 2 then 1 else 2 - 2 * t

noncomputable def tubeEdgeCoeffB (t : ℝ) : ℝ := if t ≤ 1 / 2 then 2 * t else 1

noncomputable def tubeEdgeParam (k : Fin 4) (h t : ℝ) : (ℝ × ℝ) × ℝ :=
  (tubeEdgeCoeffA t • fourSpokeModelLeaf k + tubeEdgeCoeffB t • fourSpokeModelLeaf (k + 1), h)

def tubeEdge (k : Fin 4) (h : ℝ) : Set ((ℝ × ℝ) × ℝ) := tubeEdgeParam k h '' Icc 0 1

theorem tubeEdgeCoeff_of_le {t : ℝ} (ht : t ≤ 1 / 2) :
    tubeEdgeCoeffA t = 1 ∧ tubeEdgeCoeffB t = 2 * t :=
  ⟨ite_eq_left ht, ite_eq_left ht⟩

theorem tubeEdgeCoeff_of_ge {t : ℝ} (ht : 1 / 2 ≤ t) :
    tubeEdgeCoeffA t = 2 - 2 * t ∧ tubeEdgeCoeffB t = 1 := by
  unfold tubeEdgeCoeffA tubeEdgeCoeffB
  split_ifs with h
  · constructor <;> linarith
  · exact ⟨rfl, rfl⟩

theorem tubeEdgeParam_zero (k : Fin 4) (h : ℝ) :
    tubeEdgeParam k h 0 = (fourSpokeModelLeaf k, h) := by
  obtain ⟨ha, hb⟩ := tubeEdgeCoeff_of_le (t := 0) (by norm_num)
  rw [tubeEdgeParam, ha, hb]
  simp

theorem tubeEdgeParam_one (k : Fin 4) (h : ℝ) :
    tubeEdgeParam k h 1 = (fourSpokeModelLeaf (k + 1), h) := by
  obtain ⟨ha, hb⟩ := tubeEdgeCoeff_of_ge (t := 1) (by norm_num)
  rw [tubeEdgeParam, ha, hb]
  simp

theorem tubeEdgeCoeff_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    tubeEdgeCoeffA t ∈ Icc (0 : ℝ) 1 ∧ tubeEdgeCoeffB t ∈ Icc (0 : ℝ) 1 ∧
      (tubeEdgeCoeffA t = 1 ∨ tubeEdgeCoeffB t = 1) := by
  rcases le_total t (1 / 2) with h | h
  · obtain ⟨ha, hb⟩ := tubeEdgeCoeff_of_le h
    rw [ha, hb]
    exact ⟨⟨zero_le_one, le_rfl⟩, ⟨by linarith [ht.1], by linarith⟩, Or.inl rfl⟩
  · obtain ⟨ha, hb⟩ := tubeEdgeCoeff_of_ge h
    rw [ha, hb]
    exact ⟨⟨by linarith [ht.2], by linarith⟩, ⟨zero_le_one, le_rfl⟩, Or.inr rfl⟩

theorem tubeLeafCoord_leaf_combination (k : Fin 4) (a b : ℝ) :
    tubeLeafCoord k (a • fourSpokeModelLeaf k + b • fourSpokeModelLeaf (k + 1)) = a ∧
      tubeLeafCoord (k + 1) (a • fourSpokeModelLeaf k + b • fourSpokeModelLeaf (k + 1)) = b := by
  rw [tubeLeafCoord_add, tubeLeafCoord_add, tubeLeafCoord_smul, tubeLeafCoord_smul,
    tubeLeafCoord_smul, tubeLeafCoord_smul, tubeLeafCoord_self, tubeLeafCoord_self_add_one,
    tubeLeafCoord_add_one_self, tubeLeafCoord_add_one_add_one]
  constructor <;> ring

theorem injOn_tubeEdgeParam (k : Fin 4) (h : ℝ) : InjOn (tubeEdgeParam k h) (Icc 0 1) := by
  intro t ht s hs hts
  have h1 := congrArg (fun p : (ℝ × ℝ) × ℝ => tubeLeafCoord k p.1) hts
  have h2 := congrArg (fun p : (ℝ × ℝ) × ℝ => tubeLeafCoord (k + 1) p.1) hts
  simp only [tubeEdgeParam, (tubeLeafCoord_leaf_combination k _ _).1,
    (tubeLeafCoord_leaf_combination k _ _).2] at h1 h2
  rcases le_total t (1 / 2) with ht' | ht' <;> rcases le_total s (1 / 2) with hs' | hs'
  · rw [(tubeEdgeCoeff_of_le ht').2, (tubeEdgeCoeff_of_le hs').2] at h2
    linarith
  · rw [(tubeEdgeCoeff_of_le ht').1, (tubeEdgeCoeff_of_ge hs').1] at h1
    rw [(tubeEdgeCoeff_of_le ht').2, (tubeEdgeCoeff_of_ge hs').2] at h2
    linarith
  · rw [(tubeEdgeCoeff_of_ge ht').1, (tubeEdgeCoeff_of_le hs').1] at h1
    rw [(tubeEdgeCoeff_of_ge ht').2, (tubeEdgeCoeff_of_le hs').2] at h2
    linarith
  · rw [(tubeEdgeCoeff_of_ge ht').1, (tubeEdgeCoeff_of_ge hs').1] at h1
    linarith

theorem isPiecewiseAffineOn_tubeEdgeParam (k : Fin 4) (h : ℝ) :
    IsPiecewiseAffineOn (tubeEdgeParam k h) (Icc 0 1) := by
  let r := fourSpokeModelLeaf k
  let r' := fourSpokeModelLeaf (k + 1)
  let A₁ : ℝ →ᵃ[ℝ] (ℝ × ℝ) × ℝ := AffineMap.lineMap (r, h) (r + (2 : ℝ) • r', h)
  let A₂ : ℝ →ᵃ[ℝ] (ℝ × ℝ) × ℝ := AffineMap.lineMap ((2 : ℝ) • r + r', h) (r', h)
  have h₁ : IsPiecewiseAffineOn (tubeEdgeParam k h) (Icc 0 (1 / 2)) := by
    refine (isPiecewiseAffineOn_of_affine_of_isHPolytope A₁ isHPolytope_Icc).congr ?_
    intro t ht
    obtain ⟨ha, hb⟩ := tubeEdgeCoeff_of_le ht.2
    rw [tubeEdgeParam, ha, hb]
    simp only [A₁, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Prod.mk_sub_mk, sub_self,
      Prod.smul_mk, smul_zero, Prod.mk_add_mk, zero_add, add_sub_cancel_left, one_smul, r, r',
      smul_smul]
    rw [add_comm, mul_comm]
  have h₂ : IsPiecewiseAffineOn (tubeEdgeParam k h) (Icc (1 / 2) 1) := by
    refine (isPiecewiseAffineOn_of_affine_of_isHPolytope A₂ isHPolytope_Icc).congr ?_
    intro t ht
    obtain ⟨ha, hb⟩ := tubeEdgeCoeff_of_ge ht.1
    rw [tubeEdgeParam, ha, hb]
    simp only [A₂, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Prod.mk_sub_mk, sub_self,
      Prod.smul_mk, smul_zero, Prod.mk_add_mk, zero_add, one_smul, r, r']
    congr 1
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
      Prod.snd_sub, smul_eq_mul] <;> ring
  have h12 := h₁.union_of_isClosed h₂ isClosed_Icc isClosed_Icc
  rwa [Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)] at h12

theorem isPLHomeomorphOn_tubeEdgeParam (k : Fin 4) (h : ℝ) :
    IsPLHomeomorphOn (tubeEdgeParam k h) (Icc 0 1) (tubeEdge k h) :=
  isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
    (isPiecewiseAffineOn_tubeEdgeParam k h) (injOn_tubeEdgeParam k h).bijOn_image

theorem mem_tubeEdge_iff {k : Fin 4} {h : ℝ} {p : (ℝ × ℝ) × ℝ} :
    p ∈ tubeEdge k h ↔ ∃ a b : ℝ, a ∈ Icc (0 : ℝ) 1 ∧ b ∈ Icc (0 : ℝ) 1 ∧ (a = 1 ∨ b = 1) ∧
      p = (a • fourSpokeModelLeaf k + b • fourSpokeModelLeaf (k + 1), h) := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨ha, hb, hab⟩ := tubeEdgeCoeff_mem ht
    exact ⟨_, _, ha, hb, hab, rfl⟩
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    rcases hab with rfl | rfl
    · refine ⟨b / 2, ⟨by linarith [hb.1], by linarith [hb.2]⟩, ?_⟩
      obtain ⟨h1, h2⟩ := tubeEdgeCoeff_of_le (t := b / 2) (by linarith [hb.2])
      rw [tubeEdgeParam, h1, h2]
      congr 3
      ring
    · refine ⟨1 - a / 2, ⟨by linarith [ha.2], by linarith [ha.1]⟩, ?_⟩
      obtain ⟨h1, h2⟩ := tubeEdgeCoeff_of_ge (t := 1 - a / 2) (by linarith [ha.2])
      rw [tubeEdgeParam, h1, h2]
      congr 3
      ring

theorem leaf_combination_mem_spliceSquareBoundary (k : Fin 4) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hab : a = 1 ∨ b = 1) :
    a • fourSpokeModelLeaf k + b • fourSpokeModelLeaf (k + 1) ∈ spliceSquareBoundary := by
  rw [fourSpokeModelLeaf_add_one, mem_spliceSquareBoundary, mem_spliceSquare]
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  rcases fourSpokeIndexCases k with rfl | rfl | rfl | rfl <;>
    simp only [fourSpokeModelLeaf, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, mul_one, mul_zero,
      neg_zero, mul_neg, add_zero, zero_add] <;>
    refine ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, ?_⟩ <;>
    rcases hab with rfl | rfl <;> simp

theorem tubeEdge_subset_tubeSector (k : Fin 4) {h : ℝ} (hh : h ∈ Icc (0 : ℝ) 1) :
    tubeEdge k h ⊆ tubeSector k := by
  intro p hp
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := mem_tubeEdge_iff.mp hp
  refine ⟨Or.inr ⟨leaf_combination_mem_spliceSquareBoundary k ha hb hab, hh⟩, ?_, ?_⟩
  · rw [(tubeLeafCoord_leaf_combination k a b).1]
    exact ha.1
  · rw [(tubeLeafCoord_leaf_combination k a b).2]
    exact hb.1

theorem tubeEdge_subset_tubeCellSphere (k : Fin 4) {h : ℝ} (hh : h ∈ Icc (0 : ℝ) 1) :
    tubeEdge k h ⊆ tubeCellSphere := fun _ hp => (tubeEdge_subset_tubeSector k hh hp).1

theorem fourSpokeModelLeaf_mem_tubeCellArc (k : Fin 4) {h : ℝ} (hh : h = 0 ∨ h = 1) :
    (fourSpokeModelLeaf k, h) ∈ tubeCellArc k :=
  mem_tubeMeridian_iff.mpr ⟨1, h, ⟨zero_le_one, le_rfl⟩, by rcases hh with rfl | rfl <;> norm_num,
    Or.inl rfl, by rw [one_smul]⟩

theorem tubeEdge_inter_tubeCellArc (k : Fin 4) {h : ℝ} (hh : h = 0 ∨ h = 1) :
    tubeEdge k h ∩ (tubeCellArc k ∪ tubeCellArc (k + 1)) =
      {(fourSpokeModelLeaf k, h), (fourSpokeModelLeaf (k + 1), h)} := by
  have hh' : h ∈ Icc (0 : ℝ) 1 := by rcases hh with rfl | rfl <;> norm_num
  ext p
  constructor
  · rintro ⟨hp, hA | hA⟩
    · obtain ⟨a, b, ha, hb, hab, rfl⟩ := mem_tubeEdge_iff.mp hp
      have h0 := ((mem_tubeCellArc_iff_tubeLeafCoord k).mp hA).2.1
      rw [(tubeLeafCoord_leaf_combination k a b).2] at h0
      subst h0
      rcases hab with rfl | h1
      · left
        simp
      · norm_num at h1
    · obtain ⟨a, b, ha, hb, hab, rfl⟩ := mem_tubeEdge_iff.mp hp
      have h0 := ((mem_tubeCellArc_iff_tubeLeafCoord (k + 1)).mp hA).2.1
      rw [fin_four_add_one_add_one, tubeLeafCoord_add_two,
        (tubeLeafCoord_leaf_combination k a b).1, neg_eq_zero] at h0
      subst h0
      rcases hab with h1 | rfl
      · norm_num at h1
      · right
        simp
  · rintro (rfl | rfl)
    · exact ⟨⟨0, ⟨le_rfl, zero_le_one⟩, tubeEdgeParam_zero k h⟩,
        Or.inl (fourSpokeModelLeaf_mem_tubeCellArc k hh)⟩
    · exact ⟨⟨1, ⟨zero_le_one, le_rfl⟩, tubeEdgeParam_one k h⟩,
        Or.inr (fourSpokeModelLeaf_mem_tubeCellArc (k + 1) hh)⟩

theorem mem_tubeEdge_of_mem_spliceSquareBoundary {k : Fin 4} {q : ℝ × ℝ} (h : ℝ)
    (hq : q ∈ spliceSquareBoundary) (h1 : 0 ≤ tubeLeafCoord k q)
    (h2 : 0 ≤ tubeLeafCoord (k + 1) q) : (q, h) ∈ tubeEdge k h := by
  rw [mem_spliceSquareBoundary, mem_spliceSquare] at hq
  obtain ⟨⟨⟨hx0, hx1⟩, hy0, hy1⟩, hb⟩ := hq
  refine mem_tubeEdge_iff.mpr ⟨tubeLeafCoord k q, tubeLeafCoord (k + 1) q, ?_, ?_, ?_,
    Prod.ext (eq_tubeLeafCoord_smul_add k q) rfl⟩
  · rcases fourSpokeIndexCases k with rfl | rfl | rfl | rfl <;>
      simp only [tubeLeafCoord_zero, tubeLeafCoord_one, tubeLeafCoord_two, tubeLeafCoord_three,
        mem_Icc] at h1 ⊢ <;>
      constructor <;> linarith
  · rcases fourSpokeIndexCases k with rfl | rfl | rfl | rfl <;>
      simp only [tubeLeafCoord_zero_add_one, tubeLeafCoord_one_add_one,
        tubeLeafCoord_two_add_one, tubeLeafCoord_three_add_one, mem_Icc] at h2 ⊢ <;>
      constructor <;> linarith
  · rcases fourSpokeIndexCases k with rfl | rfl | rfl | rfl <;>
      simp only [tubeLeafCoord_zero, tubeLeafCoord_one, tubeLeafCoord_two, tubeLeafCoord_three,
        tubeLeafCoord_zero_add_one, tubeLeafCoord_one_add_one, tubeLeafCoord_two_add_one,
        tubeLeafCoord_three_add_one] at h1 h2 ⊢ <;>
      rcases hb with hb | hb | hb | hb <;>
      first
      | (left; linarith)
      | (right; linarith)

theorem iUnion_tubeEdge (h : ℝ) :
    (⋃ k, tubeEdge k h) = spliceSquareBoundary ×ˢ ({h} : Set ℝ) := by
  apply Subset.antisymm
  · refine iUnion_subset fun k p hp => ?_
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := mem_tubeEdge_iff.mp hp
    exact ⟨leaf_combination_mem_spliceSquareBoundary k ha hb hab, rfl⟩
  · rintro ⟨q, z⟩ ⟨hq, hz⟩
    rw [mem_singleton_iff] at hz
    subst hz
    have hquad : ∃ k : Fin 4, 0 ≤ tubeLeafCoord k q ∧ 0 ≤ tubeLeafCoord (k + 1) q := by
      rcases le_total 0 q.1 with hx | hx <;> rcases le_total 0 q.2 with hy | hy
      · exact ⟨0, by rw [tubeLeafCoord_zero]; exact hx,
          by rw [tubeLeafCoord_zero_add_one]; exact hy⟩
      · exact ⟨3, by rw [tubeLeafCoord_three]; linarith,
          by rw [tubeLeafCoord_three_add_one]; exact hx⟩
      · exact ⟨1, by rw [tubeLeafCoord_one]; exact hy,
          by rw [tubeLeafCoord_one_add_one]; linarith⟩
      · exact ⟨2, by rw [tubeLeafCoord_two]; linarith,
          by rw [tubeLeafCoord_two_add_one]; linarith⟩
    obtain ⟨k, h1, h2⟩ := hquad
    exact mem_iUnion.mpr ⟨k, mem_tubeEdge_of_mem_spliceSquareBoundary z hq h1 h2⟩

end DifferentialGeometry.Topology.PiecewiseLinear

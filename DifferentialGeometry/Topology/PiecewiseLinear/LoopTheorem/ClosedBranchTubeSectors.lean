/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleFourPoints
import DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscutExtension
import DifferentialGeometry.Topology.PiecewiseLinear.FourArcSphere
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchTubeModel

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_param_of_sdiff_eq_inter_isOpen {S J W O : Set E} (hS : IsPLSphere 2 S)
    (hJ : IsPLSphere 1 J) (hJW : J ⊆ W) (hWS : W ⊆ S) (hWc : IsClosed W) (hO : IsOpen O)
    (hWO : W \ J = S ∩ O) (hne : (W \ J).Nonempty) (hne' : (S \ W).Nonempty) :
    ∃ r : (Fin 3 → ℝ) → E, IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) W ∧
      r '' stdSimplexBoundary 2 = J := by
  obtain ⟨D₁, D₂, hU, hI, f₁, f₂, hf₁, hf₂, hb₁, hb₂⟩ :=
    exists_disk_decomposition_of_isPLSphere_one_subset_two hS hJ (hJW.trans hWS)
  have hside : ∀ (D : Set E) (f : (Fin 3 → ℝ) → E), D ⊆ S →
      IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D → f '' stdSimplexBoundary 2 = J →
        D \ J ⊆ O ∨ D \ J ⊆ Wᶜ := by
    intro D f hDS hf hb
    have hc : IsPreconnected (D \ J) := by
      rw [← hb]
      exact hf.isConnected_sdiff_image_stdSimplexBoundary.isPreconnected
    refine isPreconnected_iff_subset_of_disjoint.mp hc O Wᶜ hO hWc.isOpen_compl ?_ ?_
    · intro x hx
      by_cases hxW : x ∈ W
      · have hxO : x ∈ S ∩ O := hWO ▸ ⟨hxW, hx.2⟩
        exact Or.inl hxO.2
      · exact Or.inr hxW
    · ext x
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      intro hx hxO hxW
      have hxWJ : x ∈ W \ J := hWO ▸ ⟨hDS hx.1, hxO⟩
      exact hxW hxWJ.1
  have hD₁S : D₁ ⊆ S := hU ▸ subset_union_left
  have hD₂S : D₂ ⊆ S := hU ▸ subset_union_right
  have hJD₁ : J ⊆ D₁ := hI ▸ inter_subset_left
  have hJD₂ : J ⊆ D₂ := hI ▸ inter_subset_right
  obtain ⟨y, hyS, hyW⟩ := hne'
  obtain ⟨x, hxW, hxJ⟩ := hne
  have hyJ : y ∉ J := fun h => hyW (hJW h)
  have heq : ∀ (Da Db : Set E), Da ∪ Db = S → J ⊆ Da → Da \ J ⊆ O → Db \ J ⊆ Wᶜ →
      Da ⊆ S → W = Da := by
    intro Da Db hDab hJDa hDaO hDbW hDaS
    apply Subset.antisymm
    · intro z hzW
      by_cases hzJ : z ∈ J
      · exact hJDa hzJ
      · rcases (hDab.symm ▸ hWS hzW : z ∈ Da ∪ Db) with hz | hz
        · exact hz
        · exact absurd hzW (hDbW ⟨hz, hzJ⟩)
    · intro z hz
      by_cases hzJ : z ∈ J
      · exact hJW hzJ
      · have hzO : z ∈ S ∩ O := ⟨hDaS hz, hDaO ⟨hz, hzJ⟩⟩
        exact (hWO ▸ hzO : z ∈ W \ J).1
  rcases hside D₁ f₁ hD₁S hf₁ hb₁ with h₁ | h₁ <;> rcases hside D₂ f₂ hD₂S hf₂ hb₂ with h₂ | h₂
  · exfalso
    rcases (hU.symm ▸ hyS : y ∈ D₁ ∪ D₂) with hy | hy
    · exact hyW (hWO ▸ (⟨hyS, h₁ ⟨hy, hyJ⟩⟩ : y ∈ S ∩ O) : y ∈ W \ J).1
    · exact hyW (hWO ▸ (⟨hyS, h₂ ⟨hy, hyJ⟩⟩ : y ∈ S ∩ O) : y ∈ W \ J).1
  · exact ⟨f₁, heq D₁ D₂ hU hJD₁ h₁ h₂ hD₁S ▸ hf₁, hb₁⟩
  · exact ⟨f₂, heq D₂ D₁ ((union_comm _ _).trans hU) hJD₂ h₂ h₁ hD₂S ▸ hf₂, hb₂⟩
  · exfalso
    rcases (hU.symm ▸ hWS hxW : x ∈ D₁ ∪ D₂) with hx | hx
    · exact h₁ ⟨hx, hxJ⟩ hxW
    · exact h₂ ⟨hx, hxJ⟩ hxW

theorem exists_isPLHomeomorphOn_crosscut_move {W J β e : Set E} {u : (Fin 3 → ℝ) → E}
    (hu : IsPLHomeomorphOn u (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) W) (huJ : u '' stdSimplexBoundary 2 = J)
    {γ δ : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) β) (hδ : IsPLHomeomorphOn δ (Icc 0 1) e)
    (hβW : β ⊆ W) (heW : e ⊆ W) (hβJ : β ∩ J = {γ 0, γ 1}) (heJ : e ∩ J = {γ 0, γ 1})
    (h0 : δ 0 = γ 0) (h1 : δ 1 = γ 1) :
    ∃ H : E → E, IsPLHomeomorphOn H W W ∧ EqOn H id J ∧ H '' β = e := by
  have hJ : IsPLSphere 1 J := huJ ▸ hu.isPLSphere_image_stdSimplexBoundary
  have hβ : IsPLBall 1 β := (isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn hγ
  have hmem0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hmem1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hk : IsPLHomeomorphOn (δ ∘ Function.invFunOn γ (Icc 0 1)) β e := hγ.symm.trans hδ
  have hk0 : (δ ∘ Function.invFunOn γ (Icc 0 1)) (γ 0) = γ 0 := by
    simp only [Function.comp_apply, hγ.bijOn.invOn_invFunOn.1 hmem0, h0]
  have hk1 : (δ ∘ Function.invFunOn γ (Icc 0 1)) (γ 1) = γ 1 := by
    simp only [Function.comp_apply, hγ.bijOn.invOn_invFunOn.1 hmem1, h1]
  obtain ⟨f, hf, hfJ, hfβ⟩ := exists_isPLHomeomorphOn_union hJ.isPolyhedron hβ.isPolyhedron
    hJ.isPolyhedron.isPLHomeomorphOn_id hk
    (by
      rw [inter_comm, hβJ]
      rintro x (rfl | rfl)
      · exact hk0.symm
      · exact hk1.symm)
    (by
      rw [inter_comm J β, hβJ, inter_comm J e, heJ]
      rintro y (rfl | rfl)
      · exact ⟨γ 0, Or.inl rfl, rfl⟩
      · exact ⟨γ 1, Or.inr rfl, rfl⟩)
  have hfJ' : f '' J = J := (hfJ.image_eq).trans (image_id J)
  have hfβ' : f '' β = e := hfβ.image_eq.trans hk.image_eq
  obtain ⟨G, hG, hGf⟩ := exists_isPLHomeomorphOn_eqOn_disk_crosscut hu huJ hu huJ hγ hβW
    (by rw [hβJ]) heW hf hfJ' hfβ'
  exact ⟨G, hG, fun x hx => (hGf (Or.inl hx)).trans (hfJ hx),
    (hGf.mono subset_union_right).image_eq.trans hfβ'⟩

end Generic

theorem fourSpokeModelLeaf_add_one (k : Fin 4) :
    fourSpokeModelLeaf (k + 1) = (-(fourSpokeModelLeaf k).2, (fourSpokeModelLeaf k).1) := by
  rcases fourSpokeIndexCases k with rfl | rfl | rfl | rfl
  · change fourSpokeModelLeaf 1 = _
    simp [fourSpokeModelLeaf]
  · change fourSpokeModelLeaf 2 = _
    simp [fourSpokeModelLeaf]
  · change fourSpokeModelLeaf 3 = _
    simp [fourSpokeModelLeaf]
  · change fourSpokeModelLeaf 0 = _
    simp [fourSpokeModelLeaf]

theorem fourSpokeModelLeaf_add_two (k : Fin 4) :
    fourSpokeModelLeaf (k + 2) = -fourSpokeModelLeaf k := by
  rcases fourSpokeIndexCases k with rfl | rfl | rfl | rfl
  · change fourSpokeModelLeaf 2 = _
    simp [fourSpokeModelLeaf]
  · change fourSpokeModelLeaf 3 = _
    simp [fourSpokeModelLeaf]
  · change fourSpokeModelLeaf 0 = _
    simp [fourSpokeModelLeaf]
  · change fourSpokeModelLeaf 1 = _
    simp [fourSpokeModelLeaf]

theorem fourSpokeModelLeaf_add_three (k : Fin 4) :
    fourSpokeModelLeaf (k + 3) = ((fourSpokeModelLeaf k).2, -(fourSpokeModelLeaf k).1) := by
  rcases fourSpokeIndexCases k with rfl | rfl | rfl | rfl
  · change fourSpokeModelLeaf 3 = _
    simp [fourSpokeModelLeaf]
  · change fourSpokeModelLeaf 0 = _
    simp [fourSpokeModelLeaf]
  · change fourSpokeModelLeaf 1 = _
    simp [fourSpokeModelLeaf]
  · change fourSpokeModelLeaf 2 = _
    simp [fourSpokeModelLeaf]

theorem fourSpokeModelLeaf_norm (k : Fin 4) :
    (fourSpokeModelLeaf k).1 * (fourSpokeModelLeaf k).1 +
      (fourSpokeModelLeaf k).2 * (fourSpokeModelLeaf k).2 = 1 := by
  rcases fourSpokeIndexCases k with rfl | rfl | rfl | rfl <;> norm_num [fourSpokeModelLeaf]

theorem fin_four_ne_add_one (k : Fin 4) : k ≠ k + 1 := by
  rcases fourSpokeIndexCases k with rfl | rfl | rfl | rfl <;> decide

theorem fin_four_add_one_add_one (k : Fin 4) : k + 1 + 1 = k + 2 := by
  rw [add_assoc]
  rfl

def tubeLeafCoord (k : Fin 4) (p : ℝ × ℝ) : ℝ :=
  p.1 * (fourSpokeModelLeaf k).1 + p.2 * (fourSpokeModelLeaf k).2

theorem continuous_tubeLeafCoord (k : Fin 4) : Continuous (tubeLeafCoord k) :=
  (continuous_fst.mul continuous_const).add (continuous_snd.mul continuous_const)

theorem tubeLeafCoord_smul (k : Fin 4) (c : ℝ) (p : ℝ × ℝ) :
    tubeLeafCoord k (c • p) = c * tubeLeafCoord k p := by
  simp only [tubeLeafCoord, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem tubeLeafCoord_add (k : Fin 4) (p q : ℝ × ℝ) :
    tubeLeafCoord k (p + q) = tubeLeafCoord k p + tubeLeafCoord k q := by
  simp only [tubeLeafCoord, Prod.fst_add, Prod.snd_add]
  ring

theorem tubeLeafCoord_add_one (k : Fin 4) (p : ℝ × ℝ) :
    tubeLeafCoord (k + 1) p =
      -(p.1 * (fourSpokeModelLeaf k).2) + p.2 * (fourSpokeModelLeaf k).1 := by
  rw [tubeLeafCoord, fourSpokeModelLeaf_add_one]
  ring

theorem tubeLeafCoord_add_two (k : Fin 4) (p : ℝ × ℝ) :
    tubeLeafCoord (k + 2) p = -tubeLeafCoord k p := by
  rw [tubeLeafCoord, fourSpokeModelLeaf_add_two, tubeLeafCoord, Prod.fst_neg, Prod.snd_neg]
  ring

theorem tubeLeafCoord_self (k : Fin 4) : tubeLeafCoord k (fourSpokeModelLeaf k) = 1 :=
  fourSpokeModelLeaf_norm k

theorem tubeLeafCoord_add_one_self (k : Fin 4) :
    tubeLeafCoord (k + 1) (fourSpokeModelLeaf k) = 0 := by
  rw [tubeLeafCoord_add_one]
  ring

theorem tubeLeafCoord_self_add_one (k : Fin 4) :
    tubeLeafCoord k (fourSpokeModelLeaf (k + 1)) = 0 := by
  rw [tubeLeafCoord, fourSpokeModelLeaf_add_one]
  ring

theorem tubeLeafCoord_add_one_add_one (k : Fin 4) :
    tubeLeafCoord (k + 1) (fourSpokeModelLeaf (k + 1)) = 1 := by
  rw [tubeLeafCoord_add_one, fourSpokeModelLeaf_add_one]
  linear_combination fourSpokeModelLeaf_norm k

theorem eq_tubeLeafCoord_smul_add (k : Fin 4) (p : ℝ × ℝ) :
    p = tubeLeafCoord k p • fourSpokeModelLeaf k +
      tubeLeafCoord (k + 1) p • fourSpokeModelLeaf (k + 1) := by
  rw [tubeLeafCoord_add_one, fourSpokeModelLeaf_add_one]
  obtain ⟨x, y⟩ := p
  have hn := fourSpokeModelLeaf_norm k
  refine Prod.ext ?_ ?_
  · simp only [tubeLeafCoord, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    linear_combination (-x) * hn
  · simp only [tubeLeafCoord, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    linear_combination (-y) * hn

theorem smul_fourSpokeModelLeaf_mem_spliceSquare_iff (k : Fin 4) (c : ℝ) :
    c • fourSpokeModelLeaf k ∈ spliceSquare ↔ -1 ≤ c ∧ c ≤ 1 := by
  rw [mem_spliceSquare]
  rcases fourSpokeIndexCases k with rfl | rfl | rfl | rfl <;>
    simp only [fourSpokeModelLeaf, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero, mul_neg] <;>
    constructor <;> intro h <;> first
      | exact ⟨by linarith [h.1.1, h.1.2, h.2.1, h.2.2], by linarith [h.1.1, h.1.2, h.2.1, h.2.2]⟩
      | exact ⟨⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩, by linarith [h.1, h.2],
          by linarith [h.1, h.2]⟩

theorem smul_fourSpokeModelLeaf_mem_spliceSquareBoundary_iff (k : Fin 4) {c : ℝ} (hc : 0 ≤ c) :
    c • fourSpokeModelLeaf k ∈ spliceSquareBoundary ↔ c = 1 := by
  rw [mem_spliceSquareBoundary, smul_fourSpokeModelLeaf_mem_spliceSquare_iff]
  rcases fourSpokeIndexCases k with rfl | rfl | rfl | rfl <;>
    simp only [fourSpokeModelLeaf, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero, mul_neg] <;>
    constructor
  all_goals first
    | (rintro ⟨-, h⟩
       rcases h with h | h | h | h <;> linarith)
    | (rintro rfl
       norm_num)

theorem mem_tubeCellSphere_iff {p : (ℝ × ℝ) × ℝ} :
    p ∈ tubeCellSphere ↔ (p.1 ∈ spliceSquare ∧ (p.2 = 0 ∨ p.2 = 1)) ∨
      (p.1 ∈ spliceSquareBoundary ∧ 0 ≤ p.2 ∧ p.2 ≤ 1) := by
  simp only [tubeCellSphere, mem_union, mem_prod, mem_insert_iff, mem_singleton_iff, mem_Icc]

theorem mem_tubeCellArc_iff_tubeLeafCoord (k : Fin 4) {p : (ℝ × ℝ) × ℝ} :
    p ∈ tubeCellArc k ↔ p ∈ tubeCellSphere ∧ tubeLeafCoord (k + 1) p.1 = 0 ∧
      0 ≤ tubeLeafCoord k p.1 := by
  constructor
  · intro hp
    refine ⟨tubeCellArc_subset_tubeCellSphere k hp, ?_⟩
    obtain ⟨c, z, hc, -, -, rfl⟩ := mem_tubeMeridian_iff.mp hp
    rw [tubeLeafCoord_smul, tubeLeafCoord_smul, tubeLeafCoord_add_one_self, tubeLeafCoord_self]
    exact ⟨mul_zero c, by linarith [hc.1]⟩
  · rintro ⟨hS, h0, hc⟩
    have hp1 : p.1 = tubeLeafCoord k p.1 • fourSpokeModelLeaf k := by
      conv_lhs => rw [eq_tubeLeafCoord_smul_add k p.1, h0, zero_smul, add_zero]
    refine mem_tubeMeridian_iff.mpr ⟨tubeLeafCoord k p.1, p.2, ?_⟩
    rcases mem_tubeCellSphere_iff.mp hS with ⟨hsq, hz⟩ | ⟨hbd, hz0, hz1⟩
    · rw [hp1, smul_fourSpokeModelLeaf_mem_spliceSquare_iff] at hsq
      refine ⟨⟨hc, hsq.2⟩, ?_, Or.inr hz, Prod.ext hp1 rfl⟩
      rcases hz with h | h <;> rw [h] <;> norm_num
    · rw [hp1, smul_fourSpokeModelLeaf_mem_spliceSquareBoundary_iff k hc] at hbd
      refine ⟨⟨hc, hbd.le⟩, ⟨hz0, hz1⟩, Or.inl hbd, Prod.ext hp1 rfl⟩

def tubeSector (k : Fin 4) : Set ((ℝ × ℝ) × ℝ) :=
  tubeCellSphere ∩ {p | 0 ≤ tubeLeafCoord k p.1 ∧ 0 ≤ tubeLeafCoord (k + 1) p.1}

theorem isClosed_tubeCellSphere : IsClosed tubeCellSphere :=
  isPLSphere_tubeCellSphere.isPolyhedron.isCompact.isClosed

theorem isClosed_tubeSector (k : Fin 4) : IsClosed (tubeSector k) :=
  isClosed_tubeCellSphere.inter
    ((isClosed_le continuous_const ((continuous_tubeLeafCoord k).comp continuous_fst)).inter
      (isClosed_le continuous_const ((continuous_tubeLeafCoord (k + 1)).comp continuous_fst)))

theorem tubeCellArc_subset_tubeSector (k : Fin 4) : tubeCellArc k ⊆ tubeSector k := by
  intro p hp
  obtain ⟨hS, h0, hc⟩ := (mem_tubeCellArc_iff_tubeLeafCoord k).mp hp
  exact ⟨hS, hc, h0.ge⟩

theorem tubeCellArc_add_one_subset_tubeSector (k : Fin 4) :
    tubeCellArc (k + 1) ⊆ tubeSector k := by
  intro p hp
  obtain ⟨hS, h0, hc⟩ := (mem_tubeCellArc_iff_tubeLeafCoord (k + 1)).mp hp
  rw [fin_four_add_one_add_one, tubeLeafCoord_add_two, neg_eq_zero] at h0
  exact ⟨hS, h0.ge, hc⟩

theorem tubeSector_sdiff (k : Fin 4) :
    tubeSector k \ (tubeCellArc k ∪ tubeCellArc (k + 1)) =
      tubeCellSphere ∩ {p | 0 < tubeLeafCoord k p.1 ∧ 0 < tubeLeafCoord (k + 1) p.1} := by
  ext p
  constructor
  · rintro ⟨⟨hS, h1, h2⟩, hn⟩
    refine ⟨hS, lt_of_le_of_ne h1 fun h => hn (Or.inr ?_), lt_of_le_of_ne h2 fun h => hn
      (Or.inl ((mem_tubeCellArc_iff_tubeLeafCoord k).mpr ⟨hS, h.symm, h1⟩))⟩
    refine (mem_tubeCellArc_iff_tubeLeafCoord (k + 1)).mpr ⟨hS, ?_, h2⟩
    rw [fin_four_add_one_add_one, tubeLeafCoord_add_two, ← h, neg_zero]
  · rintro ⟨hS, h1, h2⟩
    refine ⟨⟨hS, h1.le, h2.le⟩, ?_⟩
    rintro (h | h)
    · exact h2.ne' ((mem_tubeCellArc_iff_tubeLeafCoord k).mp h).2.1
    · have h' := ((mem_tubeCellArc_iff_tubeLeafCoord (k + 1)).mp h).2.1
      rw [fin_four_add_one_add_one, tubeLeafCoord_add_two, neg_eq_zero] at h'
      exact h1.ne' h'

end DifferentialGeometry.Topology.PiecewiseLinear

/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedra
import Mathlib.Basic.Sign.Defs

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem signType_cases_of_sign {a : ℝ} {s : SignType} :
    (SignType.sign a = s ∨ SignType.sign a = 0) ↔
      (s = 0 → a = 0) ∧ (s = 1 → 0 ≤ a) ∧ (s = -1 → a ≤ 0) := by
  rcases s with _ | _ | _
  · simp [sign_eq_zero_iff]
  · constructor
    · rintro (h | h)
      · exact ⟨fun h0 => by simp at h0, fun h1 => by simp at h1, fun _ => (sign_eq_neg_one_iff.mp
          h).le⟩
      · exact ⟨fun h0 => by simp at h0, fun h1 => by simp at h1, fun _ => (sign_eq_zero_iff.mp
          h).le⟩
    · rintro ⟨-, -, h⟩
      rcases (h rfl).lt_or_eq with h' | h'
      · exact Or.inl (sign_eq_neg_one_iff.mpr h')
      · exact Or.inr (sign_eq_zero_iff.mpr h')
  · constructor
    · rintro (h | h)
      · exact ⟨fun h0 => by simp at h0, fun _ => (sign_eq_one_iff.mp h).le, fun h1 => by simp at h1⟩
      · exact ⟨fun h0 => by simp at h0, fun _ => (sign_eq_zero_iff.mp h).ge,
          fun h1 => by simp at h1⟩
    · rintro ⟨-, h, -⟩
      rcases (h rfl).lt_or_eq with h' | h'
      · exact Or.inl (sign_eq_one_iff.mpr h')
      · exact Or.inr (sign_eq_zero_iff.mpr h'.symm)

theorem isClosed_setOf_imp {X : Type*} [TopologicalSpace X] (p : Prop) {q : X → Prop}
    (hq : IsClosed {y | q y}) : IsClosed {y | p → q y} := by
  by_cases hp : p
  · have h : {y : X | p → q y} = {y | q y} := by
      ext y
      simp [hp]
    rw [h]
    exact hq
  · have h : {y : X | p → q y} = univ := by
      ext y
      simp [hp]
    rw [h]
    exact isClosed_univ

theorem isOpen_setOf_imp {X : Type*} [TopologicalSpace X] (p : Prop) {q : X → Prop}
    (hq : IsOpen {y | q y}) : IsOpen {y | p → q y} := by
  by_cases hp : p
  · have h : {y : X | p → q y} = {y | q y} := by
      ext y
      simp [hp]
    rw [h]
    exact hq
  · have h : {y : X | p → q y} = univ := by
      ext y
      simp [hp]
    rw [h]
    exact isOpen_univ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Cells

variable {ι : Type*} (l : ι → E →ᵃ[ℝ] ℝ)

def SignLE (σ σ' : ι → SignType) : Prop := ∀ k, σ k = σ' k ∨ σ k = 0

theorem SignLE.refl (σ : ι → SignType) : SignLE σ σ := fun _ => Or.inl rfl

theorem SignLE.trans {σ σ' σ'' : ι → SignType} (h : SignLE σ σ') (h' : SignLE σ' σ'') :
    SignLE σ σ'' := fun k => by
  rcases h k with h1 | h1
  · rw [h1]
    exact h' k
  · exact Or.inr h1

theorem SignLE.antisymm {σ σ' : ι → SignType} (h : SignLE σ σ') (h' : SignLE σ' σ) : σ = σ' := by
  funext k
  rcases h k with h1 | h1
  · exact h1
  · rcases h' k with h2 | h2
    · exact h2.symm
    · rw [h1, h2]

noncomputable def signVec (x : E) : ι → SignType := fun k => SignType.sign (l k x)

def openCell (σ : ι → SignType) : Set E := {y | signVec l y = σ}

def closedCell (σ : ι → SignType) : Set E := {y | SignLE (signVec l y) σ}

theorem mem_openCell_iff {σ : ι → SignType} {y : E} : y ∈ openCell l σ ↔ signVec l y = σ := Iff.rfl

theorem mem_closedCell_iff {σ : ι → SignType} {y : E} :
    y ∈ closedCell l σ ↔ SignLE (signVec l y) σ := Iff.rfl

theorem mem_openCell_signVec (x : E) : x ∈ openCell l (signVec l x) := rfl

theorem openCell_subset_closedCell (σ : ι → SignType) : openCell l σ ⊆ closedCell l σ :=
  fun _ hy => hy ▸ SignLE.refl _

theorem closedCell_mono {σ σ' : ι → SignType} (h : SignLE σ σ') :
    closedCell l σ ⊆ closedCell l σ' :=
  fun _ hy => SignLE.trans hy h

theorem closedCell_signVec_subset {σ : ι → SignType} {y : E} (hy : y ∈ closedCell l σ) :
    closedCell l (signVec l y) ⊆ closedCell l σ :=
  closedCell_mono l hy

theorem openCell_signVec_subset {σ : ι → SignType} {y : E} (hy : y ∈ closedCell l σ) :
    openCell l (signVec l y) ⊆ closedCell l σ :=
  (openCell_subset_closedCell l _).trans (closedCell_signVec_subset l hy)

theorem openCell_disjoint {σ σ' : ι → SignType} (h : σ ≠ σ') :
    Disjoint (openCell l σ) (openCell l σ') :=
  Set.disjoint_left.mpr fun _ hy hy' => h (hy.symm.trans hy')

theorem signLE_of_openCell_subset_closedCell {σ σ' : ι → SignType} {x : E} (hx : x ∈ openCell l σ)
    (h : openCell l σ ⊆ closedCell l σ') : SignLE σ σ' :=
  hx ▸ h hx

theorem mem_closedCell_iff_forall {σ : ι → SignType} {y : E} :
    y ∈ closedCell l σ ↔
      ∀ k, (σ k = 0 → l k y = 0) ∧ (σ k = 1 → 0 ≤ l k y) ∧ (σ k = -1 → l k y ≤ 0) := by
  simp only [mem_closedCell_iff, SignLE, signVec, signType_cases_of_sign]

theorem eq_zero_of_mem_closedCell {σ : ι → SignType} {y : E} (hy : y ∈ closedCell l σ) {k : ι}
    (hk : σ k = 0) : l k y = 0 :=
  ((mem_closedCell_iff_forall l).mp hy k).1 hk

theorem combo_mem_openCell {σ : ι → SignType} {p y : E} (hp : p ∈ openCell l σ)
    (hy : y ∈ closedCell l σ) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • p + b • y ∈ openCell l σ := by
  funext k
  have hpk : SignType.sign (l k p) = σ k := congrFun hp k
  have hyk := (mem_closedCell_iff_forall l).mp hy k
  change SignType.sign (l k (a • p + b • y)) = σ k
  rw [Convex.combo_affine_apply hab, smul_eq_mul, smul_eq_mul]
  rcases hσ : σ k with _ | _ | _
  · rw [hσ] at hpk hyk
    rw [sign_eq_zero_iff.mp hpk, hyk.1 rfl]
    simp
  · rw [hσ] at hpk hyk
    have h1 := sign_eq_neg_one_iff.mp hpk
    have h2 := hyk.2.2 rfl
    exact sign_eq_neg_one_iff.mpr (by nlinarith)
  · rw [hσ] at hpk hyk
    have h1 := sign_eq_one_iff.mp hpk
    have h2 := hyk.2.1 rfl
    exact sign_eq_one_iff.mpr (by nlinarith)

theorem convex_closedCell (σ : ι → SignType) : Convex ℝ (closedCell l σ) := by
  intro y hy y' hy' a b ha hb hab
  rw [mem_closedCell_iff_forall] at hy hy' ⊢
  intro k
  rw [Convex.combo_affine_apply hab, smul_eq_mul, smul_eq_mul]
  obtain ⟨h0, h1, h2⟩ := hy k
  obtain ⟨h0', h1', h2'⟩ := hy' k
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [h0 h, h0' h]
    ring
  · nlinarith [h1 h, h1' h]
  · nlinarith [h2 h, h2' h]

theorem exists_ne_zero_eq_zero_of_notMem_openCell {σ : ι → SignType} {y : E}
    (hy : y ∈ closedCell l σ) (hyo : y ∉ openCell l σ) : ∃ k, σ k ≠ 0 ∧ l k y = 0 := by
  by_contra h
  push Not at h
  apply hyo
  funext k
  rcases hy k with h1 | h1
  · exact h1
  · by_cases hσ : σ k = 0
    · rw [hσ]
      exact h1
    · exact absurd (sign_eq_zero_iff.mp h1) (h k hσ)

theorem closedCell_subset_hyperplane {σ : ι → SignType} {k : ι} (hk : σ k = 0) :
    closedCell l σ ⊆ {y | l k y = 0} :=
  fun _ hy => eq_zero_of_mem_closedCell l hy hk

theorem mem_openCell_of_lt {σ : ι → SignType} {p x : E} (hp : p ∈ openCell l σ) {T T' : ℝ}
    (hT : 0 < T) (hlt : T < T') (hy' : p + T' • (x - p) ∈ closedCell l σ) :
    p + T • (x - p) ∈ openCell l σ := by
  have hT' : 0 < T' := hT.trans hlt
  have hcombo : p + T • (x - p) = (1 - T / T') • p + (T / T') • (p + T' • (x - p)) := by
    have hTT : T / T' * T' = T := div_mul_cancel₀ T hT'.ne'
    rw [smul_add, smul_smul, hTT, sub_smul, one_smul]
    abel
  rw [hcombo]
  exact combo_mem_openCell l hp hy' (by rw [sub_pos, div_lt_one hT']; exact hlt)
    (div_nonneg hT.le hT'.le) (by ring)

theorem exit_unique {σ : ι → SignType} {p x : E} (hp : p ∈ openCell l σ) {T T' : ℝ} (hT : 0 < T)
    (hT' : 0 < T') (hy : p + T • (x - p) ∈ closedCell l σ)
    (hy' : p + T' • (x - p) ∈ closedCell l σ) (hyo : p + T • (x - p) ∉ openCell l σ)
    (hyo' : p + T' • (x - p) ∉ openCell l σ) : T = T' := by
  rcases lt_trichotomy T T' with hlt | heq | hgt
  · exact absurd (mem_openCell_of_lt l hp hT hlt hy') hyo
  · exact heq
  · exact absurd (mem_openCell_of_lt l hp hT' hgt hy) hyo'

variable [FiniteDimensional ℝ E]

theorem isClosed_closedCell (σ : ι → SignType) : IsClosed (closedCell l σ) := by
  have h : closedCell l σ = ⋂ k, ({y | σ k = 0 → l k y = 0} ∩ {y | σ k = 1 → 0 ≤ l k y} ∩
      {y | σ k = -1 → l k y ≤ 0}) := by
    ext y
    rw [mem_closedCell_iff_forall, mem_iInter]
    refine forall_congr' fun k => ?_
    simp only [mem_inter_iff, mem_ofPred_eq, and_assoc]
  rw [h]
  refine isClosed_iInter fun k => ?_
  have hc : Continuous (l k) := (l k).continuous_of_finiteDimensional
  exact ((isClosed_setOf_imp _ (isClosed_eq hc continuous_const)).inter
    (isClosed_setOf_imp _ (isClosed_le continuous_const hc))).inter
    (isClosed_setOf_imp _ (isClosed_le hc continuous_const))

theorem exists_extension_of_mem_openCell [Finite ι] {σ : ι → SignType} {p y : E}
    (hp : p ∈ closedCell l σ) (hy : y ∈ openCell l σ) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) δ, y + t • (y - p) ∈ openCell l σ := by
  let g : ι → ℝ → ℝ := fun k t => l k (y + t • (y - p))
  have hg : ∀ k, Continuous (g k) := fun k =>
    (l k).continuous_of_finiteDimensional.comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have hg0 : ∀ k, g k 0 = l k y := fun k => by simp [g]
  let U : Set ℝ := ⋂ k, ({t | σ k = 1 → 0 < g k t} ∩ {t | σ k = -1 → g k t < 0})
  have hU : IsOpen U :=
    isOpen_iInter_of_finite fun k =>
      (isOpen_setOf_imp _ (isOpen_lt continuous_const (hg k))).inter
        (isOpen_setOf_imp _ (isOpen_lt (hg k) continuous_const))
  have h0U : (0 : ℝ) ∈ U := by
    refine mem_iInter.mpr fun k => ?_
    have hyk : SignType.sign (l k y) = σ k := congrFun hy k
    refine ⟨fun h1 => ?_, fun h1 => ?_⟩
    · rw [hg0]
      exact sign_eq_one_iff.mp (hyk.trans h1)
    · rw [hg0]
      exact sign_eq_neg_one_iff.mp (hyk.trans h1)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0U)
  refine ⟨ε / 2, by positivity, fun t ht => ?_⟩
  have htU : t ∈ U := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    linarith [ht.2]
  have htk := mem_iInter.mp htU
  funext k
  change SignType.sign (g k t) = σ k
  rcases hσ : σ k with _ | _ | _
  · have hyk : l k y = 0 := eq_zero_of_mem_closedCell l (openCell_subset_closedCell l σ hy) hσ
    have hpk : l k p = 0 := eq_zero_of_mem_closedCell l hp hσ
    have hlin : (l k).linear (y - p) = 0 := by
      rw [← vsub_eq_sub, (l k).linearMap_vsub, hyk, hpk, vsub_eq_sub, sub_zero]
    have hg : g k t = 0 := by
      simp only [g]
      rw [add_comm, ← vadd_eq_add, (l k).map_vadd, vadd_eq_add, map_smul, hlin, smul_zero,
        zero_add, hyk]
    rw [hg]
    exact sign_zero
  · have h1 : σ k = -1 → g k t < 0 := (htk k).2
    exact sign_neg (h1 hσ)
  · have h1 : σ k = 1 → 0 < g k t := (htk k).1
    exact sign_pos (h1 hσ)

theorem exists_exit_of_mem_openCell [Finite ι] {σ : ι → SignType} (hc : IsCompact (closedCell l σ))
    {p x : E} (hp : p ∈ openCell l σ) (hx : x ∈ closedCell l σ) (hne : x ≠ p) :
    ∃ T : ℝ, 1 ≤ T ∧ p + T • (x - p) ∈ closedCell l σ ∧ p + T • (x - p) ∉ openCell l σ := by
  let S : Set ℝ := {t | p + t • (x - p) ∈ closedCell l σ}
  have hS_closed : IsClosed S :=
    (isClosed_closedCell l σ).preimage (continuous_const.add (continuous_id.smul continuous_const))
  have hxp : 0 < ‖x - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hS_bdd : BddAbove S := by
    obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall p
    refine ⟨R / ‖x - p‖, fun t ht => ?_⟩
    have h := hR ht
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at h
    rw [le_div_iff₀ hxp]
    exact (mul_le_mul_of_nonneg_right (le_abs_self t) hxp.le).trans h
  have h0 : (0 : ℝ) ∈ S := by
    change p + (0 : ℝ) • (x - p) ∈ closedCell l σ
    rw [zero_smul, add_zero]
    exact openCell_subset_closedCell l σ hp
  have h1 : (1 : ℝ) ∈ S := by
    change p + (1 : ℝ) • (x - p) ∈ closedCell l σ
    rw [one_smul, add_sub_cancel]
    exact hx
  have hT : sSup S ∈ S := hS_closed.csSup_mem ⟨0, h0⟩ hS_bdd
  have hT1 : 1 ≤ sSup S := le_csSup hS_bdd h1
  refine ⟨sSup S, hT1, hT, fun hTo => ?_⟩
  obtain ⟨δ, hδ, hext⟩ :=
    exists_extension_of_mem_openCell l (openCell_subset_closedCell l σ hp) hTo
  have hmem : sSup S * (1 + δ) ∈ S := by
    have h := hext δ ⟨hδ.le, le_rfl⟩
    have heq : p + sSup S • (x - p) + δ • (p + sSup S • (x - p) - p) =
        p + (sSup S * (1 + δ)) • (x - p) := by
      rw [add_sub_cancel_left, smul_smul, mul_comm δ, mul_add, mul_one, add_smul, add_assoc]
    rw [heq] at h
    exact openCell_subset_closedCell l σ h
  have := le_csSup hS_bdd hmem
  nlinarith

end Cells

end DifferentialGeometry.Topology.PiecewiseLinear

/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchTubeSectorDisks

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem tubeLeafCoord_neg_of_pos_pos {j m : Fin 4} (hjm : j ≠ m) {q : ℝ × ℝ}
    (h1 : 0 < tubeLeafCoord j q) (h2 : 0 < tubeLeafCoord (j + 1) q) :
    tubeLeafCoord m q < 0 ∨ tubeLeafCoord (m + 1) q < 0 := by
  rcases fourSpokeIndexCases j with rfl | rfl | rfl | rfl <;>
    rcases fourSpokeIndexCases m with rfl | rfl | rfl | rfl <;>
    simp only [tubeLeafCoord_zero, tubeLeafCoord_one, tubeLeafCoord_two, tubeLeafCoord_three,
      tubeLeafCoord_zero_add_one, tubeLeafCoord_one_add_one, tubeLeafCoord_two_add_one,
      tubeLeafCoord_three_add_one] at h1 h2 ⊢ <;>
    first
    | exact absurd rfl hjm
    | (left; linarith)
    | (right; linarith)

theorem exists_subset_tubeSector_of_isPreconnected {U : Set ((ℝ × ℝ) × ℝ)}
    (hU : U ⊆ tubeCellSphere) (hUa : ∀ k, Disjoint U (tubeCellArc k))
    (hconn : IsPreconnected U) (hne : U.Nonempty) : ∃ m, U ⊆ tubeSector m := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨m, hm1, hm2⟩ := exists_tubeLeafCoord_pos_of_notMem (hU hp)
    (fun k hk => disjoint_left.mp (hUa k) hp hk)
  have hu : IsOpen {q : (ℝ × ℝ) × ℝ | 0 < tubeLeafCoord m q.1 ∧ 0 < tubeLeafCoord (m + 1) q.1} :=
    (isOpen_lt continuous_const ((continuous_tubeLeafCoord m).comp continuous_fst)).inter
      (isOpen_lt continuous_const ((continuous_tubeLeafCoord (m + 1)).comp continuous_fst))
  have hv : IsOpen {q : (ℝ × ℝ) × ℝ | tubeLeafCoord m q.1 < 0 ∨ tubeLeafCoord (m + 1) q.1 < 0} :=
    (isOpen_lt ((continuous_tubeLeafCoord m).comp continuous_fst) continuous_const).union
      (isOpen_lt ((continuous_tubeLeafCoord (m + 1)).comp continuous_fst) continuous_const)
  have hdisj : Disjoint
      {q : (ℝ × ℝ) × ℝ | 0 < tubeLeafCoord m q.1 ∧ 0 < tubeLeafCoord (m + 1) q.1}
      {q : (ℝ × ℝ) × ℝ | tubeLeafCoord m q.1 < 0 ∨ tubeLeafCoord (m + 1) q.1 < 0} := by
    rw [disjoint_left]
    rintro q ⟨h1, h2⟩ (h | h) <;> linarith
  have hcover : U ⊆
      {q : (ℝ × ℝ) × ℝ | 0 < tubeLeafCoord m q.1 ∧ 0 < tubeLeafCoord (m + 1) q.1} ∪
        {q : (ℝ × ℝ) × ℝ | tubeLeafCoord m q.1 < 0 ∨ tubeLeafCoord (m + 1) q.1 < 0} := by
    intro q hq
    obtain ⟨j, hj1, hj2⟩ := exists_tubeLeafCoord_pos_of_notMem (hU hq)
      (fun k hk => disjoint_left.mp (hUa k) hq hk)
    by_cases hjm : j = m
    · rw [hjm] at hj1 hj2
      exact Or.inl ⟨hj1, hj2⟩
    · exact Or.inr (tubeLeafCoord_neg_of_pos_pos hjm hj1 hj2)
  have hsub := hconn.subset_left_of_subset_union hu hv hdisj hcover ⟨p, hp, hm1, hm2⟩
  exact ⟨m, fun q hq => ⟨hU hq, (hsub hq).1.le, (hsub hq).2.le⟩⟩

theorem exists_subset_tubeSector_of_arc {P : Set ((ℝ × ℝ) × ℝ)} {π : ℝ → (ℝ × ℝ) × ℝ}
    (hπ : IsPLHomeomorphOn π (Icc 0 1) P) (hPS : P ⊆ tubeCellSphere)
    (hPa : ∀ k, P ∩ tubeCellArc k ⊆ {π 0, π 1}) : ∃ m, P ⊆ tubeSector m := by
  have himg : π '' Icc 0 1 = P := hπ.image_eq
  have hsubP : π '' Ioo 0 1 ⊆ P := by
    rw [← himg]
    exact image_mono Ioo_subset_Icc_self
  have hdis : ∀ k, Disjoint (π '' Ioo 0 1) (tubeCellArc k) := by
    intro k
    rw [disjoint_left]
    rintro _ ⟨t, ht, rfl⟩ hk
    rcases hPa k ⟨hsubP ⟨t, ht, rfl⟩, hk⟩ with h | h
    · have := hπ.bijOn.injOn (Ioo_subset_Icc_self ht) ⟨le_rfl, zero_le_one⟩ h
      linarith [ht.1]
    · have := hπ.bijOn.injOn (Ioo_subset_Icc_self ht) ⟨zero_le_one, le_rfl⟩ h
      linarith [ht.2]
  have hcont : ContinuousOn π (Icc 0 1) := hπ.isPiecewiseAffineOn.continuousOn
  obtain ⟨m, hm⟩ := exists_subset_tubeSector_of_isPreconnected (hsubP.trans hPS) hdis
    (isPreconnected_Ioo.image π (hcont.mono Ioo_subset_Icc_self))
    ⟨π (1 / 2), 1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩
  refine ⟨m, ?_⟩
  have hcl : π '' closure (Ioo 0 1) ⊆ closure (π '' Ioo 0 1) :=
    ContinuousOn.image_closure (by rwa [closure_Ioo zero_ne_one])
  rw [closure_Ioo zero_ne_one, himg] at hcl
  exact hcl.trans (closure_minimal hm (isClosed_tubeSector m))

theorem mem_tubeCellArc_of_inter_eq {C : Set ((ℝ × ℝ) × ℝ)} {c : ℝ} {k : Fin 4}
    (hCa : C ∩ tubeCellArc k = {(fourSpokeModelLeaf k, c)}) :
    (fourSpokeModelLeaf k, c) ∈ C ∧ (fourSpokeModelLeaf k, c) ∈ tubeCellArc k := by
  have h' : (fourSpokeModelLeaf k, c) ∈ C ∩ tubeCellArc k := by
    rw [hCa]
    exact mem_singleton _
  exact h'

theorem eq_of_mem_inter_eq {C : Set ((ℝ × ℝ) × ℝ)} {c : ℝ} {k : Fin 4}
    (hCa : C ∩ tubeCellArc k = {(fourSpokeModelLeaf k, c)}) {p : (ℝ × ℝ) × ℝ} (hp : p ∈ C)
    (hk : p ∈ tubeCellArc k) : p = (fourSpokeModelLeaf k, c) := by
  have h' : p ∈ C ∩ tubeCellArc k := ⟨hp, hk⟩
  rw [hCa] at h'
  exact h'

theorem tubeCrosscut_piece {C P : Set ((ℝ × ℝ) × ℝ)} {c : ℝ}
    (hCa : ∀ k, C ∩ tubeCellArc k = {(fourSpokeModelLeaf k, c)}) (hCS : C ⊆ tubeCellSphere)
    (hPC : P ⊆ C) {π : ℝ → (ℝ × ℝ) × ℝ} (hπ : IsPLHomeomorphOn π (Icc 0 1) P) {i : Fin 4}
    (h0 : π 0 = (fourSpokeModelLeaf i, c)) (h1 : π 1 = (fourSpokeModelLeaf (i + 1), c))
    (hno : ∀ j, (fourSpokeModelLeaf j, c) ∈ P → j = i ∨ j = i + 1) :
    P ⊆ tubeSector i ∧ P ∩ (tubeCellArc i ∪ tubeCellArc (i + 1)) = {π 0, π 1} := by
  have hmem0 : π 0 ∈ P := hπ.bijOn.mapsTo ⟨le_rfl, zero_le_one⟩
  have hmem1 : π 1 ∈ P := hπ.bijOn.mapsTo ⟨zero_le_one, le_rfl⟩
  obtain ⟨m, hm⟩ := exists_subset_tubeSector_of_arc hπ (hPC.trans hCS) (fun k p hp => by
    have hpk := eq_of_mem_inter_eq (hCa k) (hPC hp.1) hp.2
    have hwP : (fourSpokeModelLeaf k, c) ∈ P := hpk ▸ hp.1
    rcases hno k hwP with hk | hk
    · rw [hk] at hpk
      exact Or.inl (hpk.trans h0.symm)
    · rw [hk] at hpk
      exact Or.inr (hpk.trans h1.symm))
  have hmi : m = i := by
    have ha := eq_or_eq_add_one_of_mem_tubeSector (hm (h0 ▸ hmem0))
    have hb := eq_or_eq_add_one_of_mem_tubeSector (hm (h1 ▸ hmem1))
    have key : ∀ a b : Fin 4, (a = b ∨ a = b + 1) → (a + 1 = b ∨ a + 1 = b + 1) → b = a := by
      decide
    exact key i m ha hb
  rw [hmi] at hm
  refine ⟨hm, Subset.antisymm ?_ ?_⟩
  · rintro p ⟨hp, hk | hk⟩
    · exact Or.inl ((eq_of_mem_inter_eq (hCa i) (hPC hp) hk).trans h0.symm)
    · exact Or.inr ((eq_of_mem_inter_eq (hCa (i + 1)) (hPC hp) hk).trans h1.symm)
  · rintro p (rfl | rfl)
    · refine ⟨hmem0, Or.inl ?_⟩
      rw [h0]
      exact (mem_tubeCellArc_of_inter_eq (hCa i)).2
    · refine ⟨hmem1, Or.inr ?_⟩
      rw [h1]
      exact (mem_tubeCellArc_of_inter_eq (hCa (i + 1))).2

theorem false_of_tubeArc_zero_two {C P : Set ((ℝ × ℝ) × ℝ)} {c : ℝ}
    (hCa : ∀ k, C ∩ tubeCellArc k = {(fourSpokeModelLeaf k, c)}) (hCS : C ⊆ tubeCellSphere)
    (hPC : P ⊆ C) {π : ℝ → (ℝ × ℝ) × ℝ} (hπ : IsPLHomeomorphOn π (Icc 0 1) P)
    (h0 : π 0 = (fourSpokeModelLeaf 0, c)) (h1 : π 1 = (fourSpokeModelLeaf 2, c))
    (hn1 : (fourSpokeModelLeaf 1, c) ∉ P) (hn3 : (fourSpokeModelLeaf 3, c) ∉ P) : False := by
  have hmem0 : π 0 ∈ P := hπ.bijOn.mapsTo ⟨le_rfl, zero_le_one⟩
  have hmem1 : π 1 ∈ P := hπ.bijOn.mapsTo ⟨zero_le_one, le_rfl⟩
  obtain ⟨m, hm⟩ := exists_subset_tubeSector_of_arc hπ (hPC.trans hCS) (fun k p hp => by
    have hpk := eq_of_mem_inter_eq (hCa k) (hPC hp.1) hp.2
    have hwP : (fourSpokeModelLeaf k, c) ∈ P := hpk ▸ hp.1
    rcases fourSpokeIndexCases k with rfl | rfl | rfl | rfl
    · exact Or.inl (hpk.trans h0.symm)
    · exact absurd hwP hn1
    · exact Or.inr (hpk.trans h1.symm)
    · exact absurd hwP hn3)
  have ha := eq_or_eq_add_one_of_mem_tubeSector (hm (h0 ▸ hmem0))
  have hb := eq_or_eq_add_one_of_mem_tubeSector (hm (h1 ▸ hmem1))
  have key : ∀ b : Fin 4, ((0 : Fin 4) = b ∨ (0 : Fin 4) = b + 1) →
      ((2 : Fin 4) = b ∨ (2 : Fin 4) = b + 1) → False := by
    decide
  exact key m ha hb

theorem exists_tubeCrosscuts_of_split {C A B' : Set ((ℝ × ℝ) × ℝ)} {c : ℝ}
    (hCa : ∀ k, C ∩ tubeCellArc k = {(fourSpokeModelLeaf k, c)}) (hCS : C ⊆ tubeCellSphere)
    {α β' : ℝ → (ℝ × ℝ) × ℝ} (hα : IsPLHomeomorphOn α (Icc 0 1) A)
    (hβ' : IsPLHomeomorphOn β' (Icc 0 1) B') (hα0 : α 0 = (fourSpokeModelLeaf 0, c))
    (hα1 : α 1 = (fourSpokeModelLeaf 2, c)) (hβ'0 : β' 0 = (fourSpokeModelLeaf 0, c))
    (hβ'1 : β' 1 = (fourSpokeModelLeaf 2, c)) (hU : A ∪ B' = C)
    (hI : A ∩ B' = {(fourSpokeModelLeaf 0, c), (fourSpokeModelLeaf 2, c)}) {s r : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) (hαs : α s = (fourSpokeModelLeaf 1, c))
    (hβr : β' r = (fourSpokeModelLeaf 3, c)) :
    ∃ (B : Fin 4 → Set ((ℝ × ℝ) × ℝ)) (β : Fin 4 → ℝ → (ℝ × ℝ) × ℝ),
      (∀ k, IsPLHomeomorphOn (β k) (Icc 0 1) (B k)) ∧
        (∀ k, β k 0 = (fourSpokeModelLeaf k, c)) ∧
          (∀ k, β k 1 = (fourSpokeModelLeaf (k + 1), c)) ∧ (∀ k, B k ⊆ tubeSector k) ∧
            (∀ k, B k ∩ (tubeCellArc k ∪ tubeCellArc (k + 1)) = {β k 0, β k 1}) ∧
              (∀ k, B k ⊆ C) ∧ C ⊆ ⋃ k, B k := by
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨hr0, hr1⟩ := hr
  have hwinj : ∀ i j : Fin 4, ((fourSpokeModelLeaf i, c) : (ℝ × ℝ) × ℝ) =
      (fourSpokeModelLeaf j, c) → i = j :=
    fun i j h => fourSpokeModelLeaf_injective (congrArg Prod.fst h)
  have hAC : A ⊆ C := hU ▸ subset_union_left
  have hBC : B' ⊆ C := hU ▸ subset_union_right
  have hmemA : ∀ t ∈ Icc (0 : ℝ) 1, α t ∈ A := fun t ht => hα.bijOn.mapsTo ht
  have hmemB : ∀ t ∈ Icc (0 : ℝ) 1, β' t ∈ B' := fun t ht => hβ'.bijOn.mapsTo ht
  have hw3A : (fourSpokeModelLeaf 3, c) ∉ A := fun h => by
    have hmem : (fourSpokeModelLeaf 3, c) ∈ A ∩ B' :=
      ⟨h, hβr ▸ hmemB r ⟨hr0.le, hr1.le⟩⟩
    rw [hI] at hmem
    rcases hmem with h' | h'
    · exact absurd (hwinj 3 0 h') (by decide)
    · exact absurd (hwinj 3 2 h') (by decide)
  have hw1B : (fourSpokeModelLeaf 1, c) ∉ B' := fun h => by
    have hmem : (fourSpokeModelLeaf 1, c) ∈ A ∩ B' :=
      ⟨hαs ▸ hmemA s ⟨hs0.le, hs1.le⟩, h⟩
    rw [hI] at hmem
    rcases hmem with h' | h'
    · exact absurd (hwinj 1 0 h') (by decide)
    · exact absurd (hwinj 1 2 h') (by decide)
  have notMem_image {γ : ℝ → (ℝ × ℝ) × ℝ} {X : Set ((ℝ × ℝ) × ℝ)}
      (hγ : IsPLHomeomorphOn γ (Icc 0 1) X) {a b t : ℝ} (hab : Icc a b ⊆ Icc 0 1)
      (ht : t ∈ Icc (0 : ℝ) 1) (hnt : t ∉ Icc a b) : γ t ∉ γ '' Icc a b := by
    rintro ⟨x, hx, hxt⟩
    exact hnt (hγ.bijOn.injOn (hab hx) ht hxt ▸ hx)
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1I : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hp0 := isPLHomeomorphOn_comp_mul_add_Icc hα le_rfl hs0 hs1.le
  have hp1 := isPLHomeomorphOn_comp_mul_add_Icc hα hs0.le hs1 le_rfl
  have hp2 := isPLHomeomorphOn_comp_one_sub
    (isPLHomeomorphOn_comp_mul_add_Icc hβ' hr0.le hr1 le_rfl)
  have hp3 := isPLHomeomorphOn_comp_one_sub
    (isPLHomeomorphOn_comp_mul_add_Icc hβ' le_rfl hr0 hr1.le)
  have hsub0 : α '' Icc 0 s ⊆ A := fun _ ⟨t, ht, hte⟩ => hte ▸ hmemA t ⟨ht.1, ht.2.trans hs1.le⟩
  have hsub1 : α '' Icc s 1 ⊆ A := fun _ ⟨t, ht, hte⟩ => hte ▸ hmemA t ⟨hs0.le.trans ht.1, ht.2⟩
  have hsub2 : β' '' Icc r 1 ⊆ B' :=
    fun _ ⟨t, ht, hte⟩ => hte ▸ hmemB t ⟨hr0.le.trans ht.1, ht.2⟩
  have hsub3 : β' '' Icc 0 r ⊆ B' := fun _ ⟨t, ht, hte⟩ => hte ▸ hmemB t ⟨ht.1, ht.2.trans hr1.le⟩
  have hn2in0 : (fourSpokeModelLeaf 2, c) ∉ α '' Icc 0 s := by
    rw [← hα1]
    exact notMem_image hα (Icc_subset_Icc le_rfl hs1.le) h1I (fun h => by linarith [h.2])
  have hn0in1 : (fourSpokeModelLeaf 0, c) ∉ α '' Icc s 1 := by
    rw [← hα0]
    exact notMem_image hα (Icc_subset_Icc hs0.le le_rfl) h0I (fun h => by linarith [h.1])
  have hn0in2 : (fourSpokeModelLeaf 0, c) ∉ β' '' Icc r 1 := by
    rw [← hβ'0]
    exact notMem_image hβ' (Icc_subset_Icc hr0.le le_rfl) h0I (fun h => by linarith [h.1])
  have hn2in3 : (fourSpokeModelLeaf 2, c) ∉ β' '' Icc 0 r := by
    rw [← hβ'1]
    exact notMem_image hβ' (Icc_subset_Icc le_rfl hr1.le) h1I (fun h => by linarith [h.2])
  obtain ⟨hS0, hI0⟩ := tubeCrosscut_piece hCa hCS (hsub0.trans hAC) hp0 (i := 0)
    (by simp only [sub_zero, mul_zero, add_zero]; exact hα0)
    (by simp only [sub_zero, mul_one, add_zero]; exact hαs)
    (fun j hj => by
      rcases fourSpokeIndexCases j with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hj hn2in0
      · exact absurd (hsub0 hj) hw3A)
  obtain ⟨hS1, hI1⟩ := tubeCrosscut_piece hCa hCS (hsub1.trans hAC) hp1 (i := 1)
    (by simp only [mul_zero, zero_add]; exact hαs)
    (by simp only [mul_one, sub_add_cancel]; exact hα1)
    (fun j hj => by
      rcases fourSpokeIndexCases j with rfl | rfl | rfl | rfl
      · exact absurd hj hn0in1
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd (hsub1 hj) hw3A)
  obtain ⟨hS2, hI2⟩ := tubeCrosscut_piece hCa hCS (hsub2.trans hBC) hp2 (i := 2)
    (by simp only [sub_zero, mul_one, sub_add_cancel]; exact hβ'1)
    (by simp only [sub_self, mul_zero, zero_add]; exact hβr)
    (fun j hj => by
      rcases fourSpokeIndexCases j with rfl | rfl | rfl | rfl
      · exact absurd hj hn0in2
      · exact absurd (hsub2 hj) hw1B
      · exact Or.inl rfl
      · exact Or.inr rfl)
  obtain ⟨hS3, hI3⟩ := tubeCrosscut_piece hCa hCS (hsub3.trans hBC) hp3 (i := 3)
    (by simp only [sub_zero, mul_one, add_zero]; exact hβr)
    (by simp only [sub_zero, sub_self, mul_zero, add_zero]; exact hβ'0)
    (fun j hj => by
      rcases fourSpokeIndexCases j with rfl | rfl | rfl | rfl
      · exact Or.inr rfl
      · exact absurd (hsub3 hj) hw1B
      · exact absurd hj hn2in3
      · exact Or.inl rfl)
  refine ⟨![α '' Icc 0 s, α '' Icc s 1, β' '' Icc r 1, β' '' Icc 0 r],
    ![fun x => α ((s - 0) * x + 0), fun x => α ((1 - s) * x + s),
      fun x => β' ((1 - r) * (1 - x) + r), fun x => β' ((r - 0) * (1 - x) + 0)],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    rcases fourSpokeIndexCases k with rfl | rfl | rfl | rfl
    · exact hp0
    · exact hp1
    · exact hp2
    · exact hp3
  · intro k
    rcases fourSpokeIndexCases k with rfl | rfl | rfl | rfl
    · change α ((s - 0) * 0 + 0) = _
      simp only [sub_zero, mul_zero, add_zero]
      exact hα0
    · change α ((1 - s) * 0 + s) = _
      simp only [mul_zero, zero_add]
      exact hαs
    · change β' ((1 - r) * (1 - 0) + r) = _
      simp only [sub_zero, mul_one, sub_add_cancel]
      exact hβ'1
    · change β' ((r - 0) * (1 - 0) + 0) = _
      simp only [sub_zero, mul_one, add_zero]
      exact hβr
  · intro k
    rcases fourSpokeIndexCases k with rfl | rfl | rfl | rfl
    · change α ((s - 0) * 1 + 0) = _
      simp only [sub_zero, mul_one, add_zero]
      exact hαs
    · change α ((1 - s) * 1 + s) = _
      simp only [mul_one, sub_add_cancel]
      exact hα1
    · change β' ((1 - r) * (1 - 1) + r) = _
      simp only [sub_self, mul_zero, zero_add]
      exact hβr
    · change β' ((r - 0) * (1 - 1) + 0) = _
      simp only [sub_zero, sub_self, mul_zero, add_zero]
      exact hβ'0
  · intro k
    rcases fourSpokeIndexCases k with rfl | rfl | rfl | rfl
    · exact hS0
    · exact hS1
    · exact hS2
    · exact hS3
  · intro k
    rcases fourSpokeIndexCases k with rfl | rfl | rfl | rfl
    · exact hI0
    · exact hI1
    · exact hI2
    · exact hI3
  · intro k
    rcases fourSpokeIndexCases k with rfl | rfl | rfl | rfl
    · exact hsub0.trans hAC
    · exact hsub1.trans hAC
    · exact hsub2.trans hBC
    · exact hsub3.trans hBC
  · have hA' : A = α '' Icc 0 s ∪ α '' Icc s 1 := by
      rw [← image_union, Icc_union_Icc_eq_Icc hs0.le hs1.le, hα.image_eq]
    have hB' : B' = β' '' Icc 0 r ∪ β' '' Icc r 1 := by
      rw [← image_union, Icc_union_Icc_eq_Icc hr0.le hr1.le, hβ'.image_eq]
    rw [← hU, hA', hB']
    rintro p ((hp | hp) | (hp | hp))
    · exact mem_iUnion.mpr ⟨0, hp⟩
    · exact mem_iUnion.mpr ⟨1, hp⟩
    · exact mem_iUnion.mpr ⟨3, hp⟩
    · exact mem_iUnion.mpr ⟨2, hp⟩

theorem exists_tubeCrosscuts {C : Set ((ℝ × ℝ) × ℝ)} (hC : IsPLSphere 1 C)
    (hCS : C ⊆ tubeCellSphere) {c : ℝ}
    (hCa : ∀ k, C ∩ tubeCellArc k = {(fourSpokeModelLeaf k, c)}) :
    ∃ (B : Fin 4 → Set ((ℝ × ℝ) × ℝ)) (β : Fin 4 → ℝ → (ℝ × ℝ) × ℝ),
      (∀ k, IsPLHomeomorphOn (β k) (Icc 0 1) (B k)) ∧
        (∀ k, β k 0 = (fourSpokeModelLeaf k, c)) ∧
          (∀ k, β k 1 = (fourSpokeModelLeaf (k + 1), c)) ∧ (∀ k, B k ⊆ tubeSector k) ∧
            (∀ k, B k ∩ (tubeCellArc k ∪ tubeCellArc (k + 1)) = {β k 0, β k 1}) ∧
              (∀ k, B k ⊆ C) ∧ C ⊆ ⋃ k, B k := by
  have hwC : ∀ k, (fourSpokeModelLeaf k, c) ∈ C := fun k => (mem_tubeCellArc_of_inter_eq (hCa k)).1
  have hwinj : ∀ i j : Fin 4, ((fourSpokeModelLeaf i, c) : (ℝ × ℝ) × ℝ) =
      (fourSpokeModelLeaf j, c) → i = j :=
    fun i j h => fourSpokeModelLeaf_injective (congrArg Prod.fst h)
  obtain ⟨A, B', α, β', hα, hβ', hα0, hα1, hβ'0, hβ'1, hU, hI⟩ :=
    exists_arc_decomposition_of_isPLSphere_one hC (hwC 0) (hwC 2)
      (fun h => absurd (hwinj 0 2 h) (by decide))
  have hAC : A ⊆ C := hU ▸ subset_union_left
  have hBC : B' ⊆ C := hU ▸ subset_union_right
  have hmid : ∀ {X : Set ((ℝ × ℝ) × ℝ)} {γ : ℝ → (ℝ × ℝ) × ℝ},
      IsPLHomeomorphOn γ (Icc 0 1) X → γ 0 = (fourSpokeModelLeaf 0, c) →
        γ 1 = (fourSpokeModelLeaf 2, c) → ∀ j : Fin 4, j ≠ 0 → j ≠ 2 →
          (fourSpokeModelLeaf j, c) ∈ X → ∃ t ∈ Ioo (0 : ℝ) 1, γ t = (fourSpokeModelLeaf j, c) := by
    intro X γ hγ hγ0 hγ1 j hj0 hj2 hjX
    rw [← hγ.image_eq] at hjX
    obtain ⟨t, ht, hte⟩ := hjX
    refine ⟨t, ⟨lt_of_le_of_ne ht.1 fun h => ?_, lt_of_le_of_ne ht.2 fun h => ?_⟩, hte⟩
    · rw [← h, hγ0] at hte
      exact hj0 (hwinj _ _ hte.symm)
    · rw [h, hγ1] at hte
      exact hj2 (hwinj _ _ hte.symm)
  have hnotboth : ∀ j : Fin 4, j ≠ 0 → j ≠ 2 → (fourSpokeModelLeaf j, c) ∈ A →
      (fourSpokeModelLeaf j, c) ∉ B' := fun j hj0 hj2 hA hB => by
    have hmem : (fourSpokeModelLeaf j, c) ∈ A ∩ B' := ⟨hA, hB⟩
    rw [hI] at hmem
    rcases hmem with h | h
    · exact hj0 (hwinj _ _ h)
    · exact hj2 (hwinj _ _ h)
  have h1 : (fourSpokeModelLeaf 1, c) ∈ A ∪ B' := hU.symm ▸ hwC 1
  have h3 : (fourSpokeModelLeaf 3, c) ∈ A ∪ B' := hU.symm ▸ hwC 3
  rcases h1 with h1A | h1B <;> rcases h3 with h3A | h3B
  · exact (false_of_tubeArc_zero_two hCa hCS hBC hβ' hβ'0 hβ'1
      (hnotboth 1 (by decide) (by decide) h1A) (hnotboth 3 (by decide) (by decide) h3A)).elim
  · obtain ⟨s, hs, hαs⟩ := hmid hα hα0 hα1 1 (by decide) (by decide) h1A
    obtain ⟨r, hr, hβr⟩ := hmid hβ' hβ'0 hβ'1 3 (by decide) (by decide) h3B
    exact exists_tubeCrosscuts_of_split hCa hCS hα hβ' hα0 hα1 hβ'0 hβ'1 hU hI hs hr hαs hβr
  · obtain ⟨s, hs, hβs⟩ := hmid hβ' hβ'0 hβ'1 1 (by decide) (by decide) h1B
    obtain ⟨r, hr, hαr⟩ := hmid hα hα0 hα1 3 (by decide) (by decide) h3A
    exact exists_tubeCrosscuts_of_split hCa hCS hβ' hα hβ'0 hβ'1 hα0 hα1
      ((union_comm B' A).trans hU) ((inter_comm B' A).trans hI) hs hr hβs hαr
  · have hn1 : (fourSpokeModelLeaf 1, c) ∉ A := fun h =>
      hnotboth 1 (by decide) (by decide) h h1B
    have hn3 : (fourSpokeModelLeaf 3, c) ∉ A := fun h =>
      hnotboth 3 (by decide) (by decide) h h3B
    exact (false_of_tubeArc_zero_two hCa hCS hAC hα hα0 hα1 hn1 hn3).elim

end DifferentialGeometry.Topology.PiecewiseLinear

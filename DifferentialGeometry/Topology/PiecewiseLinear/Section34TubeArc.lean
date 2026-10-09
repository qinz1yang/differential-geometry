/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TubeGeneralPath

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_first_notMem_param {O : Set E3} (hO : IsOpen O) {u v : E3} {l : ℝ}
    (hl : u + l • (v - u) ∈ O) (hv : ∃ s ∈ Icc l 1, u + s • (v - u) ∉ O) :
    ∃ t ∈ Ioc l 1, u + t • (v - u) ∉ O ∧ ∀ s ∈ Ico l t, u + s • (v - u) ∈ O := by
  set T := {t : ℝ | t ∈ Icc l 1 ∧ u + t • (v - u) ∉ O} with hT
  have hTc : IsClosed T := isClosed_Icc.inter (hO.isClosed_compl.preimage (by fun_prop))
  have hTne : T.Nonempty := by
    obtain ⟨s, hs, hsO⟩ := hv
    exact ⟨s, hs, hsO⟩
  have hTb : BddBelow T := ⟨l, fun t ht => ht.1.1⟩
  have hmem := hTc.csInf_mem hTne hTb
  have hpos : l < sInf T := by
    rcases hmem.1.1.lt_or_eq with h | h
    · exact h
    · exfalso
      apply hmem.2
      rw [← h]
      exact hl
  refine ⟨sInf T, ⟨hpos, hmem.1.2⟩, hmem.2, fun s hs => ?_⟩
  by_contra hno
  have := csInf_le hTb ⟨⟨hs.1, hs.2.le.trans hmem.1.2⟩, hno⟩
  linarith [hs.2]

theorem exists_crossing_params {X W : Set E3} (hXc : IsClosed X) (hWc : IsClosed W)
    (hXW : X ⊆ interior W) {w : ℕ → E3} {N : ℕ} (hN : 0 < N) (hw0 : w 0 ∈ X) (hwN : w N ∉ W)
    (hvX : ∀ k ≤ N, w k ∉ frontier X) (hvW : ∀ k ≤ N, w k ∉ frontier W) :
    ∃ j k : ℕ, ∃ ta tb : ℝ, j ≤ k ∧ k < N ∧ 0 < ta ∧ ta < 1 ∧ 0 < tb ∧ tb < 1 ∧
      (k = j → ta < tb) ∧
      w j + ta • (w (j + 1) - w j) ∈ frontier X ∧
      (∀ s, ta < s → s ≤ 1 → w j + s • (w (j + 1) - w j) ∉ X) ∧
      (∀ i, j < i → i < N → ∀ s ∈ Icc (0 : ℝ) 1, w i + s • (w (i + 1) - w i) ∉ X) ∧
      w k + tb • (w (k + 1) - w k) ∈ frontier W ∧
      (∀ s, (if k = j then ta else 0) ≤ s → s < tb →
        w k + s • (w (k + 1) - w k) ∈ interior W) ∧
      (∀ i, j ≤ i → i < k → ∀ s, (if i = j then ta else 0) ≤ s → s ≤ 1 →
        w i + s • (w (i + 1) - w i) ∈ interior W) := by
  classical
  set P : ℕ → Prop := fun i => ∃ s ∈ Icc (0 : ℝ) 1, w i + s • (w (i + 1) - w i) ∈ X with hP
  have hP0 : P 0 := ⟨0, ⟨le_rfl, zero_le_one⟩, by simpa using hw0⟩
  set j := Nat.findGreatest P (N - 1) with hj
  have hPj : P j := Nat.findGreatest_spec (Nat.zero_le _) hP0
  have hjN : j ≤ N - 1 := Nat.findGreatest_le _
  have hgt : ∀ i, j < i → i ≤ N - 1 → ¬ P i := fun i hi hiN =>
    Nat.findGreatest_is_greatest hi hiN
  obtain ⟨ta, htaI, haX, hafter⟩ := exists_last_mem_segment hXc hPj
  have hta1 : ta < 1 := by
    rcases htaI.2.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [h, one_smul, add_sub_cancel] at haX
      by_cases hj1 : j + 1 ≤ N - 1
      · exact hgt (j + 1) (Nat.lt_succ_self j) hj1
          ⟨0, ⟨le_rfl, zero_le_one⟩, by simpa using haX⟩
      · have hjN' : j + 1 = N := by omega
        rw [hjN'] at haX
        exact hwN (interior_subset (hXW haX))
  set d := w (j + 1) - w j with hd
  have hafr : w j + ta • d ∈ frontier X := by
    refine ⟨subset_closure haX, fun hint => ?_⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior _ hint
    set μ := min ((1 - ta) / 2) (r / (2 * (‖d‖ + 1))) with hμ
    have hμ0 : 0 < μ := lt_min (by linarith) (div_pos hr (by positivity))
    have hμ1 : μ ≤ (1 - ta) / 2 := min_le_left _ _
    apply hafter (ta + μ) ⟨by linarith, by linarith⟩
    apply interior_subset
    apply hball
    rw [mem_ball, dist_eq_norm]
    have heq : w j + (ta + μ) • d - (w j + ta • d) = μ • d := by rw [add_smul]; abel
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hμ0]
    calc μ * ‖d‖ ≤ r / (2 * (‖d‖ + 1)) * ‖d‖ := by
          gcongr
          exact min_le_right _ _
      _ < r := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg d]
  have hta0 : 0 < ta := by
    rcases htaI.1.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, zero_smul, add_zero] at hafr
      exact hvX j (by omega) hafr
  have hlater : ∀ i, j < i → i < N → ∀ s ∈ Icc (0 : ℝ) 1, w i + s • (w (i + 1) - w i) ∉ X :=
    fun i hji hiN s hs hsX => hgt i hji (by omega) ⟨s, hs, hsX⟩
  set Q : ℕ → Prop := fun i => j ≤ i ∧ i < N ∧
    ∃ s ∈ Icc (if i = j then ta else 0) 1, w i + s • (w (i + 1) - w i) ∉ interior W with hQ
  have hQex : ∃ i, Q i := by
    refine ⟨N - 1, hjN, by omega, 1, ⟨by split_ifs <;> linarith, le_rfl⟩, ?_⟩
    have hN1 : N - 1 + 1 = N := by omega
    rw [hN1, one_smul, add_sub_cancel]
    exact fun h => hwN (interior_subset h)
  set k := Nat.find hQex with hk
  obtain ⟨hjk, hkN, hQk⟩ := Nat.find_spec hQex
  have hmin : ∀ i, j ≤ i → i < k → ∀ s, (if i = j then ta else 0) ≤ s → s ≤ 1 →
      w i + s • (w (i + 1) - w i) ∈ interior W := by
    intro i hji hik s hs1 hs2
    by_contra hno
    exact Nat.find_min hQex hik ⟨hji, by omega, s, ⟨hs1, hs2⟩, hno⟩
  have hl : w k + (if k = j then ta else 0) • (w (k + 1) - w k) ∈ interior W := by
    split_ifs with hkj
    · rw [hkj]
      exact hXW haX
    · rw [zero_smul, add_zero]
      have hk1 : j ≤ k - 1 := by omega
      have h := hmin (k - 1) hk1 (by omega) 1 (by split_ifs <;> linarith) le_rfl
      have hkk : k - 1 + 1 = k := by omega
      rwa [hkk, one_smul, add_sub_cancel] at h
  obtain ⟨tb, ⟨htbl, htb1⟩, hbW, hbefore⟩ := exists_first_notMem_param isOpen_interior hl hQk
  have hlow0 : 0 ≤ (if k = j then ta else 0) := by split_ifs <;> linarith
  set dk := w (k + 1) - w k with hdk
  have hbW' : w k + tb • dk ∈ W := by
    by_contra hno
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hWc.isOpen_compl _ hno
    set μ := min ((tb - (if k = j then ta else 0)) / 2) (r / (2 * (‖dk‖ + 1))) with hμ
    have hμ0 : 0 < μ := lt_min (by linarith) (div_pos hr (by positivity))
    have hμ1 : μ ≤ (tb - (if k = j then ta else 0)) / 2 := min_le_left _ _
    have hmem := hbefore (tb - μ) ⟨by linarith, by linarith⟩
    apply hball _ (interior_subset hmem)
    rw [mem_ball, dist_eq_norm]
    have heq : w k + (tb - μ) • dk - (w k + tb • dk) = -(μ • dk) := by rw [sub_smul]; abel
    rw [heq, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hμ0]
    calc μ * ‖dk‖ ≤ r / (2 * (‖dk‖ + 1)) * ‖dk‖ := by
          gcongr
          exact min_le_right _ _
      _ < r := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg dk]
  have hbfr : w k + tb • dk ∈ frontier W := ⟨subset_closure hbW', hbW⟩
  have htb1' : tb < 1 := by
    rcases htb1.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [h, one_smul, hdk, add_sub_cancel] at hbfr
      exact hvW (k + 1) hkN hbfr
  refine ⟨j, k, ta, tb, hjk, hkN, hta0, hta1, by linarith, htb1', fun hkj => ?_, hafr,
    fun s hs1 hs2 => hafter s ⟨hs1, hs2⟩, hlater, hbfr, fun s hs1 hs2 => hbefore s ⟨hs1, hs2⟩,
    hmin⟩
  rw [ite_eq_left hkj] at htbl
  exact htbl

theorem inner_bisector_pos {x y : E3} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : ‖x‖ • y + ‖y‖ • x ≠ 0) :
    0 < inner ℝ (‖y‖⁻¹ • y + ‖x‖⁻¹ • x) y ∧ 0 < inner ℝ (‖y‖⁻¹ • y + ‖x‖⁻¹ • x) x := by
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hny : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hsq : 0 < ‖‖x‖ • y + ‖y‖ • x‖ ^ 2 := by
    have := norm_pos_iff.mpr hxy
    positivity
  rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hnx, abs_of_pos hny] at hsq
  have hkey : 0 < ‖x‖ * ‖y‖ + inner ℝ x y := by
    rw [real_inner_comm] at hsq
    nlinarith [mul_pos hnx hny]
  have hyy : inner ℝ y y = ‖y‖ ^ 2 := real_inner_self_eq_norm_sq y
  have hxx : inner ℝ x x = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x
  constructor
  · rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hyy]
    have h1 : ‖y‖⁻¹ * ‖y‖ ^ 2 = ‖y‖ := by field_simp
    rw [h1]
    have h2 : ‖y‖ + ‖x‖⁻¹ * inner ℝ x y = (‖x‖ * ‖y‖ + inner ℝ x y) / ‖x‖ := by
      field_simp
    rw [h2]
    exact div_pos hkey hnx
  · rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hxx, real_inner_comm]
    have h1 : ‖x‖⁻¹ * ‖x‖ ^ 2 = ‖x‖ := by field_simp
    rw [h1]
    have h2 : ‖y‖⁻¹ * inner ℝ x y + ‖x‖ = (‖x‖ * ‖y‖ + inner ℝ x y) / ‖y‖ := by
      field_simp
      ring
    rw [h2]
    exact div_pos hkey hny

theorem bisector_ne_zero_of_notMem_affineSpan {a b c : E3} (hab : a ≠ b)
    (hc : c ∉ affineSpan ℝ ({a, b} : Set E3)) :
    ‖b - a‖ • (c - b) + ‖c - b‖ • (b - a) ≠ 0 := by
  intro h0
  have hnba : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab.symm)
  have h1 : ‖b - a‖ • (c - b) = -(‖c - b‖ • (b - a)) := eq_neg_of_add_eq_zero_left h0
  have h2 : c - b = (‖b - a‖⁻¹ * ‖c - b‖) • (a - b) := by
    calc c - b = ‖b - a‖⁻¹ • (‖b - a‖ • (c - b)) := by
          rw [smul_smul, inv_mul_cancel₀ hnba.ne', one_smul]
      _ = ‖b - a‖⁻¹ • (‖c - b‖ • (a - b)) := by rw [h1, ← smul_neg, neg_sub]
      _ = (‖b - a‖⁻¹ * ‖c - b‖) • (a - b) := by rw [smul_smul]
  apply hc
  have hc' : c = AffineMap.lineMap b a (‖b - a‖⁻¹ * ‖c - b‖) := by
    rw [AffineMap.lineMap_apply_module', ← h2]
    abel
  rw [hc']
  exact AffineMap.lineMap_mem _ (mem_affineSpan ℝ (mem_insert_of_mem _ rfl))
    (mem_affineSpan ℝ (mem_insert _ _))

end DifferentialGeometry.Topology.PiecewiseLinear

import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldHypPieces

/-!
# The pieces of the hyperbolic compact fold cover the triangle outside the core

Lane CF-H3, tier 3 (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §5, curvature `-1`, with review 23 §6.1). Every point
of the triangle other than `v₃ = 0` and outside the shrunk core
`‖mob (hypCoreCenter σ) z‖ < hypCoreRadius σ - hypCoreMargin σ` lies in the good set
`hypGoodSet σ` of `CompactFoldHypPieces` (`mem_hypGoodSet`).

The validity conditions of the formulas hold at every point of the triangle other than the three
vertices (`mem_validOne`, …, from `CompactFoldHypValid`: the sector conditions, the bridge
positivity and the corner Jacobians). The branch conditions follow from the canonical sums
`canon i + canon j ≥ 0` on the triangle (`CompactFoldHypBlend`): inside a corner region the other
two canonical coordinates are positive. Outside both corner regions the lens coordinate is below
`β`, or above `β'` because the switch window lies in the shrunk core (`window_mem_core`); on the
boundary of a corner region above the switch the outer weight saturates strictly, since the
canonical sum of wall 2 is positive off wall 2 (`one_lt_blendThree`, `blendThree_lt_neg_one`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace HypFold

variable {σ : CompactShape}

section Hyp

variable (h : σ.curv = .hyperbolic)
include h

theorem hd_zero_ne_zero_of_ne {z : ℂ} (hz : ‖z‖ < 1) (h1 : z ≠ σ.vertexOne) : hd σ 0 z ≠ 0 := by
  rw [← norm_rotOne_eq_hd h]
  exact norm_ne_zero_iff.2 (rotOne_ne_zero h hz h1)

theorem b_lt_hd_of_canon {j : Fin 3} {z : ℂ} {b e : ℝ} (hb1 : b < 1)
    (hcb : canonForm (tau σ j) b < -e) (hc : -e ≤ canon σ j z) : b < hd σ j z := by
  by_contra hn
  push Not at hn
  rcases hn.lt_or_eq with hlt | heq
  · have := canonForm_lt_canonForm (tau_mem h j).1 (tau_mem h j).2 hlt hb1
    change -e ≤ canonForm (tau σ j) (hd σ j z) at hc
    linarith
  · change -e ≤ canonForm (tau σ j) (hd σ j z) at hc
    rw [heq] at hc
    linarith

theorem lensCoord_nonneg {z : ℂ} (hz : z ∈ σ.triangle) : 0 ≤ lensCoord σ z := by
  have hz1 := norm_lt_one_of_mem h hz
  have hn := normSq_lt_one_of_norm_lt (norm_rotTwo_lt_one h hz1)
  have hi := (sector_two h hz).1
  unfold lensCoord
  exact div_nonneg (by linarith) (by linarith)

theorem wallSide_two_pos_of_lens {z : ℂ} (hz1 : ‖z‖ < 1) (hl : 0 < lensCoord σ z) :
    0 < σ.wallSide 2 z := by
  have hn := normSq_lt_one_of_norm_lt (norm_rotTwo_lt_one h hz1)
  unfold lensCoord at hl
  have hi : 0 < (σ.rotTwo z).im := by
    by_contra hc
    push Not at hc
    have : 2 * (σ.rotTwo z).im / (1 - normSq (σ.rotTwo z)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    linarith
  rw [CompactShape.wallSide_two_eq, CompactShape.eps_hyp h]
  apply mul_pos hi
  apply normSq_pos.2
  simpa using one_sub_conj_mul_ne_zero (norm_vertexTwo_lt_one h) hz1

theorem canon_sum_pos_of_lens {z : ℂ} (hz : z ∈ σ.triangle) (h1 : z ≠ σ.vertexOne)
    (h2 : z ≠ σ.vertexTwo) (hl : 0 < lensCoord σ z) : 0 < canon σ 0 z + canon σ 1 z := by
  have d12 := mem_domOneTwo h hz h1 h2
  rw [canon_add_canon_one_two h d12]
  exact mul_pos (pow_pos (wallSide_two_pos_of_lens h (norm_lt_one_of_mem h hz) hl) 2)
    (cofOneTwo_pos h d12)

omit h in
theorem one_lt_blendThree {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) {e : ℝ} (he : 0 < e)
    (hc0 : canon σ 0 z ≤ -e) (hs : 0 < canon σ 0 z + canon σ 1 z) :
    1 < blendThree σ 1 e z := by
  have hd := discAngle_mem hz h0
  have hθ := θ₃_pos σ
  have h1 : -1 ≤ 2 * discAngle z / σ.θ₃ - 1 := by
    have : 0 ≤ 2 * discAngle z / σ.θ₃ := div_nonneg (by linarith [hd.1]) hθ.le
    linarith
  have h2 : 2 < 1 / e * (canon σ 1 z - canon σ 0 z) := by
    rw [one_div_mul_eq_div, lt_div_iff₀ he]
    linarith
  unfold blendThree
  linarith

omit h in
theorem blendThree_lt_neg_one {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) {e : ℝ} (he : 0 < e)
    (hc1 : canon σ 1 z ≤ -e) (hs : 0 < canon σ 0 z + canon σ 1 z) :
    blendThree σ 1 e z < -1 := by
  have hd := discAngle_mem hz h0
  have hθ := θ₃_pos σ
  have h1 : 2 * discAngle z / σ.θ₃ - 1 ≤ 1 := by
    have : 2 * discAngle z / σ.θ₃ ≤ 2 := by
      rw [div_le_iff₀ hθ]
      linarith [hd.2]
    linarith
  have h2 : 1 / e * (canon σ 1 z - canon σ 0 z) < -2 := by
    rw [one_div_mul_eq_div, div_lt_iff₀ he]
    linarith
  unfold blendThree
  linarith

theorem mem_hypGoodSet {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (hc : hypCoreRadius σ - hypCoreMargin σ < ‖mob (hypCoreCenter σ) z‖) :
    z ∈ hypGoodSet σ := by
  have hz1 := norm_lt_one_of_mem h hz
  obtain ⟨hg0, hga, hab, hb1, he, hc1, hc2, hβ0, hββ, -, -, hg30, hg3a, ha3b, hb3t, hb35⟩ :=
    hypLayout_params h
  by_cases hA : hd σ 0 z < (hypLayout σ).g
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨hz1, hA⟩)))))))
  by_cases hB : hd σ 1 z < (hypLayout σ).g
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨hz1, hB⟩)))))))
  by_cases hC : ‖z‖ < (hypLayout σ).g₃
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨norm_pos_iff.2 h0, hC⟩))))))
  push Not at hA hB hC
  have h1 : z ≠ σ.vertexOne := by
    intro e1; subst e1
    have : hd σ 0 σ.vertexOne = 0 := by simp [hd, mob_self]
    linarith
  have h2 : z ≠ σ.vertexTwo := by
    intro e2; subst e2
    have : hd σ 1 σ.vertexTwo = 0 := by simp [hd, mob_self]
    linarith
  have s01 := canon_zero_add_one_nonneg h hz
  have s02 := canon_zero_add_two_nonneg h hz
  have s12 := canon_one_add_two_nonneg h hz
  have d13 := mem_domOneThree h hz h0 h1
  have d03 := mem_domZeroThree h hz h0 h2
  have d12 := mem_domOneTwo h hz h1 h2
  have v1 := valid_one h hz h1
  have v2 := valid_two h hz h2
  have v3 := valid_three hz h0
  have τ1 := tau_mem h 0
  have τ2 := tau_mem h 1
  have hτ3 : (hypLayout σ).b₃ < tauThree σ := hb3t
  by_cases cA : canon σ 0 z < -(hypLayout σ).e
  · refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨hz1, by linarith, cA, ?_, ?_,
      ⟨d13, d12, v1.1, hpos_one_at_one h hz1, hpos_two_at_one h d12⟩,
      det_fderiv_cornerOne_pos_of_mem h hab hββ hz h0 h1 h2⟩)))))
    · exact lt_hd_of_canon_nonneg h 1 (by linarith) (by linarith) hb1 he hc2
    · have := tau_le_hd_of_canon_nonneg h 2 (by linarith)
      change tauThree σ ≤ ‖z‖ at this
      linarith
  by_cases cB : canon σ 1 z < -(hypLayout σ).e
  · refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨hz1, by linarith, cB, ?_, ?_, by linarith,
      ⟨d12, d03, v2.1, hpos_two_at_two h d12, hpos_zero_at_two h hz1⟩,
      det_fderiv_cornerTwo_pos_of_mem h hab hββ hz h0 h1 h2⟩))))
    · exact lt_hd_of_canon_nonneg h 0 (by linarith) (by linarith) hb1 he hc1
    · have := tau_le_hd_of_canon_nonneg h 2 (by linarith)
      change tauThree σ ≤ ‖z‖ at this
      linarith
  push Not at cA cB
  have hb0 : (hypLayout σ).b < hd σ 0 z := b_lt_hd_of_canon h hb1 hc1 cA
  have hb1' : (hypLayout σ).b < hd σ 1 z := b_lt_hd_of_canon h hb1 hc2 cB
  have hl0 := lensCoord_nonneg h hz
  by_cases hL : lensCoord σ z < (hypLayout σ).β
  · refine Or.inl (Or.inl (Or.inl (Or.inr ⟨hz1, hb0, hb1', by rwa [abs_of_nonneg hl0], ?_,
      d12, hpos_two_at_one h d12, hpos_two_at_two h d12, det_fderiv_bridgeTwo_pos h d12 v1.2.1⟩)))
    have := norm_gt_of_lensRegion h hz cA cB (by linarith)
    linarith
  push Not at hL
  by_cases hW : lensCoord σ z ≤ (hypLayout σ).β'
  · have := window_mem_core h hz cA cB hL hW
    linarith
  push Not at hW
  have hlp : 0 < lensCoord σ z := by linarith
  have hsum := canon_sum_pos_of_lens h hz h1 h2 hlp
  by_cases c0s : -(hypLayout σ).e < canon σ 0 z
  · by_cases c1s : -(hypLayout σ).e < canon σ 1 z
    · refine Or.inl (Or.inl (Or.inr ⟨hz1, c0s, c1s, ?_, by linarith, by linarith, by linarith,
        ⟨d13, d03, v3, hpos_one_at_three h hz1, hpos_zero_at_three h hz1⟩,
        det_fderiv_cornerThree_pos_of_mem h ha3b hb35 one_pos he hz h0 h1 h2⟩))
      rw [abs_of_nonneg hl0]; linarith
    · push Not at c1s
      refine Or.inr ⟨hz1, hb1', c0s, hW, ?_, v3, blendThree_lt_neg_one hz h0 he c1s hsum,
        by linarith, d03, hpos_zero_at_two h hz1, hpos_zero_at_three h hz1,
        det_fderiv_bridgeZero_pos h d03⟩
      have := tau_le_hd_of_canon_nonneg h 2 (by linarith)
      change tauThree σ ≤ ‖z‖ at this
      linarith
  · push Not at c0s
    refine Or.inl (Or.inr ⟨hz1, hb0, by linarith, hW, ?_, v3,
      one_lt_blendThree hz h0 he c0s hsum, by linarith, d13, hpos_one_at_one h hz1,
      hpos_one_at_three h hz1, det_fderiv_bridgeOne_pos h d13⟩)
    have := tau_le_hd_of_canon_nonneg h 2 (by linarith)
    change tauThree σ ≤ ‖z‖ at this
    linarith

end Hyp

end HypFold

end GC.Seifert

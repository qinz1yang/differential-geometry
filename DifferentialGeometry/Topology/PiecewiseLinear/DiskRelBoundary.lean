/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConeFan

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_pos_forall_exists_isPiecewiseAffineOn_stdCone_eqOn_boundary
    (f : ℝ × ℝ → F) (hf : ContinuousOn f stdCone) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (M N : ℕ) (u σ : ℕ → ℝ) (gHyp gLeg₁ gLeg₂ : ℕ → F),
      u 0 = 0 → u (M + 1) = 1 → (∀ j ≤ M, u j < u (j + 1)) → (∀ j ≤ M, u (j + 1) - u j < δ) →
      σ 0 = 0 → σ (N + 1) = 1 → (∀ k ≤ N, σ k < σ (k + 1)) → (∀ k ≤ N, σ (k + 1) - σ k < δ) →
      (∀ j ≤ M + 1, dist (gHyp j) (f (1 - u j, u j)) ≤ ε) →
      (∀ k ≤ N + 1, dist (gLeg₁ k) (f (σ k, 0)) ≤ ε) →
      (∀ k ≤ N + 1, dist (gLeg₂ k) (f (0, σ k)) ≤ ε) →
      gLeg₁ 0 = gLeg₂ 0 → gHyp 0 = gLeg₁ (N + 1) → gHyp (M + 1) = gLeg₂ (N + 1) →
      ∃ Ψ : ℝ × ℝ → F, IsPiecewiseAffineOn Ψ stdCone ∧
        (∀ k ≤ N, ∀ t ∈ Icc (σ k) (σ (k + 1)),
          Ψ (t, 0) =
            AffineMap.lineMap (gLeg₁ k) (gLeg₁ (k + 1)) ((t - σ k) / (σ (k + 1) - σ k))) ∧
        (∀ k ≤ N, ∀ t ∈ Icc (σ k) (σ (k + 1)),
          Ψ (0, t) =
            AffineMap.lineMap (gLeg₂ k) (gLeg₂ (k + 1)) ((t - σ k) / (σ (k + 1) - σ k))) ∧
        (∀ j ≤ M, ∀ r ∈ Icc (u j) (u (j + 1)),
          Ψ (1 - r, r) =
            AffineMap.lineMap (gHyp j) (gHyp (j + 1)) ((r - u j) / (u (j + 1) - u j))) ∧
        ∀ z ∈ stdCone, dist (Ψ z) (f z) ≤ 2 * ε := by
  classical
  have hcompact : IsCompact stdCone := by
    rw [← stdConeLayer_zero_one]
    exact (isHPolytope_stdConeLayer le_rfl).isCompact
  obtain ⟨δ₀, hδ₀, hunif⟩ := Metric.uniformContinuousOn_iff.mp
    (hcompact.uniformContinuousOn_of_continuous hf) ε hε
  refine ⟨δ₀ / 4, by linarith, ?_⟩
  intro M N u σ gHyp gLeg₁ gLeg₂ hu0 huM humono humesh hσ0 hσN hσmono hσmesh hclH hcl₁ hcl₂
    hcorner₀ hcorner₁ hcorner₂
  have huchain := le_of_chain (fun j hj => (humono j hj).le)
  have hσchain := le_of_chain (fun k hk => (hσmono k hk).le)
  have hunn : ∀ j ≤ M + 1, 0 ≤ u j := by
    intro j hj
    have h := huchain j hj 0 (Nat.zero_le _)
    rwa [hu0] at h
  have hule : ∀ j ≤ M + 1, u j ≤ 1 := by
    intro j hj
    have h := huchain (M + 1) le_rfl j hj
    rwa [huM] at h
  have hσnn : ∀ k ≤ N + 1, 0 ≤ σ k := by
    intro k hk
    have h := hσchain k hk 0 (Nat.zero_le _)
    rwa [hσ0] at h
  have hσle : ∀ k ≤ N + 1, σ k ≤ 1 := by
    intro k hk
    have h := hσchain (N + 1) le_rfl k hk
    rwa [hσN] at h
  set w : ℕ → ℕ → F := fun k j =>
    if k = 0 then gLeg₁ 0
    else if k = N + 1 then gHyp j
    else if j = 0 then gLeg₁ k
    else if j = M + 1 then gLeg₂ k
    else f (σ k * (1 - u j), σ k * u j) with hwdef
  have hw0 : ∀ j, w 0 j = w 0 0 := by
    intro j
    simp only [hwdef, ite_eq_left rfl]
  have hwhyp : ∀ j, w (N + 1) j = gHyp j := by
    intro j
    simp only [hwdef]
    rw [ite_eq_right (by omega)]
    simp
  have hwleg₁ : ∀ k ≤ N + 1, w k 0 = gLeg₁ k := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp only [hwdef, ite_eq_left rfl]
    · rcases eq_or_lt_of_le hk with rfl | hlt
      · rw [hwhyp 0, hcorner₁]
      · simp only [hwdef]
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        simp
  have hwleg₂ : ∀ k ≤ N + 1, w k (M + 1) = gLeg₂ k := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp only [hwdef, ite_eq_left rfl]
      exact hcorner₀
    · rcases eq_or_lt_of_le hk with rfl | hlt
      · rw [hwhyp (M + 1), hcorner₂]
      · simp only [hwdef]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
        simp
  have hwclose : ∀ a ≤ N + 1, ∀ b ≤ M + 1,
      dist (w a b) (f (σ a * (1 - u b), σ a * u b)) ≤ ε := by
    intro a ha b hb
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · have hpt : ((σ 0 * (1 - u b), σ 0 * u b) : ℝ × ℝ) = (σ 0, 0) := by
        rw [hσ0]
        norm_num
      rw [hpt]
      simp only [hwdef, ite_eq_left rfl]
      exact hcl₁ 0 (by omega)
    · rcases eq_or_lt_of_le ha with rfl | hlt
      · have hpt : ((σ (N + 1) * (1 - u b), σ (N + 1) * u b) : ℝ × ℝ) = (1 - u b, u b) := by
          rw [hσN]
          norm_num
        rw [hpt, hwhyp b]
        exact hclH b hb
      · rcases Nat.eq_zero_or_pos b with rfl | hbpos
        · have hpt : ((σ a * (1 - u 0), σ a * u 0) : ℝ × ℝ) = (σ a, 0) := by
            rw [hu0]
            norm_num
          rw [hpt, hwleg₁ a ha]
          exact hcl₁ a ha
        · rcases eq_or_lt_of_le hb with rfl | hblt
          · have hpt : ((σ a * (1 - u (M + 1)), σ a * u (M + 1)) : ℝ × ℝ) = (0, σ a) := by
              rw [huM]
              norm_num
            rw [hpt, hwleg₂ a ha]
            exact hcl₂ a ha
          · have hval : w a b = f (σ a * (1 - u b), σ a * u b) := by
              simp only [hwdef]
              rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
            rw [hval, dist_self]
            exact hε.le
  obtain ⟨Ψ, hPA, -, hray₁, hray₂, houter, himg⟩ :=
    exists_isPiecewiseAffineOn_stdCone_fan w hu0 huM humono hσ0 hσN hσmono hw0
  refine ⟨Ψ, hPA, ?_, ?_, ?_, ?_⟩
  · intro k hk t ht
    have hpt : ((t * (1 - u 0), t * u 0) : ℝ × ℝ) = (t, 0) := by
      rw [hu0]
      norm_num
    rw [← hpt, hray₁ k hk t ht, hwleg₁ k (by omega), hwleg₁ (k + 1) (by omega)]
  · intro k hk t ht
    have hpt : ((t * (1 - u (M + 1)), t * u (M + 1)) : ℝ × ℝ) = (0, t) := by
      rw [huM]
      norm_num
    rw [← hpt, hray₂ k hk t ht, hwleg₂ k (by omega), hwleg₂ (k + 1) (by omega)]
  · intro j hj r hr
    rw [houter j hj r hr, hwhyp j, hwhyp (j + 1)]
  · intro z hz
    obtain ⟨k, hk, j, hj, h1, h2, hsec, hmem⟩ := himg z hz
    have hcorner : ∀ a b : ℕ, a ≤ N + 1 → b ≤ M + 1 → σ a ∈ Icc (σ k) (σ (k + 1)) →
        u b ∈ Icc (u j) (u (j + 1)) → dist (w a b) (f z) ≤ 2 * ε := by
      intro a b ha hb hσa hub
      have hp : ((σ a * (1 - u b), σ a * u b) : ℝ × ℝ) ∈ stdCone :=
        stdConeSector_subset_stdCone _ _
          (mem_stdConeSector_smul_left le_rfl (hunn b hb) (hule b hb) ⟨hσnn a ha, hσle a ha⟩)
      have hdcell := dist_cellCorner_le hsec h1 h2 hσa hub (hunn j (by omega))
        (hule (j + 1) (by omega))
      have hdlt : dist ((σ a * (1 - u b), σ a * u b) : ℝ × ℝ) z < δ₀ := by
        have e1 := hσmesh k hk
        have e2 := humesh j hj
        linarith
      have hfd : dist (f (σ a * (1 - u b), σ a * u b)) (f z) < ε := hunif _ hp _ hz hdlt
      calc dist (w a b) (f z)
          ≤ dist (w a b) (f (σ a * (1 - u b), σ a * u b)) +
            dist (f (σ a * (1 - u b), σ a * u b)) (f z) := dist_triangle _ _ _
        _ ≤ 2 * ε := by linarith [hwclose a ha b hb]
    have hball : ({w k j, w k (j + 1), w (k + 1) j, w (k + 1) (j + 1)} : Set F) ⊆
        Metric.closedBall (f z) (2 * ε) := by
      intro x hx
      have hσk : σ k ∈ Icc (σ k) (σ (k + 1)) := ⟨le_rfl, (hσmono k hk).le⟩
      have hσk1 : σ (k + 1) ∈ Icc (σ k) (σ (k + 1)) := ⟨(hσmono k hk).le, le_rfl⟩
      have huj : u j ∈ Icc (u j) (u (j + 1)) := ⟨le_rfl, (humono j hj).le⟩
      have huj1 : u (j + 1) ∈ Icc (u j) (u (j + 1)) := ⟨(humono j hj).le, le_rfl⟩
      simp only [mem_insert_iff, mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hcorner k j (by omega) (by omega) hσk huj
      · exact hcorner k (j + 1) (by omega) (by omega) hσk huj1
      · exact hcorner (k + 1) j (by omega) (by omega) hσk1 huj
      · exact hcorner (k + 1) (j + 1) (by omega) (by omega) hσk1 huj1
    exact convexHull_min hball (convex_closedBall (f z) (2 * ε)) hmem

end DifferentialGeometry.Topology.PiecewiseLinear

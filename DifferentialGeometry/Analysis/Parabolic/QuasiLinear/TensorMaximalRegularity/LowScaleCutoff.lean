import DifferentialGeometry.Analysis.Calculus.BallRetraction
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped InnerProductSpace

section Normed

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable (ι : X →L[ℝ] H)

noncomputable def lowScaleCutoff (ρ : ℝ) (U : X) : X := (min 1 (ρ / ‖ι U‖)) • U

theorem incl_lowScaleCutoff (ρ : ℝ) (U : X) :
    ι (lowScaleCutoff ι ρ U) = ballRetraction ρ (ι U) := by
  simp only [lowScaleCutoff, ballRetraction, map_smul]

theorem lowScaleCutoff_mem_ball {ρ : ℝ} (hρ : 0 ≤ ρ) (U : X) :
    ‖ι (lowScaleCutoff ι ρ U)‖ ≤ ρ := by
  rw [incl_lowScaleCutoff]
  exact ballRetraction_mem_closedBall hρ (ι U)

theorem lowScaleCutoff_eq_self (hι : Function.Injective ι) {ρ : ℝ} {U : X}
    (hU : ‖ι U‖ ≤ ρ) : lowScaleCutoff ι ρ U = U := by
  rw [lowScaleCutoff]
  rcases eq_or_lt_of_le (norm_nonneg (ι U)) with h0 | h0
  · have hiU : ι U = 0 := norm_eq_zero.1 h0.symm
    have hU0 : U = 0 := hι (by simp [hiU])
    rw [hU0, smul_zero]
  · have : (1 : ℝ) ≤ ρ / ‖ι U‖ := (one_le_div h0).2 hU
    rw [min_eq_left this, one_smul]

private theorem lowScaleCutoff_eq_smul {ρ : ℝ} {U : X} (h : ρ < ‖ι U‖) :
    lowScaleCutoff ι ρ U = (ρ / ‖ι U‖) • U := by
  have hle : ρ / ‖ι U‖ ≤ 1 := by
    rcases eq_or_lt_of_le (norm_nonneg (ι U)) with h0 | h0
    · rw [← h0, div_zero]; exact zero_le_one
    · exact (div_le_one h0).2 (le_of_lt h)
  rw [lowScaleCutoff, min_eq_right hle]

theorem lowScaleCutoff_incl_lip {ρ : ℝ} (hρ : 0 ≤ ρ) (U V : X) :
    ‖ι (lowScaleCutoff ι ρ U) - ι (lowScaleCutoff ι ρ V)‖ ≤
      2 * ‖ι U - ι V‖ := by
  rw [incl_lowScaleCutoff, incl_lowScaleCutoff]
  simpa [dist_eq_norm] using
    (lipschitzWith_ballRetraction (X := H) hρ).dist_le_mul (ι U) (ι V)

end Normed

section Hilbert

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (ι : X →L[ℝ] H)

theorem lowScaleCutoff_incl_lip_one {ρ : ℝ} (hρ : 0 ≤ ρ) (U V : X) :
    ‖ι (lowScaleCutoff ι ρ U) - ι (lowScaleCutoff ι ρ V)‖ ≤ ‖ι U - ι V‖ := by
  rw [incl_lowScaleCutoff, incl_lowScaleCutoff]
  simpa [dist_eq_norm, NNReal.coe_one, one_mul] using
    (lipschitzWith_one_ballRetraction (X := H) hρ).dist_le_mul (ι U) (ι V)

end Hilbert

section NormedDifference

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable (ι : X →L[ℝ] H)

theorem lowScaleCutoff_sub_le
    (hι : Function.Injective ι) {ρ : ℝ} (hρ : 0 < ρ) (U V : X) :
    ‖lowScaleCutoff ι ρ U - lowScaleCutoff ι ρ V‖ ≤
      ‖U - V‖ + (1 / ρ) * max ‖U‖ ‖V‖ * ‖ι U - ι V‖ := by
  have hRinv : 0 ≤ 1 / ρ := by positivity
  have hcu : ‖U‖ ≤ max ‖U‖ ‖V‖ := le_max_left _ _
  have hcu' : ‖V‖ ≤ max ‖U‖ ‖V‖ := le_max_right _ _
  have hc0 : 0 ≤ max ‖U‖ ‖V‖ := le_trans (norm_nonneg _) hcu
  have hD0 : 0 ≤ ‖ι U - ι V‖ := norm_nonneg _
  have hcorr0 : 0 ≤ (1 / ρ) * max ‖U‖ ‖V‖ * ‖ι U - ι V‖ :=
    mul_nonneg (mul_nonneg hRinv hc0) hD0
  rcases le_or_gt ‖ι U‖ ρ with hu | hu
  · rcases le_or_gt ‖ι V‖ ρ with hv | hv
    · rw [lowScaleCutoff_eq_self ι hι hu, lowScaleCutoff_eq_self ι hι hv]
      linarith [hcorr0]
    · rw [lowScaleCutoff_eq_self ι hι hu, lowScaleCutoff_eq_smul ι hv]
      have hv0 : 0 < ‖ι V‖ := lt_trans hρ hv
      have hkey : ‖U - (ρ / ‖ι V‖) • V‖ ≤ ‖U - V‖ + (1 - ρ / ‖ι V‖) * ‖V‖ := by
        have hexp : U - (ρ / ‖ι V‖) • V = (U - V) + (1 - ρ / ‖ι V‖) • V := by
          rw [sub_smul, one_smul]; abel
        rw [hexp]
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_smul, Real.norm_eq_abs]
        have hpos : 0 ≤ 1 - ρ / ‖ι V‖ := by
          have : ρ / ‖ι V‖ ≤ 1 := (div_le_one hv0).2 (le_of_lt hv)
          linarith
        rw [abs_of_nonneg hpos]
      refine le_trans hkey ?_
      have hgeo : ‖ι V‖ - ρ ≤ ‖ι U - ι V‖ := by
        have h1 : ‖ι V‖ - ‖ι U‖ ≤ ‖ι V - ι U‖ := norm_sub_norm_le _ _
        rw [norm_sub_rev] at h1
        linarith
      have hstep : (1 - ρ / ‖ι V‖) * ‖V‖ ≤ (1 / ρ) * max ‖U‖ ‖V‖ * ‖ι U - ι V‖ := by
        have e1 : (1 - ρ / ‖ι V‖) * ‖V‖ = ((‖ι V‖ - ρ) / ‖ι V‖) * ‖V‖ := by
          field_simp
        rw [e1]
        have hfac : (‖ι V‖ - ρ) / ‖ι V‖ ≤ (‖ι V‖ - ρ) / ρ :=
          div_le_div_of_nonneg_left (by linarith) hρ (le_of_lt hv)
        have hjn : 0 ≤ ‖V‖ := norm_nonneg _
        calc ((‖ι V‖ - ρ) / ‖ι V‖) * ‖V‖
            ≤ ((‖ι V‖ - ρ) / ρ) * ‖V‖ := mul_le_mul_of_nonneg_right hfac hjn
          _ = (1 / ρ) * ‖V‖ * (‖ι V‖ - ρ) := by ring
          _ ≤ (1 / ρ) * max ‖U‖ ‖V‖ * ‖ι U - ι V‖ := by
              apply mul_le_mul
              · exact mul_le_mul_of_nonneg_left hcu' hRinv
              · exact hgeo
              · linarith
              · exact mul_nonneg hRinv hc0
      linarith
  · rcases le_or_gt ‖ι V‖ ρ with hv | hv
    · rw [lowScaleCutoff_eq_smul ι hu, lowScaleCutoff_eq_self ι hι hv]
      have hu0 : 0 < ‖ι U‖ := lt_trans hρ hu
      have hkey : ‖(ρ / ‖ι U‖) • U - V‖ ≤ ‖U - V‖ + (1 - ρ / ‖ι U‖) * ‖U‖ := by
        have hexp : (ρ / ‖ι U‖) • U - V = (U - V) - (1 - ρ / ‖ι U‖) • U := by
          rw [sub_smul, one_smul]; abel
        rw [hexp]
        refine le_trans (norm_sub_le _ _) ?_
        rw [norm_smul, Real.norm_eq_abs]
        have hpos : 0 ≤ 1 - ρ / ‖ι U‖ := by
          have : ρ / ‖ι U‖ ≤ 1 := (div_le_one hu0).2 (le_of_lt hu)
          linarith
        rw [abs_of_nonneg hpos]
      refine le_trans hkey ?_
      have hgeo : ‖ι U‖ - ρ ≤ ‖ι U - ι V‖ := by
        have h1 : ‖ι U‖ - ‖ι V‖ ≤ ‖ι U - ι V‖ := norm_sub_norm_le _ _
        linarith
      have hstep : (1 - ρ / ‖ι U‖) * ‖U‖ ≤ (1 / ρ) * max ‖U‖ ‖V‖ * ‖ι U - ι V‖ := by
        have e1 : (1 - ρ / ‖ι U‖) * ‖U‖ = ((‖ι U‖ - ρ) / ‖ι U‖) * ‖U‖ := by
          field_simp
        rw [e1]
        have hfac : (‖ι U‖ - ρ) / ‖ι U‖ ≤ (‖ι U‖ - ρ) / ρ :=
          div_le_div_of_nonneg_left (by linarith) hρ (le_of_lt hu)
        have hjn : 0 ≤ ‖U‖ := norm_nonneg _
        calc ((‖ι U‖ - ρ) / ‖ι U‖) * ‖U‖
            ≤ ((‖ι U‖ - ρ) / ρ) * ‖U‖ := mul_le_mul_of_nonneg_right hfac hjn
          _ = (1 / ρ) * ‖U‖ * (‖ι U‖ - ρ) := by ring
          _ ≤ (1 / ρ) * max ‖U‖ ‖V‖ * ‖ι U - ι V‖ := by
              apply mul_le_mul
              · exact mul_le_mul_of_nonneg_left hcu hRinv
              · exact hgeo
              · linarith
              · exact mul_nonneg hRinv hc0
      linarith
    · rw [lowScaleCutoff_eq_smul ι hu, lowScaleCutoff_eq_smul ι hv]
      have hu0 : 0 < ‖ι U‖ := lt_trans hρ hu
      have hv0 : 0 < ‖ι V‖ := lt_trans hρ hv
      have hexp : (ρ / ‖ι U‖) • U - (ρ / ‖ι V‖) • V =
          (ρ / ‖ι U‖) • (U - V) + (ρ / ‖ι U‖ - ρ / ‖ι V‖) • V := by
        rw [smul_sub, sub_smul]; abel
      rw [hexp]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hlu0 : 0 ≤ ρ / ‖ι U‖ := by positivity
      have hlu1 : ρ / ‖ι U‖ ≤ 1 := (div_le_one hu0).2 (le_of_lt hu)
      have hterm1 : |ρ / ‖ι U‖| * ‖U - V‖ ≤ ‖U - V‖ := by
        rw [abs_of_nonneg hlu0]
        nlinarith [norm_nonneg (U - V), hlu1]
      have hdiff : |ρ / ‖ι U‖ - ρ / ‖ι V‖| ≤ ρ * ‖ι U - ι V‖ / (‖ι U‖ * ‖ι V‖) := by
        have hd : ρ / ‖ι U‖ - ρ / ‖ι V‖ = ρ * (‖ι V‖ - ‖ι U‖) / (‖ι U‖ * ‖ι V‖) := by
          rw [div_sub_div _ _ (ne_of_gt hu0) (ne_of_gt hv0)]; ring
        rw [hd, abs_div, abs_of_nonneg (le_of_lt (by positivity : (0:ℝ) < ‖ι U‖ * ‖ι V‖))]
        rw [abs_mul, abs_of_nonneg (le_of_lt hρ)]
        apply div_le_div_of_nonneg_right ?_ (by positivity)
        apply mul_le_mul_of_nonneg_left ?_ (le_of_lt hρ)
        rw [abs_sub_comm]
        have h1 : ‖ι U‖ - ‖ι V‖ ≤ ‖ι U - ι V‖ := norm_sub_norm_le _ _
        have h2 : ‖ι V‖ - ‖ι U‖ ≤ ‖ι U - ι V‖ := by
          have := norm_sub_norm_le (ι V) (ι U); rw [norm_sub_rev] at this; linarith
        rw [abs_sub_le_iff]; exact ⟨h1, h2⟩
      have hterm2 : |ρ / ‖ι U‖ - ρ / ‖ι V‖| * ‖V‖ ≤
          (1 / ρ) * max ‖U‖ ‖V‖ * ‖ι U - ι V‖ := by
        have hjn : 0 ≤ ‖V‖ := norm_nonneg _
        have hRsq : ρ * ρ ≤ ‖ι U‖ * ‖ι V‖ :=
          mul_le_mul (le_of_lt hu) (le_of_lt hv) (le_of_lt hρ) (le_of_lt hu0)
        have hRle1 : ρ / (‖ι U‖ * ‖ι V‖) ≤ 1 / ρ := by
          rw [div_le_div_iff₀ (by positivity) hρ]
          nlinarith [hRsq]
        calc |ρ / ‖ι U‖ - ρ / ‖ι V‖| * ‖V‖
            ≤ (ρ * ‖ι U - ι V‖ / (‖ι U‖ * ‖ι V‖)) * ‖V‖ :=
              mul_le_mul_of_nonneg_right hdiff hjn
          _ = (ρ / (‖ι U‖ * ‖ι V‖)) * (‖V‖ * ‖ι U - ι V‖) := by ring
          _ ≤ (1 / ρ) * (max ‖U‖ ‖V‖ * ‖ι U - ι V‖) := by
              apply mul_le_mul hRle1 ?_ ?_ hRinv
              · exact mul_le_mul_of_nonneg_right hcu' hD0
              · exact mul_nonneg hjn hD0
          _ = (1 / ρ) * max ‖U‖ ‖V‖ * ‖ι U - ι V‖ := by ring
      linarith

end NormedDifference

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity

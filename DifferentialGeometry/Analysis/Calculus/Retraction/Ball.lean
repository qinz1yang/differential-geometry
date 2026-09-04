import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

namespace DifferentialGeometry.Analysis.Calculus

open scoped InnerProductSpace

section Normed

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

noncomputable def ballRetraction (R : ℝ) (x : X) : X := (min 1 (R / ‖x‖)) • x

omit [NormedSpace ℝ X] in
private theorem ballRetraction_factor_nonneg {R : ℝ} (hR : 0 ≤ R) (x : X) :
    0 ≤ min 1 (R / ‖x‖) :=
  le_min zero_le_one (div_nonneg hR (norm_nonneg x))

omit [NormedSpace ℝ X] in
private theorem ballRetraction_factor_mul_norm {R : ℝ} (hR : 0 ≤ R) (x : X) :
    (min 1 (R / ‖x‖)) * ‖x‖ = min ‖x‖ R := by
  rcases eq_or_lt_of_le (norm_nonneg x) with hx | hx
  · rw [← hx]; simp [min_eq_left hR]
  · rw [min_mul_of_nonneg _ _ (le_of_lt hx), one_mul, div_mul_cancel₀]
    exact ne_of_gt hx

theorem ballRetraction_mem_closedBall {R : ℝ} (hR : 0 ≤ R) (x : X) :
    ‖ballRetraction R x‖ ≤ R := by
  rw [ballRetraction, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (ballRetraction_factor_nonneg hR x), ballRetraction_factor_mul_norm hR]
  exact min_le_right _ _

theorem ballRetraction_eq_self_of_mem {R : ℝ} {x : X} (hx : ‖x‖ ≤ R) :
    ballRetraction R x = x := by
  rw [ballRetraction]
  rcases eq_or_lt_of_le (norm_nonneg x) with hx0 | hx0
  · simp [norm_eq_zero.1 hx0.symm]
  · have : (1 : ℝ) ≤ R / ‖x‖ := (one_le_div hx0).2 hx
    rw [min_eq_left this, one_smul]

private theorem ballRetraction_eq_smul_of_lt {R : ℝ} {x : X} (hx : R < ‖x‖) :
    ballRetraction R x = (R / ‖x‖) • x := by
  have hle : R / ‖x‖ ≤ 1 := by
    rcases eq_or_lt_of_le (norm_nonneg x) with hx0 | hx0
    · rw [← hx0, div_zero]; exact zero_le_one
    · exact (div_le_one hx0).2 (le_of_lt hx)
  rw [ballRetraction, min_eq_right hle]

theorem lipschitzWith_ballRetraction {R : ℝ} (hR : 0 ≤ R) :
    LipschitzWith 2 (ballRetraction (X := X) R) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm]
  change ‖ballRetraction R x - ballRetraction R y‖ ≤ 2 * ‖x - y‖
  rcases eq_or_lt_of_le hR with rfl | hRpos
  · simp [ballRetraction]
  rcases le_or_gt ‖x‖ R with hx | hx
  · rcases le_or_gt ‖y‖ R with hy | hy
    · rw [ballRetraction_eq_self_of_mem hx, ballRetraction_eq_self_of_mem hy]
      exact (le_mul_of_one_le_left (norm_nonneg _) one_le_two)
    · rw [ballRetraction_eq_self_of_mem hx, ballRetraction_eq_smul_of_lt hy]
      have hy0 : 0 < ‖y‖ := hRpos.trans hy
      have hfac0 : 0 ≤ 1 - R / ‖y‖ := sub_nonneg.mpr
        ((div_le_one hy0).mpr hy.le)
      have hsplit :
          x - (R / ‖y‖) • y = (x - y) + (1 - R / ‖y‖) • y := by
        module
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hfac0]
      have hradial : (1 - R / ‖y‖) * ‖y‖ = ‖y‖ - R := by
        field_simp
      rw [hradial]
      have hnormdiff : ‖y‖ - R ≤ ‖x - y‖ := by
        have hxy := norm_sub_norm_le y x
        rw [norm_sub_rev] at hxy
        linarith
      linarith [norm_nonneg (x - y)]
  · rcases le_or_gt ‖y‖ R with hy | hy
    · rw [ballRetraction_eq_smul_of_lt hx, ballRetraction_eq_self_of_mem hy]
      have hx0 : 0 < ‖x‖ := hRpos.trans hx
      have hfac0 : 0 ≤ 1 - R / ‖x‖ := sub_nonneg.mpr
        ((div_le_one hx0).mpr hx.le)
      have hsplit :
          (R / ‖x‖) • x - y = (x - y) - (1 - R / ‖x‖) • x := by
        module
      rw [hsplit]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hfac0]
      have hradial : (1 - R / ‖x‖) * ‖x‖ = ‖x‖ - R := by
        field_simp
      rw [hradial]
      have hnormdiff : ‖x‖ - R ≤ ‖x - y‖ := by
        have hxy := norm_sub_norm_le x y
        linarith
      linarith [norm_nonneg (x - y)]
    · rw [ballRetraction_eq_smul_of_lt hx, ballRetraction_eq_smul_of_lt hy]
      have hx0 : 0 < ‖x‖ := hRpos.trans hx
      have hy0 : 0 < ‖y‖ := hRpos.trans hy
      wlog hxy : ‖x‖ ≤ ‖y‖ generalizing x y
      · have hswap := this y x hy hx hy0 hx0 (le_of_not_ge hxy)
        calc
          ‖(R / ‖x‖) • x - (R / ‖y‖) • y‖ =
              ‖(R / ‖y‖) • y - (R / ‖x‖) • x‖ := norm_sub_rev _ _
          _ ≤ 2 * ‖y - x‖ := hswap
          _ = 2 * ‖x - y‖ := by rw [norm_sub_rev]
      have ha0 : 0 ≤ R / ‖x‖ := div_nonneg hR (norm_nonneg x)
      have hb0 : 0 ≤ R / ‖y‖ := div_nonneg hR (norm_nonneg y)
      have hb1 : R / ‖y‖ ≤ 1 := (div_le_one hy0).mpr hy.le
      have hab : 0 ≤ R / ‖x‖ - R / ‖y‖ := by
        exact sub_nonneg.mpr (div_le_div_of_nonneg_left hR hx0 hxy)
      have hsplit :
          (R / ‖x‖) • x - (R / ‖y‖) • y =
            (R / ‖y‖) • (x - y) +
              (R / ‖x‖ - R / ‖y‖) • x := by
        module
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hb0, abs_of_nonneg hab]
      have hfirst :
          (R / ‖y‖) * ‖x - y‖ ≤ ‖x - y‖ :=
        mul_le_of_le_one_left (norm_nonneg _) hb1
      have hsecond :
          (R / ‖x‖ - R / ‖y‖) * ‖x‖ ≤ ‖x - y‖ := by
        have hformula :
            (R / ‖x‖ - R / ‖y‖) * ‖x‖ =
              (R / ‖y‖) * (‖y‖ - ‖x‖) := by
          field_simp
        rw [hformula]
        have hdiff : ‖y‖ - ‖x‖ ≤ ‖x - y‖ := by
          have := norm_sub_norm_le y x
          rw [norm_sub_rev] at this
          exact this
        exact (mul_le_of_le_one_left (sub_nonneg.mpr hxy) hb1).trans hdiff
      linarith

end Normed

section Hilbert

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

theorem lipschitzWith_one_ballRetraction {R : ℝ} (hR : 0 ≤ R) :
    LipschitzWith 1 (ballRetraction (X := X) R) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (norm_nonneg (x - y))]
  refine Real.sqrt_le_sqrt ?_
  set a : ℝ := min 1 (R / ‖x‖) with ha
  set b : ℝ := min 1 (R / ‖y‖) with hb
  have ha0 : 0 ≤ a := ballRetraction_factor_nonneg hR x
  have hb0 : 0 ≤ b := ballRetraction_factor_nonneg hR y
  have ha1 : a ≤ 1 := min_le_left _ _
  have hb1 : b ≤ 1 := min_le_left _ _
  have hax : a * ‖x‖ = min ‖x‖ R := ballRetraction_factor_mul_norm hR x
  have hby : b * ‖y‖ = min ‖y‖ R := ballRetraction_factor_mul_norm hR y
  rw [ballRetraction, ballRetraction, ← ha, ← hb, norm_sub_sq_real, norm_sub_sq_real,
    norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg ha0, abs_of_nonneg hb0, real_inner_smul_left, real_inner_smul_right]
  have hp0 : 0 ≤ ‖x‖ := norm_nonneg x
  have hq0 : 0 ≤ ‖y‖ := norm_nonneg y
  have hcs : ⟪x, y⟫_ℝ ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
  have hab : 0 ≤ 1 - a * b := by nlinarith [mul_le_one₀ ha1 hb0 hb1]
  have hmin : (a * ‖x‖ - b * ‖y‖) ^ 2 ≤ (‖x‖ - ‖y‖) ^ 2 := by
    rw [hax, hby]
    have hlip : LipschitzWith 1 (fun t : ℝ => min t R) := (LipschitzWith.id).min_const R
    have h1 : |min ‖x‖ R - min ‖y‖ R| ≤ |‖x‖ - ‖y‖| := by
      have := hlip.dist_le_mul ‖x‖ ‖y‖
      simpa [Real.dist_eq, NNReal.coe_one, one_mul] using this
    nlinarith [abs_nonneg (min ‖x‖ R - min ‖y‖ R), abs_nonneg (‖x‖ - ‖y‖),
      sq_abs (min ‖x‖ R - min ‖y‖ R), sq_abs (‖x‖ - ‖y‖),
      mul_self_le_mul_self (abs_nonneg (min ‖x‖ R - min ‖y‖ R)) h1]
  nlinarith [hmin, hab, hcs, mul_nonneg hp0 hq0,
    mul_nonneg hab (sub_nonneg.2 hcs)]

end Hilbert

section NormedDifference

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem norm_map_ballRetraction_sub_le {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] {R : ℝ} (hR : 0 < R) (J : X →L[ℝ] Y) (u u' : X) :
    ‖J (ballRetraction R u - ballRetraction R u')‖ ≤
      ‖J (u - u')‖ + (1 / R) * max ‖J u‖ ‖J u'‖ * ‖u - u'‖ := by
  have hRinv : 0 ≤ 1 / R := by positivity
  have hcu : ‖J u‖ ≤ max ‖J u‖ ‖J u'‖ := le_max_left _ _
  have hcu' : ‖J u'‖ ≤ max ‖J u‖ ‖J u'‖ := le_max_right _ _
  have hc0 : 0 ≤ max ‖J u‖ ‖J u'‖ := le_trans (norm_nonneg _) hcu
  have hD0 : 0 ≤ ‖u - u'‖ := norm_nonneg _
  have hcorr0 : 0 ≤ (1 / R) * max ‖J u‖ ‖J u'‖ * ‖u - u'‖ :=
    mul_nonneg (mul_nonneg hRinv hc0) hD0
  rcases le_or_gt ‖u‖ R with hu | hu
  · rcases le_or_gt ‖u'‖ R with hu' | hu'
    · rw [ballRetraction_eq_self_of_mem hu, ballRetraction_eq_self_of_mem hu']
      linarith [hcorr0]
    · rw [ballRetraction_eq_self_of_mem hu, ballRetraction_eq_smul_of_lt hu']
      have hu'0 : 0 < ‖u'‖ := lt_trans hR hu'
      have hkey : ‖J (u - (R / ‖u'‖) • u')‖ ≤
          ‖J (u - u')‖ + (1 - R / ‖u'‖) * ‖J u'‖ := by
        have hexp : J (u - (R / ‖u'‖) • u') = J (u - u') + (1 - R / ‖u'‖) • J u' := by
          simp only [map_sub, map_smul, sub_smul, one_smul]
          abel
        rw [hexp]
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_smul, Real.norm_eq_abs]
        have hpos : 0 ≤ 1 - R / ‖u'‖ := by
          have : R / ‖u'‖ ≤ 1 := (div_le_one hu'0).2 (le_of_lt hu')
          linarith
        rw [abs_of_nonneg hpos]
      refine le_trans hkey ?_
      have hgeo : ‖u'‖ - R ≤ ‖u - u'‖ := by
        have h1 : ‖u'‖ - ‖u‖ ≤ ‖u' - u‖ := norm_sub_norm_le _ _
        rw [norm_sub_rev] at h1
        linarith
      have hstep : (1 - R / ‖u'‖) * ‖J u'‖ ≤
          (1 / R) * max ‖J u‖ ‖J u'‖ * ‖u - u'‖ := by
        have e1 : (1 - R / ‖u'‖) * ‖J u'‖ = ((‖u'‖ - R) / ‖u'‖) * ‖J u'‖ := by
          field_simp
        rw [e1]
        have hfac : (‖u'‖ - R) / ‖u'‖ ≤ (‖u'‖ - R) / R := by
          apply div_le_div_of_nonneg_left (by linarith) hR (le_of_lt hu')
        have hjn : 0 ≤ ‖J u'‖ := norm_nonneg _
        calc ((‖u'‖ - R) / ‖u'‖) * ‖J u'‖
            ≤ ((‖u'‖ - R) / R) * ‖J u'‖ := by
              apply mul_le_mul_of_nonneg_right hfac hjn
          _ = (1 / R) * ‖J u'‖ * (‖u'‖ - R) := by ring
          _ ≤ (1 / R) * max ‖J u‖ ‖J u'‖ * ‖u - u'‖ := by
              apply mul_le_mul
              · apply mul_le_mul_of_nonneg_left hcu' hRinv
              · exact hgeo
              · linarith
              · exact mul_nonneg hRinv hc0
      linarith
  · rcases le_or_gt ‖u'‖ R with hu' | hu'
    · rw [ballRetraction_eq_smul_of_lt hu, ballRetraction_eq_self_of_mem hu']
      have hu0 : 0 < ‖u‖ := lt_trans hR hu
      have hkey : ‖J ((R / ‖u‖) • u - u')‖ ≤
          ‖J (u - u')‖ + (1 - R / ‖u‖) * ‖J u‖ := by
        have hexp : J ((R / ‖u‖) • u - u') = J (u - u') - (1 - R / ‖u‖) • J u := by
          simp only [map_sub, map_smul, sub_smul, one_smul]
          abel
        rw [hexp]
        refine le_trans (norm_sub_le _ _) ?_
        rw [norm_smul, Real.norm_eq_abs]
        have hpos : 0 ≤ 1 - R / ‖u‖ := by
          have : R / ‖u‖ ≤ 1 := (div_le_one hu0).2 (le_of_lt hu)
          linarith
        rw [abs_of_nonneg hpos]
      refine le_trans hkey ?_
      have hgeo : ‖u‖ - R ≤ ‖u - u'‖ := by
        have h1 : ‖u‖ - ‖u'‖ ≤ ‖u - u'‖ := norm_sub_norm_le _ _
        linarith
      have hstep : (1 - R / ‖u‖) * ‖J u‖ ≤
          (1 / R) * max ‖J u‖ ‖J u'‖ * ‖u - u'‖ := by
        have e1 : (1 - R / ‖u‖) * ‖J u‖ = ((‖u‖ - R) / ‖u‖) * ‖J u‖ := by
          field_simp
        rw [e1]
        have hfac : (‖u‖ - R) / ‖u‖ ≤ (‖u‖ - R) / R := by
          apply div_le_div_of_nonneg_left (by linarith) hR (le_of_lt hu)
        have hjn : 0 ≤ ‖J u‖ := norm_nonneg _
        calc ((‖u‖ - R) / ‖u‖) * ‖J u‖
            ≤ ((‖u‖ - R) / R) * ‖J u‖ := by
              apply mul_le_mul_of_nonneg_right hfac hjn
          _ = (1 / R) * ‖J u‖ * (‖u‖ - R) := by ring
          _ ≤ (1 / R) * max ‖J u‖ ‖J u'‖ * ‖u - u'‖ := by
              apply mul_le_mul
              · apply mul_le_mul_of_nonneg_left hcu hRinv
              · exact hgeo
              · linarith
              · exact mul_nonneg hRinv hc0
      linarith
    · rw [ballRetraction_eq_smul_of_lt hu, ballRetraction_eq_smul_of_lt hu']
      have hu0 : 0 < ‖u‖ := lt_trans hR hu
      have hu'0 : 0 < ‖u'‖ := lt_trans hR hu'
      have hexp : J ((R / ‖u‖) • u - (R / ‖u'‖) • u') =
          (R / ‖u‖) • J (u - u') + (R / ‖u‖ - R / ‖u'‖) • J u' := by
        simp only [map_sub, map_smul, smul_sub, sub_smul]
        abel
      rw [hexp]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hlu0 : 0 ≤ R / ‖u‖ := by positivity
      have hlu1 : R / ‖u‖ ≤ 1 := (div_le_one hu0).2 (le_of_lt hu)
      have hterm1 : |R / ‖u‖| * ‖J (u - u')‖ ≤ ‖J (u - u')‖ := by
        rw [abs_of_nonneg hlu0]
        nlinarith [norm_nonneg (J (u - u')), hlu1]
      have hdiff : |R / ‖u‖ - R / ‖u'‖| ≤ R * ‖u - u'‖ / (‖u‖ * ‖u'‖) := by
        have hd : R / ‖u‖ - R / ‖u'‖ = R * (‖u'‖ - ‖u‖) / (‖u‖ * ‖u'‖) := by
          rw [div_sub_div _ _ (ne_of_gt hu0) (ne_of_gt hu'0)]
          ring
        rw [hd, abs_div, abs_of_nonneg (le_of_lt (by positivity : (0:ℝ) < ‖u‖ * ‖u'‖))]
        rw [abs_mul, abs_of_nonneg (le_of_lt hR)]
        apply div_le_div_of_nonneg_right ?_ (by positivity)
        apply mul_le_mul_of_nonneg_left ?_ (le_of_lt hR)
        rw [abs_sub_comm]
        have h1 : ‖u‖ - ‖u'‖ ≤ ‖u - u'‖ := norm_sub_norm_le _ _
        have h2 : ‖u'‖ - ‖u‖ ≤ ‖u - u'‖ := by
          have := norm_sub_norm_le u' u; rw [norm_sub_rev] at this; linarith
        rw [abs_sub_le_iff]; exact ⟨h1, h2⟩
      have hterm2 : |R / ‖u‖ - R / ‖u'‖| * ‖J u'‖ ≤
          (1 / R) * max ‖J u‖ ‖J u'‖ * ‖u - u'‖ := by
        have hjn : 0 ≤ ‖J u'‖ := norm_nonneg _
        have hRsq : R * R ≤ ‖u‖ * ‖u'‖ :=
          mul_le_mul (le_of_lt hu) (le_of_lt hu') (le_of_lt hR) (le_of_lt hu0)
        have hRle1 : R / (‖u‖ * ‖u'‖) ≤ 1 / R := by
          rw [div_le_div_iff₀ (by positivity) hR]
          nlinarith [hRsq]
        calc |R / ‖u‖ - R / ‖u'‖| * ‖J u'‖
            ≤ (R * ‖u - u'‖ / (‖u‖ * ‖u'‖)) * ‖J u'‖ :=
              mul_le_mul_of_nonneg_right hdiff hjn
          _ = (R / (‖u‖ * ‖u'‖)) * (‖J u'‖ * ‖u - u'‖) := by ring
          _ ≤ (1 / R) * (max ‖J u‖ ‖J u'‖ * ‖u - u'‖) := by
              apply mul_le_mul hRle1 ?_ ?_ hRinv
              · exact mul_le_mul_of_nonneg_right hcu' hD0
              · exact mul_nonneg hjn hD0
          _ = (1 / R) * max ‖J u‖ ‖J u'‖ * ‖u - u'‖ := by ring
      linarith

end NormedDifference

end DifferentialGeometry.Analysis.Calculus

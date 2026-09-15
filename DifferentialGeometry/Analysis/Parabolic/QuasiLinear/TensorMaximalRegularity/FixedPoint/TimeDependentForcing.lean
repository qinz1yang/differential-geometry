import DifferentialGeometry.Analysis.FunctionalAnalysis.Contraction.ClosedBall
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Nemytskii.TimeDependentDifference

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

theorem tame_forcing_contraction_bounds {R T D : ℝ}
    (hR : 0 ≤ R) (hT1 : T ≤ 1) (A B C : ℝ≥0) (hD : 0 ≤ D)
    (hTlo : T ≤ 1 / (64 * ((B : ℝ) + 1) ^ 2))
    (hTstay : T ≤ ((R / 4) / (2 * (D + 1))) ^ 2)
    (hsmallA : (A : ℝ) * R ≤ 1 / 16)
    (hsmallC : (C : ℝ) * R ≤ 1 / 16) :
    let κ := (A : ℝ) * R * (1 + T) + (B : ℝ) * Real.sqrt T * Real.sqrt (1 + T) +
      2 * (C : ℝ) * (R / 4) * Real.sqrt (1 + T) * (1 + T)
    Real.sqrt (1 + T) * (R / 4) ≤ R ∧ κ ≤ 1 / 2 ∧
      Real.sqrt T * D ≤ (1 - κ) * (R / 4) := by
  let ρ := R / 4
  let κ := (A : ℝ) * R * (1 + T) + (B : ℝ) * Real.sqrt T * Real.sqrt (1 + T) +
    2 * (C : ℝ) * ρ * Real.sqrt (1 + T) * (1 + T)
  have hsqrt : Real.sqrt (1 + T) ≤ 2 := by
    rw [← Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hκle : κ ≤ 1 / 2 := by
    have ha : (A : ℝ) * R * (1 + T) ≤ 1 / 8 := by
      nlinarith [mul_le_mul_of_nonneg_left (show 1 + T ≤ 2 by linarith)
        (mul_nonneg A.coe_nonneg hR)]
    have hst : Real.sqrt T ≤ 1 / (8 * ((B : ℝ) + 1)) := by
      rw [show 1 / (8 * ((B : ℝ) + 1)) = Real.sqrt ((1 / (8 * ((B : ℝ) + 1))) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      apply Real.sqrt_le_sqrt
      convert hTlo using 1
      rw [div_pow, one_pow, mul_pow]
      norm_num
    have hb : (B : ℝ) * Real.sqrt T * Real.sqrt (1 + T) ≤ 1 / 4 := by
      have hb' : (B : ℝ) * (2 * Real.sqrt T) ≤ 1 / 4 := by
        calc
          _ ≤ (B : ℝ) * (2 * (1 / (8 * ((B : ℝ) + 1)))) := by gcongr
          _ ≤ 1 / 4 := by
            have hfrac : (B : ℝ) / ((B : ℝ) + 1) ≤ 1 := by
              rw [div_le_one (by positivity)]
              linarith [B.coe_nonneg]
            have he : (B : ℝ) * (2 * (1 / (8 * ((B : ℝ) + 1)))) =
                ((B : ℝ) / ((B : ℝ) + 1)) * (1 / 4) := by field_simp; ring
            rw [he]
            nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hsqrt
        (mul_nonneg B.coe_nonneg (Real.sqrt_nonneg T))]
    have hc : 2 * (C : ℝ) * ρ * Real.sqrt (1 + T) * (1 + T) ≤ 1 / 8 := by
      calc
        _ ≤ 2 * (C : ℝ) * ρ * Real.sqrt (1 + T) * 2 := by
          apply mul_le_mul_of_nonneg_left (by linarith)
          dsimp only [ρ]
          positivity
        _ ≤ 2 * (C : ℝ) * ρ * 2 * 2 := by
          apply mul_le_mul_of_nonneg_right _ (by norm_num)
          apply mul_le_mul_of_nonneg_left hsqrt
          dsimp only [ρ]
          positivity
        _ = 2 * ((C : ℝ) * R) := by dsimp only [ρ]; ring
        _ ≤ 1 / 8 := by linarith
    dsimp only [κ]
    linarith
  refine ⟨?_, hκle, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_right hsqrt (show 0 ≤ R / 4 by positivity)]
  · have hst : Real.sqrt T ≤ ρ / (2 * (D + 1)) := by
      rw [show ρ / (2 * (D + 1)) = Real.sqrt ((ρ / (2 * (D + 1))) ^ 2) from
        (Real.sqrt_sq (by dsimp only [ρ]; positivity)).symm]
      exact Real.sqrt_le_sqrt hTstay
    have hD1 : 0 < D + 1 := by linarith
    calc
      _ ≤ (ρ / (2 * (D + 1))) * D := mul_le_mul_of_nonneg_right hst hD
      _ ≤ (ρ / (2 * (D + 1))) * (D + 1) := by
        apply mul_le_mul_of_nonneg_left (by linarith)
        dsimp only [ρ]
        positivity
      _ = ρ / 2 := by field_simp
      _ ≤ (1 - κ) * ρ := by dsimp only [ρ]; nlinarith


variable {X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

omit [CompleteSpace Y] in
private theorem lower_field_mem {T R ρ P : ℝ}
    (J : X →L[ℝ] Z) (L : timeL2 Y T →L[ℝ] timeL2 X T)
    (hP : 0 ≤ P) (hPR : P * ρ ≤ R)
    (hpoint : ∀ F, ∀ᵐ t ∂(timeMeasure T), ‖J (L F t)‖ ≤ P * ‖F‖)
    (F : timeL2 Y T) (hF : ‖F‖ ≤ ρ) :
    ∀ᵐ t ∂(timeMeasure T), L F t ∈ {x : X | ‖J x‖ ≤ R} := by
  filter_upwards [hpoint F] with t ht
  exact ht.trans ((mul_le_mul_of_nonneg_left hF hP).trans hPR)

theorem exists_fixed_forcing_of_tame
    {T R ρ H P : ℝ} (hR : 0 ≤ R) (hρ : 0 ≤ ρ)
    (hH : 0 ≤ H) (hP : 0 ≤ P)
    (J : X →L[ℝ] Z) (L : timeL2 Y T →L[ℝ] timeL2 X T)
    (hL : ∀ F, ‖L F‖ ≤ H * ‖F‖)
    (hpoint : ∀ F, ∀ᵐ t ∂(timeMeasure T), ‖J (L F t)‖ ≤ P * ‖F‖)
    (hPR : P * ρ ≤ R)
    (N : ℝ → {x : X | ‖J x‖ ≤ R} → Y)
    (A B C : ℝ≥0) (D : ℝ) (hD : 0 ≤ D)
    (hzero : ∀ᵐ t ∂(timeMeasure T), ‖N t ⟨0, by simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR⟩‖ ≤ D)
    (htame : ∀ᵐ t ∂(timeMeasure T), ∀ u v : {x : X | ‖J x‖ ≤ R},
      ‖N t u - N t v‖ ≤
        (A : ℝ) * R * ‖(u : X) - (v : X)‖ +
        (B : ℝ) * ‖J ((u : X) - (v : X))‖ +
        (C : ℝ) * (‖(u : X)‖ + ‖(v : X)‖) * ‖J ((u : X) - (v : X))‖)
    (hmeas : ∀ (f : timeL2 X T) (_ : ∀ᵐ t ∂(timeMeasure T), f t ∈ {x : X | ‖J x‖ ≤ R}),
      AEStronglyMeasurable (fun t => N t (aeSetLift
        (show (0 : X) ∈ {x : X | ‖J x‖ ≤ R} by simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR) f t)) (timeMeasure T))
    (hκ : (A : ℝ) * R * H + (B : ℝ) * Real.sqrt T * P + 2 * (C : ℝ) * ρ * P * H < 1)
    (hstay : Real.sqrt T * D ≤
      (1 - ((A : ℝ) * R * H + (B : ℝ) * Real.sqrt T * P + 2 * (C : ℝ) * ρ * P * H)) * ρ) :
    ∃ F : timeL2 Y T, ‖F‖ ≤ ρ ∧
      (∀ᵐ t ∂(timeMeasure T), L F t ∈ {x : X | ‖J x‖ ≤ R}) ∧
      F =ᵐ[timeMeasure T] fun t => N t (aeSetLift
        (show (0 : X) ∈ {x : X | ‖J x‖ ≤ R} by simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR) (L F) t) := by
  classical
  let hz : (0 : X) ∈ {x : X | ‖J x‖ ≤ R} := by simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR
  let S := {x : X | ‖J x‖ ≤ R}
  let ball := Metric.closedBall (0 : timeL2 Y T) ρ
  have hstate : ∀ (F : ball), ∀ᵐ t ∂(timeMeasure T), L F t ∈ S := by
    intro F
    apply lower_field_mem J L hP hPR hpoint F
    simpa only [ball, Metric.mem_closedBall, dist_zero_right] using F.property
  let Φ : ball → timeL2 Y T := fun F => timeNemyTame hz hR J
    (fun u => u.property) N A B C D hD hzero htame (L F) (hstate F)
      (hmeas (L F) (hstate F))
  let κ : ℝ := (A : ℝ) * R * H + (B : ℝ) * Real.sqrt T * P + 2 * (C : ℝ) * ρ * P * H
  have hκ0 : 0 ≤ κ := by dsimp only [κ]; positivity
  have hΦ : ∀ (F G : ball), ‖Φ F - Φ G‖ ≤ κ * ‖(F : timeL2 Y T) - G‖ := by
    intro F G
    have hpt : ∀ᵐ t ∂(timeMeasure T), ‖J (((L F) - (L G)) t)‖ ≤ P * ‖(F : timeL2 Y T) - G‖ := by
      rw [← map_sub]
      exact hpoint ((F : timeL2 Y T) - G)
    have hJL : ‖J.compLpL 2 (timeMeasure T) (L F - L G)‖ ≤
        Real.sqrt T * (P * ‖(F : timeL2 Y T) - G‖) := by
      apply timeL2_norm_le_of_ae_bound _ (by positivity)
      filter_upwards [J.coeFn_compLpL (p := 2) (μ := timeMeasure T) (L F - L G), hpt] with t ht hp
      rw [ht]
      exact hp
    have hLn : ‖L F - L G‖ ≤ H * ‖(F : timeL2 Y T) - G‖ := by
      rw [← map_sub]
      exact hL _
    have hLF : ‖L F‖ ≤ H * ρ := (hL F).trans (mul_le_mul_of_nonneg_left
      (show ‖(F : timeL2 Y T)‖ ≤ ρ by simpa only [ball, Metric.mem_closedBall, dist_zero_right] using F.property) hH)
    have hLG : ‖L G‖ ≤ H * ρ := (hL G).trans (mul_le_mul_of_nonneg_left
      (show ‖(G : timeL2 Y T)‖ ≤ ρ by simpa only [ball, Metric.mem_closedBall, dist_zero_right] using G.property) hH)
    have hraw := timeNemyTame_sub_norm_le hz hR J (fun u => u.property) N A B C D hD hzero htame
      (L F) (L G) (hstate F) (hstate G) (hmeas (L F) (hstate F)) (hmeas (L G) (hstate G))
      (mul_nonneg hP (norm_nonneg _)) hpt
    change ‖Φ F - Φ G‖ ≤ _
    refine hraw.trans ?_
    calc
      _ ≤ (A : ℝ) * R * (H * ‖(F : timeL2 Y T) - G‖) +
          (B : ℝ) * (Real.sqrt T * (P * ‖(F : timeL2 Y T) - G‖)) +
          (C : ℝ) * (P * ‖(F : timeL2 Y T) - G‖) * (H * ρ + H * ρ) := by
            gcongr
      _ = κ * ‖(F : timeL2 Y T) - G‖ := by dsimp only [κ]; ring
  let zeroBall : ball := ⟨0, by simpa only [ball, Metric.mem_closedBall, dist_self] using hρ⟩
  have hΦ0 : ‖Φ zeroBall‖ ≤ Real.sqrt T * D := by
    apply timeL2_norm_le_of_ae_bound _ hD
    have hcoe := timeNemyTame_ae hz hR J (fun u => u.property) N A B C D hD hzero htame
      (L zeroBall) (hstate zeroBall) (hmeas (L zeroBall) (hstate zeroBall))
    have hzL : L (zeroBall : timeL2 Y T) = 0 := map_zero L
    have hzcoe := Lp.coeFn_zero (E := X) (p := 2) (μ := timeMeasure T)
    filter_upwards [hcoe, hzcoe, hzero] with t ht hzt hn
    change ‖timeNemyTame hz hR J (fun u => u.property) N A B C D hD hzero htame
      (L zeroBall) (hstate zeroBall) (hmeas (L zeroBall) (hstate zeroBall)) t‖ ≤ D
    rw [ht]
    have hlift : aeSetLift hz (L zeroBall) t = ⟨0, hz⟩ := by
      apply Subtype.ext
      simp only [hzL, aeSetLift]
      split_ifs with hc
      · exact hzt
      · rfl
    rw [hlift]
    exact hn
  let Ψ : timeL2 Y T → timeL2 Y T := fun F => if h : F ∈ ball then Φ ⟨F, h⟩ else 0
  have hzeroBall : (0 : timeL2 Y T) ∈ ball := zeroBall.property
  have hΨ0 : ‖Ψ 0‖ ≤ (1 - (κ.toNNReal : ℝ)) * ρ := by
    simpa only [Ψ, dif_pos hzeroBall, Real.coe_toNNReal _ hκ0] using hΦ0.trans hstay
  have hΨ : LipschitzOnWith κ.toNNReal Ψ ball := by
    apply LipschitzOnWith.of_dist_le_mul
    intro F hF G hG
    simp only [Ψ, dif_pos hF, dif_pos hG, dist_eq_norm, Real.coe_toNNReal _ hκ0]
    exact hΦ ⟨F, hF⟩ ⟨G, hG⟩
  have hκnn : κ.toNNReal < 1 := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hκ0]
    exact hκ
  obtain ⟨F, ⟨hF, hfix⟩, _⟩ := DifferentialGeometry.Analysis.exists_unique_fixedPoint_mem_closedBall
    (Φ := Ψ) hρ hκnn hΨ0 hΨ
  let Fball : ball := ⟨F, hF⟩
  have hfix' : Φ Fball = F := by
    change (if h : F ∈ ball then Φ ⟨F, h⟩ else 0) = F at hfix
    rw [dif_pos (show F ∈ ball from hF)] at hfix
    exact hfix
  refine ⟨F, ?_, hstate Fball, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hF
  · have hcoe := timeNemyTame_ae hz hR J (fun u => u.property) N A B C D hD hzero htame
      (L Fball) (hstate Fball) (hmeas (L Fball) (hstate Fball))
    exact (Filter.EventuallyEq.of_eq (congrArg (fun w : timeL2 Y T => (w : ℝ → Y)) hfix'.symm)).trans hcoe

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

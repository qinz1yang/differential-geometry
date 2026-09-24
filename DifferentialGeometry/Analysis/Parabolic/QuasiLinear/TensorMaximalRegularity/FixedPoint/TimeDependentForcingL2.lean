import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import DifferentialGeometry.Analysis.FunctionalAnalysis.Contraction.ClosedBall
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Nemytskii.TimeDependentL2

section

open scoped NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

theorem tame_forcing_contraction_bounds_of_integrated_bounds
    {R T b f : ℝ} (hR : 0 ≤ R) (hT : T ≤ 1) (A C : ℝ≥0)
    (hb : b ≤ 1 / 8) (hf : f ≤ R / 8)
    (hA : (A : ℝ) * R ≤ 1 / 16) (hC : (C : ℝ) * R ≤ 1 / 16) :
    let κ := (A : ℝ) * R * (1 + T) + b * Real.sqrt (1 + T) +
      2 * (C : ℝ) * (R / 4) * Real.sqrt (1 + T) * (1 + T)
    Real.sqrt (1 + T) * (R / 4) ≤ R ∧ κ ≤ 1 / 2 ∧
      f ≤ (1 - κ) * (R / 4) := by
  let κ := (A : ℝ) * R * (1 + T) + b * Real.sqrt (1 + T) +
    2 * (C : ℝ) * (R / 4) * Real.sqrt (1 + T) * (1 + T)
  have hsqrt : Real.sqrt (1 + T) ≤ 2 := by
    rw [← Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have ha : (A : ℝ) * R * (1 + T) ≤ 1 / 8 := by
    nlinarith [mul_le_mul_of_nonneg_left (show 1 + T ≤ 2 by linarith)
      (mul_nonneg A.coe_nonneg hR)]
  have hb' : b * Real.sqrt (1 + T) ≤ 1 / 4 := by
    calc
      _ ≤ (1 / 8) * Real.sqrt (1 + T) :=
        mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg _)
      _ ≤ (1 / 8) * 2 := mul_le_mul_of_nonneg_left hsqrt (by norm_num)
      _ = 1 / 4 := by norm_num
  have hc : 2 * (C : ℝ) * (R / 4) * Real.sqrt (1 + T) * (1 + T) ≤ 1 / 8 := by
    calc
      _ ≤ 2 * (C : ℝ) * (R / 4) * Real.sqrt (1 + T) * 2 := by
        apply mul_le_mul_of_nonneg_left (by linarith)
        positivity
      _ ≤ 2 * (C : ℝ) * (R / 4) * 2 * 2 := by
        apply mul_le_mul_of_nonneg_right _ (by norm_num)
        apply mul_le_mul_of_nonneg_left hsqrt
        positivity
      _ = 2 * ((C : ℝ) * R) := by ring
      _ ≤ 1 / 8 := by linarith
  have hκ : κ ≤ 1 / 2 := by
    dsimp only [κ]
    linarith
  refine ⟨?_, hκ, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_right hsqrt (show 0 ≤ R / 4 by positivity)]
  · exact hf.trans (by nlinarith [mul_le_mul_of_nonneg_right hκ hR])

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem exists_fixed_forcing_of_tame_timeL2
    {T R ρ H P : ℝ} (hR : 0 ≤ R) (hρ : 0 ≤ ρ)
    (hH : 0 ≤ H) (hP : 0 ≤ P)
    (J : X →L[ℝ] Z) (L : timeL2 Y T →L[ℝ] timeL2 X T)
    (hL : ∀ F, ‖L F‖ ≤ H * ‖F‖)
    (hpoint : ∀ F, ∀ᵐ t ∂(timeMeasure T), ‖J (L F t)‖ ≤ P * ‖F‖)
    (hPR : P * ρ ≤ R)
    (N : ℝ → {x : X | ‖J x‖ ≤ R} → Y)
    (A C : ℝ≥0) (B : timeL2 ℝ T) (F0 : timeL2 Y T)
    (hzero : ∀ᵐ t ∂(timeMeasure T), N t ⟨0, by simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR⟩ = F0 t)
    (htame : ∀ᵐ t ∂(timeMeasure T), ∀ u v : {x : X | ‖J x‖ ≤ R},
      ‖N t u - N t v‖ ≤
        (A : ℝ) * R * ‖(u : X) - (v : X)‖ +
        ‖B t‖ * ‖J ((u : X) - (v : X))‖ +
        (C : ℝ) * (‖(u : X)‖ + ‖(v : X)‖) * ‖J ((u : X) - (v : X))‖)
    (hmeas : ∀ (f : timeL2 X T) (_ : ∀ᵐ t ∂(timeMeasure T), f t ∈ {x : X | ‖J x‖ ≤ R}),
      AEStronglyMeasurable (fun t => N t (aeSetLift
        (show (0 : X) ∈ {x : X | ‖J x‖ ≤ R} by simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR) f t)) (timeMeasure T))
    (hκ : (A : ℝ) * R * H + ‖B‖ * P + 2 * (C : ℝ) * ρ * P * H < 1)
    (hstay : ‖F0‖ ≤
      (1 - ((A : ℝ) * R * H + ‖B‖ * P + 2 * (C : ℝ) * ρ * P * H)) * ρ) :
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
    have hF : ‖(F : timeL2 Y T)‖ ≤ ρ := by
      simpa only [ball, Metric.mem_closedBall, dist_zero_right] using F.property
    filter_upwards [hpoint F] with t ht
    exact ht.trans ((mul_le_mul_of_nonneg_left hF hP).trans hPR)
  let Φ : ball → timeL2 Y T := fun F => timeNemyTameL2 hz hR J
    (fun u => u.property) N A C B F0 hzero htame (L F) (hstate F)
      (hmeas (L F) (hstate F))
  let κ : ℝ := (A : ℝ) * R * H + ‖B‖ * P + 2 * (C : ℝ) * ρ * P * H
  have hκ0 : 0 ≤ κ := by dsimp only [κ]; positivity
  have hΦ : ∀ (F G : ball), ‖Φ F - Φ G‖ ≤ κ * ‖(F : timeL2 Y T) - G‖ := by
    intro F G
    have hpt : ∀ᵐ t ∂(timeMeasure T), ‖J (((L F) - (L G)) t)‖ ≤ P * ‖(F : timeL2 Y T) - G‖ := by
      rw [← map_sub]
      exact hpoint ((F : timeL2 Y T) - G)
    have hLn : ‖L F - L G‖ ≤ H * ‖(F : timeL2 Y T) - G‖ := by
      rw [← map_sub]
      exact hL _
    have hLF : ‖L F‖ ≤ H * ρ := (hL F).trans (mul_le_mul_of_nonneg_left
      (show ‖(F : timeL2 Y T)‖ ≤ ρ by simpa only [ball, Metric.mem_closedBall, dist_zero_right] using F.property) hH)
    have hLG : ‖L G‖ ≤ H * ρ := (hL G).trans (mul_le_mul_of_nonneg_left
      (show ‖(G : timeL2 Y T)‖ ≤ ρ by simpa only [ball, Metric.mem_closedBall, dist_zero_right] using G.property) hH)
    have hraw := timeNemyTameL2_sub_norm_le hz hR J (fun u => u.property) N A C B F0 hzero htame
      (L F) (L G) (hstate F) (hstate G) (hmeas (L F) (hstate F)) (hmeas (L G) (hstate G))
      (mul_nonneg hP (norm_nonneg _)) hpt
    change ‖Φ F - Φ G‖ ≤ _
    refine hraw.trans ?_
    calc
      _ ≤ (A : ℝ) * R * (H * ‖(F : timeL2 Y T) - G‖) +
          ‖B‖ * (P * ‖(F : timeL2 Y T) - G‖) +
          (C : ℝ) * (P * ‖(F : timeL2 Y T) - G‖) * (H * ρ + H * ρ) := by
            gcongr
      _ = κ * ‖(F : timeL2 Y T) - G‖ := by dsimp only [κ]; ring
  let zeroBall : ball := ⟨0, by simpa only [ball, Metric.mem_closedBall, dist_self] using hρ⟩
  have hΦ0 : ‖Φ zeroBall‖ ≤ ‖F0‖ := by
    have hcoe := timeNemyTameL2_ae hz hR J (fun u => u.property) N A C B F0 hzero htame
      (L zeroBall) (hstate zeroBall) (hmeas (L zeroBall) (hstate zeroBall))
    have hzL : L (zeroBall : timeL2 Y T) = 0 := map_zero L
    have hzcoe := Lp.coeFn_zero (E := X) (p := 2) (μ := timeMeasure T)
    have heq : Φ zeroBall = F0 := by
      apply Lp.ext
      filter_upwards [hcoe, hzcoe, hzero] with t ht hzt hn
      change timeNemyTameL2 hz hR J (fun u => u.property) N A C B F0 hzero htame
        (L zeroBall) (hstate zeroBall) (hmeas (L zeroBall) (hstate zeroBall)) t = F0 t
      rw [ht]
      have hlift : aeSetLift hz (L zeroBall) t = ⟨0, hz⟩ := by
        apply Subtype.ext
        simp only [hzL, aeSetLift]
        split_ifs with hc
        · exact hzt
        · rfl
      rw [hlift]
      exact hn
    exact (congrArg norm heq).le
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
  · have hcoe := timeNemyTameL2_ae hz hR J (fun u => u.property) N A C B F0 hzero htame
      (L Fball) (hstate Fball) (hmeas (L Fball) (hstate Fball))
    exact (Filter.EventuallyEq.of_eq (congrArg (fun w : timeL2 Y T => (w : ℝ → Y)) hfix'.symm)).trans hcoe

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

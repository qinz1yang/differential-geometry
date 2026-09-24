import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Nemytskii.TimeDependentDifference

open MeasureTheory Filter Set
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem tame_fixed_forcing_sub_norm_le
    {T R ρ H P : ℝ} {S : Set X} (hzero : (0 : X) ∈ S) (hR : 0 ≤ R)
    (J : X →L[ℝ] Z) (hstate : ∀ u : S, ‖J (u : X)‖ ≤ R)
    (N : ℝ → S → Y) (A B C : ℝ≥0) (D : ℝ) (hD : 0 ≤ D)
    (hzeroN : ∀ᵐ t ∂(timeMeasure T), ‖N t ⟨0, hzero⟩‖ ≤ D)
    (htame : ∀ᵐ t ∂(timeMeasure T), ∀ u v : S,
      ‖N t u - N t v‖ ≤
        (A : ℝ) * R * ‖(u : X) - (v : X)‖ +
        (B : ℝ) * ‖J ((u : X) - (v : X))‖ +
        (C : ℝ) * (‖(u : X)‖ + ‖(v : X)‖) *
          ‖J ((u : X) - (v : X))‖)
    (L : timeL2 Y T →L[ℝ] timeL2 X T)
    (hL : ∀ F, ‖L F‖ ≤ H * ‖F‖)
    (hH : 0 ≤ H) (hP : 0 ≤ P)
    (hpoint : ∀ F, ∀ᵐ t ∂(timeMeasure T), ‖J (L F t)‖ ≤ P * ‖F‖)
    (F G : timeL2 Y T)
    (hstateF : ∀ᵐ t ∂(timeMeasure T), L F t ∈ S)
    (hstateG : ∀ᵐ t ∂(timeMeasure T), L G t ∈ S)
    (hF : F =ᵐ[timeMeasure T] fun t => N t (aeSetLift hzero (L F) t))
    (hmeasG : AEStronglyMeasurable
      (fun t => N t (aeSetLift hzero (L G) t)) (timeMeasure T))
    {ε κ : ℝ} (hcross :
      ‖timeNemyTame hzero hR J hstate N A B C D hD hzeroN htame (L G)
        hstateG hmeasG - G‖ ≤ ε)
    (hκ : (A : ℝ) * R * H + (B : ℝ) * Real.sqrt T * P +
      2 * (C : ℝ) * ρ * P * H ≤ κ)
    (hρF : ‖F‖ ≤ ρ) (hρG : ‖G‖ ≤ ρ)
    (hκlt : κ < 1) :
    ‖F - G‖ ≤ ε / (1 - κ) := by
  let NF := timeNemyTame hzero hR J hstate N A B C D hD hzeroN htame (L F)
    hstateF (Lp.aestronglyMeasurable F |>.congr hF)
  let NG := timeNemyTame hzero hR J hstate N A B C D hD hzeroN htame (L G)
    hstateG hmeasG
  have hNF : NF = F := by
    apply Lp.ext
    exact (timeNemyTame_ae hzero hR J hstate N A B C D hD hzeroN htame (L F)
      hstateF (Lp.aestronglyMeasurable F |>.congr hF)).trans hF.symm
  have hpt : ∀ᵐ t ∂(timeMeasure T), ‖J ((L F - L G) t)‖ ≤ P * ‖F - G‖ := by
    rw [← map_sub]
    exact hpoint (F - G)
  have hJL : ‖J.compLpL 2 (timeMeasure T) (L F - L G)‖ ≤
      Real.sqrt T * (P * ‖F - G‖) := by
    apply timeL2_norm_le_of_ae_bound _ (mul_nonneg hP (norm_nonneg _))
    filter_upwards [J.coeFn_compLpL (p := 2) (μ := timeMeasure T) (L F - L G), hpt]
      with t ht hp
    rw [ht]
    exact hp
  have hLn : ‖L F - L G‖ ≤ H * ‖F - G‖ := by
    rw [← map_sub]
    exact hL _
  have hLF : ‖L F‖ ≤ H * ρ :=
    (hL F).trans (mul_le_mul_of_nonneg_left hρF hH)
  have hLG : ‖L G‖ ≤ H * ρ :=
    (hL G).trans (mul_le_mul_of_nonneg_left hρG hH)
  have hraw := timeNemyTame_sub_norm_le hzero hR J hstate N A B C D hD hzeroN htame
    (L F) (L G) hstateF hstateG (Lp.aestronglyMeasurable F |>.congr hF) hmeasG
    (mul_nonneg hP (norm_nonneg _)) hpt
  have hdiff : ‖NF - NG‖ ≤ κ * ‖F - G‖ := by
    calc
      ‖NF - NG‖ ≤ (A : ℝ) * R * ‖L F - L G‖ +
          (B : ℝ) * ‖J.compLpL 2 (timeMeasure T) (L F - L G)‖ +
          (C : ℝ) * (P * ‖F - G‖) * (‖L F‖ + ‖L G‖) := hraw
      _ ≤ (A : ℝ) * R * (H * ‖F - G‖) +
          (B : ℝ) * (Real.sqrt T * (P * ‖F - G‖)) +
          (C : ℝ) * (P * ‖F - G‖) * (H * ρ + H * ρ) := by
        gcongr
      _ = ((A : ℝ) * R * H + (B : ℝ) * Real.sqrt T * P +
          2 * (C : ℝ) * ρ * P * H) * ‖F - G‖ := by ring
      _ ≤ κ * ‖F - G‖ := mul_le_mul_of_nonneg_right hκ (norm_nonneg _)
  have htriangle : ‖F - G‖ ≤ κ * ‖F - G‖ + ε := by
    calc
      ‖F - G‖ = ‖(NF - NG) + (NG - G)‖ := by rw [hNF]; congr 1; abel
      _ ≤ ‖NF - NG‖ + ‖NG - G‖ := norm_add_le _ _
      _ ≤ κ * ‖F - G‖ + ε := add_le_add hdiff hcross
  apply (le_div_iff₀ (sub_pos.mpr hκlt)).mpr
  nlinarith
end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Nemytskii.TimeDependent

open MeasureTheory
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem timeNemyTame_sub_norm_le
    {T R : ℝ} {S : Set X} (hzero : (0 : X) ∈ S) (hR : 0 ≤ R)
    (J : X →L[ℝ] Z) (hstate : ∀ u : S, ‖J (u : X)‖ ≤ R)
    (N : ℝ → S → Y) (A B C : ℝ≥0) (D : ℝ) (hD : 0 ≤ D)
    (hzeroN : ∀ᵐ t ∂(timeMeasure T), ‖N t ⟨0, hzero⟩‖ ≤ D)
    (htame : ∀ᵐ t ∂(timeMeasure T), ∀ u v : S,
      ‖N t u - N t v‖ ≤
        (A : ℝ) * R * ‖(u : X) - (v : X)‖ +
          (B : ℝ) * ‖J ((u : X) - (v : X))‖ +
          (C : ℝ) * (‖(u : X)‖ + ‖(v : X)‖) *
            ‖J ((u : X) - (v : X))‖)
    (f g : timeL2 X T)
    (hf : ∀ᵐ t ∂(timeMeasure T), f t ∈ S)
    (hg : ∀ᵐ t ∂(timeMeasure T), g t ∈ S)
    (hmeasf : AEStronglyMeasurable
      (fun t => N t (aeSetLift hzero f t)) (timeMeasure T))
    (hmeasg : AEStronglyMeasurable
      (fun t => N t (aeSetLift hzero g t)) (timeMeasure T))
    {P : ℝ} (hP : 0 ≤ P)
    (hpoint : ∀ᵐ t ∂(timeMeasure T), ‖J ((f - g) t)‖ ≤ P) :
    ‖timeNemyTame hzero hR J hstate N A B C D hD hzeroN htame f hf hmeasf -
      timeNemyTame hzero hR J hstate N A B C D hD hzeroN htame g hg hmeasg‖ ≤
      (A : ℝ) * R * ‖f - g‖ +
        (B : ℝ) * ‖J.compLpL 2 (timeMeasure T) (f - g)‖ +
        (C : ℝ) * P * (‖f‖ + ‖g‖) := by
  let F := timeNemyTame hzero hR J hstate N A B C D hD hzeroN htame f hf hmeasf
  let G := timeNemyTame hzero hR J hstate N A B C D hD hzeroN htame g hg hmeasg
  let j := J.compLpL 2 (timeMeasure T) (f - g)
  have hF := timeNemyTame_ae hzero hR J hstate N A B C D hD hzeroN htame f hf hmeasf
  have hG := timeNemyTame_ae hzero hR J hstate N A B C D hD hzeroN htame g hg hmeasg
  have hbound : ∀ᵐ t ∂(timeMeasure T),
      ‖(F - G) t‖ ≤ (A : ℝ) * R * ‖(f - g) t‖ +
        (B : ℝ) * ‖j t‖ + (C : ℝ) * P * ‖f t‖ + (C : ℝ) * P * ‖g t‖ := by
    filter_upwards [Lp.coeFn_sub F G, hF, hG, hf, hg, htame,
      Lp.coeFn_sub f g, J.coeFn_compLpL (p := 2) (μ := timeMeasure T) (f - g), hpoint]
      with t hFG hFt hGt hft hgt hNt hfg hj hp
    rw [hFG, Pi.sub_apply, hFt, hGt]
    simp only [aeSetLift, dif_pos hft, dif_pos hgt]
    have hraw := hNt ⟨f t, hft⟩ ⟨g t, hgt⟩
    have hfg' : f t - g t = (f - g) t := hfg.symm
    have hj' : J ((f - g) t) = j t := hj.symm
    simp only [hfg', hj'] at hraw
    rw [hj'] at hp
    calc
      _ ≤ (A : ℝ) * R * ‖(f - g) t‖ + (B : ℝ) * ‖j t‖ +
          (C : ℝ) * (‖f t‖ + ‖g t‖) * ‖j t‖ := hraw
      _ ≤ (A : ℝ) * R * ‖(f - g) t‖ + (B : ℝ) * ‖j t‖ +
          (C : ℝ) * (‖f t‖ + ‖g t‖) * P :=
        add_le_add_right (mul_le_mul_of_nonneg_left hp (by positivity)) _
      _ = _ := by ring
  have hmain := timeL2_norm_le_four (F - G) (f - g) j f g
    (mul_nonneg A.coe_nonneg hR) B.coe_nonneg
    (mul_nonneg C.coe_nonneg hP) (mul_nonneg C.coe_nonneg hP) hbound
  change ‖F - G‖ ≤ _
  convert hmain using 1
  ring

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

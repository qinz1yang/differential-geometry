import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Nemytskii.Local

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem memLp_time_tame_of_timeL2
    {T R : ℝ} {S : Set X} (hzero : (0 : X) ∈ S) (hR : 0 ≤ R)
    (J : X →L[ℝ] Z) (hstate : ∀ u : S, ‖J (u : X)‖ ≤ R)
    (N : ℝ → S → Y) (A C : ℝ≥0) (B : timeL2 ℝ T) (F0 : timeL2 Y T)
    (hzeroN : ∀ᵐ t ∂(timeMeasure T), N t ⟨0, hzero⟩ = F0 t)
    (htame : ∀ᵐ t ∂(timeMeasure T), ∀ u v : S,
      ‖N t u - N t v‖ ≤
        (A : ℝ) * R * ‖(u : X) - (v : X)‖ +
          ‖B t‖ * ‖J ((u : X) - (v : X))‖ +
          (C : ℝ) * (‖(u : X)‖ + ‖(v : X)‖) *
            ‖J ((u : X) - (v : X))‖)
    (f : timeL2 X T) (hf : ∀ᵐ t ∂(timeMeasure T), f t ∈ S)
    (hmeas : AEStronglyMeasurable
      (fun t => N t (aeSetLift hzero f t)) (timeMeasure T)) :
    MemLp (fun t => N t (aeSetLift hzero f t)) 2 (timeMeasure T) := by
  let z : S := ⟨0, hzero⟩
  let K : ℝ := (A : ℝ) * R + (C : ℝ) * R
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  let major : ℝ → ℝ := fun t => K * ‖f t‖ + R * ‖B t‖ + ‖F0 t‖
  have hmajor : MemLp major 2 (timeMeasure T) := by
    have hf' := (Lp.memLp f).norm.const_smul K
    have hB := (Lp.memLp B).norm.const_smul R
    have hF := (Lp.memLp F0).norm
    apply ((hf'.add hB).add hF).ae_eq
    filter_upwards [] with t
    simp only [major, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine hmajor.of_le hmeas ?_
  filter_upwards [hf, hzeroN, htame] with t ht htzero httame
  let u : S := ⟨f t, ht⟩
  have huJ : ‖J (f t)‖ ≤ R := hstate u
  have hdiff : ‖N t u - N t z‖ ≤ K * ‖f t‖ + R * ‖B t‖ := by
    have hraw : ‖N t u - N t z‖ ≤
        (A : ℝ) * R * ‖f t‖ + ‖B t‖ * ‖J (f t)‖ +
          (C : ℝ) * ‖f t‖ * ‖J (f t)‖ := by
      simpa only [u, z, Subtype.coe_mk, sub_zero, map_zero, norm_zero, add_zero] using httame u z
    calc
      _ ≤ (A : ℝ) * R * ‖f t‖ + ‖B t‖ * ‖J (f t)‖ +
          (C : ℝ) * ‖f t‖ * ‖J (f t)‖ := hraw
      _ ≤ (A : ℝ) * R * ‖f t‖ + ‖B t‖ * R + (C : ℝ) * ‖f t‖ * R := by
        gcongr
      _ = K * ‖f t‖ + R * ‖B t‖ := by dsimp only [K]; ring
  have hn : ‖N t u‖ ≤ major t := by
    calc
      _ = ‖(N t u - N t z) + N t z‖ := by rw [sub_add_cancel]
      _ ≤ ‖N t u - N t z‖ + ‖N t z‖ := norm_add_le _ _
      _ ≤ (K * ‖f t‖ + R * ‖B t‖) + ‖F0 t‖ := by
        exact add_le_add hdiff (congrArg norm (show N t z = F0 t from htzero)).le
      _ = major t := rfl
  have hmajor0 : 0 ≤ major t := by dsimp only [major]; positivity
  change ‖N t (aeSetLift hzero f t)‖ ≤ ‖major t‖
  have hu : aeSetLift hzero f t = u := by simp only [aeSetLift, dif_pos ht, u]
  rw [hu, Real.norm_eq_abs, abs_of_nonneg hmajor0]
  exact hn

def timeNemyTameL2
    {T R : ℝ} {S : Set X} (hzero : (0 : X) ∈ S) (hR : 0 ≤ R)
    (J : X →L[ℝ] Z) (hstate : ∀ u : S, ‖J (u : X)‖ ≤ R)
    (N : ℝ → S → Y) (A C : ℝ≥0) (B : timeL2 ℝ T) (F0 : timeL2 Y T)
    (hzeroN : ∀ᵐ t ∂(timeMeasure T), N t ⟨0, hzero⟩ = F0 t)
    (htame : ∀ᵐ t ∂(timeMeasure T), ∀ u v : S,
      ‖N t u - N t v‖ ≤
        (A : ℝ) * R * ‖(u : X) - (v : X)‖ +
          ‖B t‖ * ‖J ((u : X) - (v : X))‖ +
          (C : ℝ) * (‖(u : X)‖ + ‖(v : X)‖) *
            ‖J ((u : X) - (v : X))‖)
    (f : timeL2 X T) (hf : ∀ᵐ t ∂(timeMeasure T), f t ∈ S)
    (hmeas : AEStronglyMeasurable
      (fun t => N t (aeSetLift hzero f t)) (timeMeasure T)) :
    timeL2 Y T :=
  (memLp_time_tame_of_timeL2 hzero hR J hstate N A C B F0 hzeroN htame f hf hmeas).toLp
    (fun t => N t (aeSetLift hzero f t))

theorem timeNemyTameL2_ae
    {T R : ℝ} {S : Set X} (hzero : (0 : X) ∈ S) (hR : 0 ≤ R)
    (J : X →L[ℝ] Z) (hstate : ∀ u : S, ‖J (u : X)‖ ≤ R)
    (N : ℝ → S → Y) (A C : ℝ≥0) (B : timeL2 ℝ T) (F0 : timeL2 Y T)
    (hzeroN : ∀ᵐ t ∂(timeMeasure T), N t ⟨0, hzero⟩ = F0 t)
    (htame : ∀ᵐ t ∂(timeMeasure T), ∀ u v : S,
      ‖N t u - N t v‖ ≤
        (A : ℝ) * R * ‖(u : X) - (v : X)‖ +
          ‖B t‖ * ‖J ((u : X) - (v : X))‖ +
          (C : ℝ) * (‖(u : X)‖ + ‖(v : X)‖) *
            ‖J ((u : X) - (v : X))‖)
    (f : timeL2 X T) (hf : ∀ᵐ t ∂(timeMeasure T), f t ∈ S)
    (hmeas : AEStronglyMeasurable
      (fun t => N t (aeSetLift hzero f t)) (timeMeasure T)) :
    timeNemyTameL2 hzero hR J hstate N A C B F0 hzeroN htame f hf hmeas
      =ᵐ[timeMeasure T] fun t => N t (aeSetLift hzero f t) :=
  (memLp_time_tame_of_timeL2 hzero hR J hstate N A C B F0 hzeroN htame f hf hmeas).coeFn_toLp

theorem timeNemyTameL2_sub_norm_le
    {T R : ℝ} {S : Set X} (hzero : (0 : X) ∈ S) (hR : 0 ≤ R)
    (J : X →L[ℝ] Z) (hstate : ∀ u : S, ‖J (u : X)‖ ≤ R)
    (N : ℝ → S → Y) (A C : ℝ≥0) (B : timeL2 ℝ T) (F0 : timeL2 Y T)
    (hzeroN : ∀ᵐ t ∂(timeMeasure T), N t ⟨0, hzero⟩ = F0 t)
    (htame : ∀ᵐ t ∂(timeMeasure T), ∀ u v : S,
      ‖N t u - N t v‖ ≤
        (A : ℝ) * R * ‖(u : X) - (v : X)‖ +
          ‖B t‖ * ‖J ((u : X) - (v : X))‖ +
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
    ‖timeNemyTameL2 hzero hR J hstate N A C B F0 hzeroN htame f hf hmeasf -
      timeNemyTameL2 hzero hR J hstate N A C B F0 hzeroN htame g hg hmeasg‖ ≤
      (A : ℝ) * R * ‖f - g‖ + ‖B‖ * P + (C : ℝ) * P * (‖f‖ + ‖g‖) := by
  let F := timeNemyTameL2 hzero hR J hstate N A C B F0 hzeroN htame f hf hmeasf
  let G := timeNemyTameL2 hzero hR J hstate N A C B F0 hzeroN htame g hg hmeasg
  have hF := timeNemyTameL2_ae hzero hR J hstate N A C B F0 hzeroN htame f hf hmeasf
  have hG := timeNemyTameL2_ae hzero hR J hstate N A C B F0 hzeroN htame g hg hmeasg
  have hbound : ∀ᵐ t ∂(timeMeasure T),
      ‖(F - G) t‖ ≤ (A : ℝ) * R * ‖(f - g) t‖ +
        P * ‖B t‖ + (C : ℝ) * P * ‖f t‖ + (C : ℝ) * P * ‖g t‖ := by
    filter_upwards [Lp.coeFn_sub F G, hF, hG, hf, hg, htame,
      Lp.coeFn_sub f g, hpoint] with t hFG hFt hGt hft hgt hNt hfg hp
    rw [hFG, Pi.sub_apply, hFt, hGt]
    simp only [aeSetLift, dif_pos hft, dif_pos hgt]
    have hraw := hNt ⟨f t, hft⟩ ⟨g t, hgt⟩
    have hfg' : f t - g t = (f - g) t := hfg.symm
    simp only [hfg'] at hraw
    calc
      _ ≤ (A : ℝ) * R * ‖(f - g) t‖ + ‖B t‖ * ‖J ((f - g) t)‖ +
          (C : ℝ) * (‖f t‖ + ‖g t‖) * ‖J ((f - g) t)‖ := hraw
      _ ≤ (A : ℝ) * R * ‖(f - g) t‖ + ‖B t‖ * P +
          (C : ℝ) * (‖f t‖ + ‖g t‖) * P := by gcongr
      _ = _ := by ring
  have hmain := timeL2_norm_le_four (F - G) (f - g) B f g
    (mul_nonneg A.coe_nonneg hR) hP
    (mul_nonneg C.coe_nonneg hP) (mul_nonneg C.coe_nonneg hP) hbound
  change ‖F - G‖ ≤ _
  convert hmain using 1
  ring

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

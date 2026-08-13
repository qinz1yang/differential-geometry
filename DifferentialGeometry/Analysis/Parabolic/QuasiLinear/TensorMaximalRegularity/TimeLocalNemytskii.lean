import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.LocalNemytskii
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

def TimeNemyMeas {S : Set X} (hzero : (0 : X) ∈ S)
    (N : ℝ → S → Y) (τ : ℝ) : Prop :=
  ∀ {T : ℝ}, T ≤ τ → ∀ (f : timeL2 X T),
    (∀ᵐ t ∂(timeMeasure T), f t ∈ S) →
      AEStronglyMeasurable (fun t => N t (aeSetLift hzero f t)) (timeMeasure T)

omit [NormedSpace ℝ Y] [CompleteSpace Y] in
theorem timeNemy_of_cont {S : Set X} (hzero : (0 : X) ∈ S)
    {N : ℝ → S → Y} {τ : ℝ}
    (hN : Continuous (fun p : ℝ × S => N p.1 p.2)) :
    TimeNemyMeas hzero N τ := by
  intro T _hT f hf
  exact hN.comp_aestronglyMeasurable
    (aestronglyMeasurable_id.prodMk (aeSetLift_aesm hzero f hf))

omit [NormedSpace ℝ Y] [CompleteSpace Y] in
theorem memLp_time_tame
    {T R : ℝ} {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {S : Set X} (hzero : (0 : X) ∈ S) (hR : 0 ≤ R)
    (J : X →L[ℝ] Z) (hstate : ∀ u : S, ‖J (u : X)‖ ≤ R)
    (N : ℝ → S → Y)
    (f : timeL2 X T) (hf : ∀ᵐ t ∂(timeMeasure T), f t ∈ S)
    (hmeas : AEStronglyMeasurable
      (fun t => N t (aeSetLift hzero f t)) (timeMeasure T))
    (A B C : ℝ≥0) (D : ℝ) (hD : 0 ≤ D)
    (hzeroN : ∀ᵐ t ∂(timeMeasure T), ‖N t ⟨0, hzero⟩‖ ≤ D)
    (htame : ∀ᵐ t ∂(timeMeasure T), ∀ u v : S,
      ‖N t u - N t v‖ ≤
        (A : ℝ) * R * ‖(u : X) - (v : X)‖ +
          (B : ℝ) * ‖J ((u : X) - (v : X))‖ +
          (C : ℝ) * (‖(u : X)‖ + ‖(v : X)‖) *
            ‖J ((u : X) - (v : X))‖) :
    MemLp (fun t => N t (aeSetLift hzero f t)) 2 (timeMeasure T) := by
  let z : S := ⟨0, hzero⟩
  let K : ℝ := (A : ℝ) * R + (C : ℝ) * R
  let Q : ℝ := (B : ℝ) * R + D
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  let major : ℝ → ℝ := fun t => K * ‖f t‖ + Q
  have hmajor : MemLp major 2 (timeMeasure T) := by
    have hnorm : MemLp (fun t => ‖f t‖) 2 (timeMeasure T) := (Lp.memLp f).norm
    have hscaled : MemLp (K • fun t => ‖f t‖) 2 (timeMeasure T) := hnorm.const_smul K
    have hconst : MemLp (fun _ : ℝ => Q) 2 (timeMeasure T) := memLp_const Q
    have hadd := hscaled.add hconst
    simpa only [major, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hadd
  refine hmajor.of_le hmeas ?_
  filter_upwards [hf, hzeroN, htame] with t ht htzero httame
  let u : S := ⟨f t, ht⟩
  have huJ : ‖J (f t)‖ ≤ R := by
    simpa only [u] using hstate u
  have hdiff : ‖N t u - N t z‖ ≤ K * ‖f t‖ + (B : ℝ) * R := by
    have hraw := httame u z
    have hraw' : ‖N t u - N t z‖ ≤
        (A : ℝ) * R * ‖f t‖ + (B : ℝ) * ‖J (f t)‖ +
          (C : ℝ) * ‖f t‖ * ‖J (f t)‖ := by
      simpa only [u, z, Subtype.coe_mk, sub_zero, map_zero, norm_zero, add_zero] using hraw
    calc
      ‖N t u - N t z‖ ≤
          (A : ℝ) * R * ‖f t‖ + (B : ℝ) * ‖J (f t)‖ +
            (C : ℝ) * ‖f t‖ * ‖J (f t)‖ := hraw'
      _ ≤ (A : ℝ) * R * ‖f t‖ + (B : ℝ) * R +
            (C : ℝ) * ‖f t‖ * R := by
        gcongr
      _ = K * ‖f t‖ + (B : ℝ) * R := by
        dsimp only [K]
        ring
  have hn : ‖N t u‖ ≤ major t := by
    calc
      ‖N t u‖ = ‖(N t u - N t z) + N t z‖ := by rw [sub_add_cancel]
      _ ≤ ‖N t u - N t z‖ + ‖N t z‖ := norm_add_le _ _
      _ ≤ (K * ‖f t‖ + (B : ℝ) * R) + D := add_le_add hdiff htzero
      _ = major t := by
        dsimp only [major, Q]
        ring
  have hmajor0 : 0 ≤ major t := by
    dsimp only [major]
    exact add_nonneg (mul_nonneg hK (norm_nonneg _)) hQ
  change ‖N t (aeSetLift hzero f t)‖ ≤ ‖major t‖
  have hu : aeSetLift hzero f t = u := by
    simp only [aeSetLift, dif_pos ht, u]
  rw [hu, Real.norm_eq_abs, abs_of_nonneg hmajor0]
  exact hn

def timeNemyTame
    {T R : ℝ} {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {S : Set X} (hzero : (0 : X) ∈ S) (hR : 0 ≤ R)
    (J : X →L[ℝ] Z) (hstate : ∀ u : S, ‖J (u : X)‖ ≤ R)
    (N : ℝ → S → Y) (A B C : ℝ≥0) (D : ℝ) (hD : 0 ≤ D)
    (hzeroN : ∀ᵐ t ∂(timeMeasure T), ‖N t ⟨0, hzero⟩‖ ≤ D)
    (htame : ∀ᵐ t ∂(timeMeasure T), ∀ u v : S,
      ‖N t u - N t v‖ ≤
        (A : ℝ) * R * ‖(u : X) - (v : X)‖ +
          (B : ℝ) * ‖J ((u : X) - (v : X))‖ +
          (C : ℝ) * (‖(u : X)‖ + ‖(v : X)‖) *
            ‖J ((u : X) - (v : X))‖)
    (f : timeL2 X T) (hf : ∀ᵐ t ∂(timeMeasure T), f t ∈ S)
    (hmeas : AEStronglyMeasurable
      (fun t => N t (aeSetLift hzero f t)) (timeMeasure T)) :
    timeL2 Y T :=
  (memLp_time_tame hzero hR J hstate N f hf hmeas A B C D hD hzeroN htame).toLp
    (fun t => N t (aeSetLift hzero f t))

theorem timeNemyTame_ae
    {T R : ℝ} {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {S : Set X} (hzero : (0 : X) ∈ S) (hR : 0 ≤ R)
    (J : X →L[ℝ] Z) (hstate : ∀ u : S, ‖J (u : X)‖ ≤ R)
    (N : ℝ → S → Y) (A B C : ℝ≥0) (D : ℝ) (hD : 0 ≤ D)
    (hzeroN : ∀ᵐ t ∂(timeMeasure T), ‖N t ⟨0, hzero⟩‖ ≤ D)
    (htame : ∀ᵐ t ∂(timeMeasure T), ∀ u v : S,
      ‖N t u - N t v‖ ≤
        (A : ℝ) * R * ‖(u : X) - (v : X)‖ +
          (B : ℝ) * ‖J ((u : X) - (v : X))‖ +
          (C : ℝ) * (‖(u : X)‖ + ‖(v : X)‖) *
            ‖J ((u : X) - (v : X))‖)
    (f : timeL2 X T) (hf : ∀ᵐ t ∂(timeMeasure T), f t ∈ S)
    (hmeas : AEStronglyMeasurable
      (fun t => N t (aeSetLift hzero f t)) (timeMeasure T)) :
    timeNemyTame hzero hR J hstate N A B C D hD hzeroN htame f hf hmeas
      =ᵐ[timeMeasure T] fun t => N t (aeSetLift hzero f t) :=
  (memLp_time_tame hzero hR J hstate N f hf hmeas A B C D hD hzeroN htame).coeFn_toLp

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end

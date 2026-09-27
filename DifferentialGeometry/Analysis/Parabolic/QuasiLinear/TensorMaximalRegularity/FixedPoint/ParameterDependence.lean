import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.FixedPoint.Stability
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.AffineMajorant
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.FixedPoint.TimeDependentForcing

open MeasureTheory Filter Set
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

theorem exists_lipschitz_fixed_forcing_of_tame
    {X Y Z Ptype : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [PseudoMetricSpace Ptype]
    {T R ρ H P : ℝ} (hR : 0 ≤ R) (hρ : 0 ≤ ρ)
    (hH : 0 ≤ H) (hP : 0 ≤ P)
    (J : X →L[ℝ] Z) (L : timeL2 Y T →L[ℝ] timeL2 X T)
    (hL : ∀ F, ‖L F‖ ≤ H * ‖F‖)
    (hpoint : ∀ F, ∀ᵐ t ∂(timeMeasure T), ‖J (L F t)‖ ≤ P * ‖F‖)
    (hPR : P * ρ ≤ R)
    (N : Ptype → ℝ → {x : X | ‖J x‖ ≤ R} → Y)
    (A B C : ℝ≥0) (D : ℝ) (hD : 0 ≤ D)
    (hzero : ∀ p, ∀ᵐ t ∂(timeMeasure T),
      ‖N p t ⟨0, by simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR⟩‖ ≤ D)
    (htame : ∀ p, ∀ᵐ t ∂(timeMeasure T), ∀ u v : {x : X | ‖J x‖ ≤ R},
      ‖N p t u - N p t v‖ ≤
        (A : ℝ) * R * ‖(u : X) - (v : X)‖ +
        (B : ℝ) * ‖J ((u : X) - (v : X))‖ +
        (C : ℝ) * (‖(u : X)‖ + ‖(v : X)‖) * ‖J ((u : X) - (v : X))‖)
    (hmeas : ∀ p (f : timeL2 X T)
      (_ : ∀ᵐ t ∂(timeMeasure T), f t ∈ {x : X | ‖J x‖ ≤ R}),
      AEStronglyMeasurable (fun t => N p t (aeSetLift
        (show (0 : X) ∈ {x : X | ‖J x‖ ≤ R} by
          simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR) f t)) (timeMeasure T))
    (hκ : (A : ℝ) * R * H + (B : ℝ) * Real.sqrt T * P + 2 * (C : ℝ) * ρ * P * H < 1)
    (hstay : Real.sqrt T * D ≤
      (1 - ((A : ℝ) * R * H + (B : ℝ) * Real.sqrt T * P + 2 * (C : ℝ) * ρ * P * H)) * ρ)
    (K₀ K₁ : ℝ≥0)
    (hparam : ∀ p q, ∀ᵐ t ∂(timeMeasure T), ∀ u : {x : X | ‖J x‖ ≤ R},
      ‖N p t u - N q t u‖ ≤ ((K₁ : ℝ) * ‖(u : X)‖ + (K₀ : ℝ)) * dist p q) :
    let κ := (A : ℝ) * R * H + (B : ℝ) * Real.sqrt T * P + 2 * (C : ℝ) * ρ * P * H
    ∃ F : Ptype → timeL2 Y T,
      LipschitzWith ((K₁ * H.toNNReal * ρ.toNNReal + (Real.sqrt T).toNNReal * K₀) /
        (1 - κ).toNNReal) F ∧
      ∀ p, ‖F p‖ ≤ ρ ∧
        (∀ᵐ t ∂(timeMeasure T), L (F p) t ∈ {x : X | ‖J x‖ ≤ R}) ∧
        F p =ᵐ[timeMeasure T] fun t => N p t (aeSetLift
          (show (0 : X) ∈ {x : X | ‖J x‖ ≤ R} by
            simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR) (L (F p)) t) := by
  classical
  let hz : (0 : X) ∈ {x : X | ‖J x‖ ≤ R} := by
    simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR
  let κ := (A : ℝ) * R * H + (B : ℝ) * Real.sqrt T * P + 2 * (C : ℝ) * ρ * P * H
  have hex (p : Ptype) := exists_fixed_forcing_of_tame hR hρ hH hP J L hL hpoint hPR
    (N p) A B C D hD (hzero p) (htame p) (hmeas p) hκ hstay
  choose F hF hstate hforce using hex
  refine ⟨F, ?_, fun p => ⟨hF p, hstate p, hforce p⟩⟩
  apply LipschitzWith.of_dist_le_mul
  intro p q
  let Gpq := timeNemyTame hz hR J (fun u => u.property) (N p) A B C D hD
    (hzero p) (htame p) (L (F q)) (hstate q) (hmeas p (L (F q)) (hstate q))
  have hcrosspoint : ∀ᵐ t ∂(timeMeasure T),
      ‖(Gpq - F q) t‖ ≤ ((K₁ : ℝ) * dist p q) * ‖L (F q) t‖ + (K₀ : ℝ) * dist p q := by
    filter_upwards [Lp.coeFn_sub Gpq (F q),
      timeNemyTame_ae hz hR J (fun u => u.property) (N p) A B C D hD
        (hzero p) (htame p) (L (F q)) (hstate q) (hmeas p (L (F q)) (hstate q)),
      hforce q, hparam p q, hstate q] with t hsub hpt hqt hpqt hst
    rw [hsub, Pi.sub_apply, hpt, hqt]
    have h := hpqt ⟨L (F q) t, hst⟩
    simpa only [aeSetLift, Set.mem_ofPred_eq, dif_pos hst, mul_add, mul_comm, mul_left_comm, mul_assoc] using h
  have hcross : ‖Gpq - F q‖ ≤
      ((K₁ : ℝ) * H * ρ + Real.sqrt T * K₀) * dist p q := by
    have hraw := timeL2_norm_le_of_ae_affine_bound (Gpq - F q) (L (F q))
      (mul_nonneg K₁.coe_nonneg dist_nonneg) (mul_nonneg K₀.coe_nonneg dist_nonneg) hcrosspoint
    have hLq : ‖L (F q)‖ ≤ H * ρ := (hL _).trans
      (mul_le_mul_of_nonneg_left (hF q) hH)
    calc
      ‖Gpq - F q‖ ≤ (K₁ : ℝ) * dist p q * ‖L (F q)‖ +
          Real.sqrt T * ((K₀ : ℝ) * dist p q) := hraw
      _ ≤ (K₁ : ℝ) * dist p q * (H * ρ) +
          Real.sqrt T * ((K₀ : ℝ) * dist p q) := by gcongr
      _ = _ := by ring
  have hbound := tame_fixed_forcing_sub_norm_le hz hR J (fun u => u.property)
    (N p) A B C D hD (hzero p) (htame p) L hL hH hP hpoint
      (F p) (F q) (hstate p) (hstate q) (hforce p)
      (hmeas p (L (F q)) (hstate q)) hcross (le_refl κ) (hF p) (hF q) hκ
  rw [dist_eq_norm]
  simpa only [NNReal.coe_div, NNReal.coe_add, NNReal.coe_mul,
    Real.coe_toNNReal _ hH, Real.coe_toNNReal _ hρ,
    Real.coe_toNNReal _ (Real.sqrt_nonneg T),
    Real.coe_toNNReal _ (sub_nonneg.mpr hκ.le), mul_div_assoc, div_mul_eq_mul_div] using hbound

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

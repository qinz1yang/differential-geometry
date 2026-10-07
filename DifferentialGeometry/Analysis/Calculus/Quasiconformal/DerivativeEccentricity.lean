/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Analysis.Calculus.Quasiconformal.MetricDifferentiability
import Mathlib.Analysis.Normed.Operator.Conformal

noncomputable section

open Set Filter MeasureTheory

namespace DifferentialGeometry.DerivativeEccentricity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def eccentricity (A B : E →L[ℝ] E) : ℝ := ‖A‖ * ‖B‖

theorem eccentricity_nonneg (A B : E →L[ℝ] E) : 0 ≤ eccentricity A B :=
  mul_nonneg (norm_nonneg _) (norm_nonneg _)

theorem eccentricity_comm (A B : E →L[ℝ] E) : eccentricity A B = eccentricity B A :=
  mul_comm _ _

theorem eccentricity_smul (A B : E →L[ℝ] E) {c : ℝ} (hc : c ≠ 0) :
    eccentricity (c • A) (c⁻¹ • B) = eccentricity A B := by
  simp only [eccentricity, norm_smul, norm_inv]
  have hn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  field_simp

theorem eccentricity_le_of_comparison (A B : E →L[ℝ] E) {H : ℝ} (hH : 0 ≤ H)
    (hAB : A.comp B = ContinuousLinearMap.id ℝ E)
    (hcomp : ∀ v w : E, ‖v‖ ≤ ‖w‖ → ‖A v‖ ≤ H * ‖A w‖) :
    eccentricity A B ≤ H := by
  have hAB' (w : E) : A (B w) = w := congrArg (fun L : E →L[ℝ] E => L w) hAB
  have hscaled (w : E) : ‖(‖B w‖ • A : E →L[ℝ] E)‖ ≤ H * ‖w‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hH (norm_nonneg _))
    intro v
    have he : ‖‖B w‖ • v‖ = ‖‖v‖ • B w‖ := by
      simp only [norm_smul, Real.norm_of_nonneg (norm_nonneg _)]
      ring
    have hb := hcomp (‖B w‖ • v) (‖v‖ • B w) he.le
    simp only [map_smul, norm_smul, Real.norm_of_nonneg (norm_nonneg _), hAB'] at hb
    simpa only [smul_apply, norm_smul,
      Real.norm_of_nonneg (norm_nonneg _), mul_comm ‖v‖ ‖w‖, mul_assoc] using hb
  have hb : ‖(‖A‖ • B : E →L[ℝ] E)‖ ≤ H := by
    apply ContinuousLinearMap.opNorm_le_bound _ hH
    intro w
    simpa only [smul_apply, norm_smul,
      Real.norm_of_nonneg (norm_nonneg _), mul_comm ‖B w‖ ‖A‖] using hscaled w
  simpa only [eccentricity, norm_smul, Real.norm_of_nonneg (norm_nonneg _)] using hb

variable [Nontrivial E]

theorem one_le_eccentricity (A B : E →L[ℝ] E)
    (hBA : B.comp A = ContinuousLinearMap.id ℝ E) :
    1 ≤ eccentricity A B := by
  have h := B.opNorm_comp_le A
  rw [hBA, ContinuousLinearMap.norm_id] at h
  simpa only [eccentricity, mul_comm] using h

theorem eccentricity_eq_one_iff (A B : E →L[ℝ] E)
    (hBA : B.comp A = ContinuousLinearMap.id ℝ E)
    (hAB : A.comp B = ContinuousLinearMap.id ℝ E) :
    eccentricity A B = 1 ↔ IsConformalMap A := by
  constructor
  · intro he
    have hmul : ‖A‖ * ‖B‖ = 1 := he
    have hA : ‖A‖ ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at hmul
      exact zero_ne_one hmul
    have hnorm (v : E) : ‖A v‖ = ‖A‖ * ‖v‖ := by
      apply le_antisymm (A.le_opNorm v)
      have hBA' : B (A v) = v := congrArg (fun L : E →L[ℝ] E => L v) hBA
      have h := B.le_opNorm (A v)
      rw [hBA'] at h
      calc
        ‖A‖ * ‖v‖ ≤ ‖A‖ * (‖B‖ * ‖A v‖) := mul_le_mul_of_nonneg_left h (norm_nonneg _)
        _ = ‖A v‖ := by rw [← mul_assoc, hmul, one_mul]
    let L : E →ₗᵢ[ℝ] E :=
      { toLinearMap := (‖A‖⁻¹ • A).toLinearMap
        norm_map' v := by
          change ‖‖A‖⁻¹ • A v‖ = ‖v‖
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
            hnorm, ← mul_assoc, inv_mul_cancel₀ hA, one_mul] }
    refine ⟨‖A‖, hA, L, ?_⟩
    ext v
    change A v = ‖A‖ • (‖A‖⁻¹ • A v)
    rw [smul_smul, mul_inv_cancel₀ hA, one_smul]
  · rintro ⟨c, _, L, hA⟩
    apply le_antisymm _ (one_le_eccentricity A B hBA)
    apply eccentricity_le_of_comparison A B zero_le_one hAB
    intro v w hvw
    simp only [hA, smul_apply, LinearIsometry.coe_toContinuousLinearMap,
      norm_smul, L.norm_map, one_mul]
    exact mul_le_mul_of_nonneg_left hvw (norm_nonneg _)

theorem norm_comp_isometryEquiv (A : E →L[ℝ] E) (R : E ≃ₗᵢ[ℝ] E) :
    ‖A.comp R.toContinuousLinearEquiv.toContinuousLinearMap‖ = ‖A‖ := by
  apply le_antisymm
  · simpa only [LinearIsometryEquiv.norm_toContinuousLinearMap, mul_one] using
      A.opNorm_comp_le R.toContinuousLinearEquiv.toContinuousLinearMap
  · have h : (A.comp R.toContinuousLinearEquiv.toContinuousLinearMap).comp
        R.symm.toContinuousLinearEquiv.toContinuousLinearMap = A := by
      ext v
      simp
    have hb := (A.comp R.toContinuousLinearEquiv.toContinuousLinearMap).opNorm_comp_le
      R.symm.toContinuousLinearEquiv.toContinuousLinearMap
    simpa only [h, LinearIsometryEquiv.norm_toContinuousLinearMap, mul_one] using hb

theorem eccentricity_isometric_coordinates (A B : E →L[ℝ] E) (R S : E ≃ₗᵢ[ℝ] E) :
    eccentricity
      (S.toLinearIsometry.toContinuousLinearMap.comp
        (A.comp R.toContinuousLinearEquiv.toContinuousLinearMap))
      (R.symm.toLinearIsometry.toContinuousLinearMap.comp
        (B.comp S.symm.toContinuousLinearEquiv.toContinuousLinearMap)) =
      eccentricity A B := by
  simp only [eccentricity, LinearIsometry.norm_toContinuousLinearMap_comp,
    norm_comp_isometryEquiv]

def chartEccentricity (F : E ≃ₜ E) (x : E) : ℝ :=
  eccentricity (fderiv ℝ F x) (fderiv ℝ F.symm (F x))

omit [Nontrivial E] in
theorem chartEccentricity_inverse (F : E ≃ₜ E) (x : E) :
    chartEccentricity F.symm (F x) = chartEccentricity F x := by
  simp only [chartEccentricity, Homeomorph.symm_symm, Homeomorph.symm_apply_apply,
    eccentricity_comm]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [Nontrivial E] in
theorem measurable_chartEccentricity (F : E ≃ₜ E) : Measurable (chartEccentricity F) :=
  (measurable_fderiv ℝ F).norm.mul
    ((measurable_fderiv ℝ F.symm).norm.comp F.continuous.measurable)

omit [FiniteDimensional ℝ E] [BorelSpace E] in
theorem ae_chartEccentricity_bounds (μ : Measure E) (F : E ≃ₜ E)
    (hd : MetricDifferentiability.HasLocalDistortion F)
    (hf : ∀ᵐ x ∂μ, DifferentiableAt ℝ F x)
    (hi : ∀ᵐ x ∂μ,
      (fderiv ℝ F.symm (F x)).comp (fderiv ℝ F x) = ContinuousLinearMap.id ℝ E ∧
      (fderiv ℝ F x).comp (fderiv ℝ F.symm (F x)) = ContinuousLinearMap.id ℝ E) :
    ∃ H : ℝ, 0 < H ∧ ∀ᵐ x ∂μ, 1 ≤ chartEccentricity F x ∧ chartEccentricity F x ≤ H := by
  obtain ⟨H, hH, hlocal⟩ := hd
  refine ⟨H, hH, ?_⟩
  filter_upwards [hf, hi] with x hx hix
  refine ⟨one_le_eccentricity _ _ hix.1, ?_⟩
  obtain ⟨r, hr, hb⟩ := hlocal x
  exact eccentricity_le_of_comparison _ _ hH.le hix.2
    (MetricDifferentiability.norm_derivative_comparison hr hb hx.hasFDerivAt)

omit [FiniteDimensional ℝ E] [BorelSpace E] in
theorem ae_chartEccentricity_eq_one_iff (μ : Measure E) (F : E ≃ₜ E)
    (hi : ∀ᵐ x ∂μ,
      (fderiv ℝ F.symm (F x)).comp (fderiv ℝ F x) = ContinuousLinearMap.id ℝ E ∧
      (fderiv ℝ F x).comp (fderiv ℝ F.symm (F x)) = ContinuousLinearMap.id ℝ E) :
    ∀ᵐ x ∂μ, chartEccentricity F x = 1 ↔ IsConformalMap (fderiv ℝ F x) :=
  hi.mono (fun _ hx => eccentricity_eq_one_iff _ _ hx.1 hx.2)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_comp_conformal_left (A S : E →L[ℝ] E) (hS : IsConformalMap S) :
    ‖S.comp A‖ = ‖S‖ * ‖A‖ := by
  obtain ⟨c, _, R, rfl⟩ := hS
  simp only [ContinuousLinearMap.smul_comp, norm_smul,
    LinearIsometry.norm_toContinuousLinearMap_comp, LinearIsometry.norm_toContinuousLinearMap,
    mul_one]

omit [MeasurableSpace E] [BorelSpace E] in
theorem norm_comp_conformal_right (A R : E →L[ℝ] E) (hR : IsConformalMap R) :
    ‖A.comp R‖ = ‖A‖ * ‖R‖ := by
  obtain ⟨c, _, L, rfl⟩ := hR
  have h := norm_comp_isometryEquiv A (L.toLinearIsometryEquiv rfl)
  change ‖A.comp L.toContinuousLinearMap‖ = ‖A‖ at h
  rw [ContinuousLinearMap.comp_smul, norm_smul, h, norm_smul,
    LinearIsometry.norm_toContinuousLinearMap, mul_one, mul_comm]

omit [MeasurableSpace E] [BorelSpace E] in
theorem eccentricity_conjugacy (A B C D R Ri S Si : E →L[ℝ] E)
    (hAB : A.comp B = ContinuousLinearMap.id ℝ E)
    (hDC : D.comp C = ContinuousLinearMap.id ℝ E)
    (hRiR : Ri.comp R = ContinuousLinearMap.id ℝ E)
    (hRRi : R.comp Ri = ContinuousLinearMap.id ℝ E)
    (hSiS : Si.comp S = ContinuousLinearMap.id ℝ E)
    (hSSi : S.comp Si = ContinuousLinearMap.id ℝ E)
    (hR : IsConformalMap R) (hS : IsConformalMap S)
    (hchain : C.comp R = S.comp A) :
    eccentricity C D = eccentricity A B := by
  have heR := (eccentricity_eq_one_iff R Ri hRiR hRRi).mpr hR
  have heS := (eccentricity_eq_one_iff S Si hSiS hSSi).mpr hS
  have hRi : IsConformalMap Ri :=
    (eccentricity_eq_one_iff Ri R hRRi hRiR).mp ((eccentricity_comm Ri R).trans heR)
  have hSi : IsConformalMap Si :=
    (eccentricity_eq_one_iff Si S hSSi hSiS).mp ((eccentricity_comm Si S).trans heS)
  have hC : C = (S.comp A).comp Ri := by
    calc
      C = C.comp (R.comp Ri) := by rw [hRRi, ContinuousLinearMap.comp_id]
      _ = (C.comp R).comp Ri := rfl
      _ = (S.comp A).comp Ri := by rw [hchain]
  have hDS : D.comp S = R.comp B := by
    calc
      D.comp S = (D.comp S).comp (A.comp B) := by rw [hAB, ContinuousLinearMap.comp_id]
      _ = (D.comp (S.comp A)).comp B := rfl
      _ = (D.comp (C.comp R)).comp B := by rw [← hchain]
      _ = ((D.comp C).comp R).comp B := rfl
      _ = R.comp B := by rw [hDC, ContinuousLinearMap.id_comp]
  have hD : D = (R.comp B).comp Si := by
    calc
      D = D.comp (S.comp Si) := by rw [hSSi, ContinuousLinearMap.comp_id]
      _ = (D.comp S).comp Si := rfl
      _ = (R.comp B).comp Si := by rw [hDS]
  calc
    eccentricity C D = eccentricity R Ri * eccentricity S Si * eccentricity A B := by
      rw [eccentricity, hC, hD,
        norm_comp_conformal_right _ _ hRi, norm_comp_conformal_right _ _ hSi,
        norm_comp_conformal_left _ _ hS, norm_comp_conformal_left _ _ hR]
      unfold eccentricity
      ring
    _ = eccentricity A B := by rw [heR, heS, one_mul, one_mul]

end DifferentialGeometry.DerivativeEccentricity

import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.LowerScaleBounds
import DifferentialGeometry.Analysis.DenseExtension
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Nonautonomous.L2.CrossEstimate

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev
  (covariantJetNormSq exists_covariantJetNormSq_le_spectralSobolevNorm_sq)
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Sobolev (iteratedCovGrad)
open DifferentialGeometry.Analysis.Spectral
  (operatorFieldComposition_zero_eq_operatorFieldApply operatorFieldComposition_zero_left ccTensorToHs ccTensorToHs_smul
    ccToHsLin ccToHsLin_apply ccToHsLin_dense iteratedCovGrad_smul)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private abbrev metricThirdOrderSobolev (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (3 : ℝ)

private abbrev metricH2 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

private abbrev metricH1 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (1 : ℝ)

private noncomputable abbrev incl32
    (g : SmoothRiemannianMetric I M) :
    metricThirdOrderSobolev (I := I) (M := M) g →L[ℝ]
      metricH2 (I := I) (M := M) g :=
  tensorHsInclusion (I := I) (M := M) (g := g)
    (r := 0) (s := 2) (by norm_num)

private noncomputable abbrev incl12
    (g : SmoothRiemannianMetric I M) :
    metricH2 (I := I) (M := M) g →L[ℝ]
      metricH1 (I := I) (M := M) g :=
  tensorHsInclusion (I := I) (M := M) (g := g)
    (r := 0) (s := 2) (by norm_num)

private noncomputable def zeroData
    (g : SmoothRiemannianMetric I M) : LowerScaleActionCoefficients g where
  zeroOrderCoefficient := 0
  firstOrderCoefficient := 0
  secondOrderCoefficient := 0

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem zeroData_a1
    (g : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    (zeroData (I := I) (M := M) g).firstOrderAction (I := I) (M := M) W = 0 := by
  simp only [zeroData, LowerScaleActionCoefficients.firstOrderAction, ← operatorFieldComposition_zero_eq_operatorFieldApply,
    operatorFieldComposition_zero_left, zero_add]

omit [CompactSpace M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem iter_zero
    (g : SmoothRiemannianMetric I M) (r s j : ℕ) :
    iteratedCovGrad (I := I) g r s j
        (0 : SmoothCcTensor g r s) = 0 := by
  have h := iteratedCovGrad_smul (I := I) (M := M) g r s j
    (0 : ℝ) (0 : SmoothCcTensor g r s)
  simpa only [zero_smul] using h

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem lowJet_zero
    (g : SmoothRiemannianMetric I M) (r s m : ℕ) :
    covariantJetNormSq (I := I) (M := M) g m
        (0 : SmoothCcTensor g r s) = 0 := by
  simp only [covariantJetNormSq, iter_zero (I := I) (M := M), norm_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero]

private theorem zeroData_pair
    (g : SmoothRiemannianMetric I M) :
    ‖(zeroData (I := I) (M := M) g).firstOrderActionThirdToSecondOrder (I := I) (M := M)‖ = 0 ∧
      ‖(zeroData (I := I) (M := M) g).firstOrderActionSecondToFirstOrder (I := I) (M := M)‖ = 0 := by
  obtain ⟨C, _, hpair⟩ := exists_firstOrderAction_spectralSobolev_extensions (I := I) (M := M) g
  have hHi : ∀ W : SmoothCcTensor g 0 2,
      covariantJetNormSq (I := I) (M := M) g 2
          ((zeroData (I := I) (M := M) g).firstOrderAction (I := I) (M := M) W) ≤
        (0 : ℝ) * covariantJetNormSq (I := I) (M := M) g 3 W := by
    intro W
    rw [zeroData_a1 (I := I) (M := M),
      lowJet_zero (I := I) (M := M)]
    simp only [zero_mul]
    exact le_rfl
  have hLo : ∀ W : SmoothCcTensor g 0 2,
      covariantJetNormSq (I := I) (M := M) g 1
          ((zeroData (I := I) (M := M) g).firstOrderAction (I := I) (M := M) W) ≤
        (0 : ℝ) * covariantJetNormSq (I := I) (M := M) g 2 W := by
    intro W
    rw [zeroData_a1 (I := I) (M := M),
      lowJet_zero (I := I) (M := M)]
    simp only [zero_mul]
    exact le_rfl
  obtain ⟨hHiNorm, hLoNorm, _⟩ := hpair
    (zeroData (I := I) (M := M) g) 0 le_rfl hHi hLo
  constructor
  · exact le_antisymm (by simpa only [Real.sqrt_zero, mul_zero] using hHiNorm)
      (norm_nonneg
        ((zeroData (I := I) (M := M) g).firstOrderActionThirdToSecondOrder (I := I) (M := M)))
  · exact le_antisymm (by simpa only [Real.sqrt_zero, mul_zero] using hLoNorm)
      (norm_nonneg
        ((zeroData (I := I) (M := M) g).firstOrderActionSecondToFirstOrder (I := I) (M := M)))

private theorem zeroOrderCoefficient_core_affine
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ0 : ℝ, 0 < ρ0 ∧
      ∀ {ρ δ : ℝ} (hρ : 0 < ρ) (_ : ρ ≤ ρ0)
        (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hreal : ∀ S : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
            gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g S) δ),
      ∃ Z L : ℝ, 0 ≤ Z ∧ 0 ≤ L ∧
        ∀ T : SmoothCcTensor g 0 2,
          let A := radialLowerScaleActionCoefficients (I := I) (M := M)
            g hρ.le hδ0 hδ_le hreal T
          ‖A.firstOrderActionThirdToSecondOrder (I := I) (M := M)‖ ≤
              Z + L * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ ∧
            ‖A.firstOrderActionSecondToFirstOrder (I := I) (M := M)‖ ≤
              Z + L * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ := by
  obtain ⟨ρ0, B0, B1, hρ0, hB0, hB1, hcoeff⟩ :=
    exists_affineLowerScaleCoefficients_covariantJetNormSq_two_bound
      (I := I) (M := M) hDim g
  obtain ⟨C2, hC2, hjet2⟩ := exists_covariantJetNormSq_le_spectralSobolevNorm_sq (I := I) (M := M) g 2 2
  obtain ⟨C3, hC3, hjet3⟩ := exists_covariantJetNormSq_le_spectralSobolevNorm_sq (I := I) (M := M) g 2 3
  obtain ⟨Ca, hCa, hact⟩ := exists_firstOrderAction_spectralSobolev_difference_bounds (I := I) (M := M) hDim g
  refine ⟨ρ0, hρ0, ?_⟩
  intro ρ δ hρ hρρ0 hδ0 hδ_le hreal
  let R2 : ℝ := C2 * ρ
  let Z : ℝ := Ca * B0 R2
  let L : ℝ := Ca * B1 R2 * C3
  have hR2 : 0 ≤ R2 := mul_nonneg hC2 hρ.le
  have hZ : 0 ≤ Z := mul_nonneg hCa (hB0 R2 hR2)
  have hL : 0 ≤ L :=
    mul_nonneg (mul_nonneg hCa (hB1 R2 hR2)) hC3
  refine ⟨Z, L, hZ, hL, ?_⟩
  intro T
  let S : SmoothCcTensor g 0 2 :=
    lowRadial (I := I) (M := M) g ρ T
  let A : LowerScaleActionCoefficients g := radialLowerScaleActionCoefficients (I := I) (M := M)
    g hρ.le hδ0 hδ_le hreal T
  let A3 : ℝ := C3 *
    ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖
  let Q : ℝ := B0 R2 + B1 R2 * A3
  have hA3 : 0 ≤ A3 := mul_nonneg hC3 (norm_nonneg _)
  have hQ : 0 ≤ Q := add_nonneg (hB0 R2 hR2)
    (mul_nonneg (hB1 R2 hR2) hA3)
  have hSρ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ :=
    lowRadial_norm (I := I) (M := M) g hρ.le T
  have hSδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g S) δ := hreal S hSρ
  have hzeroHs :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (0 : SmoothCcTensor g 0 2)‖ ≤ ρ := by
    rw [show (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • (0 : SmoothCcTensor g 0 2) by simp,
      ccTensorToHs_smul, zero_smul, norm_zero]
    exact hρ.le
  have hZδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ := hreal _ hzeroHs
  have hS2 : covariantJetNormSq (I := I) (M := M) g 2 S ≤ R2 ^ 2 := by
    refine (hjet2 S).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC2 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hSρ hC2) 2
  have hS3n :
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) S‖ ≤
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ := by
    have hrad := lowRadialH3_le (I := I) (M := M) g hρ
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T)
    rw [lowRadialH3_apply_ccToHsLin (I := I) (M := M) g hρ T] at hrad
    simpa only [S, ccToHsLin_apply] using hrad
  have hS3 : covariantJetNormSq (I := I) (M := M) g 3 S ≤ A3 ^ 2 := by
    refine (hjet3 S).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC3 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hS3n hC3) 2
  have hcoeffRaw := hcoeff S
    (lowRadial_symm (I := I) (M := M) g ρ T)
    hδ_le hδ0 hSδ hZδ R2 A3 hR2 hA3 hS2 hS3
    (hSρ.trans hρρ0)
  have hcoeffAct :
      covariantJetNormSq (I := I) (M := M) g 2
          (A.zeroOrderCoefficient - (zeroData (I := I) (M := M) g).zeroOrderCoefficient) +
        covariantJetNormSq (I := I) (M := M) g 2
          (A.firstOrderCoefficient - (zeroData (I := I) (M := M) g).firstOrderCoefficient) ≤ Q ^ 2 := by
    simpa only [A, radialLowerScaleActionCoefficients, S, zeroData, sub_zero] using hcoeffRaw
  have hop := hact A (zeroData (I := I) (M := M) g) Q hQ hcoeffAct
  have hz := zeroData_pair (I := I) (M := M) g
  have hzHi :
      (zeroData (I := I) (M := M) g).firstOrderActionThirdToSecondOrder (I := I) (M := M) = 0 :=
    (ContinuousLinearMap.opNorm_zero_iff
      ((zeroData (I := I) (M := M) g).firstOrderActionThirdToSecondOrder (I := I) (M := M))).mp hz.1
  have hzLo :
      (zeroData (I := I) (M := M) g).firstOrderActionSecondToFirstOrder (I := I) (M := M) = 0 :=
    (ContinuousLinearMap.opNorm_zero_iff
      ((zeroData (I := I) (M := M) g).firstOrderActionSecondToFirstOrder (I := I) (M := M))).mp hz.2
  change
    ‖A.firstOrderActionThirdToSecondOrder (I := I) (M := M)‖ ≤
        Z + L * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ ∧
      ‖A.firstOrderActionSecondToFirstOrder (I := I) (M := M)‖ ≤
        Z + L * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖
  constructor
  · calc
      ‖A.firstOrderActionThirdToSecondOrder (I := I) (M := M)‖ ≤ Ca * Q := by
        simpa only [hzHi, sub_zero] using hop.1
      _ = Z + L * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ := by
        simp only [Q, A3, Z, L]
        ring
  · calc
      ‖A.firstOrderActionSecondToFirstOrder (I := I) (M := M)‖ ≤ Ca * Q := by
        simpa only [hzLo, sub_zero] using hop.2
      _ = Z + L * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ := by
        simp only [Q, A3, Z, L]
        ring

private theorem first_order_action_sobolev_extensions_commute_local
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (A : LowerScaleActionCoefficients g) :
    (incl12 (I := I) (M := M) g).comp
        (A.firstOrderActionThirdToSecondOrder (I := I) (M := M)) =
      (A.firstOrderActionSecondToFirstOrder (I := I) (M := M)).comp
        (incl32 (I := I) (M := M) g) := by
  obtain ⟨_, _, hpair⟩ := exists_firstOrderAction_spectralSobolev_extensions (I := I) (M := M) g
  obtain ⟨Ch, hCh, hhigh⟩ :=
    exists_lowerScaleFirstOrderAction_thirdToSecondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨Cl, hCl, hlow⟩ :=
    exists_lowerScaleFirstOrderAction_secondToFirstOrder_bound (I := I) (M := M) hDim g
  let J : ℝ :=
    covariantJetNormSq (I := I) (M := M) g 2 A.zeroOrderCoefficient +
      covariantJetNormSq (I := I) (M := M) g 2 A.firstOrderCoefficient
  let B : ℝ := Real.sqrt J
  let Ca : ℝ := Ch + Cl
  let Q : ℝ := (Ca * B) ^ 2
  have hJ : 0 ≤ J := add_nonneg
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBsq : B ^ 2 = J := by
    simpa only [B] using Real.sq_sqrt hJ
  have hCa : 0 ≤ Ca := add_nonneg hCh hCl
  have hQ : 0 ≤ Q := sq_nonneg _
  have hHi : ∀ W : SmoothCcTensor g 0 2,
      covariantJetNormSq (I := I) (M := M) g 2
          (A.firstOrderAction (I := I) (M := M) W) ≤
        Q * covariantJetNormSq (I := I) (M := M) g 3 W := by
    intro W
    let S : ℝ := Real.sqrt (covariantJetNormSq (I := I) (M := M) g 3 W)
    have hW : 0 ≤ covariantJetNormSq (I := I) (M := M) g 3 W :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hS : 0 ≤ S := Real.sqrt_nonneg _
    have hSsq : S ^ 2 = covariantJetNormSq (I := I) (M := M) g 3 W := by
      simpa only [S] using Real.sq_sqrt hW
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (A.firstOrderAction (I := I) (M := M) W) ≤ (Ch * B * S) ^ 2 :=
        hhigh A W B S hB hS (by rw [hBsq]) (by rw [hSsq])
      _ ≤ (Ca * B * S) ^ 2 := by
        exact pow_le_pow_left₀
          (mul_nonneg (mul_nonneg hCh hB) hS)
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_right hCl) hB) hS) 2
      _ = Q * covariantJetNormSq (I := I) (M := M) g 3 W := by
        rw [show (Ca * B * S) ^ 2 = (Ca * B) ^ 2 * S ^ 2 by ring,
          hSsq]
  have hLo : ∀ W : SmoothCcTensor g 0 2,
      covariantJetNormSq (I := I) (M := M) g 1
          (A.firstOrderAction (I := I) (M := M) W) ≤
        Q * covariantJetNormSq (I := I) (M := M) g 2 W := by
    intro W
    let S : ℝ := Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 W)
    have hW : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2 W :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hS : 0 ≤ S := Real.sqrt_nonneg _
    have hSsq : S ^ 2 = covariantJetNormSq (I := I) (M := M) g 2 W := by
      simpa only [S] using Real.sq_sqrt hW
    calc
      covariantJetNormSq (I := I) (M := M) g 1
          (A.firstOrderAction (I := I) (M := M) W) ≤ (Cl * B * S) ^ 2 :=
        hlow A W B S hB hS (by rw [hBsq]) (by rw [hSsq])
      _ ≤ (Ca * B * S) ^ 2 := by
        exact pow_le_pow_left₀
          (mul_nonneg (mul_nonneg hCl hB) hS)
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_left hCh) hB) hS) 2
      _ = Q * covariantJetNormSq (I := I) (M := M) g 2 W := by
        rw [show (Ca * B * S) ^ 2 = (Ca * B) ^ 2 * S ^ 2 by ring,
          hSsq]
  obtain ⟨_, _, _, _, hcomm⟩ := hpair A Q hQ hHi hLo
  simpa only [incl12, incl32] using hcomm

theorem exists_radialLowerScaleActionCoefficients_continuous_operator_extensions
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ0 : ℝ, 0 < ρ0 ∧
      ∀ {ρ δ : ℝ} (hρ : 0 < ρ) (_ : ρ ≤ ρ0)
        (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hreal : ∀ S : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
            gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g S) δ),
      ∃ Z L : ℝ, 0 ≤ Z ∧ 0 ≤ L ∧
        ∃ FHi : metricThirdOrderSobolev (I := I) (M := M) g →
              (metricThirdOrderSobolev (I := I) (M := M) g →L[ℝ]
                metricH2 (I := I) (M := M) g),
          ∃ FLo : metricThirdOrderSobolev (I := I) (M := M) g →
              (metricH2 (I := I) (M := M) g →L[ℝ]
                metricH1 (I := I) (M := M) g),
            Continuous FHi ∧ Continuous FLo ∧
            (∀ T : SmoothCcTensor g 0 2,
              FHi (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T) =
                (radialLowerScaleActionCoefficients (I := I) (M := M)
                  g hρ.le hδ0 hδ_le hreal T).firstOrderActionThirdToSecondOrder
                    (I := I) (M := M)) ∧
            (∀ T : SmoothCcTensor g 0 2,
              FLo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T) =
                (radialLowerScaleActionCoefficients (I := I) (M := M)
                  g hρ.le hδ0 hδ_le hreal T).firstOrderActionSecondToFirstOrder
                    (I := I) (M := M)) ∧
            (∀ x : metricThirdOrderSobolev (I := I) (M := M) g,
              ‖FHi x‖ ≤ Z + L * ‖x‖) ∧
            (∀ x : metricThirdOrderSobolev (I := I) (M := M) g,
              ‖FLo x‖ ≤ Z + L * ‖x‖) ∧
            (∀ x : metricThirdOrderSobolev (I := I) (M := M) g,
              (incl12 (I := I) (M := M) g).comp (FHi x) =
                (FLo x).comp (incl32 (I := I) (M := M) g)) := by
  obtain ⟨ρp, hρp, hpair⟩ :=
    exists_radialLowerScaleActionCoefficients_lipschitz_on_hs_three_ball
      (I := I) (M := M) hDim g
  obtain ⟨ρa, hρa, haff⟩ := zeroOrderCoefficient_core_affine (I := I) (M := M) hDim g
  let ρ0 : ℝ := min ρp ρa
  have hρ0 : 0 < ρ0 := lt_min hρp hρa
  refine ⟨ρ0, hρ0, ?_⟩
  intro ρ δ hρ hρρ0 hδ0 hδ_le hreal
  have hρp' : ρ ≤ ρp := hρρ0.trans (min_le_left _ _)
  have hρa' : ρ ≤ ρa := hρρ0.trans (min_le_right _ _)
  obtain ⟨Z, L, hZ, hL, hbd⟩ :=
    haff hρ hρa' hδ0 hδ_le hreal
  let fHi : SmoothCcTensor g 0 2 →
      (metricThirdOrderSobolev (I := I) (M := M) g →L[ℝ]
        metricH2 (I := I) (M := M) g) := fun T =>
    (radialLowerScaleActionCoefficients (I := I) (M := M)
      g hρ.le hδ0 hδ_le hreal T).firstOrderActionThirdToSecondOrder (I := I) (M := M)
  let fLo : SmoothCcTensor g 0 2 →
      (metricH2 (I := I) (M := M) g →L[ℝ]
        metricH1 (I := I) (M := M) g) := fun T =>
    (radialLowerScaleActionCoefficients (I := I) (M := M)
      g hρ.le hδ0 hδ_le hreal T).firstOrderActionSecondToFirstOrder (I := I) (M := M)
  have hpairHi : ∀ r : ℝ, ∃ K : ℝ,
      ∀ T U : SmoothCcTensor g 0 2,
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ r →
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ ≤ r →
        ‖fHi T - fHi U‖ ≤ K *
          ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
            ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ := by
    intro r
    obtain ⟨K, _, hK⟩ := hpair hρ hρp' hδ0 hδ_le hreal r
    refine ⟨K, ?_⟩
    intro T U hT hU
    simpa only [fHi] using (hK T U hT hU).1
  have hpairLo : ∀ r : ℝ, ∃ K : ℝ,
      ∀ T U : SmoothCcTensor g 0 2,
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ r →
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ ≤ r →
        ‖fLo T - fLo U‖ ≤ K *
          ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
            ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ := by
    intro r
    obtain ⟨K, _, hK⟩ := hpair hρ hρp' hδ0 hδ_le hreal r
    refine ⟨K, ?_⟩
    intro T U hT hU
    simpa only [fLo] using (hK T U hT hU).2
  have hbdHi : ∀ T : SmoothCcTensor g 0 2,
      ‖fHi T‖ ≤ Z + L *
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ := by
    intro T
    simpa only [fHi] using (hbd T).1
  have hbdLo : ∀ T : SmoothCcTensor g 0 2,
      ‖fLo T‖ ≤ Z + L *
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ := by
    intro T
    simpa only [fLo] using (hbd T).2
  have hΦ : Continuous (fun x : ℝ => Z + L * x) := by
    fun_prop
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  obtain ⟨FHi, hFHi, hFHiCore, hFHiBd⟩ :=
    DifferentialGeometry.Analysis.exists_extend_le
      (j := ccToHsLin (I := I) (M := M) g 2 (3 : ℝ))
      hdense fHi hΦ hpairHi hbdHi
  obtain ⟨FLo, hFLo, hFLoCore, hFLoBd⟩ :=
    DifferentialGeometry.Analysis.exists_extend_le
      (j := ccToHsLin (I := I) (M := M) g 2 (3 : ℝ))
      hdense fLo hΦ hpairLo hbdLo
  have hleft : Continuous (fun x : metricThirdOrderSobolev (I := I) (M := M) g =>
      (incl12 (I := I) (M := M) g).comp (FHi x)) :=
    (ContinuousLinearMap.compL ℝ
      (metricThirdOrderSobolev (I := I) (M := M) g)
      (metricH2 (I := I) (M := M) g)
      (metricH1 (I := I) (M := M) g)).continuous₂.comp
        (continuous_const.prodMk hFHi)
  have hright : Continuous (fun x : metricThirdOrderSobolev (I := I) (M := M) g =>
      (FLo x).comp (incl32 (I := I) (M := M) g)) :=
    (ContinuousLinearMap.compL ℝ
      (metricThirdOrderSobolev (I := I) (M := M) g)
      (metricH2 (I := I) (M := M) g)
      (metricH1 (I := I) (M := M) g)).continuous₂.comp
        (hFLo.prodMk continuous_const)
  have hcomm : ∀ x : metricThirdOrderSobolev (I := I) (M := M) g,
      (incl12 (I := I) (M := M) g).comp (FHi x) =
        (FLo x).comp (incl32 (I := I) (M := M) g) := by
    intro x
    refine hdense.induction_on x (isClosed_eq hleft hright) ?_
    intro T
    rw [hFHiCore T, hFLoCore T]
    exact first_order_action_sobolev_extensions_commute_local (I := I) (M := M) hDim g _
  exact ⟨Z, L, hZ, hL, FHi, FLo, hFHi, hFLo,
    hFHiCore, hFLoCore, hFHiBd, hFLoBd, hcomm⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end

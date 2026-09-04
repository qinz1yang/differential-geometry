import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Action.LowerScaleSobolevExtensions
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Time.LowOrderOperators

noncomputable section

open Bundle Manifold
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private abbrev metricH2 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

private abbrev metricThirdOrderSobolev (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (3 : ℝ)

private noncomputable abbrev incl32 (g : SmoothRiemannianMetric I M) :
    metricThirdOrderSobolev (I := I) (M := M) g →L[ℝ]
      metricH2 (I := I) (M := M) g :=
  tensorHsInclusion (I := I) (M := M) (g := g)
    (r := 0) (s := 2) (by norm_num)

private theorem radial_j2
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ T : SmoothCcTensor g 0 2,
        covariantJetNormSq (I := I) (M := M) g 2
            (lowRadial (I := I) (M := M) g ρ T) ≤
          (C * ρ) ^ 2) ∧
      (∀ T U : SmoothCcTensor g 0 2,
        covariantJetNormSq (I := I) (M := M) g 2
            (lowRadial (I := I) (M := M) g ρ T -
              lowRadial (I := I) (M := M) g ρ U) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
            ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖) ^ 2) := by
  obtain ⟨C, hC, hjet⟩ := exists_covariantJetNormSq_le_spectralSobolevNorm_sq (I := I) (M := M) g 2 2
  refine ⟨C, hC, ?_, ?_⟩
  · intro T
    refine (hjet (lowRadial (I := I) (M := M) g ρ T)).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC (norm_nonneg _))
      (mul_le_mul_of_nonneg_left
        (lowRadial_norm (I := I) (M := M) g hρ T) hC) 2
  · intro T U
    have hrad := lowRadial_lip (I := I) (M := M) g hρ T U
    have hnorm :
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
              (lowRadial (I := I) (M := M) g ρ T -
                lowRadial (I := I) (M := M) g ρ U)‖ ≤
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
            ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by
      rw [show
        ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
              (lowRadial (I := I) (M := M) g ρ T -
                lowRadial (I := I) (M := M) g ρ U) =
            ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
                (lowRadial (I := I) (M := M) g ρ T) -
              ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
                (lowRadial (I := I) (M := M) g ρ U) by
          simpa only [ccToHsLin_apply] using
            map_sub (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ))
              (lowRadial (I := I) (M := M) g ρ T)
              (lowRadial (I := I) (M := M) g ρ U)]
      exact hrad
    refine (hjet
      (lowRadial (I := I) (M := M) g ρ T -
        lowRadial (I := I) (M := M) g ρ U)).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hnorm hC) 2

private theorem radial_j3
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ T : SmoothCcTensor g 0 2,
        covariantJetNormSq (I := I) (M := M) g 3
            (lowRadial (I := I) (M := M) g ρ T) ≤
          (C * ‖ccTensorToHs (I := I) (M := M)
            g 2 (3 : ℝ) T‖) ^ 2) ∧
      (∀ T U : SmoothCcTensor g 0 2,
        covariantJetNormSq (I := I) (M := M) g 3
            (lowRadial (I := I) (M := M) g ρ T -
              lowRadial (I := I) (M := M) g ρ U) ≤
          (C *
            (‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T -
                ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ +
              (1 / ρ) *
                max
                  ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
                  ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
                ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
                  ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖)) ^ 2) := by
  obtain ⟨C, hC, hjet⟩ := exists_covariantJetNormSq_le_spectralSobolevNorm_sq (I := I) (M := M) g 2 3
  refine ⟨C, hC, ?_, ?_⟩
  · intro T
    have hrad := lowRadialH3_le (I := I) (M := M) g hρ
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T)
    rw [lowRadialH3_core (I := I) (M := M) g hρ T] at hrad
    simp only [ccToHsLin_apply] at hrad
    refine (hjet (lowRadial (I := I) (M := M) g ρ T)).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hrad hC) 2
  · intro T U
    let Q : ℝ :=
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T -
          ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ +
        (1 / ρ) *
          max
            ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
            ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
            ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖
    have hQ : 0 ≤ Q := by
      dsimp only [Q]
      positivity
    have hrad := lowRadial_h3_sub (I := I) (M := M) g hρ T U
    have hnorm :
        ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ)
              (lowRadial (I := I) (M := M) g ρ T -
                lowRadial (I := I) (M := M) g ρ U)‖ ≤ Q := by
      rw [show
        ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ)
              (lowRadial (I := I) (M := M) g ρ T -
                lowRadial (I := I) (M := M) g ρ U) =
            ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ)
                (lowRadial (I := I) (M := M) g ρ T) -
              ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ)
                (lowRadial (I := I) (M := M) g ρ U) by
          simpa only [ccToHsLin_apply] using
            map_sub (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ))
              (lowRadial (I := I) (M := M) g ρ T)
              (lowRadial (I := I) (M := M) g ρ U)]
      simpa only [Q] using hrad
    refine (hjet
      (lowRadial (I := I) (M := M) g ρ T -
        lowRadial (I := I) (M := M) g ρ U)).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hnorm hC) 2

theorem radialFirstOrderAction_pairing_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧
      ∀ T : SmoothCcTensor g 0 2,
      let A := lowCoreActionCoefficients (I := I) (M := M)
        g hρ.le hδ0 hδ_le hreal T
      ‖A.firstOrderActionThirdToSecondOrder (I := I) (M := M)‖ ≤
          C * Real.sqrt
            (K * (1 + covariantJetNormSq (I := I) (M := M) g 3
              (lowRadial (I := I) (M := M) g ρ T)) ^ 6) ∧
        ‖A.firstOrderActionSecondToFirstOrder (I := I) (M := M)‖ ≤
          C * Real.sqrt
            (K * (1 + covariantJetNormSq (I := I) (M := M) g 3
              (lowRadial (I := I) (M := M) g ρ T)) ^ 6) ∧
        (tensorHsInclusion (I := I) (M := M) (g := g)
            (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
              (A.firstOrderActionThirdToSecondOrder (I := I) (M := M)) =
          (A.firstOrderActionSecondToFirstOrder (I := I) (M := M)).comp
            (tensorHsInclusion (I := I) (M := M) (g := g)
              (r := 0) (s := 2) (show (2 : ℝ) ≤ 3 by norm_num)) := by
  obtain ⟨K₀, hK₀, hcoeff⟩ :=
    exists_lowerScaleAction_coefficient_bound (I := I) (M := M) hDim g
  obtain ⟨C₃, hC₃, hact₃⟩ :=
    exists_lowerScaleFirstOrderAction_thirdToSecondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨C₂, hC₂, hact₂⟩ :=
    exists_lowerScaleFirstOrderAction_secondToFirstOrder_bound (I := I) (M := M) hDim g
  obtain ⟨C, hC, hpair⟩ :=
    exists_firstOrderAction_spectralSobolev_extensions (I := I) (M := M) g
  let K : ℝ := (C₃ ^ 2 + C₂ ^ 2) * K₀
  have hK : 0 ≤ K :=
    mul_nonneg (add_nonneg (sq_nonneg C₃) (sq_nonneg C₂)) hK₀
  refine ⟨C, K, hC, hK, ?_⟩
  intro T
  dsimp only
  let S : SmoothCcTensor g 0 2 :=
    lowRadial (I := I) (M := M) g ρ T
  have hSρ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ :=
    lowRadial_norm (I := I) (M := M) g hρ.le T
  have hSδ :
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g S) δ :=
    hreal S hSρ
  have hzeroHs :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (0 : SmoothCcTensor g 0 2)‖ ≤ ρ := by
    rw [show (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • (0 : SmoothCcTensor g 0 2) by simp,
      ccTensorToHs_smul, zero_smul, norm_zero]
    exact hρ.le
  have hZδ :
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g
          (0 : SmoothCcTensor g 0 2)) δ :=
    hreal _ hzeroHs
  let A : LowerScaleActionCoefficients g :=
    lowCoreActionCoefficients (I := I) (M := M)
      g hρ.le hδ0 hδ_le hreal T
  let X : ℝ := 1 + covariantJetNormSq (I := I) (M := M) g 3 S
  have hX0 : 0 ≤ X := by
    simp only [X]
    unfold covariantJetNormSq
    positivity
  have hcoeffA :
      covariantJetNormSq (I := I) (M := M) g 2 A.zeroOrderCoefficient +
          covariantJetNormSq (I := I) (M := M) g 2 A.firstOrderCoefficient ≤ K₀ * X ^ 6 := by
    simpa only [A, lowCoreActionCoefficients, S, X] using
      hcoeff S
        (lowRadial_symm (I := I) (M := M) g ρ T)
        hδ_le hδ0 hSδ hZδ
  have hHiAct :
      ∀ W : SmoothCcTensor g 0 2,
        covariantJetNormSq (I := I) (M := M) g 2
            (A.firstOrderAction (I := I) (M := M) W) ≤
          K * X ^ 6 * covariantJetNormSq (I := I) (M := M) g 3 W := by
    intro W
    let JW : ℝ := covariantJetNormSq (I := I) (M := M) g 3 W
    let B : ℝ := Real.sqrt (K₀ * X ^ 6)
    let D : ℝ := Real.sqrt JW
    have hBX : 0 ≤ K₀ * X ^ 6 :=
      mul_nonneg hK₀ (pow_nonneg hX0 6)
    have hJW : 0 ≤ JW := by
      simp only [JW]
      unfold covariantJetNormSq
      positivity
    have hB : 0 ≤ B := Real.sqrt_nonneg _
    have hD : 0 ≤ D := Real.sqrt_nonneg _
    have hBsq : B ^ 2 = K₀ * X ^ 6 := by
      simpa only [B] using Real.sq_sqrt hBX
    have hDsq : D ^ 2 = JW := by
      simpa only [D] using Real.sq_sqrt hJW
    have hraw := hact₃ A W B D hB hD
      (by rw [hBsq]; exact hcoeffA)
      (by rw [hDsq])
    have hC :
        C₃ ^ 2 * K₀ ≤ (C₃ ^ 2 + C₂ ^ 2) * K₀ :=
      mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (sq_nonneg C₂)) hK₀
    have htail : 0 ≤ X ^ 6 * JW :=
      mul_nonneg (pow_nonneg hX0 6) hJW
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (A.firstOrderAction (I := I) (M := M) W) ≤ (C₃ * B * D) ^ 2 := hraw
      _ = (C₃ ^ 2 * K₀) * (X ^ 6 * JW) := by
        rw [show (C₃ * B * D) ^ 2 = C₃ ^ 2 * B ^ 2 * D ^ 2 by ring,
          hBsq, hDsq]
        ring
      _ ≤ ((C₃ ^ 2 + C₂ ^ 2) * K₀) * (X ^ 6 * JW) :=
        mul_le_mul_of_nonneg_right hC htail
      _ = K * X ^ 6 * JW := by simp only [K]; ring
      _ = K * X ^ 6 *
          covariantJetNormSq (I := I) (M := M) g 3 W := by simp only [JW]
  have hLoAct :
      ∀ W : SmoothCcTensor g 0 2,
        covariantJetNormSq (I := I) (M := M) g 1
            (A.firstOrderAction (I := I) (M := M) W) ≤
          K * X ^ 6 * covariantJetNormSq (I := I) (M := M) g 2 W := by
    intro W
    let JW : ℝ := covariantJetNormSq (I := I) (M := M) g 2 W
    let B : ℝ := Real.sqrt (K₀ * X ^ 6)
    let D : ℝ := Real.sqrt JW
    have hBX : 0 ≤ K₀ * X ^ 6 :=
      mul_nonneg hK₀ (pow_nonneg hX0 6)
    have hJW : 0 ≤ JW := by
      simp only [JW]
      unfold covariantJetNormSq
      positivity
    have hB : 0 ≤ B := Real.sqrt_nonneg _
    have hD : 0 ≤ D := Real.sqrt_nonneg _
    have hBsq : B ^ 2 = K₀ * X ^ 6 := by
      simpa only [B] using Real.sq_sqrt hBX
    have hDsq : D ^ 2 = JW := by
      simpa only [D] using Real.sq_sqrt hJW
    have hraw := hact₂ A W B D hB hD
      (by rw [hBsq]; exact hcoeffA)
      (by rw [hDsq])
    have hC :
        C₂ ^ 2 * K₀ ≤ (C₃ ^ 2 + C₂ ^ 2) * K₀ :=
      mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left (sq_nonneg C₃)) hK₀
    have htail : 0 ≤ X ^ 6 * JW :=
      mul_nonneg (pow_nonneg hX0 6) hJW
    calc
      covariantJetNormSq (I := I) (M := M) g 1
          (A.firstOrderAction (I := I) (M := M) W) ≤ (C₂ * B * D) ^ 2 := hraw
      _ = (C₂ ^ 2 * K₀) * (X ^ 6 * JW) := by
        rw [show (C₂ * B * D) ^ 2 = C₂ ^ 2 * B ^ 2 * D ^ 2 by ring,
          hBsq, hDsq]
        ring
      _ ≤ ((C₃ ^ 2 + C₂ ^ 2) * K₀) * (X ^ 6 * JW) :=
        mul_le_mul_of_nonneg_right hC htail
      _ = K * X ^ 6 * JW := by simp only [K]; ring
      _ = K * X ^ 6 *
          covariantJetNormSq (I := I) (M := M) g 2 W := by simp only [JW]
  let Q : ℝ := K * X ^ 6
  have hQ : 0 ≤ Q :=
    mul_nonneg hK (pow_nonneg hX0 6)
  obtain ⟨hHi, hLo, _, _, hcompat⟩ :=
    hpair A Q hQ
      (by simpa only [Q] using hHiAct)
      (by simpa only [Q] using hLoAct)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [A, Q, X, S] using hHi
  · simpa only [A, Q, X, S] using hLo
  · simpa only [A] using hcompat

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end

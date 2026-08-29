import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.FirstOrderPairing
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.TimeFirstOrder
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantJetInterpolation

noncomputable section

open Bundle Manifold
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev
  (covariantJetNormSq exists_covariantJetNormSq_le_spectralSobolevNorm_sq)
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral
  (ccTensorToHs ccTensorToHs_coeff ccToHsLin ccToHsLin_apply)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private theorem inclCc32
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)
        (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T) =
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T := by
  refine tensorHs.ext ?_
  funext i
  rw [tensorHsInclusion_coeff_apply, ccTensorToHs_coeff,
    ccTensorToHs_coeff]

private theorem ccToHsSub
    (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (T U : SmoothCcTensor g 0 2) :
    ccTensorToHs (I := I) (M := M) g 2 σ (T - U) =
      ccTensorToHs (I := I) (M := M) g 2 σ T -
        ccTensorToHs (I := I) (M := M) g 2 σ U := by
  simpa only [ccToHsLin_apply] using
    map_sub (ccToHsLin (I := I) (M := M) g 2 σ) T U

theorem radialFirstOrderActionSecondToFirstOrder_pairing_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ {ρ δ : ℝ} (hρ : 0 < ρ) (_ : ρ ≤ ρ₀)
        (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3),
      ∀ (hreal : ∀ S : SmoothCcTensor g 0 2,
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
          gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g S) δ),
      ∀ r : ℝ, ∃ K : ℝ, ∀ T U : SmoothCcTensor g 0 2,
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ r →
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ ≤ r →
        ‖(lowCoreActionCoefficients (I := I) (M := M) g
              hρ.le hδ0 hδ_le hreal T).firstOrderActionSecondToFirstOrder
                (I := I) (M := M) -
            (lowCoreActionCoefficients (I := I) (M := M) g
              hρ.le hδ0 hδ_le hreal U).firstOrderActionSecondToFirstOrder
                (I := I) (M := M)‖ ≤
          K * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
            ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ := by
  obtain ⟨ρ₀, K₀, hρ₀, hK₀, hpair⟩ :=
    firstOrderActionSecondToFirstOrder_pairing_lipschitz_bound (I := I) (M := M) hDim g
  obtain ⟨C₂, hC₂, hjet₂⟩ := exists_covariantJetNormSq_le_spectralSobolevNorm_sq (I := I) (M := M) g 2 2
  obtain ⟨C₃, hC₃, hjet₃⟩ := exists_covariantJetNormSq_le_spectralSobolevNorm_sq (I := I) (M := M) g 2 3
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ δ hρ hρρ₀ hδ0 hδ_le hreal r
  let R₂ : ℝ := C₂ * ρ
  let A₃ : ℝ := C₃ * r
  let L : ℝ := 1 + (1 / ρ) * r
  let P : ℝ := 1 + A₃ + A₃ ^ 2
  let K : ℝ := K₀ R₂ * P ^ 2 * (C₃ * L + C₂ + 1)
  refine ⟨K, ?_⟩
  intro T U hTr hUr
  have hr : 0 ≤ r := (norm_nonneg _).trans hTr
  have hρ0 : 0 ≤ ρ := hρ.le
  have hR₂ : 0 ≤ R₂ := mul_nonneg hC₂ hρ0
  have hA₃ : 0 ≤ A₃ := mul_nonneg hC₃ hr
  have hρinv : 0 ≤ (1 / ρ : ℝ) := (one_div_pos.mpr hρ).le
  have hL : 0 ≤ L := by
    simp only [L]
    positivity
  let D : ℝ :=
    ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
      ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖
  let D₂ : ℝ := C₂ * D
  let D₃ : ℝ := C₃ * L * D
  have hD : 0 ≤ D := norm_nonneg _
  have hD₂ : 0 ≤ D₂ := mul_nonneg hC₂ hD
  have hD₃ : 0 ≤ D₃ := mul_nonneg (mul_nonneg hC₃ hL) hD
  let T₀ : SmoothCcTensor g 0 2 :=
    lowRadial (I := I) (M := M) g ρ T
  let U₀ : SmoothCcTensor g 0 2 :=
    lowRadial (I := I) (M := M) g ρ U
  have hT₀ρ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T₀‖ ≤ ρ :=
    lowRadial_norm (I := I) (M := M) g hρ0 T
  have hU₀ρ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U₀‖ ≤ ρ :=
    lowRadial_norm (I := I) (M := M) g hρ0 U
  have hTδ :
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g T₀) δ :=
    hreal T₀ hT₀ρ
  have hUδ :
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g U₀) δ :=
    hreal U₀ hU₀ρ
  have hZδ :
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g
          (0 : SmoothCcTensor g 0 2)) δ := by
    apply hreal
    have hz :
        ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (0 : SmoothCcTensor g 0 2) = 0 := by
      simpa only [ccToHsLin_apply] using
        map_zero (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ))
    rw [hz, norm_zero]
    exact hρ0
  have hT₂ :
      covariantJetNormSq (I := I) (M := M) g 2 T₀ ≤ R₂ ^ 2 := by
    refine (hjet₂ T₀).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC₂ (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hT₀ρ hC₂) 2
  have hU₂ :
      covariantJetNormSq (I := I) (M := M) g 2 U₀ ≤ R₂ ^ 2 := by
    refine (hjet₂ U₀).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC₂ (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hU₀ρ hC₂) 2
  have hT₀top :
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T₀‖ ≤ r := by
    have hrad := lowRadialH3_le (I := I) (M := M) g hρ
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T)
    rw [lowRadialH3_core (I := I) (M := M) g hρ T] at hrad
    simp only [ccToHsLin_apply] at hrad
    exact hrad.trans hTr
  have hU₀top :
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U₀‖ ≤ r := by
    have hrad := lowRadialH3_le (I := I) (M := M) g hρ
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U)
    rw [lowRadialH3_core (I := I) (M := M) g hρ U] at hrad
    simp only [ccToHsLin_apply] at hrad
    exact hrad.trans hUr
  have hT₃ :
      covariantJetNormSq (I := I) (M := M) g 3 T₀ ≤ A₃ ^ 2 := by
    refine (hjet₃ T₀).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC₃ (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hT₀top hC₃) 2
  have hU₃ :
      covariantJetNormSq (I := I) (M := M) g 3 U₀ ≤ A₃ ^ 2 := by
    refine (hjet₃ U₀).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC₃ (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hU₀top hC₃) 2
  have hincl :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ D := by
    have h := tensorHsInclusion_norm_le (I := I) (M := M)
      (g := g) (r := 0) (s := 2)
      (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)
      (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T -
        ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U)
    rw [map_sub, inclCc32 (I := I) (M := M) g T,
      inclCc32 (I := I) (M := M) g U] at h
    simpa only [D, ccToHsLin_apply] using h
  have hrad₂ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T₀ - U₀)‖ ≤ D := by
    rw [ccToHsSub]
    exact (lowRadial_lip (I := I) (M := M) g hρ0 T U).trans hincl
  have hTU₂ :
      covariantJetNormSq (I := I) (M := M) g 2 (T₀ - U₀) ≤ D₂ ^ 2 := by
    refine (hjet₂ (T₀ - U₀)).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC₂ (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hrad₂ hC₂) 2
  have hmax :
      max
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ ≤ r := by
    exact max_le hTr hUr
  have hprod :
      max
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
            ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤
        r * D :=
    mul_le_mul hmax hincl (norm_nonneg _) hr
  have hrad₃ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) (T₀ - U₀)‖ ≤
        L * D := by
    rw [ccToHsSub]
    refine (lowRadial_h3_sub (I := I) (M := M) g hρ T U).trans ?_
    have hscaled := mul_le_mul_of_nonneg_left hprod hρinv
    have hscaled' :
        (1 / ρ) *
              max
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
                ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤
          (1 / ρ) * (r * D) := by
      calc
        (1 / ρ) *
              max
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
                ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ =
            (1 / ρ) *
              (max
                  ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
                  ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
                ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
                  ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖) := by ring
        _ ≤ (1 / ρ) * (r * D) := hscaled
    calc
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T -
          ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ +
            (1 / ρ) *
              max
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
                ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤
          D + (1 / ρ) * (r * D) := by
        change D + _ ≤ D + _
        exact add_le_add_right hscaled' D
      _ = L * D := by
        simp only [L]
        ring
  have hTU₃ :
      covariantJetNormSq (I := I) (M := M) g 3 (T₀ - U₀) ≤ D₃ ^ 2 := by
    refine (hjet₃ (T₀ - U₀)).trans ?_
    dsimp only [D₃]
    have hthree : ((3 : ℕ) : ℝ) = (3 : ℝ) := by norm_num
    rw [hthree]
    simpa only [mul_assoc] using pow_le_pow_left₀
      (mul_nonneg hC₃ (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hrad₃ hC₃) 2
  have hout := hpair T₀ U₀
    (lowRadial_symm (I := I) (M := M) g ρ T)
    (lowRadial_symm (I := I) (M := M) g ρ U)
    hδ_le hδ0 hTδ hUδ hZδ
    R₂ A₃ D₂ D₃ D hR₂ hA₃ hD₂ hD₃ hD
    hT₂ hU₂ hT₃ hU₃ hTU₂ hTU₃
    (hT₀ρ.trans hρρ₀) (hU₀ρ.trans hρρ₀) hrad₂
  dsimp only at hout
  have hcore :
      ‖(lowCoreActionCoefficients (I := I) (M := M) g
            hρ.le hδ0 hδ_le hreal T).firstOrderActionSecondToFirstOrder (I := I) (M := M) -
          (lowCoreActionCoefficients (I := I) (M := M) g
            hρ.le hδ0 hδ_le hreal U).firstOrderActionSecondToFirstOrder (I := I) (M := M)‖ ≤
        K₀ R₂ * P ^ 2 * (D₃ + D₂ + D) := by
    simpa only [lowCoreActionCoefficients, T₀, U₀, P, A₃] using hout
  calc
    ‖(lowCoreActionCoefficients (I := I) (M := M) g
          hρ.le hδ0 hδ_le hreal T).firstOrderActionSecondToFirstOrder (I := I) (M := M) -
        (lowCoreActionCoefficients (I := I) (M := M) g
          hρ.le hδ0 hδ_le hreal U).firstOrderActionSecondToFirstOrder (I := I) (M := M)‖ ≤
      K₀ R₂ * P ^ 2 * (D₃ + D₂ + D) := hcore
    _ = K * D := by
      simp only [K, D₂, D₃]
      ring
    _ = K * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
        ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ := by
      simp only [D]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end

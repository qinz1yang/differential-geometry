import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Time.SecondOrder
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Time.FirstOrder
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Action.FirstOrderCommutator
import DifferentialGeometry.Analysis.DenseExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Background.FirstOrder.Pairing
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Background.Lifting.LowerScaleCoefficientBounds

noncomputable section

open Bundle Manifold MeasureTheory
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev
  (covariantJetNormSq exists_covariantJetNormSq_le_spectralSobolevNorm_sq)
open DifferentialGeometry.Analysis.Spectral
  (ccTensorToHs ccTensorToHs_coeff ccToHsLin ccToHsLin_apply ccToHsLin_dense
    ccToHs_injective deTurckSmoothRemainder)
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

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem zero_fibre_bound
    (g : SmoothRiemannianMetric I M) {δ : ℝ} (hδ : 0 ≤ δ) :
    gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ := by
  intro x u v
  refine
    (gFibreOpBound_ccTensorBilinSymm_zero
      (I := I) (M := M) g x u v).trans ?_
  simp only [zero_mul]
  exact mul_nonneg
    (mul_nonneg hδ (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

noncomputable def lowCoreActionCoefficientsBackground
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) : LowerScaleActionCoefficients g :=
  lowerScaleActionCoefficients (I := I) (M := M) g gB
    (lowRadial (I := I) (M := M) g ρ T)
    (lt_of_le_of_lt hδ_le (by norm_num))
    (hreal _ (lowRadial_norm (I := I) (M := M) g hρ T))
    (zero_fibre_bound (I := I) (M := M) g hδ0)

theorem lowCoreBackground_split
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    let S := lowRadial (I := I) (M := M) g ρ T
    let A := lowCoreActionCoefficientsBackground (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal T
    deTurckSmoothRemainder (I := I) g gB S
          (lt_of_le_of_lt hδ_le (by norm_num))
          (hreal S (lowRadial_norm (I := I) (M := M) g hρ T)) -
        deTurckSmoothRemainder (I := I) g gB
          (0 : SmoothCcTensor g 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num))
          (zero_fibre_bound (I := I) (M := M) g hδ0) =
      A.secondOrderAction (I := I) (M := M) S + A.firstOrderAction (I := I) (M := M) S := by
  obtain ⟨_, _, hsplit⟩ := lowData_split (I := I) (M := M) g gB
  let S := lowRadial (I := I) (M := M) g ρ T
  have hs := hsplit S
    (lowRadial_symm (I := I) (M := M) g ρ T)
    hδ_le hδ0
    (hreal S (lowRadial_norm (I := I) (M := M) g hρ T))
    (zero_fibre_bound (I := I) (M := M) g hδ0)
  have hA : lowCoreActionCoefficientsBackground (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal T =
    lowerScaleActionCoefficients (I := I) (M := M) g gB S
      (lt_of_le_of_lt hδ_le (by norm_num))
      (hreal S (lowRadial_norm (I := I) (M := M) g hρ T))
      (zero_fibre_bound (I := I) (M := M) g hδ0) := rfl
  have hs' := hs.1
  rw [← hA] at hs'
  simpa only [S] using hs'

private abbrev lowA2LoBackgroundOp (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
    TensorHs (I := I) (M := M) g 0 2 (1 : ℝ)

private noncomputable def lowBackgroundRep
    (g : SmoothRiemannianMetric I M)
    (x : LowerScaleTimeInternal.LowCore (I := I) (M := M) g) :
    SmoothCcTensor g 0 2 :=
  Classical.choose x.property

private theorem lowBackgroundRep_spec
    (g : SmoothRiemannianMetric I M)
    (x : LowerScaleTimeInternal.LowCore (I := I) (M := M) g) :
    ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)
        (lowBackgroundRep (I := I) (M := M) g x) =
      (x : metricH2 (I := I) (M := M) g) :=
  Classical.choose_spec x.property

private noncomputable def lowBackgroundCore
    {Y : Type*} (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (proj : LowerScaleActionCoefficients g → Y) :
    LowerScaleTimeInternal.LowCore (I := I) (M := M) g → Y :=
  fun x => proj (lowCoreActionCoefficientsBackground (I := I) (M := M)
    g gB hρ hδ0 hδ_le hreal (lowBackgroundRep (I := I) (M := M) g x))

private theorem lowBackgroundCore_value
    {Y : Type*} (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (proj : LowerScaleActionCoefficients g → Y) (T : SmoothCcTensor g 0 2) :
    lowBackgroundCore (I := I) (M := M) g gB hρ hδ0 hδ_le hreal proj
        ⟨ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T, ⟨T, rfl⟩⟩ =
      proj (lowCoreActionCoefficientsBackground (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T) := by
  have hrep : lowBackgroundRep (I := I) (M := M) g
      ⟨ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T, ⟨T, rfl⟩⟩ = T := by
    apply ccToHs_injective (I := I) (M := M) g 2 (2 : ℝ)
    simpa only [ccToHsLin_apply] using
      lowBackgroundRep_spec (I := I) (M := M) g
        ⟨ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T, ⟨T, rfl⟩⟩
  simp only [lowBackgroundCore, hrep]

private noncomputable def highBackgroundRep
    (g : SmoothRiemannianMetric I M)
    (x : LowerScaleTimeInternal.HighCore (I := I) (M := M) g) :
    SmoothCcTensor g 0 2 :=
  Classical.choose x.property

private theorem highBackgroundRep_spec
    (g : SmoothRiemannianMetric I M)
    (x : LowerScaleTimeInternal.HighCore (I := I) (M := M) g) :
    ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)
        (highBackgroundRep (I := I) (M := M) g x) =
      (x : metricThirdOrderSobolev (I := I) (M := M) g) :=
  Classical.choose_spec x.property

private noncomputable def highBackgroundCore
    {Y : Type*} (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (proj : LowerScaleActionCoefficients g → Y) :
    LowerScaleTimeInternal.HighCore (I := I) (M := M) g → Y :=
  fun x => proj (lowCoreActionCoefficientsBackground (I := I) (M := M)
    g gB hρ hδ0 hδ_le hreal (highBackgroundRep (I := I) (M := M) g x))

private theorem highBackgroundCore_value
    {Y : Type*} (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (proj : LowerScaleActionCoefficients g → Y) (T : SmoothCcTensor g 0 2) :
    highBackgroundCore (I := I) (M := M) g gB hρ hδ0 hδ_le hreal proj
        ⟨ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T, ⟨T, rfl⟩⟩ =
      proj (lowCoreActionCoefficientsBackground (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T) := by
  have hrep : highBackgroundRep (I := I) (M := M) g
      ⟨ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T, ⟨T, rfl⟩⟩ = T := by
    apply ccToHs_injective (I := I) (M := M) g 2 (3 : ℝ)
    simpa only [ccToHsLin_apply] using
      highBackgroundRep_spec (I := I) (M := M) g
        ⟨ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T, ⟨T, rfl⟩⟩
  simp only [highBackgroundCore, hrep]

def BackgroundFirstOrderActionCorePair
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) : Prop :=
  ∀ r : ℝ, ∃ K : ℝ, ∀ T U : SmoothCcTensor g 0 2,
    ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ r →
    ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ ≤ r →
      ‖(lowCoreActionCoefficientsBackground (I := I) (M := M)
            g gB hρ hδ0 hδ_le hreal T).firstOrderActionSecondToFirstOrder (I := I) (M := M) -
          (lowCoreActionCoefficientsBackground (I := I) (M := M)
            g gB hρ hδ0 hδ_le hreal U).firstOrderActionSecondToFirstOrder (I := I) (M := M)‖ ≤
        K * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
          ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖

def BackgroundFirstOrderActionThirdToSecondOrderCorePair
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) : Prop :=
  ∀ r : ℝ, ∃ K : ℝ, ∀ T U : SmoothCcTensor g 0 2,
    ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ r →
    ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ ≤ r →
      ‖(lowCoreActionCoefficientsBackground (I := I) (M := M)
            g gB hρ hδ0 hδ_le hreal T).firstOrderActionThirdToSecondOrder (I := I) (M := M) -
          (lowCoreActionCoefficientsBackground (I := I) (M := M)
            g gB hρ hδ0 hδ_le hreal U).firstOrderActionThirdToSecondOrder (I := I) (M := M)‖ ≤
        K * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
          ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖

noncomputable def lowerScaleFirstOrderActionThirdToSecondOrderBackground
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    metricThirdOrderSobolev (I := I) (M := M) g →
      LowerScaleTimeInternal.FirstOrderActionThirdToSecondOrderSpace (I := I) (M := M) g :=
  Dense.extend
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
    (highBackgroundCore (I := I) (M := M) g gB hρ hδ0 hδ_le hreal
      fun A => A.firstOrderActionThirdToSecondOrder (I := I) (M := M))

noncomputable def lowerScaleFirstOrderActionSecondToFirstOrderBackground
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    metricThirdOrderSobolev (I := I) (M := M) g →
      LowerScaleTimeInternal.FirstOrderActionSecondToFirstOrderSpace (I := I) (M := M) g :=
  Dense.extend
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
    (highBackgroundCore (I := I) (M := M) g gB hρ hδ0 hδ_le hreal
      fun A => A.firstOrderActionSecondToFirstOrder (I := I) (M := M))

private theorem inclCc32_bg
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)
        (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T) =
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T := by
  refine TensorHs.ext ?_
  funext i
  rw [tensorHsInclusion_coeff_apply, ccTensorToHs_coeff,
    ccTensorToHs_coeff]

private theorem ccToHsSub_bg
    (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (T U : SmoothCcTensor g 0 2) :
    ccTensorToHs (I := I) (M := M) g 2 σ (T - U) =
      ccTensorToHs (I := I) (M := M) g 2 σ T -
        ccTensorToHs (I := I) (M := M) g 2 σ U := by
  simpa only [ccToHsLin_apply] using
    map_sub (ccToHsLin (I := I) (M := M) g 2 σ) T U

private theorem sqrt_scale
    (q d : ℝ) (hq : 0 ≤ q) (hd : 0 ≤ d) :
    Real.sqrt (q * d ^ 2) = Real.sqrt q * d := by
  rw [Real.sqrt_mul hq, Real.sqrt_sq hd]

theorem radialFirstOrderActionBackground_pairing_bound
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ {ρ δ : ℝ} (hρ : 0 < ρ) (_ : ρ ≤ ρ₀)
        (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hreal : ∀ S : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
            gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g S) δ),
        BackgroundFirstOrderActionCorePair (I := I) (M := M)
          g gB hρ.le hδ0 hδ_le hreal := by
  obtain ⟨ρ₀, Bs, Z0, Z1, O0, O1, Ca, hρ₀, hBs, hZ0, hZ1,
      hO0, hO1, hCa, hpair⟩ :=
    firstOrderActionSecondToFirstOrder_background_pairing_bound (I := I) (M := M) hDim g gB
  obtain ⟨C₂, hC₂, hjet₂⟩ := exists_covariantJetNormSq_le_spectralSobolevNorm_sq (I := I) (M := M) g 2 2
  obtain ⟨C₃, hC₃, hjet₃⟩ := exists_covariantJetNormSq_le_spectralSobolevNorm_sq (I := I) (M := M) g 2 3
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ δ hρ hρρ₀ hδ0 hδ_le hreal
  dsimp only [BackgroundFirstOrderActionCorePair]
  intro r
  let R₂ : ℝ := C₂ * ρ
  let A₃ : ℝ := C₃ * r
  let L : ℝ := 1 + (1 / ρ) * r
  let P : ℝ := 1 + A₃ + A₃ ^ 2
  let E0 : ℝ :=
    2 *
      (Bs R₂ * (P ^ 4 * (C₂ ^ 2 + 1)) +
        (Z0 R₂ A₃ * C₂ + Z1 A₃) ^ 2)
  let E1 : ℝ := O0 * C₃ * L + O1 + O1 * A₃
  let K : ℝ := Ca * (Real.sqrt E0 + E1)
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
          (0 : SmoothCcTensor g 0 2)) δ :=
    zero_fibre_bound (I := I) (M := M) g hδ0
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
    rw [map_sub, inclCc32_bg (I := I) (M := M) g T,
      inclCc32_bg (I := I) (M := M) g U] at h
    simpa only [D, ccToHsLin_apply] using h
  have hrad₂ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T₀ - U₀)‖ ≤ D := by
    rw [ccToHsSub_bg]
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
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ ≤ r :=
    max_le hTr hUr
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
    rw [ccToHsSub_bg]
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
      ‖(lowCoreActionCoefficientsBackground (I := I) (M := M)
            g gB hρ.le hδ0 hδ_le hreal T).firstOrderActionSecondToFirstOrder (I := I) (M := M) -
          (lowCoreActionCoefficientsBackground (I := I) (M := M)
            g gB hρ.le hδ0 hδ_le hreal U).firstOrderActionSecondToFirstOrder (I := I) (M := M)‖ ≤
        Ca *
          (Real.sqrt
              (2 *
                (Bs R₂ * (P ^ 4 * (D₂ ^ 2 + D ^ 2)) +
                  (Z0 R₂ A₃ * D₂ + Z1 A₃ * D) ^ 2)) +
            (O0 * D₃ + O1 * D + O1 * A₃ * D)) := by
    simpa only [lowCoreActionCoefficientsBackground, T₀, U₀, P, A₃] using hout
  have hfirst :
      0 ≤ Bs R₂ * (P ^ 4 * (C₂ ^ 2 + 1)) :=
    mul_nonneg (hBs R₂ hR₂)
      (mul_nonneg (by positivity) (by nlinarith [sq_nonneg C₂]))
  have hE0 : 0 ≤ E0 := by
    dsimp only [E0]
    exact mul_nonneg (by norm_num)
      (add_nonneg hfirst (sq_nonneg _))
  have hquad :
      2 *
          (Bs R₂ * (P ^ 4 * (D₂ ^ 2 + D ^ 2)) +
            (Z0 R₂ A₃ * D₂ + Z1 A₃ * D) ^ 2) =
        E0 * D ^ 2 := by
    simp only [D₂, E0]
    ring
  have hsqrt :
      Real.sqrt
          (2 *
            (Bs R₂ * (P ^ 4 * (D₂ ^ 2 + D ^ 2)) +
              (Z0 R₂ A₃ * D₂ + Z1 A₃ * D) ^ 2)) =
        Real.sqrt E0 * D := by
    rw [hquad]
    exact sqrt_scale E0 D hE0 hD
  have hlin :
      O0 * D₃ + O1 * D + O1 * A₃ * D = E1 * D := by
    simp only [D₃, E1]
    ring
  calc
    ‖(lowCoreActionCoefficientsBackground (I := I) (M := M)
          g gB hρ.le hδ0 hδ_le hreal T).firstOrderActionSecondToFirstOrder (I := I) (M := M) -
        (lowCoreActionCoefficientsBackground (I := I) (M := M)
          g gB hρ.le hδ0 hδ_le hreal U).firstOrderActionSecondToFirstOrder (I := I) (M := M)‖ ≤
        Ca *
          (Real.sqrt
              (2 *
                (Bs R₂ * (P ^ 4 * (D₂ ^ 2 + D ^ 2)) +
                  (Z0 R₂ A₃ * D₂ + Z1 A₃ * D) ^ 2)) +
            (O0 * D₃ + O1 * D + O1 * A₃ * D)) := hcore
    _ = K * D := by
      rw [hsqrt, hlin]
      simp only [K]
      ring
    _ = K * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
        ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ := by
      simp only [D]

theorem radialFirstOrderActionThirdToSecondOrder_self
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ {ρ δ : ℝ} (hρ : 0 < ρ) (_ : ρ ≤ ρ₀)
        (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hreal : ∀ S : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
            gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g S) δ),
        BackgroundFirstOrderActionThirdToSecondOrderCorePair (I := I) (M := M)
          g g hρ.le hδ0 hδ_le hreal := by
  obtain ⟨ρ₀, B, O0, O1, Ca, hρ₀, hB, hO0, hO1, hCa, hpair⟩ :=
    firstOrderActionThirdToSecondOrder_self_pairing_bound (I := I) (M := M) hDim g
  obtain ⟨C₂, hC₂, hjet₂⟩ := exists_covariantJetNormSq_le_spectralSobolevNorm_sq (I := I) (M := M) g 2 2
  obtain ⟨C₃, hC₃, hjet₃⟩ := exists_covariantJetNormSq_le_spectralSobolevNorm_sq (I := I) (M := M) g 2 3
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ δ hρ hρρ₀ hδ0 hδ_le hreal
  dsimp only [BackgroundFirstOrderActionThirdToSecondOrderCorePair]
  intro r
  let R₂ : ℝ := C₂ * ρ
  let A₃ : ℝ := C₃ * r
  let L : ℝ := 1 + (1 / ρ) * r
  let F0 : ℝ := B R₂ * (1 + A₃ ^ 2) * (C₃ * L + C₂ + 1)
  let F1 : ℝ := O0 * C₃ * L + O1 + O1 * A₃
  let E0 : ℝ := F0 ^ 2 + F1 ^ 2
  let K : ℝ := Ca * Real.sqrt E0
  refine ⟨K, ?_⟩
  intro T U hTr hUr
  have hr : 0 ≤ r := (norm_nonneg _).trans hTr
  have hρ0 : 0 ≤ ρ := hρ.le
  have hR₂ : 0 ≤ R₂ := mul_nonneg hC₂ hρ0
  have hA₃ : 0 ≤ A₃ := mul_nonneg hC₃ hr
  have hρinv : 0 ≤ (1 / ρ : ℝ) := (one_div_pos.mpr hρ).le
  have hL : 0 ≤ L := by
    dsimp only [L]
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
          (0 : SmoothCcTensor g 0 2)) δ :=
    zero_fibre_bound (I := I) (M := M) g hδ0
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
    rw [map_sub, inclCc32_bg (I := I) (M := M) g T,
      inclCc32_bg (I := I) (M := M) g U] at h
    simpa only [D, ccToHsLin_apply] using h
  have hrad₂ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T₀ - U₀)‖ ≤ D := by
    rw [ccToHsSub_bg]
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
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ ≤ r :=
    max_le hTr hUr
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
    rw [ccToHsSub_bg]
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
      ‖(lowCoreActionCoefficientsBackground (I := I) (M := M)
            g g hρ.le hδ0 hδ_le hreal T).firstOrderActionThirdToSecondOrder (I := I) (M := M) -
          (lowCoreActionCoefficientsBackground (I := I) (M := M)
            g g hρ.le hδ0 hδ_le hreal U).firstOrderActionThirdToSecondOrder (I := I) (M := M)‖ ≤
        Ca * Real.sqrt
          ((B R₂ * (1 + A₃ ^ 2) * (D₃ + D₂ + D)) ^ 2 +
            (O0 * D₃ + O1 * D + O1 * A₃ * D) ^ 2) := by
    simpa only [lowCoreActionCoefficientsBackground, T₀, U₀] using hout
  have hE0 : 0 ≤ E0 := by
    dsimp only [E0]
    exact add_nonneg (sq_nonneg F0) (sq_nonneg F1)
  have hquad :
      (B R₂ * (1 + A₃ ^ 2) * (D₃ + D₂ + D)) ^ 2 +
          (O0 * D₃ + O1 * D + O1 * A₃ * D) ^ 2 =
        E0 * D ^ 2 := by
    simp only [D₂, D₃, E0, F0, F1]
    ring
  have hsqrt :
      Real.sqrt
          ((B R₂ * (1 + A₃ ^ 2) * (D₃ + D₂ + D)) ^ 2 +
            (O0 * D₃ + O1 * D + O1 * A₃ * D) ^ 2) =
        Real.sqrt E0 * D := by
    rw [hquad]
    exact sqrt_scale E0 D hE0 hD
  calc
    ‖(lowCoreActionCoefficientsBackground (I := I) (M := M)
          g g hρ.le hδ0 hδ_le hreal T).firstOrderActionThirdToSecondOrder (I := I) (M := M) -
        (lowCoreActionCoefficientsBackground (I := I) (M := M)
          g g hρ.le hδ0 hδ_le hreal U).firstOrderActionThirdToSecondOrder (I := I) (M := M)‖ ≤
        Ca * Real.sqrt
          ((B R₂ * (1 + A₃ ^ 2) * (D₃ + D₂ + D)) ^ 2 +
            (O0 * D₃ + O1 * D + O1 * A₃ * D) ^ 2) := hcore
    _ = K * D := by
      rw [hsqrt]
      simp only [K]
      ring
    _ = K * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
        ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ := by
      simp only [D]

theorem radialFirstOrderActionThirdToSecondOrderBackground_pairing_bound
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ {ρ δ : ℝ} (hρ : 0 < ρ) (_ : ρ ≤ ρ₀)
        (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hreal : ∀ S : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
            gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g S) δ),
        BackgroundFirstOrderActionThirdToSecondOrderCorePair (I := I) (M := M)
          g gB hρ.le hδ0 hδ_le hreal := by
  obtain ⟨ρ₀, Bs, B0, B1, O0, O1, Ca, hρ₀, hBs, hB0, hB1,
      hO0, hO1, hCa, hpair⟩ :=
    firstOrderActionThirdToSecondOrder_background_pairing_bound (I := I) (M := M) hDim g gB
  obtain ⟨C2, hC2, hjet2⟩ := exists_covariantJetNormSq_le_spectralSobolevNorm_sq (I := I) (M := M) g 2 2
  obtain ⟨C3, hC3, hjet3⟩ := exists_covariantJetNormSq_le_spectralSobolevNorm_sq (I := I) (M := M) g 2 3
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ δ hρ hρρ₀ hδ0 hδ_le hreal
  dsimp only [BackgroundFirstOrderActionThirdToSecondOrderCorePair]
  intro r
  let R2 : ℝ := C2 * ρ
  let A3 : ℝ := C3 * r
  let L : ℝ := 1 + (1 / ρ) * r
  let Fs : ℝ := Bs R2 * (1 + A3 ^ 2) * (C3 * L + C2 + 1)
  let Fb : ℝ :=
    B0 R2 * C3 * L + B1 R2 * C2 + B1 R2 * A3 * C2 +
      B1 R2 + B1 R2 * A3
  let F1 : ℝ := O0 * C3 * L + O1 + O1 * A3
  let E0 : ℝ := 2 * (Fs ^ 2 + Fb ^ 2) + F1 ^ 2
  let K : ℝ := Ca * Real.sqrt E0
  refine ⟨K, ?_⟩
  intro T U hTr hUr
  have hr : 0 ≤ r := (norm_nonneg _).trans hTr
  have hρ0 : 0 ≤ ρ := hρ.le
  have hR2 : 0 ≤ R2 := mul_nonneg hC2 hρ0
  have hA3 : 0 ≤ A3 := mul_nonneg hC3 hr
  have hρinv : 0 ≤ (1 / ρ : ℝ) := (one_div_pos.mpr hρ).le
  have hL : 0 ≤ L := by
    dsimp only [L]
    positivity
  let D : ℝ :=
    ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
      ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖
  let D2r : ℝ := C2 * D
  let D3r : ℝ := C3 * L * D
  have hD : 0 ≤ D := norm_nonneg _
  have hD2r : 0 ≤ D2r := mul_nonneg hC2 hD
  have hD3r : 0 ≤ D3r := mul_nonneg (mul_nonneg hC3 hL) hD
  let T0 : SmoothCcTensor g 0 2 :=
    lowRadial (I := I) (M := M) g ρ T
  let U0 : SmoothCcTensor g 0 2 :=
    lowRadial (I := I) (M := M) g ρ U
  have hT0ρ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T0‖ ≤ ρ :=
    lowRadial_norm (I := I) (M := M) g hρ0 T
  have hU0ρ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U0‖ ≤ ρ :=
    lowRadial_norm (I := I) (M := M) g hρ0 U
  have hTδ :
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g T0) δ :=
    hreal T0 hT0ρ
  have hUδ :
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g U0) δ :=
    hreal U0 hU0ρ
  have hZδ :
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g
          (0 : SmoothCcTensor g 0 2)) δ :=
    zero_fibre_bound (I := I) (M := M) g hδ0
  have hT2 :
      covariantJetNormSq (I := I) (M := M) g 2 T0 ≤ R2 ^ 2 := by
    refine (hjet2 T0).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC2 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hT0ρ hC2) 2
  have hU2 :
      covariantJetNormSq (I := I) (M := M) g 2 U0 ≤ R2 ^ 2 := by
    refine (hjet2 U0).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC2 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hU0ρ hC2) 2
  have hT0top :
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T0‖ ≤ r := by
    have hrad := lowRadialH3_le (I := I) (M := M) g hρ
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T)
    rw [lowRadialH3_core (I := I) (M := M) g hρ T] at hrad
    simp only [ccToHsLin_apply] at hrad
    exact hrad.trans hTr
  have hU0top :
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U0‖ ≤ r := by
    have hrad := lowRadialH3_le (I := I) (M := M) g hρ
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U)
    rw [lowRadialH3_core (I := I) (M := M) g hρ U] at hrad
    simp only [ccToHsLin_apply] at hrad
    exact hrad.trans hUr
  have hT3 :
      covariantJetNormSq (I := I) (M := M) g 3 T0 ≤ A3 ^ 2 := by
    refine (hjet3 T0).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC3 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hT0top hC3) 2
  have hU3 :
      covariantJetNormSq (I := I) (M := M) g 3 U0 ≤ A3 ^ 2 := by
    refine (hjet3 U0).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC3 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hU0top hC3) 2
  have hincl :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ D := by
    have h := tensorHsInclusion_norm_le (I := I) (M := M)
      (g := g) (r := 0) (s := 2)
      (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)
      (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T -
        ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U)
    rw [map_sub, inclCc32_bg (I := I) (M := M) g T,
      inclCc32_bg (I := I) (M := M) g U] at h
    simpa only [D, ccToHsLin_apply] using h
  have hrad2 :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T0 - U0)‖ ≤ D := by
    rw [ccToHsSub_bg]
    exact (lowRadial_lip (I := I) (M := M) g hρ0 T U).trans hincl
  have hTU2 :
      covariantJetNormSq (I := I) (M := M) g 2 (T0 - U0) ≤ D2r ^ 2 := by
    refine (hjet2 (T0 - U0)).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC2 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hrad2 hC2) 2
  have hmax :
      max
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ ≤ r :=
    max_le hTr hUr
  have hprod :
      max
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
            ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤
        r * D :=
    mul_le_mul hmax hincl (norm_nonneg _) hr
  have hrad3 :
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) (T0 - U0)‖ ≤
        L * D := by
    rw [ccToHsSub_bg]
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
  have hTU3 :
      covariantJetNormSq (I := I) (M := M) g 3 (T0 - U0) ≤ D3r ^ 2 := by
    refine (hjet3 (T0 - U0)).trans ?_
    dsimp only [D3r]
    have hthree : ((3 : ℕ) : ℝ) = (3 : ℝ) := by norm_num
    rw [hthree]
    simpa only [mul_assoc] using pow_le_pow_left₀
      (mul_nonneg hC3 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hrad3 hC3) 2
  have hout := hpair T0 U0
    (lowRadial_symm (I := I) (M := M) g ρ T)
    (lowRadial_symm (I := I) (M := M) g ρ U)
    hδ_le hδ0 hTδ hUδ hZδ
    R2 A3 D2r D3r D hR2 hA3 hD2r hD3r hD
    hT2 hU2 hT3 hU3 hTU2 hTU3
    (hT0ρ.trans hρρ₀) (hU0ρ.trans hρρ₀) hrad2
  dsimp only at hout
  have hcore :
      ‖(lowCoreActionCoefficientsBackground (I := I) (M := M)
            g gB hρ.le hδ0 hδ_le hreal T).firstOrderActionThirdToSecondOrder (I := I) (M := M) -
          (lowCoreActionCoefficientsBackground (I := I) (M := M)
            g gB hρ.le hδ0 hδ_le hreal U).firstOrderActionThirdToSecondOrder (I := I) (M := M)‖ ≤
        Ca * Real.sqrt
          (2 * ((Bs R2 * (1 + A3 ^ 2) * (D3r + D2r + D)) ^ 2 +
              (B0 R2 * D3r + B1 R2 * D2r + B1 R2 * A3 * D2r +
                B1 R2 * D + B1 R2 * A3 * D) ^ 2) +
            (O0 * D3r + O1 * D + O1 * A3 * D) ^ 2) := by
    simpa only [lowCoreActionCoefficientsBackground, T0, U0] using hout
  have hE0 : 0 ≤ E0 := by
    dsimp only [E0]
    exact add_nonneg
      (mul_nonneg (by norm_num) (add_nonneg (sq_nonneg Fs) (sq_nonneg Fb)))
      (sq_nonneg F1)
  have hquad :
      2 * ((Bs R2 * (1 + A3 ^ 2) * (D3r + D2r + D)) ^ 2 +
            (B0 R2 * D3r + B1 R2 * D2r + B1 R2 * A3 * D2r +
              B1 R2 * D + B1 R2 * A3 * D) ^ 2) +
          (O0 * D3r + O1 * D + O1 * A3 * D) ^ 2 =
        E0 * D ^ 2 := by
    simp only [D2r, D3r, E0, Fs, Fb, F1]
    ring
  have hsqrt :
      Real.sqrt
          (2 * ((Bs R2 * (1 + A3 ^ 2) * (D3r + D2r + D)) ^ 2 +
                (B0 R2 * D3r + B1 R2 * D2r + B1 R2 * A3 * D2r +
                  B1 R2 * D + B1 R2 * A3 * D) ^ 2) +
            (O0 * D3r + O1 * D + O1 * A3 * D) ^ 2) =
        Real.sqrt E0 * D := by
    rw [hquad]
    exact sqrt_scale E0 D hE0 hD
  calc
    ‖(lowCoreActionCoefficientsBackground (I := I) (M := M)
          g gB hρ.le hδ0 hδ_le hreal T).firstOrderActionThirdToSecondOrder (I := I) (M := M) -
        (lowCoreActionCoefficientsBackground (I := I) (M := M)
          g gB hρ.le hδ0 hδ_le hreal U).firstOrderActionThirdToSecondOrder (I := I) (M := M)‖ ≤
        Ca * Real.sqrt
          (2 * ((Bs R2 * (1 + A3 ^ 2) * (D3r + D2r + D)) ^ 2 +
              (B0 R2 * D3r + B1 R2 * D2r + B1 R2 * A3 * D2r +
                B1 R2 * D + B1 R2 * A3 * D) ^ 2) +
            (O0 * D3r + O1 * D + O1 * A3 * D) ^ 2) := hcore
    _ = K * D := by
      rw [hsqrt]
      simp only [K]
      ring
    _ = K * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
        ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ := by
      simp only [D]


theorem lowerScaleFirstOrderActionSecondToFirstOrderBackground_core
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} {hρ : 0 ≤ ρ} {hδ0 : 0 ≤ δ} {hδ_le : δ ≤ 1 / 3}
    {hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ}
    (hpair : BackgroundFirstOrderActionCorePair (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal)
    (T : SmoothCcTensor g 0 2) :
    lowerScaleFirstOrderActionSecondToFirstOrderBackground (I := I) (M := M) g gB hρ hδ0 hδ_le hreal
        (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T) =
      (lowCoreActionCoefficientsBackground (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T).firstOrderActionSecondToFirstOrder (I := I) (M := M) :=
  DifferentialGeometry.Analysis.extend_pair_apply
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
    (highBackgroundCore (I := I) (M := M) g gB hρ hδ0 hδ_le hreal
      fun A => A.firstOrderActionSecondToFirstOrder (I := I) (M := M))
    (fun U => (lowCoreActionCoefficientsBackground (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal U).firstOrderActionSecondToFirstOrder (I := I) (M := M))
    (highBackgroundCore_value (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal
        (fun A => A.firstOrderActionSecondToFirstOrder (I := I) (M := M)))
    (by simpa only [BackgroundFirstOrderActionCorePair] using hpair) T


theorem lowerScaleFirstOrderActionSecondToFirstOrderBackground_continuous
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} {hρ : 0 ≤ ρ} {hδ0 : 0 ≤ δ} {hδ_le : δ ≤ 1 / 3}
    {hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ}
    (hpair : BackgroundFirstOrderActionCorePair (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal) :
    Continuous (lowerScaleFirstOrderActionSecondToFirstOrderBackground (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal) :=
  DifferentialGeometry.Analysis.cont_extend_pair
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
    (highBackgroundCore (I := I) (M := M) g gB hρ hδ0 hδ_le hreal
      fun A => A.firstOrderActionSecondToFirstOrder (I := I) (M := M))
    (fun U => (lowCoreActionCoefficientsBackground (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal U).firstOrderActionSecondToFirstOrder (I := I) (M := M))
    (highBackgroundCore_value (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal
        (fun A => A.firstOrderActionSecondToFirstOrder (I := I) (M := M)))
    (by simpa only [BackgroundFirstOrderActionCorePair] using hpair)

theorem lowerScaleFirstOrderActionSecondToFirstOrderBackground_aestronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} {hρ : 0 ≤ ρ} {hδ0 : 0 ≤ δ} {hδ_le : δ ≤ 1 / 3}
    {hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ}
    (hpair : BackgroundFirstOrderActionCorePair (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal)
    (u : Ω → metricThirdOrderSobolev (I := I) (M := M) g)
    (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable
      (fun t => lowerScaleFirstOrderActionSecondToFirstOrderBackground (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal (u t)) μ :=
  (lowerScaleFirstOrderActionSecondToFirstOrderBackground_continuous (I := I) (M := M) g gB hpair).comp_aestronglyMeasurable hu


theorem lowerScaleFirstOrderActionThirdToSecondOrderBackground_core
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} {hρ : 0 ≤ ρ} {hδ0 : 0 ≤ δ} {hδ_le : δ ≤ 1 / 3}
    {hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ}
    (hpair : BackgroundFirstOrderActionThirdToSecondOrderCorePair (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal)
    (T : SmoothCcTensor g 0 2) :
    lowerScaleFirstOrderActionThirdToSecondOrderBackground (I := I) (M := M) g gB hρ hδ0 hδ_le hreal
        (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T) =
      (lowCoreActionCoefficientsBackground (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T).firstOrderActionThirdToSecondOrder (I := I) (M := M) :=
  DifferentialGeometry.Analysis.extend_pair_apply
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
    (highBackgroundCore (I := I) (M := M) g gB hρ hδ0 hδ_le hreal
      fun A => A.firstOrderActionThirdToSecondOrder (I := I) (M := M))
    (fun U => (lowCoreActionCoefficientsBackground (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal U).firstOrderActionThirdToSecondOrder (I := I) (M := M))
    (highBackgroundCore_value (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal
        (fun A => A.firstOrderActionThirdToSecondOrder (I := I) (M := M)))
    (by simpa only [BackgroundFirstOrderActionThirdToSecondOrderCorePair] using hpair) T


theorem lowerScaleFirstOrderActionThirdToSecondOrderBackground_continuous
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} {hρ : 0 ≤ ρ} {hδ0 : 0 ≤ δ} {hδ_le : δ ≤ 1 / 3}
    {hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ}
    (hpair : BackgroundFirstOrderActionThirdToSecondOrderCorePair (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal) :
    Continuous (lowerScaleFirstOrderActionThirdToSecondOrderBackground (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal) :=
  DifferentialGeometry.Analysis.cont_extend_pair
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
    (highBackgroundCore (I := I) (M := M) g gB hρ hδ0 hδ_le hreal
      fun A => A.firstOrderActionThirdToSecondOrder (I := I) (M := M))
    (fun U => (lowCoreActionCoefficientsBackground (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal U).firstOrderActionThirdToSecondOrder (I := I) (M := M))
    (highBackgroundCore_value (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal
        (fun A => A.firstOrderActionThirdToSecondOrder (I := I) (M := M)))
    (by simpa only [BackgroundFirstOrderActionThirdToSecondOrderCorePair] using hpair)

theorem lowerScaleFirstOrderActionThirdToSecondOrderBackground_aestronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} {hρ : 0 ≤ ρ} {hδ0 : 0 ≤ δ} {hδ_le : δ ≤ 1 / 3}
    {hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ}
    (hpair : BackgroundFirstOrderActionThirdToSecondOrderCorePair (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal)
    (u : Ω → metricThirdOrderSobolev (I := I) (M := M) g)
    (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable
      (fun t => lowerScaleFirstOrderActionThirdToSecondOrderBackground (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal (u t)) μ :=
  (lowerScaleFirstOrderActionThirdToSecondOrderBackground_continuous (I := I) (M := M) g gB hpair).comp_aestronglyMeasurable hu

theorem lowerScaleFirstOrderActionBackground_extensions_commute
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hHi : BackgroundFirstOrderActionThirdToSecondOrderCorePair (I := I) (M := M)
      g g hρ.le hδ0 hδ_le hreal)
    (hLo : BackgroundFirstOrderActionCorePair (I := I) (M := M)
      g g hρ.le hδ0 hδ_le hreal)
    (v : metricThirdOrderSobolev (I := I) (M := M) g) :
    (tensorHsInclusion (I := I) (M := M) (g := g)
        (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
        (lowerScaleFirstOrderActionThirdToSecondOrderBackground (I := I) (M := M)
          g g hρ.le hδ0 hδ_le hreal v) =
      (lowerScaleFirstOrderActionSecondToFirstOrderBackground (I := I) (M := M)
          g g hρ.le hδ0 hδ_le hreal v).comp
        (tensorHsInclusion (I := I) (M := M) (g := g)
          (r := 0) (s := 2) (show (2 : ℝ) ≤ 3 by norm_num)) := by
  obtain ⟨_, _, _, _, hcoreComm⟩ :=
    radialFirstOrderAction_pairing_bound (I := I) (M := M) hDim g hρ hδ0 hδ_le hreal
  let J12 :=
    tensorHsInclusion (I := I) (M := M) (g := g)
      (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)
  let J23 :=
    tensorHsInclusion (I := I) (M := M) (g := g)
      (r := 0) (s := 2) (show (2 : ℝ) ≤ 3 by norm_num)
  let AHi := lowerScaleFirstOrderActionThirdToSecondOrderBackground (I := I) (M := M)
    g g hρ.le hδ0 hδ_le hreal
  let ALo := lowerScaleFirstOrderActionSecondToFirstOrderBackground (I := I) (M := M)
    g g hρ.le hδ0 hδ_le hreal
  have hleft : Continuous (fun w => J12.comp (AHi w)) :=
    (ContinuousLinearMap.compL ℝ
      (TensorHs (I := I) (M := M) g 0 2 (3 : ℝ))
      (TensorHs (I := I) (M := M) g 0 2 (2 : ℝ))
      (TensorHs (I := I) (M := M) g 0 2 (1 : ℝ))).continuous₂.comp
        (continuous_const.prodMk
          (lowerScaleFirstOrderActionThirdToSecondOrderBackground_continuous (I := I) (M := M) g g hHi))
  have hright : Continuous (fun w => (ALo w).comp J23) :=
    (ContinuousLinearMap.compL ℝ
      (TensorHs (I := I) (M := M) g 0 2 (3 : ℝ))
      (TensorHs (I := I) (M := M) g 0 2 (2 : ℝ))
      (TensorHs (I := I) (M := M) g 0 2 (1 : ℝ))).continuous₂.comp
        ((lowerScaleFirstOrderActionSecondToFirstOrderBackground_continuous (I := I) (M := M) g g hLo).prodMk
          continuous_const)
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  refine hdense.induction_on v (isClosed_eq hleft hright) ?_
  intro T
  rw [lowerScaleFirstOrderActionThirdToSecondOrderBackground_core (I := I) (M := M) g g hHi T,
    lowerScaleFirstOrderActionSecondToFirstOrderBackground_core (I := I) (M := M) g g hLo T]
  simpa only [lowCoreActionCoefficientsBackground, lowCoreActionCoefficients] using (hcoreComm T).2.2

theorem lowerScaleFirstOrderActionBackground_extensions_commute_background
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hHi : BackgroundFirstOrderActionThirdToSecondOrderCorePair (I := I) (M := M)
      g gB hρ.le hδ0 hδ_le hreal)
    (hLo : BackgroundFirstOrderActionCorePair (I := I) (M := M)
      g gB hρ.le hδ0 hδ_le hreal)
    (v : metricThirdOrderSobolev (I := I) (M := M) g) :
    (tensorHsInclusion (I := I) (M := M) (g := g)
        (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
        (lowerScaleFirstOrderActionThirdToSecondOrderBackground (I := I) (M := M)
          g gB hρ.le hδ0 hδ_le hreal v) =
      (lowerScaleFirstOrderActionSecondToFirstOrderBackground (I := I) (M := M)
          g gB hρ.le hδ0 hδ_le hreal v).comp
        (tensorHsInclusion (I := I) (M := M) (g := g)
          (r := 0) (s := 2) (show (2 : ℝ) ≤ 3 by norm_num)) := by
  let J12 :=
    tensorHsInclusion (I := I) (M := M) (g := g)
      (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)
  let J23 :=
    tensorHsInclusion (I := I) (M := M) (g := g)
      (r := 0) (s := 2) (show (2 : ℝ) ≤ 3 by norm_num)
  let AHi := lowerScaleFirstOrderActionThirdToSecondOrderBackground (I := I) (M := M)
    g gB hρ.le hδ0 hδ_le hreal
  let ALo := lowerScaleFirstOrderActionSecondToFirstOrderBackground (I := I) (M := M)
    g gB hρ.le hδ0 hδ_le hreal
  have hleft : Continuous (fun w => J12.comp (AHi w)) :=
    (ContinuousLinearMap.compL ℝ
      (TensorHs (I := I) (M := M) g 0 2 (3 : ℝ))
      (TensorHs (I := I) (M := M) g 0 2 (2 : ℝ))
      (TensorHs (I := I) (M := M) g 0 2 (1 : ℝ))).continuous₂.comp
        (continuous_const.prodMk
          (lowerScaleFirstOrderActionThirdToSecondOrderBackground_continuous (I := I) (M := M) g gB hHi))
  have hright : Continuous (fun w => (ALo w).comp J23) :=
    (ContinuousLinearMap.compL ℝ
      (TensorHs (I := I) (M := M) g 0 2 (3 : ℝ))
      (TensorHs (I := I) (M := M) g 0 2 (2 : ℝ))
      (TensorHs (I := I) (M := M) g 0 2 (1 : ℝ))).continuous₂.comp
        ((lowerScaleFirstOrderActionSecondToFirstOrderBackground_continuous (I := I) (M := M) g gB hLo).prodMk
          continuous_const)
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  refine hdense.induction_on v (isClosed_eq hleft hright) ?_
  intro T
  rw [lowerScaleFirstOrderActionThirdToSecondOrderBackground_core (I := I) (M := M) g gB hHi T,
    lowerScaleFirstOrderActionSecondToFirstOrderBackground_core (I := I) (M := M) g gB hLo T]
  exact first_order_action_sobolev_extensions_commute (I := I) (M := M) hDim g
    (lowCoreActionCoefficientsBackground (I := I) (M := M) g gB hρ.le hδ0 hδ_le hreal T)

noncomputable def lowerScaleSecondOrderActionFourthToSecondOrderBackground
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    metricH2 (I := I) (M := M) g → lowerScaleSecondOrderActionFourthToSecondOrderSpace (I := I) (M := M) g :=
  Dense.extend
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
    (lowBackgroundCore (I := I) (M := M) g gB hρ hδ0 hδ_le hreal
      fun A => A.secondOrderActionFourthToSecondOrder (I := I) (M := M))

noncomputable def lowerScaleSecondOrderActionThirdToFirstOrderBackground
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    metricH2 (I := I) (M := M) g → lowA2LoBackgroundOp (I := I) (M := M) g :=
  Dense.extend
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
    (lowBackgroundCore (I := I) (M := M) g gB hρ hδ0 hδ_le hreal
      fun A => A.secondOrderActionThirdToFirstOrder (I := I) (M := M))

private theorem lowBackgroundCore_pair
    {Y : Type*} [NormedAddCommGroup Y]
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ C : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (proj : LowerScaleActionCoefficients g → Y)
    (hpair : ∀ T U : SmoothCcTensor g 0 2,
      ‖proj (lowCoreActionCoefficientsBackground (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal T) -
        proj (lowCoreActionCoefficientsBackground (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal U)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖)
    (x y : LowerScaleTimeInternal.LowCore (I := I) (M := M) g) :
    ‖lowBackgroundCore (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal proj x -
        lowBackgroundCore (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal proj y‖ ≤
      C * ‖(x : metricH2 (I := I) (M := M) g) -
        (y : metricH2 (I := I) (M := M) g)‖ := by
  obtain ⟨T, hT⟩ := x.property
  obtain ⟨U, hU⟩ := y.property
  have hx : x =
      ⟨ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T, ⟨T, rfl⟩⟩ := by
    apply Subtype.ext
    exact hT.symm
  have hy : y =
      ⟨ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) U, ⟨U, rfl⟩⟩ := by
    apply Subtype.ext
    exact hU.symm
  rw [hx, hy, lowBackgroundCore_value, lowBackgroundCore_value, ← map_sub]
  simpa only [ccToHsLin_apply] using hpair T U

private theorem lowBackground_ext_lip
    {Y : Type*} [NormedAddCommGroup Y] [CompleteSpace Y]
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ C : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (proj : LowerScaleActionCoefficients g → Y) (hC : 0 ≤ C)
    (hpair : ∀ T U : SmoothCcTensor g 0 2,
      ‖proj (lowCoreActionCoefficientsBackground (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal T) -
        proj (lowCoreActionCoefficientsBackground (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal U)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖) :
    LipschitzWith ⟨C, hC⟩
      (Dense.extend
        (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
        (lowBackgroundCore (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal proj)) := by
  refine DifferentialGeometry.Analysis.Parabolic.QuasiLinear.dense_lipschitz
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)) _ ?_
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hxy := lowBackgroundCore_pair (I := I) (M := M)
    g gB hρ hδ0 hδ_le hreal proj hpair x y
  have hcoe : ((⟨C, hC⟩ : NNReal) : ℝ) = C := rfl
  calc
    dist (lowBackgroundCore (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal proj x)
        (lowBackgroundCore (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal proj y) ≤
      C * dist x y := by
        simpa only [dist_eq_norm, Subtype.dist_eq] using hxy
    _ = ((⟨C, hC⟩ : NNReal) : ℝ) * dist x y := by rw [hcoe]

private theorem lowBackground_ext_core
    {Y : Type*} [NormedAddCommGroup Y]
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ C : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (proj : LowerScaleActionCoefficients g → Y) (hC : 0 ≤ C)
    (hpair : ∀ T U : SmoothCcTensor g 0 2,
      ‖proj (lowCoreActionCoefficientsBackground (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal T) -
        proj (lowCoreActionCoefficientsBackground (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal U)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖)
    (T : SmoothCcTensor g 0 2) :
    Dense.extend
        (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
        (lowBackgroundCore (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal proj)
        (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T) =
      proj (lowCoreActionCoefficientsBackground (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T) := by
  let D : Set (metricH2 (I := I) (M := M) g) :=
    Set.range (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ))
  let F : D → Y := lowBackgroundCore (I := I) (M := M)
    g gB hρ hδ0 hδ_le hreal proj
  have hF : LipschitzWith ⟨C, hC⟩ F := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hxy := lowBackgroundCore_pair (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal proj hpair x y
    have hcoe : ((⟨C, hC⟩ : NNReal) : ℝ) = C := rfl
    calc
      dist (F x) (F y) ≤ C * dist x y := by
        simpa only [dist_eq_norm, Subtype.dist_eq, F] using hxy
      _ = ((⟨C, hC⟩ : NNReal) : ℝ) * dist x y := by rw [hcoe]
  let x : D :=
    ⟨ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T, ⟨T, rfl⟩⟩
  have hext :=
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)).extend_eq
      hF.continuous x
  change Dense.extend
      (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
      F (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T) = _
  calc
    Dense.extend
        (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
        F (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T) = F x := hext
    _ = _ := lowBackgroundCore_value (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal proj T

theorem radialSecondOrderActionBackground_lipschitz
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M)
    {ρ₀ δ : ℝ} (hρ₀ : 0 < ρ₀) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ₀ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    ∃ (ρ : ℝ) (C : NNReal) (_hρ : 0 < ρ) (hρ_le : ρ ≤ ρ₀),
      ∀ {r : ℝ} (hr0 : 0 ≤ r) (hr_le : r ≤ ρ),
        let hreal' : ∀ S : SmoothCcTensor g 0 2,
            ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ r →
              gFibreOpBound (I := I) (M := M) g
                (ccTensorBilinSymm (I := I) g S) δ :=
          fun S hS => hreal S (hS.trans (hr_le.trans hρ_le))
        LipschitzWith C
            (lowerScaleSecondOrderActionFourthToSecondOrderBackground (I := I) (M := M)
              g gB hr0 hδ0 hδ_le hreal') ∧
          LipschitzWith C
            (lowerScaleSecondOrderActionThirdToFirstOrderBackground (I := I) (M := M)
              g gB hr0 hδ0 hδ_le hreal') ∧
          (∀ T : SmoothCcTensor g 0 2,
            lowerScaleSecondOrderActionFourthToSecondOrderBackground (I := I) (M := M)
                g gB hr0 hδ0 hδ_le hreal'
                (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T) =
              (lowCoreActionCoefficientsBackground (I := I) (M := M)
                g gB hr0 hδ0 hδ_le hreal' T).secondOrderActionFourthToSecondOrder (I := I) (M := M)) ∧
          (∀ T : SmoothCcTensor g 0 2,
            lowerScaleSecondOrderActionThirdToFirstOrderBackground (I := I) (M := M)
                g gB hr0 hδ0 hδ_le hreal'
                (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T) =
              (lowCoreActionCoefficientsBackground (I := I) (M := M)
                g gB hr0 hδ0 hδ_le hreal' T).secondOrderActionThirdToFirstOrder (I := I) (M := M)) ∧
          ∀ v : metricH2 (I := I) (M := M) g,
            (tensorHsInclusion (I := I) (M := M) (g := g)
                (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
                (lowerScaleSecondOrderActionFourthToSecondOrderBackground (I := I) (M := M)
                  g gB hr0 hδ0 hδ_le hreal' v) =
              (lowerScaleSecondOrderActionThirdToFirstOrderBackground (I := I) (M := M)
                  g gB hr0 hδ0 hδ_le hreal' v).comp
                (tensorHsInclusion (I := I) (M := M) (g := g)
                  (r := 0) (s := 2)
                  (show (3 : ℝ) ≤ 4 by norm_num)) := by
  obtain ⟨ρp, C, hρp, hC, hpair⟩ :=
    secondOrderAction_pairing_lipschitz_bound (I := I) (M := M) hDim g gB
  let ρ : ℝ := min ρ₀ ρp
  have hρ : 0 < ρ := lt_min hρ₀ hρp
  have hρ_le : ρ ≤ ρ₀ := min_le_left _ _
  have hρp_le : ρ ≤ ρp := min_le_right _ _
  refine ⟨ρ, ⟨C, hC⟩, hρ, hρ_le, ?_⟩
  intro r hr0 hr_le
  dsimp only
  let hreal' : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ r →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ :=
    fun S hS => hreal S (hS.trans (hr_le.trans hρ_le))
  have hδlt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  have hZδ :
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g
          (0 : SmoothCcTensor g 0 2)) δ :=
    zero_fibre_bound (I := I) (M := M) g hδ0
  have hBoth : ∀ T U : SmoothCcTensor g 0 2,
      ‖(lowCoreActionCoefficientsBackground (I := I) (M := M)
          g gB hr0 hδ0 hδ_le hreal' T).secondOrderActionFourthToSecondOrder (I := I) (M := M) -
        (lowCoreActionCoefficientsBackground (I := I) (M := M)
          g gB hr0 hδ0 hδ_le hreal' U).secondOrderActionFourthToSecondOrder (I := I) (M := M)‖ ≤
          C * ‖ccTensorToHs (I := I) (M := M)
            g 2 (2 : ℝ) (T - U)‖ ∧
      ‖(lowCoreActionCoefficientsBackground (I := I) (M := M)
          g gB hr0 hδ0 hδ_le hreal' T).secondOrderActionThirdToFirstOrder (I := I) (M := M) -
        (lowCoreActionCoefficientsBackground (I := I) (M := M)
          g gB hr0 hδ0 hδ_le hreal' U).secondOrderActionThirdToFirstOrder (I := I) (M := M)‖ ≤
          C * ‖ccTensorToHs (I := I) (M := M)
            g 2 (2 : ℝ) (T - U)‖ := by
    intro T U
    let S := lowRadial (I := I) (M := M) g r T
    let V := lowRadial (I := I) (M := M) g r U
    have hSρ :
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ r :=
      lowRadial_norm (I := I) (M := M) g hr0 T
    have hVρ :
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) V‖ ≤ r :=
      lowRadial_norm (I := I) (M := M) g hr0 U
    have hSδ :
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ := hreal' S hSρ
    have hVδ :
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g V) δ := hreal' V hVρ
    obtain ⟨hHi, hLo⟩ :=
      hpair S V hδlt hSδ hVδ hZδ
        (hSρ.trans (hr_le.trans hρp_le))
        (hVρ.trans (hr_le.trans hρp_le))
    have hSV :
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (S - V)‖ ≤
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ := by
      have hrad := lowRadial_lip (I := I) (M := M) g hr0 T U
      have hmapSV :
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (S - V) =
            ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S -
              ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) V := by
        simpa only [ccToHsLin_apply] using
          map_sub (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) S V
      have hmapTU :
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U) =
            ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
              ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U := by
        simpa only [ccToHsLin_apply] using
          map_sub (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) T U
      rw [hmapSV, hmapTU]
      simpa only [S, V] using hrad
    have hbound :
        C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (S - V)‖ ≤
          C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ :=
      mul_le_mul_of_nonneg_left hSV hC
    refine ⟨?_, ?_⟩
    · have hHi' :
          ‖(lowCoreActionCoefficientsBackground (I := I) (M := M)
              g gB hr0 hδ0 hδ_le hreal' T).secondOrderActionFourthToSecondOrder (I := I) (M := M) -
            (lowCoreActionCoefficientsBackground (I := I) (M := M)
              g gB hr0 hδ0 hδ_le hreal' U).secondOrderActionFourthToSecondOrder (I := I) (M := M)‖ ≤
            C * ‖ccTensorToHs (I := I) (M := M)
              g 2 (2 : ℝ) (S - V)‖ := by
        simpa only [lowCoreActionCoefficientsBackground, S, V] using hHi
      exact hHi'.trans hbound
    · have hLo' :
          ‖(lowCoreActionCoefficientsBackground (I := I) (M := M)
              g gB hr0 hδ0 hδ_le hreal' T).secondOrderActionThirdToFirstOrder (I := I) (M := M) -
            (lowCoreActionCoefficientsBackground (I := I) (M := M)
              g gB hr0 hδ0 hδ_le hreal' U).secondOrderActionThirdToFirstOrder (I := I) (M := M)‖ ≤
            C * ‖ccTensorToHs (I := I) (M := M)
              g 2 (2 : ℝ) (S - V)‖ := by
        simpa only [lowCoreActionCoefficientsBackground, S, V] using hLo
      exact hLo'.trans hbound
  have hHiPair : ∀ T U : SmoothCcTensor g 0 2,
      ‖(lowCoreActionCoefficientsBackground (I := I) (M := M)
          g gB hr0 hδ0 hδ_le hreal' T).secondOrderActionFourthToSecondOrder (I := I) (M := M) -
        (lowCoreActionCoefficientsBackground (I := I) (M := M)
          g gB hr0 hδ0 hδ_le hreal' U).secondOrderActionFourthToSecondOrder (I := I) (M := M)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M)
          g 2 (2 : ℝ) (T - U)‖ := fun T U => (hBoth T U).1
  have hLoPair : ∀ T U : SmoothCcTensor g 0 2,
      ‖(lowCoreActionCoefficientsBackground (I := I) (M := M)
          g gB hr0 hδ0 hδ_le hreal' T).secondOrderActionThirdToFirstOrder (I := I) (M := M) -
        (lowCoreActionCoefficientsBackground (I := I) (M := M)
          g gB hr0 hδ0 hδ_le hreal' U).secondOrderActionThirdToFirstOrder (I := I) (M := M)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M)
          g 2 (2 : ℝ) (T - U)‖ := fun T U => (hBoth T U).2
  have hHiLip : LipschitzWith ⟨C, hC⟩
      (lowerScaleSecondOrderActionFourthToSecondOrderBackground (I := I) (M := M)
        g gB hr0 hδ0 hδ_le hreal') := by
    simpa only [lowerScaleSecondOrderActionFourthToSecondOrderBackground] using
      lowBackground_ext_lip (I := I) (M := M)
        g gB hr0 hδ0 hδ_le hreal'
          (fun A => A.secondOrderActionFourthToSecondOrder (I := I) (M := M)) hC hHiPair
  have hLoLip : LipschitzWith ⟨C, hC⟩
      (lowerScaleSecondOrderActionThirdToFirstOrderBackground (I := I) (M := M)
        g gB hr0 hδ0 hδ_le hreal') := by
    simpa only [lowerScaleSecondOrderActionThirdToFirstOrderBackground] using
      lowBackground_ext_lip (I := I) (M := M)
        g gB hr0 hδ0 hδ_le hreal'
          (fun A => A.secondOrderActionThirdToFirstOrder (I := I) (M := M)) hC hLoPair
  have hHiCore : ∀ T : SmoothCcTensor g 0 2,
      lowerScaleSecondOrderActionFourthToSecondOrderBackground (I := I) (M := M)
          g gB hr0 hδ0 hδ_le hreal'
          (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T) =
        (lowCoreActionCoefficientsBackground (I := I) (M := M)
          g gB hr0 hδ0 hδ_le hreal' T).secondOrderActionFourthToSecondOrder (I := I) (M := M) := by
    intro T
    simpa only [lowerScaleSecondOrderActionFourthToSecondOrderBackground] using
      lowBackground_ext_core (I := I) (M := M)
        g gB hr0 hδ0 hδ_le hreal'
          (fun A => A.secondOrderActionFourthToSecondOrder (I := I) (M := M)) hC hHiPair T
  have hLoCore : ∀ T : SmoothCcTensor g 0 2,
      lowerScaleSecondOrderActionThirdToFirstOrderBackground (I := I) (M := M)
          g gB hr0 hδ0 hδ_le hreal'
          (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T) =
        (lowCoreActionCoefficientsBackground (I := I) (M := M)
          g gB hr0 hδ0 hδ_le hreal' T).secondOrderActionThirdToFirstOrder (I := I) (M := M) := by
    intro T
    simpa only [lowerScaleSecondOrderActionThirdToFirstOrderBackground] using
      lowBackground_ext_core (I := I) (M := M)
        g gB hr0 hδ0 hδ_le hreal'
          (fun A => A.secondOrderActionThirdToFirstOrder (I := I) (M := M)) hC hLoPair T
  refine ⟨hHiLip, hLoLip, hHiCore, hLoCore, ?_⟩
  let J12 :=
    tensorHsInclusion (I := I) (M := M) (g := g)
      (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)
  let J34 :=
    tensorHsInclusion (I := I) (M := M) (g := g)
      (r := 0) (s := 2) (show (3 : ℝ) ≤ 4 by norm_num)
  let AHi := lowerScaleSecondOrderActionFourthToSecondOrderBackground (I := I) (M := M)
    g gB hr0 hδ0 hδ_le hreal'
  let ALo := lowerScaleSecondOrderActionThirdToFirstOrderBackground (I := I) (M := M)
    g gB hr0 hδ0 hδ_le hreal'
  have hleft : Continuous (fun v => J12.comp (AHi v)) :=
    (ContinuousLinearMap.compL ℝ
      (TensorHs (I := I) (M := M) g 0 2 (4 : ℝ))
      (TensorHs (I := I) (M := M) g 0 2 (2 : ℝ))
      (TensorHs (I := I) (M := M) g 0 2 (1 : ℝ))).continuous₂.comp
        (continuous_const.prodMk hHiLip.continuous)
  have hright : Continuous (fun v => (ALo v).comp J34) :=
    (ContinuousLinearMap.compL ℝ
      (TensorHs (I := I) (M := M) g 0 2 (4 : ℝ))
      (TensorHs (I := I) (M := M) g 0 2 (3 : ℝ))
      (TensorHs (I := I) (M := M) g 0 2 (1 : ℝ))).continuous₂.comp
        (hLoLip.continuous.prodMk continuous_const)
  intro v
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  refine hdense.induction_on v (isClosed_eq hleft hright) ?_
  intro T
  rw [hHiCore T, hLoCore T]
  exact secondOrderAction_sobolev_extensions_commute (I := I) (M := M) hDim g
    (lowCoreActionCoefficientsBackground (I := I) (M := M)
      g gB hr0 hδ0 hδ_le hreal' T)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end

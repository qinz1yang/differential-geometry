import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.NonautonomousL2Cross
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.TimeFirstOrder
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PrincipalOperatorPairing
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.TimeSecondOrder
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.ExponentCongr
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.PrincipalTime

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private abbrev metricH1 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)

private abbrev metricH2 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

private abbrev metricH4 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (4 : ℝ)

private abbrev solH3 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 2)

private abbrev opH3 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (3 : ℝ)

private abbrev a1Op (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
    tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

private abbrev a2Op (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (4 : ℝ) →L[ℝ]
    tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

private abbrev a1LoOp (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) →L[ℝ]
    tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)

private abbrev a2LoOp (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
    tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)

private abbrev pLoOp (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
    tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)

private abbrev solToOpH3 (g : SmoothRiemannianMetric I M) :
    solH3 (I := I) (M := M) g ≃ₗᵢ[ℝ] opH3 (I := I) (M := M) g :=
  tensorHsCongr (I := I) (M := M) g 0 2
    (show (1 : ℝ) + 2 = (3 : ℝ) by norm_num)

def lowRegularityFirstOrderActionTime
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    {T : ℝ} (hT : 0 < T)
    (f : timeL2 (metricH1 (I := I) (M := M) g) T) :
    ℝ → (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) :=
  fun t => lowerScaleFirstOrderActionThirdToSecondOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal
    (solToOpH3 (I := I) (M := M) g
      (maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT
        (0 : solH3 (I := I) (M := M) g) f t))

theorem lowRegularityFirstOrderActionTime_memLp
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hcont : Continuous
      (lowerScaleFirstOrderActionThirdToSecondOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal))
    {Φ : ℝ} (hΦ : 0 ≤ Φ)
    (hlin : ∀ v : opH3 (I := I) (M := M) g,
      ‖show a1Op (I := I) (M := M) g from
        lowerScaleFirstOrderActionThirdToSecondOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal v‖ ≤ Φ * (1 + ‖v‖))
    {T : ℝ} (hT : 0 < T)
    (f : timeL2 (metricH1 (I := I) (M := M) g) T) :
    AEStronglyMeasurable
        (lowRegularityFirstOrderActionTime (I := I) (M := M) g hρ hδ0 hδ_le hreal hT f)
        (timeMeasure T) ∧
      (∀ᵐ t ∂timeMeasure T,
        ‖lowRegularityFirstOrderActionTime (I := I) (M := M) g hρ hδ0 hδ_le hreal hT f t‖ ≤
          Φ * (1 + ‖maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT
            (0 : solH3 (I := I) (M := M) g) f t‖)) ∧
      MemLp (lowRegularityFirstOrderActionTime (I := I) (M := M) g hρ hδ0 hδ_le hreal hT f) 2
        (timeMeasure T) := by
  have hufield : AEStronglyMeasurable
      (fun t => maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT
        (0 : solH3 (I := I) (M := M) g) f t) (timeMeasure T) :=
    Lp.aestronglyMeasurable _
  have hiso : AEStronglyMeasurable
      (fun t => solToOpH3 (I := I) (M := M) g
        (maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT
          (0 : solH3 (I := I) (M := M) g) f t)) (timeMeasure T) :=
    (LinearIsometry.toContinuousLinearMap
      (solToOpH3 (I := I) (M := M) g).toLinearIsometry).continuous
        |>.comp_aestronglyMeasurable hufield
  have hmeas : AEStronglyMeasurable
      (lowRegularityFirstOrderActionTime (I := I) (M := M) g hρ hδ0 hδ_le hreal hT f)
      (timeMeasure T) :=
    hcont.comp_aestronglyMeasurable hiso
  have hbound : ∀ᵐ t ∂timeMeasure T,
      ‖lowRegularityFirstOrderActionTime (I := I) (M := M) g hρ hδ0 hδ_le hreal hT f t‖ ≤
        Φ * (1 + ‖maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT
          (0 : solH3 (I := I) (M := M) g) f t‖) := by
    refine Eventually.of_forall fun t => ?_
    have h := hlin (solToOpH3 (I := I) (M := M) g
      (maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT
        (0 : solH3 (I := I) (M := M) g) f t))
    rwa [LinearIsometryEquiv.norm_map] at h
  have haffine : ∀ᵐ t ∂timeMeasure T,
      ‖lowRegularityFirstOrderActionTime (I := I) (M := M) g hρ hδ0 hδ_le hreal hT f t‖ ≤
        Φ + Φ * ‖maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT
          (0 : solH3 (I := I) (M := M) g) f t‖ := by
    filter_upwards [hbound] with t ht
    calc
      _ ≤ Φ * (1 + ‖maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT
            (0 : solH3 (I := I) (M := M) g) f t‖) := ht
      _ = Φ + Φ * ‖maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT
            (0 : solH3 (I := I) (M := M) g) f t‖ := by ring
  obtain ⟨hmem, -⟩ :=
    memLp_clm_affine (T := T)
      (maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT
        (0 : solH3 (I := I) (M := M) g) f)
      (lowRegularityFirstOrderActionTime (I := I) (M := M) g hρ hδ0 hδ_le hreal hT f)
      hmeas hΦ hΦ haffine
  exact ⟨hmeas, hbound, hmem⟩

private theorem coreLip
    {X Y : Type*} [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]
    {D : Set X} {C : ℝ} (hC : 0 ≤ C) (F : D → Y)
    (hF : ∀ x y : D, ‖F x - F y‖ ≤ C * ‖(x : X) - (y : X)‖) :
    LipschitzWith ⟨C, hC⟩ F := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hcoe : ((⟨C, hC⟩ : NNReal) : ℝ) = C := rfl
  calc
    dist (F x) (F y) = ‖F x - F y‖ := dist_eq_norm _ _
    _ ≤ C * ‖(x : X) - (y : X)‖ := hF x y
    _ = ((⟨C, hC⟩ : NNReal) : ℝ) * ‖(x : X) - (y : X)‖ :=
      congrArg (fun a : ℝ => a * ‖(x : X) - (y : X)‖) hcoe.symm
    _ = ((⟨C, hC⟩ : NNReal) : ℝ) * dist x y := by
      rw [Subtype.dist_eq, dist_eq_norm]

private theorem highCorePair {Y : Type*} [SeminormedAddCommGroup Y]
    (g : SmoothRiemannianMetric I M) {C : ℝ}
    (F : LowerScaleTimeInternal.HighCore (I := I) (M := M) g → Y)
    (c : SmoothCcTensor g 0 2 → Y)
    (hval : ∀ T : SmoothCcTensor g 0 2,
      F ⟨ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T, ⟨T, rfl⟩⟩ = c T)
    (hpair : ∀ T U : SmoothCcTensor g 0 2,
      ‖c T - c U‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) (T - U)‖)
    (x y : LowerScaleTimeInternal.HighCore (I := I) (M := M) g) :
    ‖F x - F y‖ ≤
      C * ‖(x : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ)) -
        (y : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ))‖ := by
  obtain ⟨T, hT⟩ := x.property
  obtain ⟨U, hU⟩ := y.property
  have hx : x = ⟨ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T, ⟨T, rfl⟩⟩ :=
    Subtype.ext hT.symm
  have hy : y = ⟨ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U, ⟨U, rfl⟩⟩ :=
    Subtype.ext hU.symm
  rw [hx, hy, hval, hval, ← map_sub]
  simpa only [ccToHsLin_apply] using hpair T U

theorem lowerScaleFirstOrderAction_lipschitz
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {ρ δ C : ℝ}
    (hρ : 0 < ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hC : 0 ≤ C)
    (hHiPair : ∀ T U : SmoothCcTensor g 0 2,
      ‖(lowCoreActionCoefficients (I := I) (M := M) g hρ.le hδ0 hδ_le hreal T).firstOrderActionThirdToSecondOrder
            (I := I) (M := M) -
          (lowCoreActionCoefficients (I := I) (M := M) g hρ.le hδ0 hδ_le hreal U).firstOrderActionThirdToSecondOrder
            (I := I) (M := M)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) (T - U)‖)
    (hLoPair : ∀ T U : SmoothCcTensor g 0 2,
      ‖(lowCoreActionCoefficients (I := I) (M := M) g hρ.le hδ0 hδ_le hreal T).firstOrderActionSecondToFirstOrder
            (I := I) (M := M) -
          (lowCoreActionCoefficients (I := I) (M := M) g hρ.le hδ0 hδ_le hreal U).firstOrderActionSecondToFirstOrder
            (I := I) (M := M)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) (T - U)‖) :
    LipschitzWith ⟨C, hC⟩
        (lowerScaleFirstOrderActionThirdToSecondOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal) ∧
      LipschitzWith ⟨C, hC⟩
        (lowerScaleFirstOrderActionSecondToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal) ∧
      (∀ T : SmoothCcTensor g 0 2,
        lowerScaleFirstOrderActionThirdToSecondOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal
            (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T) =
          (lowCoreActionCoefficients (I := I) (M := M) g hρ.le hδ0 hδ_le hreal T).firstOrderActionThirdToSecondOrder
            (I := I) (M := M)) ∧
      (∀ T : SmoothCcTensor g 0 2,
        lowerScaleFirstOrderActionSecondToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal
            (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T) =
          (lowCoreActionCoefficients (I := I) (M := M) g hρ.le hδ0 hδ_le hreal T).firstOrderActionSecondToFirstOrder
            (I := I) (M := M)) ∧
      (∀ v : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ),
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (1 : ℝ) ≤ 2 by norm_num)).comp
              (lowerScaleFirstOrderActionThirdToSecondOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal v) =
          (lowerScaleFirstOrderActionSecondToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal v).comp
            (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              (show (2 : ℝ) ≤ 3 by norm_num))) := by
  have hdense : DenseRange (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  let FHi : LowerScaleTimeInternal.HighCore (I := I) (M := M) g →
      a1Op (I := I) (M := M) g :=
    LowerScaleTimeInternal.firstOrderActionThirdToSecondOrderCore (I := I) (M := M) g hρ.le hδ0 hδ_le hreal
  let FLo : LowerScaleTimeInternal.HighCore (I := I) (M := M) g →
      a1LoOp (I := I) (M := M) g :=
    LowerScaleTimeInternal.firstOrderActionSecondToFirstOrderCore (I := I) (M := M) g hρ.le hδ0 hδ_le hreal
  have hFHi : LipschitzWith ⟨C, hC⟩ FHi :=
    coreLip hC FHi
      (highCorePair (I := I) (M := M) g FHi _
        (LowerScaleTimeInternal.firstOrderActionThirdToSecondOrderCore_value (I := I) (M := M)
          g hρ.le hδ0 hδ_le hreal) hHiPair)
  have hFLo : LipschitzWith ⟨C, hC⟩ FLo :=
    coreLip hC FLo
      (highCorePair (I := I) (M := M) g FLo _
        (LowerScaleTimeInternal.firstOrderActionSecondToFirstOrderCore_value (I := I) (M := M)
          g hρ.le hδ0 hδ_le hreal) hLoPair)
  have hlipHi : LipschitzWith ⟨C, hC⟩
      (lowerScaleFirstOrderActionThirdToSecondOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal) :=
    dense_lipschitz (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
      FHi hFHi
  have hlipLo : LipschitzWith ⟨C, hC⟩
      (lowerScaleFirstOrderActionSecondToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal) :=
    dense_lipschitz (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
      FLo hFLo
  have hcoreHi : ∀ T : SmoothCcTensor g 0 2,
      lowerScaleFirstOrderActionThirdToSecondOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal
          (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T) =
        (lowCoreActionCoefficients (I := I) (M := M) g hρ.le hδ0 hδ_le hreal T).firstOrderActionThirdToSecondOrder
          (I := I) (M := M) := by
    intro T
    have hext :=
      (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)).extend_eq
        hFHi.continuous
        (⟨ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T, ⟨T, rfl⟩⟩ :
          LowerScaleTimeInternal.HighCore (I := I) (M := M) g)
    exact hext.trans
      (LowerScaleTimeInternal.firstOrderActionThirdToSecondOrderCore_value (I := I) (M := M)
        g hρ.le hδ0 hδ_le hreal T)
  have hcoreLo : ∀ T : SmoothCcTensor g 0 2,
      lowerScaleFirstOrderActionSecondToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal
          (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T) =
        (lowCoreActionCoefficients (I := I) (M := M) g hρ.le hδ0 hδ_le hreal T).firstOrderActionSecondToFirstOrder
          (I := I) (M := M) := by
    intro T
    have hext :=
      (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)).extend_eq
        hFLo.continuous
        (⟨ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T, ⟨T, rfl⟩⟩ :
          LowerScaleTimeInternal.HighCore (I := I) (M := M) g)
    exact hext.trans
      (LowerScaleTimeInternal.firstOrderActionSecondToFirstOrderCore_value (I := I) (M := M)
        g hρ.le hδ0 hδ_le hreal T)
  refine ⟨hlipHi, hlipLo, hcoreHi, hcoreLo, ?_⟩
  obtain ⟨CP, K, hCP, hK, hpair⟩ :=
    radialFirstOrderAction_pairing_bound (I := I) (M := M) hDim g hρ hδ0 hδ_le hreal
  have hleft : Continuous fun v : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) =>
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ 2 by norm_num)).comp
        (lowerScaleFirstOrderActionThirdToSecondOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal v) :=
    (ContinuousLinearMap.compL ℝ
      (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ))
      (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ))
      (tensorHs (I := I) (M := M) g 0 2 (1 : ℝ))).continuous₂.comp
        (continuous_const.prodMk hlipHi.continuous)
  have hright : Continuous fun v : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) =>
      (lowerScaleFirstOrderActionSecondToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal v).comp
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ 3 by norm_num)) :=
    (ContinuousLinearMap.compL ℝ
      (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ))
      (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ))
      (tensorHs (I := I) (M := M) g 0 2 (1 : ℝ))).continuous₂.comp
        (hlipLo.continuous.prodMk continuous_const)
  intro v
  refine hdense.induction_on v (isClosed_eq hleft hright) ?_
  intro T
  rw [hcoreHi T, hcoreLo T]
  exact (hpair T).2.2

theorem lowerScaleFirstOrderAction_extensions_commute
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {ρ δ C : ℝ}
    (hρ : 0 < ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hC : 0 ≤ C)
    (hHiPair : ∀ T U : SmoothCcTensor g 0 2,
      ‖(lowCoreActionCoefficients (I := I) (M := M) g hρ.le hδ0 hδ_le hreal T).firstOrderActionThirdToSecondOrder
            (I := I) (M := M) -
          (lowCoreActionCoefficients (I := I) (M := M) g hρ.le hδ0 hδ_le hreal U).firstOrderActionThirdToSecondOrder
            (I := I) (M := M)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) (T - U)‖)
    (hLoPair : ∀ T U : SmoothCcTensor g 0 2,
      ‖(lowCoreActionCoefficients (I := I) (M := M) g hρ.le hδ0 hδ_le hreal T).firstOrderActionSecondToFirstOrder
            (I := I) (M := M) -
          (lowCoreActionCoefficients (I := I) (M := M) g hρ.le hδ0 hδ_le hreal U).firstOrderActionSecondToFirstOrder
            (I := I) (M := M)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) (T - U)‖)
    (v : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ)) :
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) ≤ 2 by norm_num)).comp
          (lowerScaleFirstOrderActionThirdToSecondOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal v) =
      (lowerScaleFirstOrderActionSecondToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal v).comp
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ 3 by norm_num)) :=
  (lowerScaleFirstOrderAction_lipschitz (I := I) (M := M) hDim g hρ hδ0 hδ_le hreal hC
    hHiPair hLoPair).2.2.2.2 v

def lowRegularityFirstOrderActionLowerScaleTime
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    {T : ℝ} (hT : 0 < T)
    (f : timeL2 (metricH1 (I := I) (M := M) g) T) :
    ℝ → (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)) :=
  fun t => lowerScaleFirstOrderActionSecondToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal
    (solToOpH3 (I := I) (M := M) g
      (maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT
        (0 : solH3 (I := I) (M := M) g) f t))

theorem lowRegularityFirstOrderActionTime_extensions_commute
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {ρ δ C : ℝ}
    (hρ : 0 < ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hC : 0 ≤ C)
    (hHiPair : ∀ T U : SmoothCcTensor g 0 2,
      ‖(lowCoreActionCoefficients (I := I) (M := M) g hρ.le hδ0 hδ_le hreal T).firstOrderActionThirdToSecondOrder
            (I := I) (M := M) -
          (lowCoreActionCoefficients (I := I) (M := M) g hρ.le hδ0 hδ_le hreal U).firstOrderActionThirdToSecondOrder
            (I := I) (M := M)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) (T - U)‖)
    (hLoPair : ∀ T U : SmoothCcTensor g 0 2,
      ‖(lowCoreActionCoefficients (I := I) (M := M) g hρ.le hδ0 hδ_le hreal T).firstOrderActionSecondToFirstOrder
            (I := I) (M := M) -
          (lowCoreActionCoefficients (I := I) (M := M) g hρ.le hδ0 hδ_le hreal U).firstOrderActionSecondToFirstOrder
            (I := I) (M := M)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) (T - U)‖)
    {T : ℝ} (hT : 0 < T)
    (f : timeL2 (metricH1 (I := I) (M := M) g) T) :
    ∀ t : ℝ,
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ 2 by norm_num)).comp
            (lowRegularityFirstOrderActionTime (I := I) (M := M)
              g hρ.le hδ0 hδ_le hreal hT f t) =
        (lowRegularityFirstOrderActionLowerScaleTime (I := I) (M := M)
            g hρ.le hδ0 hδ_le hreal hT f t).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ 3 by norm_num)) :=
  fun _ =>
    lowerScaleFirstOrderAction_extensions_commute (I := I) (M := M) hDim g hρ hδ0 hδ_le hreal hC
      hHiPair hLoPair _

theorem lowRegularityFirstOrderActionLowerScaleTime_memLp
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hcont : Continuous
      (lowerScaleFirstOrderActionSecondToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal))
    {Φ : ℝ} (hΦ : 0 ≤ Φ)
    (hlin : ∀ v : opH3 (I := I) (M := M) g,
      ‖show a1LoOp (I := I) (M := M) g from
        lowerScaleFirstOrderActionSecondToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal v‖ ≤ Φ * (1 + ‖v‖))
    {T : ℝ} (hT : 0 < T)
    (f : timeL2 (metricH1 (I := I) (M := M) g) T) :
    AEStronglyMeasurable
        (lowRegularityFirstOrderActionLowerScaleTime (I := I) (M := M) g hρ hδ0 hδ_le hreal hT f)
        (timeMeasure T) ∧
      MemLp (lowRegularityFirstOrderActionLowerScaleTime (I := I) (M := M) g hρ hδ0 hδ_le hreal hT f) 2
        (timeMeasure T) := by
  have hufield : AEStronglyMeasurable
      (fun t => maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT
        (0 : solH3 (I := I) (M := M) g) f t) (timeMeasure T) :=
    Lp.aestronglyMeasurable _
  have hiso : AEStronglyMeasurable
      (fun t => solToOpH3 (I := I) (M := M) g
        (maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT
          (0 : solH3 (I := I) (M := M) g) f t)) (timeMeasure T) :=
    (LinearIsometry.toContinuousLinearMap
      (solToOpH3 (I := I) (M := M) g).toLinearIsometry).continuous
        |>.comp_aestronglyMeasurable hufield
  have hmeas : AEStronglyMeasurable
      (lowRegularityFirstOrderActionLowerScaleTime (I := I) (M := M) g hρ hδ0 hδ_le hreal hT f)
      (timeMeasure T) :=
    hcont.comp_aestronglyMeasurable hiso
  have haffine : ∀ᵐ t ∂timeMeasure T,
      ‖lowRegularityFirstOrderActionLowerScaleTime (I := I) (M := M) g hρ hδ0 hδ_le hreal hT f t‖ ≤
        Φ + Φ * ‖maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT
          (0 : solH3 (I := I) (M := M) g) f t‖ := by
    refine Filter.Eventually.of_forall fun t => ?_
    have h := hlin (solToOpH3 (I := I) (M := M) g
      (maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT
        (0 : solH3 (I := I) (M := M) g) f t))
    rw [LinearIsometryEquiv.norm_map] at h
    calc
      _ ≤ Φ * (1 + ‖maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT
            (0 : solH3 (I := I) (M := M) g) f t‖) := h
      _ = Φ + Φ * ‖maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT
            (0 : solH3 (I := I) (M := M) g) f t‖ := by ring
  obtain ⟨hmem, -⟩ :=
    memLp_clm_affine (T := T)
      (maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT
        (0 : solH3 (I := I) (M := M) g) f)
      (lowRegularityFirstOrderActionLowerScaleTime (I := I) (M := M) g hρ hδ0 hδ_le hreal hT f)
      hmeas hΦ hΦ haffine
  exact ⟨hmeas, hmem⟩

def lowRegularitySecondOrderActionTotal
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    {T R : ℝ} (hT : 0 < T)
    (f : timeL2 (metricH1 (I := I) (M := M) g) T)
    (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂timeMeasure T,
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          (1 : ℝ) hT
          (0 : solH3 (I := I) (M := M) g) f t)‖ ≤ R) :
    ℝ → (tensorHs (I := I) (M := M) g 0 2 (4 : ℝ) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) :=
  fun t =>
    lowRegularityPrincipalSecondOrderActionTime (I := I) (M := M) g hT f hR hball t +
      lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal
        (lowRegularityStateL2 (I := I) (M := M) g hT f hR hball t)

private theorem a2Hi_total_le
    (g : SmoothRiemannianMetric I M) {ρ δ c : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hcont : Continuous
      (lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal))
    (hcore : ∀ S : SmoothCcTensor g 0 2,
      lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal
          (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) S) =
        (lowCoreActionCoefficients (I := I) (M := M) g hρ hδ0 hδ_le hreal S).secondOrderActionFourthToSecondOrder
          (I := I) (M := M))
    (hbd : ∀ S : SmoothCcTensor g 0 2,
      ‖(lowCoreActionCoefficients (I := I) (M := M) g hρ hδ0 hδ_le hreal S).secondOrderActionFourthToSecondOrder
        (I := I) (M := M)‖ ≤ c)
    (v : metricH2 (I := I) (M := M) g) :
    ‖show a2Op (I := I) (M := M) g from
      lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal v‖ ≤ c := by
  have hdense : DenseRange (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by norm_num)
  have hclosed : IsClosed {w : metricH2 (I := I) (M := M) g |
      ‖show a2Op (I := I) (M := M) g from
        lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal w‖ ≤ c} :=
    isClosed_le
      (Continuous.comp
        (continuous_norm (E := a2Op (I := I) (M := M) g)) hcont)
      continuous_const
  refine hdense.induction_on v hclosed ?_
  intro S
  have h := hbd S
  rw [← hcore S] at h
  exact h

private theorem a2Lo_total_le
    (g : SmoothRiemannianMetric I M) {ρ δ c : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hcont : Continuous
      (lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal))
    (hcore : ∀ S : SmoothCcTensor g 0 2,
      lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal
          (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) S) =
        (lowCoreActionCoefficients (I := I) (M := M) g hρ hδ0 hδ_le hreal S).secondOrderActionThirdToFirstOrder
          (I := I) (M := M))
    (hbd : ∀ S : SmoothCcTensor g 0 2,
      ‖(lowCoreActionCoefficients (I := I) (M := M) g hρ hδ0 hδ_le hreal S).secondOrderActionThirdToFirstOrder
        (I := I) (M := M)‖ ≤ c)
    (v : metricH2 (I := I) (M := M) g) :
    ‖show a2LoOp (I := I) (M := M) g from
      lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal v‖ ≤ c := by
  have hdense : DenseRange (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by norm_num)
  have hclosed : IsClosed {w : metricH2 (I := I) (M := M) g |
      ‖show a2LoOp (I := I) (M := M) g from
        lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal w‖ ≤ c} :=
    isClosed_le
      (Continuous.comp
        (continuous_norm (E := a2LoOp (I := I) (M := M) g)) hcont)
      continuous_const
  refine hdense.induction_on v hclosed ?_
  intro S
  have h := hbd S
  rw [← hcore S] at h
  exact h

theorem lowerScaleSecondOrderAction_small
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {ρ₀ δ : ℝ}
    (hρ₀ : 0 < ρ₀) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ₀ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    ∃ ρ C : ℝ, 0 < ρ ∧ ρ ≤ ρ₀ ∧ 0 ≤ C ∧
      ∀ (hρ0 : 0 ≤ ρ)
        (hreal' : ∀ S : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
            gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g S) δ),
        Continuous (lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M) g hρ0 hδ0 hδ_le hreal') ∧
          Continuous (lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ0 hδ0 hδ_le hreal') ∧
          (∀ v : metricH2 (I := I) (M := M) g,
            ‖show a2Op (I := I) (M := M) g from
              lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M) g hρ0 hδ0 hδ_le hreal' v‖ ≤ C * ρ) ∧
          (∀ v : metricH2 (I := I) (M := M) g,
            ‖show a2LoOp (I := I) (M := M) g from
              lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ0 hδ0 hδ_le hreal' v‖ ≤ C * ρ) ∧
          (∀ v : metricH2 (I := I) (M := M) g,
            (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
                (show (1 : ℝ) ≤ 2 by norm_num)).comp
                  (lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M) g hρ0 hδ0 hδ_le hreal' v) =
              (lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ0 hδ0 hδ_le hreal' v).comp
                (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
                  (show (3 : ℝ) ≤ 4 by norm_num))) := by
  obtain ⟨ρL, CL, hρL, hρL_le, hlipdata⟩ :=
    radialSecondOrderAction_lipschitz (I := I) (M := M) hDim g hρ₀ hδ0 hδ_le hreal
  have hrealL : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρL →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ :=
    fun S hS => hreal S (hS.trans hρL_le)
  obtain ⟨ρA, CA, hρA, hρA_le, hCA, hpairdata⟩ :=
    radialSecondOrderAction_pairing_bound (I := I) (M := M) hDim g hρL hδ0 hδ_le hrealL
  refine ⟨ρA, CA, hρA, hρA_le.trans hρL_le, hCA, ?_⟩
  intro hρ0 hreal'
  obtain ⟨hlip, hlipLo, hcore, hcoreLo, hsq⟩ := hlipdata (r := ρA) hρ0 hρA_le
  refine ⟨hlip.continuous, hlipLo.continuous, fun v => ?_, fun v => ?_, hsq⟩
  · exact a2Hi_total_le (I := I) (M := M) g hρ0 hδ0 hδ_le hreal'
      hlip.continuous hcore (fun S => (hpairdata S hρ0 hρA_le).1) v
  · exact a2Lo_total_le (I := I) (M := M) g hρ0 hδ0 hδ_le hreal'
      hlipLo.continuous hcoreLo (fun S => (hpairdata S hρ0 hρA_le).2.1) v

theorem lowerScaleSecondOrderAction_norm_lt_one
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {ρ₀ δ : ℝ}
    (hρ₀ : 0 < ρ₀) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ₀ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    ∃ ρ C : ℝ, 0 < ρ ∧ ρ ≤ ρ₀ ∧ 0 ≤ C ∧ C * ρ < 1 ∧
      ∀ (hρ0 : 0 ≤ ρ)
        (hreal' : ∀ S : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
            gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g S) δ),
        Continuous (lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M) g hρ0 hδ0 hδ_le hreal') ∧
          Continuous (lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ0 hδ0 hδ_le hreal') ∧
          (∀ v : metricH2 (I := I) (M := M) g,
            ‖show a2Op (I := I) (M := M) g from
              lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M) g hρ0 hδ0 hδ_le hreal' v‖ ≤ C * ρ) ∧
          (∀ v : metricH2 (I := I) (M := M) g,
            ‖show a2LoOp (I := I) (M := M) g from
              lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ0 hδ0 hδ_le hreal' v‖ ≤ C * ρ) ∧
          (∀ v : metricH2 (I := I) (M := M) g,
            (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
                (show (1 : ℝ) ≤ 2 by norm_num)).comp
                  (lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M) g hρ0 hδ0 hδ_le hreal' v) =
              (lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ0 hδ0 hδ_le hreal' v).comp
                (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
                  (show (3 : ℝ) ≤ 4 by norm_num))) := by
  obtain ⟨ρL, CL, hρL, hρL_le, hlipdata⟩ :=
    radialSecondOrderAction_lipschitz (I := I) (M := M) hDim g hρ₀ hδ0 hδ_le hreal
  have hrealL : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρL →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ :=
    fun S hS => hreal S (hS.trans hρL_le)
  obtain ⟨ρA, CA, hρA_le, hρA, hCA, hpairdata⟩ :=
    radialSecondOrderAction_pairing_bound_on_radius (I := I) (M := M) hDim g hρL hδ0 hδ_le hrealL
  let ρ : ℝ := min ρA (1 / (CA + 1))
  have hden : 0 < CA + 1 := by linarith only [hCA]
  have hρ : 0 < ρ := lt_min hρA (one_div_pos.mpr hden)
  have hρA' : ρ ≤ ρA := min_le_left _ _
  have hρL' : ρ ≤ ρL := hρA'.trans hρA_le
  have hρ₀' : ρ ≤ ρ₀ := hρL'.trans hρL_le
  have hρcap : ρ ≤ 1 / (CA + 1) := min_le_right _ _
  have hsmall : CA * ρ < 1 := by
    calc
      CA * ρ ≤ CA * (1 / (CA + 1)) := mul_le_mul_of_nonneg_left hρcap hCA
      _ = CA / (CA + 1) := by ring
      _ < 1 := (div_lt_one hden).2 (by linarith only [hCA])
  refine ⟨ρ, CA, hρ, hρ₀', hCA, hsmall, ?_⟩
  intro hρ0 hreal'
  obtain ⟨hlip, hlipLo, hcore, hcoreLo, hsq⟩ :=
    hlipdata (r := ρ) hρ0 hρL'
  refine ⟨hlip.continuous, hlipLo.continuous, fun v => ?_, fun v => ?_, hsq⟩
  · exact a2Hi_total_le (I := I) (M := M) g hρ0 hδ0 hδ_le hreal'
      hlip.continuous hcore (fun S => (hpairdata hρ0 hρA' S).1) v
  · exact a2Lo_total_le (I := I) (M := M) g hρ0 hδ0 hδ_le hreal'
      hlipLo.continuous hcoreLo (fun S => (hpairdata hρ0 hρA' S).2.1) v

theorem lowRegularitySecondOrderActionTotal_data
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {ρ₀ δ : ℝ}
    (hρ₀ : 0 < ρ₀) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ₀ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    ∃ ρ C : ℝ, 0 < ρ ∧ ρ ≤ ρ₀ ∧ 0 ≤ C ∧
      ∀ (hρ0 : 0 ≤ ρ)
        (hreal' : ∀ S : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
            gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g S) δ)
        {R : ℝ} (hR : 0 ≤ R), R ≤ ρ →
        ∀ {T : ℝ} (hT : 0 < T)
          (f : timeL2 (metricH1 (I := I) (M := M) g) T)
          (hball : ∀ᵐ t ∂timeMeasure T,
            ‖tensorHsInclusion (I := I) (M := M)
              (g := g) (r := 0) (s := 2)
              (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
              (maxRegDuhamelSolField (I := I) (M := M)
                (1 : ℝ) hT
                (0 : solH3 (I := I) (M := M) g) f t)‖ ≤ R),
          AEStronglyMeasurable
              (lowRegularitySecondOrderActionTotal (I := I) (M := M)
                g hρ0 hδ0 hδ_le hreal' hT f hR hball)
              (timeMeasure T) ∧
            (∀ᵐ t ∂timeMeasure T,
              ‖lowRegularitySecondOrderActionTotal (I := I) (M := M)
                g hρ0 hδ0 hδ_le hreal' hT f hR hball t‖ ≤ C * ρ) := by
  obtain ⟨ρP, CP, hρP, hdataP⟩ :=
    lowRegularityPrincipalSecondOrderActionTime_data (I := I) (M := M) hDim g
  have hρ₁ : 0 < min ρ₀ ρP := lt_min hρ₀ hρP
  have hreal₁ : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ min ρ₀ ρP →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ :=
    fun S hS => hreal S (hS.trans (min_le_left _ _))
  obtain ⟨ρ, CA, hρ, hρ_le₁, hCA, hA2⟩ :=
    lowerScaleSecondOrderAction_small (I := I) (M := M) hDim g hρ₁ hδ0 hδ_le hreal₁
  refine ⟨ρ, (CP : ℝ) + CA, hρ, hρ_le₁.trans (min_le_left _ _),
    add_nonneg CP.coe_nonneg hCA, ?_⟩
  intro hρ0 hreal' R hR hRρ T hT f hball
  obtain ⟨hcont, -, hsmall, -, -⟩ := hA2 hρ0 hreal'
  obtain ⟨hmeasP, hboundP, -⟩ :=
    hdataP hR (hRρ.trans (hρ_le₁.trans (min_le_right _ _))) hT f hball
  have hstate : AEStronglyMeasurable
      (fun t => lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M) g hρ0 hδ0 hδ_le hreal'
        (lowRegularityStateL2 (I := I) (M := M) g hT f hR hball t))
      (timeMeasure T) :=
    hcont.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable
        (lowRegularityStateL2 (I := I) (M := M) g hT f hR hball))
  refine ⟨hmeasP.add hstate, ?_⟩
  filter_upwards [hboundP] with t ht
  have ht' : ‖show a2Op (I := I) (M := M) g from
      lowRegularityPrincipalSecondOrderActionTime (I := I) (M := M) g hT f hR hball t‖ ≤ (CP : ℝ) * R := ht
  calc
    ‖lowRegularitySecondOrderActionTotal (I := I) (M := M)
        g hρ0 hδ0 hδ_le hreal' hT f hR hball t‖ ≤
        ‖show a2Op (I := I) (M := M) g from
            lowRegularityPrincipalSecondOrderActionTime (I := I) (M := M) g hT f hR hball t‖ +
          ‖show a2Op (I := I) (M := M) g from
            lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M) g hρ0 hδ0 hδ_le hreal'
              (lowRegularityStateL2 (I := I) (M := M) g hT f hR hball t)‖ :=
      ContinuousLinearMap.opNorm_add_le _ _
    _ ≤ (CP : ℝ) * R + CA * ρ :=
      add_le_add ht'
        (hsmall (lowRegularityStateL2 (I := I) (M := M) g hT f hR hball t))
    _ ≤ (CP : ℝ) * ρ + CA * ρ :=
      add_le_add (mul_le_mul_of_nonneg_left hRρ CP.coe_nonneg) le_rfl
    _ = ((CP : ℝ) + CA) * ρ := by ring

def lowRegularitySecondOrderActionLowerScaleTime
    (g : SmoothRiemannianMetric I M) {T R : ℝ}
    (hT : 0 < T)
    (f : timeL2 (metricH1 (I := I) (M := M) g) T)
    (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂timeMeasure T,
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          (1 : ℝ) hT
          (0 : solH3 (I := I) (M := M) g) f t)‖ ≤ R) :
    ℝ → (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)) :=
  fun t =>
    (tensorHsCongrL (I := I) (M := M) g 0 2
        (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)).comp
      (lowRegularityPrincipalOperatorH1 (I := I) (M := M) g
        (aeSetLift (principalOperatorDomainBall_zero (I := I) (M := M) g hR)
          (lowRegularityStateL2 (I := I) (M := M) g hT f hR hball) t).1)

theorem lowRegularitySecondOrderActionLowerScaleTime_data
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ {R : ℝ} (hR : 0 ≤ R), R ≤ ρ →
        ∀ {T : ℝ} (hT : 0 < T)
          (f : timeL2 (metricH1 (I := I) (M := M) g) T)
    (hball : ∀ᵐ t ∂timeMeasure T,
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          (1 : ℝ) hT
          (0 : solH3 (I := I) (M := M) g) f t)‖ ≤ R),
          AEStronglyMeasurable
              (lowRegularitySecondOrderActionLowerScaleTime (I := I) (M := M) g hT f hR hball)
              (timeMeasure T) ∧
            (∀ t : ℝ,
              ‖show a2LoOp (I := I) (M := M) g from
                lowRegularitySecondOrderActionLowerScaleTime (I := I) (M := M) g hT f hR hball t‖ ≤
                  C * R) ∧
            (∀ t : ℝ,
              (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
                  (show (1 : ℝ) ≤ 2 by norm_num)).comp
                    (lowRegularityPrincipalSecondOrderActionTime (I := I) (M := M) g hT f hR hball t) =
                (lowRegularitySecondOrderActionLowerScaleTime (I := I) (M := M) g hT f hR hball t).comp
                  (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
                    (show (3 : ℝ) ≤ 4 by norm_num))) := by
  obtain ⟨ρc, hρc, hcomm⟩ := lowRegularityPrincipalOperators_commute (I := I) (M := M) hDim g
  obtain ⟨ρn, C42, C31, hρn, hC42, hC31, hnorm⟩ :=
    lowRegularityPrincipalOperators_pairing_bound (I := I) (M := M) hDim g
  obtain ⟨ρk, hρk, hcontOn⟩ := lowRegularityPrincipalOperatorH1_continuousOn (I := I) (M := M) hDim g
  refine ⟨min ρc (min ρn ρk), C31, lt_min hρc (lt_min hρn hρk), hC31, ?_⟩
  intro R hR hRρ T hT f hball
  have hRc : R ≤ ρc := hRρ.trans (min_le_left _ _)
  have hRn : R ≤ ρn :=
    hRρ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRk : R ≤ ρk :=
    hRρ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hmem : ∀ᵐ t ∂timeMeasure T,
      lowRegularityStateL2 (I := I) (M := M) g hT f hR hball t ∈
        principalOperatorDomainBall (I := I) (M := M) g R := by
    simpa only [principalOperatorDomainBall, Set.mem_ofPred_eq] using
      lowRegularityState_ae_le (I := I) (M := M) g hT f hR hball
  have hsub : principalOperatorDomainBall (I := I) (M := M) g R ⊆
      {S : tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) | ‖S‖ ≤ ρk} :=
    fun _ hS => le_trans hS hRk
  have hres : Continuous
      (Set.domRestrict (principalOperatorDomainBall (I := I) (M := M) g R)
        (lowRegularityPrincipalOperatorH1 (I := I) (M := M) g)) :=
    (hcontOn.mono hsub).domRestrict
  have hΦ : Continuous fun x : principalOperatorDomainBall (I := I) (M := M) g R =>
      (tensorHsCongrL (I := I) (M := M) g 0 2
          (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)).comp
        (lowRegularityPrincipalOperatorH1 (I := I) (M := M) g x.1) :=
    (ContinuousLinearMap.compL ℝ
      (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ))
      (tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ))
      (tensorHs (I := I) (M := M) g 0 2 (1 : ℝ))).continuous₂.comp
        (continuous_const.prodMk hres)
  refine ⟨hΦ.comp_aestronglyMeasurable
      (aeSetLift_aesm (principalOperatorDomainBall_zero (I := I) (M := M) g hR)
        (lowRegularityStateL2 (I := I) (M := M) g hT f hR hball) hmem),
    ?_, ?_⟩
  · intro t
    have hxR : ‖(aeSetLift (principalOperatorDomainBall_zero (I := I) (M := M) g hR)
          (lowRegularityStateL2 (I := I) (M := M) g hT f hR hball) t).1‖ ≤ R :=
      (aeSetLift (principalOperatorDomainBall_zero (I := I) (M := M) g hR)
        (lowRegularityStateL2 (I := I) (M := M) g hT f hR hball) t).2
    have heq : ‖show a2LoOp (I := I) (M := M) g from
          lowRegularitySecondOrderActionLowerScaleTime (I := I) (M := M) g hT f hR hball t‖ =
        ‖show pLoOp (I := I) (M := M) g from
          lowRegularityPrincipalOperatorH1 (I := I) (M := M) g
            (aeSetLift (principalOperatorDomainBall_zero (I := I) (M := M) g hR)
              (lowRegularityStateL2 (I := I) (M := M) g hT f hR hball) t).1‖ :=
      norm_congr_comp (I := I) (M := M) _ _
    rw [heq]
    exact ((hnorm _ (hxR.trans hRn)).2).trans
      (mul_le_mul_of_nonneg_left hxR hC31)
  · intro t
    have hxR : ‖(aeSetLift (principalOperatorDomainBall_zero (I := I) (M := M) g hR)
          (lowRegularityStateL2 (I := I) (M := M) g hT f hR hball) t).1‖ ≤ R :=
      (aeSetLift (principalOperatorDomainBall_zero (I := I) (M := M) g hR)
        (lowRegularityStateL2 (I := I) (M := M) g hT f hR hball) t).2
    have hsq := hcomm _ (hxR.trans hRc)
    have hstep := congrArg
      (fun L : tensorHs (I := I) (M := M) g 0 2 (4 : ℝ) →L[ℝ]
          tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ) =>
        (tensorHsCongrL (I := I) (M := M) g 0 2
          (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)).comp L) hsq
    simp only [← ContinuousLinearMap.comp_assoc] at hstep
    rw [tensorHsCongrL_incl (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num) (rfl : (2 : ℝ) = (2 : ℝ))
        (show ((1 : ℕ) : ℝ) ≤ (2 : ℝ) by norm_num)
        (show (1 : ℝ) ≤ (2 : ℝ) by norm_num),
      tensorHsCongrL_refl, ContinuousLinearMap.comp_id] at hstep
    exact hstep

def lowRegularitySecondOrderActionTotalLowerScale
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    {T R : ℝ} (hT : 0 < T)
    (f : timeL2 (metricH1 (I := I) (M := M) g) T)
    (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂timeMeasure T,
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          (1 : ℝ) hT
          (0 : solH3 (I := I) (M := M) g) f t)‖ ≤ R) :
    ℝ → (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)) :=
  fun t =>
    lowRegularitySecondOrderActionLowerScaleTime (I := I) (M := M) g hT f hR hball t +
      lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal
        (lowRegularityStateL2 (I := I) (M := M) g hT f hR hball t)

theorem lowRegularitySecondOrderActionTotalLowerScale_data
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {ρ₀ δ : ℝ}
    (hρ₀ : 0 < ρ₀) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ₀ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    ∃ ρ C : ℝ, 0 < ρ ∧ ρ ≤ ρ₀ ∧ 0 ≤ C ∧
      ∀ (hρ0 : 0 ≤ ρ)
        (hreal' : ∀ S : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
            gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g S) δ)
        {R : ℝ} (hR : 0 ≤ R), R ≤ ρ →
        ∀ {T : ℝ} (hT : 0 < T)
          (f : timeL2 (metricH1 (I := I) (M := M) g) T)
    (hball : ∀ᵐ t ∂timeMeasure T,
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          (1 : ℝ) hT
          (0 : solH3 (I := I) (M := M) g) f t)‖ ≤ R),
          AEStronglyMeasurable
              (lowRegularitySecondOrderActionTotalLowerScale (I := I) (M := M)
                g hρ0 hδ0 hδ_le hreal' hT f hR hball)
              (timeMeasure T) ∧
            (∀ᵐ t ∂timeMeasure T,
              ‖lowRegularitySecondOrderActionTotalLowerScale (I := I) (M := M)
                g hρ0 hδ0 hδ_le hreal' hT f hR hball t‖ ≤ C * ρ) ∧
            (∀ t : ℝ,
              (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
                  (show (1 : ℝ) ≤ 2 by norm_num)).comp
                    (lowRegularitySecondOrderActionTotal (I := I) (M := M)
                      g hρ0 hδ0 hδ_le hreal' hT f hR hball t) =
                (lowRegularitySecondOrderActionTotalLowerScale (I := I) (M := M)
                    g hρ0 hδ0 hδ_le hreal' hT f hR hball t).comp
                  (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
                    (show (3 : ℝ) ≤ 4 by norm_num))) := by
  obtain ⟨ρP, CP, hρP, hCP, hdataP⟩ :=
    lowRegularitySecondOrderActionLowerScaleTime_data (I := I) (M := M) hDim g
  have hρ₁ : 0 < min ρ₀ ρP := lt_min hρ₀ hρP
  have hreal₁ : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ min ρ₀ ρP →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ :=
    fun S hS => hreal S (hS.trans (min_le_left _ _))
  obtain ⟨ρ, CA, hρ, hρ_le₁, hCA, hA2⟩ :=
    lowerScaleSecondOrderAction_small (I := I) (M := M) hDim g hρ₁ hδ0 hδ_le hreal₁
  refine ⟨ρ, CP + CA, hρ, hρ_le₁.trans (min_le_left _ _),
    add_nonneg hCP hCA, ?_⟩
  intro hρ0 hreal' R hR hRρ T hT f hball
  obtain ⟨-, hcontLo, -, hsmallLo, hsqA⟩ := hA2 hρ0 hreal'
  obtain ⟨hmeasP, hboundP, hsqP⟩ :=
    hdataP hR (hRρ.trans (hρ_le₁.trans (min_le_right _ _))) hT f hball
  have hstate : AEStronglyMeasurable
      (fun t => lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ0 hδ0 hδ_le hreal'
        (lowRegularityStateL2 (I := I) (M := M) g hT f hR hball t))
      (timeMeasure T) :=
    hcontLo.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable
        (lowRegularityStateL2 (I := I) (M := M) g hT f hR hball))
  refine ⟨hmeasP.add hstate, ?_, ?_⟩
  · refine Filter.Eventually.of_forall fun t => ?_
    calc
      ‖lowRegularitySecondOrderActionTotalLowerScale (I := I) (M := M)
          g hρ0 hδ0 hδ_le hreal' hT f hR hball t‖ ≤
          ‖show a2LoOp (I := I) (M := M) g from
              lowRegularitySecondOrderActionLowerScaleTime (I := I) (M := M) g hT f hR hball t‖ +
            ‖show a2LoOp (I := I) (M := M) g from
              lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ0 hδ0 hδ_le hreal'
                (lowRegularityStateL2 (I := I) (M := M) g hT f hR hball t)‖ :=
        ContinuousLinearMap.opNorm_add_le _ _
      _ ≤ CP * R + CA * ρ :=
        add_le_add (hboundP t)
          (hsmallLo (lowRegularityStateL2 (I := I) (M := M) g hT f hR hball t))
      _ ≤ CP * ρ + CA * ρ :=
        add_le_add (mul_le_mul_of_nonneg_left hRρ hCP) le_rfl
      _ = (CP + CA) * ρ := by ring
  · intro t
    have hHi : lowRegularitySecondOrderActionTotal (I := I) (M := M)
          g hρ0 hδ0 hδ_le hreal' hT f hR hball t =
        lowRegularityPrincipalSecondOrderActionTime (I := I) (M := M) g hT f hR hball t +
          lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M) g hρ0 hδ0 hδ_le hreal'
            (lowRegularityStateL2 (I := I) (M := M) g hT f hR hball t) := rfl
    have hLo : lowRegularitySecondOrderActionTotalLowerScale (I := I) (M := M)
          g hρ0 hδ0 hδ_le hreal' hT f hR hball t =
        lowRegularitySecondOrderActionLowerScaleTime (I := I) (M := M) g hT f hR hball t +
          lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ0 hδ0 hδ_le hreal'
            (lowRegularityStateL2 (I := I) (M := M) g hT f hR hball t) := rfl
    rw [hHi, hLo, ContinuousLinearMap.comp_add, hsqP t,
      hsqA (lowRegularityStateL2 (I := I) (M := M) g hT f hR hball t),
      ← ContinuousLinearMap.add_comp]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end

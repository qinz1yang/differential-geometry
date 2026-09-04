import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Forcing.HighRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Lifting.LowerScaleAffine
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Lifting.StaticForcing
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Lifting.SmallTimeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Action.CrossScaleCompatibility
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Bounds.Class

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic (lowerState zero_mem_lowerState)
open DifferentialGeometry.Analysis.Spectral
  (ccTensorToHs ccToHsLin ccToHsLin_apply ccToHsLin_dense smoothCcToTensorHs
    tensorResolventL2_isCompactOperator)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

def HasCompatibleSecondOrderSolution
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ} (hρ : 0 < ρ)
    (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal' : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (TensorHs (I := I) (M := M) g 0 2 (1 : ℝ)) T)
    (Rcap : ℝ) : Prop :=
  ∃ (FHi : TensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
        (TensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
          TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)))
    (C2Hi : NNReal)
    (hA2Hi : AEStronglyMeasurable
      (lowAffineSecondOrderActionHigh (I := I) (M := M) g
        hρ.le hδ0 hδ_le hreal' hT f) (timeMeasure T))
    (hC2Hi : ∀ᵐ t ∂timeMeasure T,
      ‖lowAffineSecondOrderActionHigh (I := I) (M := M) g
        hρ.le hδ0 hδ_le hreal' hT f t‖ ≤ (C2Hi : ℝ))
    (hA1Hi : MemLp
      (highFirstOrderAffineOperator (I := I) (M := M) g ρ FHi hT f) 2
        (timeMeasure T))
    (uHi : MaximalRegularitySolutionSpace (I := I) (M := M)
      (g := g) (r := 0) (s := 2) (2 : ℝ) T)
    (fHi : timeL2 (TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) T)
    (u : CrossScaleField (I := I) (M := M) g 0 2 (2 : ℝ) T)
    (FLo : TensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (TensorHs (I := I) (M := M) g 0 2 (2 : ℝ) →L[ℝ]
        TensorHs (I := I) (M := M) g 0 2 (1 : ℝ)))
    (R : ℝ) (hR : 0 < R)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ),
    u.lo = uHi ∧
      u.hiL2 =
        maximalRegularityDuhamelSolutionField (I := I) (M := M) (2 : ℝ) hT 0 fHi ∧
      fHi =
        nonautL2Map (I := I) (M := M) hT hT1
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (lowAffineSecondOrderActionHigh (I := I) (M := M) g
              hρ.le hδ0 hδ_le hreal' hT f) hA2Hi C2Hi hC2Hi
            (highFirstOrderAffineOperator (I := I) (M := M) g ρ FHi hT f)
            hA1Hi fHi +
          liftForceHi (I := I) (M := M) g g T ∧
      timeH1.trace0 _ T u.lo =
        (0 : TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) ∧
      timeH1.timeDeriv _ T u.lo =
        timeScaleLaplacian (I := I) (M := M) (2 : ℝ) u.hiL2 + fHi ∧
      timeL2Inclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num) fHi = f ∧
      (∀ᵐ t ∂timeMeasure T,
        tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (1 : ℝ) ≤ (2 : ℝ) by norm_num) (fHi t) = f t) ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (1 : ℝ) ≤ (2 : ℝ) by norm_num) (u.lo.toFun t) =
          (maximalRegularityDuhamelMap (I := I) (M := M)
            (1 : ℝ) hT 0 f).toFun t) ∧
      u.repr 0 =
        (0 : TensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 1)) ∧
      ContinuousOn (fun t => ‖u.repr t‖ ^ 2) (Icc (0 : ℝ) T) ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (2 : ℝ) + 1 by norm_num) (u.repr t) =
          u.lo.toFun t) ∧
      ((fun t =>
          tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (1 : ℝ) + 2 ≤ (2 : ℝ) + 1 by norm_num) (u.repr t)) =ᵐ[
            timeMeasure T]
        fun t => maximalRegularityDuhamelSolutionField (I := I) (M := M)
          (1 : ℝ) hT 0 f t) ∧
      ((fun t => fHi t) =ᵐ[timeMeasure T]
        fun t => liftHiN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FHi
          (tensorHsCongr (I := I) (M := M) g 0 2
            (show (2 : ℝ) + 2 = (4 : ℝ) by norm_num) (u.hiL2 t))) ∧
      R ≤ ρ ∧
      Continuous (deTurckRemainderOnLowerState (I := I) (M := M) g g hR
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) hreal) ∧
      Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g g
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) hreal) ∧
      Continuous (lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal') ∧
      (∀ S : SmoothCcTensor g 0 2,
        lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'
            (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) S) =
          (combinedLowerScaleActionCoefficients (I := I) (M := M) g
            hρ.le hδ0 hδ_le hreal' S).secondOrderActionThirdToFirstOrder (I := I) (M := M)) ∧
      Continuous (lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal') ∧
      Continuous FHi ∧
      Continuous FLo ∧
      (∀ S : SmoothCcTensor g 0 2,
        FLo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
          (radialLowerScaleActionCoefficients (I := I) (M := M)
              g hρ.le hδ0 hδ_le hreal' S).firstOrderActionSecondToFirstOrder (I := I) (M := M) +
            (firstOrderCoreActionCoefficients (I := I) (M := M)
              g hρ.le hδ0 hδ_le hreal' S).firstOrderActionSecondToFirstOrder (I := I) (M := M)) ∧
      (∀ v : TensorHs (I := I) (M := M) g 0 2 (2 : ℝ),
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp
            (lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' v) =
          (lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' v).comp
            (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              (show (3 : ℝ) ≤ 4 by norm_num))) ∧
      (∀ x : TensorHs (I := I) (M := M) g 0 2 (3 : ℝ),
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp (FHi x) =
          (FLo x).comp
            (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              (show (2 : ℝ) ≤ (3 : ℝ) by norm_num))) ∧
      (∀ᵐ t ∂timeMeasure T, ‖u.lo.toFun t‖ ≤ R) ∧
      R ≤ Rcap

theorem hasCompatibleSecondOrderSolution_of_bounds
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {R ρ δ T B2 B2Hi Z L c Rcap : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hRρ : R ≤ ρ)
    (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hreal' : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hNcont : Continuous (deTurckRemainderOnLowerState (I := I) (M := M) g g hR hδ hreal))
    (hcoreN : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g g hδ hreal))
    (hA2cont : Continuous
      (lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'))
    (hA2core : ∀ S : SmoothCcTensor g 0 2,
      lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'
          (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) S) =
        (combinedLowerScaleActionCoefficients (I := I) (M := M) g
          hρ.le hδ0 hδ_le hreal' S).secondOrderActionThirdToFirstOrder (I := I) (M := M))
    (hB2 : 0 ≤ B2)
    (hA2bd : ∀ v : TensorHs (I := I) (M := M) g 0 2 (2 : ℝ),
      ‖lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' v‖ ≤ B2)
    (hA2Hicont : Continuous
      (lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'))
    (hB2Hi : 0 ≤ B2Hi)
    (hA2Hibd : ∀ v : TensorHs (I := I) (M := M) g 0 2 (2 : ℝ),
      ‖lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' v‖ ≤ B2Hi)
    (hA2sq : ∀ v : TensorHs (I := I) (M := M) g 0 2 (2 : ℝ),
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp
          (lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' v) =
        (lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' v).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (3 : ℝ) ≤ 4 by norm_num)))
    (hZ : 0 ≤ Z) (hL : 0 ≤ L)
    (FHi : TensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (TensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
        TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)))
    (FLo : TensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (TensorHs (I := I) (M := M) g 0 2 (2 : ℝ) →L[ℝ]
        TensorHs (I := I) (M := M) g 0 2 (1 : ℝ)))
    (hFHi : Continuous FHi) (hFLo : Continuous FLo)
    (hFLoCore : ∀ S : SmoothCcTensor g 0 2,
      FLo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
        (radialLowerScaleActionCoefficients (I := I) (M := M)
            g hρ.le hδ0 hδ_le hreal' S).firstOrderActionSecondToFirstOrder (I := I) (M := M) +
          (firstOrderCoreActionCoefficients (I := I) (M := M)
            g hρ.le hδ0 hδ_le hreal' S).firstOrderActionSecondToFirstOrder (I := I) (M := M))
    (hFHiBd : ∀ x : TensorHs (I := I) (M := M) g 0 2 (3 : ℝ),
      ‖FHi x‖ ≤ Z + L * ‖x‖)
    (hFLoBd : ∀ x : TensorHs (I := I) (M := M) g 0 2 (3 : ℝ),
      ‖FLo x‖ ≤ Z + L * ‖x‖)
    (hFComm : ∀ x : TensorHs (I := I) (M := M) g 0 2 (3 : ℝ),
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp (FHi x) =
        (FLo x).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)))
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (TensorHs (I := I) (M := M) g 0 2 (1 : ℝ)) T)
    (hball : ∀ᵐ t ∂timeMeasure T,
      stateField (I := I) (M := M) g hT f t ∈
        lowerState (I := I) (M := M) g 1 R)
    (hforce : f =ᵐ[timeMeasure T] fun t =>
      tensorHsCongr (I := I) (M := M) g 0 2
        (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
        (deTurckRemainderOnLowerState (I := I) (M := M) g g hR hδ hreal
          (aeSetLift
            (zero_mem_lowerState (I := I) (M := M) g 1 hR.le)
            (stateField (I := I) (M := M) g hT f) t)))
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hB2c : B2 ≤ c) (hB2Hic : B2Hi ≤ c)
    (hmargin : 6 * (2 * L * ‖f‖) ≤ (1 - c) / 2)
    (hTle : T ≤ affineLiftTimeHorizon c Z) (hRcap : R ≤ Rcap) :
    HasCompatibleSecondOrderSolution (I := I) (M := M) g hρ hδ0 hδ_le hreal' hT hT1 f Rcap := by
  obtain ⟨C2, hA2, hC2, hA1, hA1Hi, hC2eq, hA1norm, hA1HiNorm,
      hA1compat, heq⟩ :=
    exists_affine_forcing_operator_data (I := I) (M := M) hDim g hR hρ hRρ hδ0 hδ_le hδ
      hreal hreal' hNcont hcoreN hA2cont hA2core hB2 hA2bd hZ hL
      FHi FLo hFHi hFLo hFLoCore hFHiBd hFLoBd hFComm hT hT1 f hball hforce
  have hduh : L * ‖duhamelH3 (I := I) (M := M) g hT f‖ ≤ 2 * L * ‖f‖ := by
    have h1 := mul_le_mul_of_nonneg_left
      (norm_duhamelH3_le (I := I) (M := M) g hT f) hL
    have h2 : (0 : ℝ) ≤ (1 - T) * (L * ‖f‖) :=
      mul_nonneg (by linarith) (mul_nonneg hL (norm_nonneg f))
    nlinarith
  obtain ⟨C2Hi, hC2Hieq, hA2Hi, hC2Hi⟩ :=
    lowAffineSecondOrderActionHigh_data (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'
      hA2Hicont hB2Hi hA2Hibd hT f
  have hnormHi : ‖hA1Hi.toLp
      (highFirstOrderAffineOperator (I := I) (M := M) g ρ FHi hT f)‖ ≤
      2 * L * ‖f‖ + Real.sqrt T * Z := by linarith
  have hnormLo : ‖hA1.toLp
      (lowFirstOrderAffineOperator (I := I) (M := M) g ρ FLo hT f)‖ ≤
      2 * L * ‖f‖ + Real.sqrt T * Z := by linarith
  have hmarginHi :
      (C2Hi : ℝ) * (1 + T) + 2 * Real.sqrt (1 + T) *
          ‖hA1Hi.toLp (highFirstOrderAffineOperator (I := I) (M := M) g ρ FHi hT f)‖ ≤
        1 - (1 - c) / 4 :=
    lift_aff_margin (A := 2 * L * ‖f‖) (Z := Z)
      hc0 hc1 hZ hmargin hT hTle
      (show (C2Hi : ℝ) ≤ c from hC2Hieq.trans_le hB2Hic)
      (norm_nonneg _) hnormHi
  have hsmallHi :
      (C2Hi : ℝ) * (1 + T) + 2 * Real.sqrt (1 + T) *
          ‖hA1Hi.toLp (highFirstOrderAffineOperator (I := I) (M := M) g ρ FHi hT f)‖ < 1 := by
    linarith only [hmarginHi, hc1]
  have hmarginLo : 6 * (2 * L * ‖f‖) < 1 - c := by linarith only [hmargin, hc1]
  have hsmallLo :=
    lift_small_aff
      (Y := TensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 1) →L[ℝ]
        TensorHs (I := I) (M := M) g 0 2 (1 : ℝ))
      (A1 := lowFirstOrderAffineOperator (I := I) (M := M) g ρ FLo hT f) hA1
      (show (C2 : ℝ) ≤ c from hC2eq.trans_le hB2c)
      hc0 hc1 hZ hmarginLo hT hTle hnormLo
  obtain ⟨uHi, fHi, u, hpacket⟩ :=
    exists_compatible_cross_scale_field_realization (I := I) (M := M) (g := g)
      (aLo := (1 : ℝ)) (aHi := (2 : ℝ)) (T := T)
      (show (1 : ℝ) = (2 : ℝ) - 1 by norm_num)
      (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)
      (show (1 : ℝ) + 1 ≤ (2 : ℝ) + 1 by norm_num)
      (show (1 : ℝ) + 2 ≤ (2 : ℝ) + 2 by norm_num)
      (show (2 : ℝ) ≤ (2 : ℝ) + 1 by norm_num)
      (show (1 : ℝ) + 2 ≤ (2 : ℝ) + 1 by norm_num)
      hT hT1
      (lowAffineSecondOrderActionHigh (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' hT f)
      hA2Hi C2Hi hC2Hi
      (highFirstOrderAffineOperator (I := I) (M := M) g ρ FHi hT f) hA1Hi
      (liftForceHi (I := I) (M := M) g g T) hsmallHi
      (lowAffineSecondOrderAction (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' hT f)
      hA2 C2 hC2
      (lowFirstOrderAffineOperator (I := I) (M := M) g ρ FLo hT f) hA1
      (liftForceLo (I := I) (M := M) g g T) hsmallLo
      (Filter.Eventually.of_forall fun t =>
        lowAffineSecondOrderAction_compatible (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' hA2sq
          hT f t)
      hA1compat (lift_force_incl (I := I) (M := M) g g T) f heq
  obtain ⟨hlo, hhi, hfHieq, htr, hpde, hL2incl, hincl, hlopin, hrepr0,
    hreprcont, hreprpin, hreprae⟩ := hpacket
  have hctrans : ∀ {a b c : ℝ} (hab : a = b) (hbc : b = c)
      (x : TensorHs (I := I) (M := M) g 0 2 a),
      tensorHsCongr (I := I) (M := M) g 0 2 hbc
          (tensorHsCongr (I := I) (M := M) g 0 2 hab x) =
        tensorHsCongr (I := I) (M := M) g 0 2 (hab.trans hbc) x := by
    intro a b c hab hbc x
    cases hab
    cases hbc
    rfl
  have hstate := aeSetLift_coe_ae
    (zero_mem_lowerState (I := I) (M := M) g 1 hR.le)
    (stateField (I := I) (M := M) g hT f) hball
  have hsf : ∀ᵐ t ∂timeMeasure T,
      (stateField (I := I) (M := M) g hT f) t =
        tensorHsCongr (I := I) (M := M) g 0 2
          (show (1 : ℝ) + 2 = ((1 : ℕ) : ℝ) + 2 by norm_num)
          (maximalRegularityDuhamelSolutionField (I := I) (M := M) (1 : ℝ) hT 0 f t) := by
    filter_upwards [(tensorHsCongrL (I := I) (M := M) g 0 2
      (show (1 : ℝ) + 2 = ((1 : ℕ) : ℝ) + 2 by norm_num)).coeFn_compLpL
      (p := 2) (μ := timeMeasure T)
      (maximalRegularityDuhamelSolutionField (I := I) (M := M) (1 : ℝ) hT
        (0 : TensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 2)) f)] with t ht
    simpa only [stateField, tensorHsCongrL_apply] using ht
  have hballU : ∀ᵐ t ∂timeMeasure T, ‖u.lo.toFun t‖ ≤ R := by
    filter_upwards [hreprae, hsf, hball,
      ae_restrict_mem (measurableSet_Icc (a := (0 : ℝ)) (b := T))]
      with t hrae hsfa hbl htmem
    have hmem : ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
        (stateField (I := I) (M := M) g hT f t)‖ ≤ R := hbl
    calc ‖u.lo.toFun t‖
        = ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (2 : ℝ) + 1 by norm_num) (u.repr t)‖ := by
          rw [hreprpin t htmem]
      _ = ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (1 : ℝ) + 2 by norm_num)
            (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              (show (1 : ℝ) + 2 ≤ (2 : ℝ) + 1 by norm_num) (u.repr t))‖ := by
          rw [tensorHsInclusion_trans_apply (I := I) (M := M) (g := g)
            (r := 0) (s := 2) (show (2 : ℝ) ≤ (1 : ℝ) + 2 by norm_num)
            (show (1 : ℝ) + 2 ≤ (2 : ℝ) + 1 by norm_num)]
      _ = ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (1 : ℝ) + 2 by norm_num)
            (maximalRegularityDuhamelSolutionField (I := I) (M := M) (1 : ℝ) hT 0 f t)‖ := by
          rw [hrae]
      _ = ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
            (tensorHsCongr (I := I) (M := M) g 0 2
              (show (1 : ℝ) + 2 = ((1 : ℕ) : ℝ) + 2 by norm_num)
              (maximalRegularityDuhamelSolutionField (I := I) (M := M)
                (1 : ℝ) hT 0 f t))‖ :=
          (norm_incl_congr (I := I) (M := M) g
            (show (2 : ℝ) = ((1 : ℕ) : ℝ) + 1 by norm_num)
            (show (1 : ℝ) + 2 = ((1 : ℕ) : ℝ) + 2 by norm_num)
            (show (2 : ℝ) ≤ (1 : ℝ) + 2 by norm_num)
            (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num) _).symm
      _ = ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
            (stateField (I := I) (M := M) g hT f t)‖ := by rw [hsfa]
      _ ≤ R := hmem
  refine ⟨FHi, C2Hi, hA2Hi, hC2Hi, hA1Hi, uHi, fHi, u, FLo, R, hR, hreal,
    hlo, hhi, hfHieq, htr, hpde, hL2incl, hincl, hlopin, hrepr0, hreprcont,
    hreprpin, hreprae, ?_, hRρ, hNcont, hcoreN, hA2cont, hA2core, hA2Hicont,
    hFHi, hFLo, hFLoCore, hA2sq, hFComm, hballU, hRcap⟩
  have hpin : ∀ᵐ t ∂timeMeasure T,
      tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (3 : ℝ) ≤ (4 : ℝ) by norm_num)
          (tensorHsCongr (I := I) (M := M) g 0 2
            (show (2 : ℝ) + 2 = (4 : ℝ) by norm_num) (u.hiL2 t)) =
        tensorHsCongr (I := I) (M := M) g 0 2
          (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num)
          ((aeSetLift (zero_mem_lowerState (I := I) (M := M) g 1 hR.le)
            (stateField (I := I) (M := M) g hT f) t).1) := by
    filter_upwards [u.link, hreprae, hstate, hsf,
      ae_restrict_mem (measurableSet_Icc (a := (0 : ℝ)) (b := T))]
      with t hlink hrae hst hsfa htmem
    have h3 : tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (2 : ℝ) + 1 ≤ (2 : ℝ) + 2 by norm_num) (u.hiL2 t) =
        u.repr t := by
      apply tensorHsInclusion_injective (I := I) (M := M) (g := g)
        (r := 0) (s := 2) (show (2 : ℝ) ≤ (2 : ℝ) + 1 by norm_num)
      rw [← tensorHsInclusion_trans_apply (I := I) (M := M) (g := g)
        (r := 0) (s := 2) (show (2 : ℝ) ≤ (2 : ℝ) + 1 by norm_num)
        (show (2 : ℝ) + 1 ≤ (2 : ℝ) + 2 by norm_num), hlink]
      exact (hreprpin t htmem).symm
    have hRHS : tensorHsCongr (I := I) (M := M) g 0 2
          (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num)
          ((aeSetLift (zero_mem_lowerState (I := I) (M := M) g 1 hR.le)
            (stateField (I := I) (M := M) g hT f) t).1) =
        tensorHsCongr (I := I) (M := M) g 0 2
          (show (2 : ℝ) + 1 = (3 : ℝ) by norm_num) (u.repr t) := by
      rw [hst, hsfa, hctrans, ← hrae,
        tensorHsCongr_incl (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) + 2 = (3 : ℝ) by norm_num)
          (show (2 : ℝ) + 1 = (3 : ℝ) by norm_num)
          (show (1 : ℝ) + 2 ≤ (2 : ℝ) + 1 by norm_num)
          (show (3 : ℝ) ≤ (3 : ℝ) from le_rfl) (u.repr t)]
      exact tensorHsInclusion_refl_apply (I := I) (M := M) (g := g)
        (r := 0) (s := 2)
        (tensorHsCongr (I := I) (M := M) g 0 2
          (show (2 : ℝ) + 1 = (3 : ℝ) by norm_num) (u.repr t))
    rw [← tensorHsCongr_incl (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (2 : ℝ) + 1 = (3 : ℝ) by norm_num)
        (show (2 : ℝ) + 2 = (4 : ℝ) by norm_num)
        (show (2 : ℝ) + 1 ≤ (2 : ℝ) + 2 by norm_num)
        (show (3 : ℝ) ≤ (4 : ℝ) by norm_num),
      h3, hRHS]
  filter_upwards [hincl, hforce, hpin] with t h1 h2 h3
  apply tensorHsInclusion_injective (I := I) (M := M) (g := g)
    (r := 0) (s := 2) (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)
  rw [h1, h2]
  exact deTurck_remainder_lower_scale_eq_included_higher_order_forcing (I := I) (M := M) hDim g hR hρ hRρ hδ0 hδ_le hδ
    hreal hreal' hNcont hcoreN hA2cont hA2core FHi FLo hFLo hFLoCore
    hA2sq hFComm _ _ h3

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem congrLp_self (g : SmoothRiemannianMetric I M) {a T : ℝ}
    (h : a = a) (u : timeL2 (TensorHs (I := I) (M := M) g 0 2 a) T) :
    (tensorHsCongrL (I := I) (M := M) g 0 2 h).compLpL 2 (timeMeasure T) u =
      u := by
  have hrfl : h = rfl := rfl
  rw [hrfl]
  apply MeasureTheory.Lp.ext
  filter_upwards [(tensorHsCongrL (I := I) (M := M) g 0 2
    (rfl : a = a)).coeFn_compLpL (p := 2) (μ := timeMeasure T) u] with t ht
  rw [ht, tensorHsCongrL_refl, ContinuousLinearMap.id_apply]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem duhamel_congr (g : SmoothRiemannianMetric I M) {a b : ℝ}
    (h : a = b) {T : ℝ} (hT : 0 < T)
    (u : timeL2 (TensorHs (I := I) (M := M) g 0 2 a) T) :
    (tensorHsCongrL (I := I) (M := M) g 0 2
          (show b + 2 = a + 2 by rw [h])).compLpL 2 (timeMeasure T)
        (maximalRegularityDuhamelSolutionField (I := I) (M := M) b hT
          (0 : TensorHs (I := I) (M := M) g 0 2 (b + 2))
          ((tensorHsCongrL (I := I) (M := M) g 0 2 h).compLpL
            2 (timeMeasure T) u)) =
      maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT
        (0 : TensorHs (I := I) (M := M) g 0 2 (a + 2)) u := by
  cases h
  rw [congrLp_self, congrLp_self]

private theorem a2Lo_congr (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {A B : LowerScaleActionCoefficients g}
    (h : A.secondOrderCoefficient = B.secondOrderCoefficient) :
    A.secondOrderActionThirdToFirstOrder (I := I) (M := M) = B.secondOrderActionThirdToFirstOrder (I := I) (M := M) := by
  have ha2 : ∀ W : SmoothCcTensor g 0 2,
      A.secondOrderAction (I := I) (M := M) W = B.secondOrderAction (I := I) (M := M) W := by
    intro W
    rw [LowerScaleActionCoefficients.secondOrderAction, LowerScaleActionCoefficients.secondOrderAction, h]
  refine ContinuousLinearMap.ext fun v => ?_
  refine (ccToHsLin_dense (I := I) (M := M) g 2
    (by norm_num : (0 : ℝ) ≤ (3 : ℝ))).induction_on v
      (isClosed_eq (A.secondOrderActionThirdToFirstOrder (I := I) (M := M)).continuous
        (B.secondOrderActionThirdToFirstOrder (I := I) (M := M)).continuous) ?_
  intro W
  rw [ccToHsLin_apply, secondOrderActionThirdToFirstOrder_ccTensorToHs (I := I) (M := M) hDim g A W,
    secondOrderActionThirdToFirstOrder_ccTensorToHs (I := I) (M := M) hDim g B W, ha2 W]

theorem exists_compatible_second_order_solution_with_contraction
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {Rcap : ℝ} (hRcap : 0 < Rcap)
    {thr : ℝ} (hthr : 0 < thr) (hthr3 : thr ≤ 1 / 3) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ)
      (hreal' : ∀ S : SmoothCcTensor g 0 2,
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
          gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g S) thr)
      (B2 : ℝ), 0 ≤ B2 ∧ B2 < 1 ∧
      ∀ {c : ℝ}, B2 ≤ c → c < 1 →
        ∃ T₀ : ℝ, 0 < T₀ ∧
          ∀ {T : ℝ} (hT : 0 < T) (_ : T ≤ T₀) (hT1 : T ≤ 1),
            ∃ (f : timeL2 (TensorHs (I := I) (M := M) g 0 2 (1 : ℝ)) T)
              (fLo : timeL2 (TensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
              (Ctop B0 B1 D ρout P : ℝ),
              HasCompatibleSecondOrderSolution (I := I) (M := M) g hρ hthr.le hthr3 hreal' hT hT1 f
                  Rcap ∧
                (∀ᵐ t ∂timeMeasure T, f t =
                  tensorHsCongr (I := I) (M := M) g 0 2
                    (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num) (fLo t)) ∧
                IsLowRegularitySolutionAt (I := I) (M := M) (δ := thr) (Ctop := Ctop)
                  (B0 := B0) (B1 := B1) (D := D) (ρ := ρout) (P := P)
                  g hT hT1 fLo Rcap := by
  classical
  have hδ0 : 0 ≤ thr := hthr.le
  have hδ_le : thr ≤ 1 / 3 := hthr3
  have hδ : thr < 1 := lt_of_le_of_lt hthr3 (by norm_num)
  obtain ⟨ρA, hρA, hpack⟩ := exists_first_order_continuous_operator_extensions (I := I) (M := M) hDim g
  obtain ⟨Pr, hPr, hrealPr⟩ := realize_at_delta (I := I) (M := M) hDim g hthr
  obtain ⟨ρN, CtopN, B0N, B1N, hρN, -, -, -, houterN⟩ :=
    deTurckRemainderOnLowerState_outer_bound (I := I) (M := M) hDim g g hδ0 hδ
  have hcap : 0 < min ρA Pr := lt_min hρA hPr
  have hrealcap : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ min ρA Pr →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) thr := by
    intro S hS
    refine hrealPr S ?_
    rw [norm_smoothCc_congr (I := I) (M := M) g
      (show ((1 : ℕ) : ℝ) + 1 = (2 : ℝ) by norm_num) S,
      smoothCcToTensorHs_eq_ccToHs]
    exact hS.trans (min_le_right _ _)
  obtain ⟨ρL, CL, hρL, hρL_le, hlip⟩ :=
    radialSecondOrderAction_lipschitz (I := I) (M := M) hDim g hcap hδ0 hδ_le hrealcap
  have hrealL : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρL →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) thr :=
    fun S hS => hrealcap S (hS.trans hρL_le)
  obtain ⟨ρ, C, hρ, hρ_le, hC, hCρ, hA2small⟩ :=
    lowerScaleSecondOrderAction_norm_lt_one (I := I) (M := M) hDim g hρL hδ0 hδ_le hrealL
  have hreal' : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) thr :=
    fun S hS => hrealL S (hS.trans hρ_le)
  obtain ⟨hA2Hicont, hA2cont, hA2Hibd, hA2bd, hA2sq⟩ := hA2small hρ.le hreal'
  obtain ⟨-, -, -, hcoreLo, -⟩ := hlip (r := ρ) hρ.le hρ_le
  have hA2core : ∀ S : SmoothCcTensor g 0 2,
      lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'
          (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) S) =
        (combinedLowerScaleActionCoefficients (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' S).secondOrderActionThirdToFirstOrder
          (I := I) (M := M) := by
    intro S
    refine (hcoreLo S).trans (a2Lo_congr (I := I) (M := M) hDim g ?_)
    rfl
  obtain ⟨Z, L, hZ, hL, FHi, FLo, hFHi, hFLo, -, hFLoCore,
      hFHiBd, hFLoBd, hFComm⟩ :=
    hpack hρ (hρ_le.trans (hρL_le.trans (min_le_left _ _)))
      hδ0 hδ_le hreal'
  refine ⟨ρ, hρ, hreal', C * ρ, mul_nonneg hC hρ.le, hCρ, ?_⟩
  intro c hB2c hc1
  have hc0 : 0 ≤ c := (mul_nonneg hC hρ.le).trans hB2c
  have h1c : (0 : ℝ) < 1 - c := by linarith
  have hL1 : (0 : ℝ) < 6 * (L + 1) := by linarith
  set P : ℝ :=
    min (min (min ρ ρN) ((1 - c) / (6 * (L + 1)))) Rcap with hPdef
  have hPle0 : P ≤ min (min ρ ρN) ((1 - c) / (6 * (L + 1))) := min_le_left _ _
  have hPle1 : P ≤ min ρ ρN := hPle0.trans (min_le_left _ _)
  have hPρ : P ≤ ρ := hPle1.trans (min_le_left _ _)
  have hPN : P ≤ ρN := hPle1.trans (min_le_right _ _)
  have hPc : P ≤ (1 - c) / (6 * (L + 1)) := hPle0.trans (min_le_right _ _)
  have hPcap : P ≤ Rcap := min_le_right _ _
  have hPpos : 0 < P :=
    lt_min (lt_min (lt_min hρ hρN) (div_pos h1c hL1)) hRcap
  have hrealP := realizeOfLE (I := I) (M := M) g
    (show P ≤ Pr from
      hPρ.trans (hρ_le.trans (hρL_le.trans (min_le_right _ _)))) hrealPr
  obtain ⟨Ctop, B0, B1, D, ρout, hCtop, hB1, hρout, hB0, hcont, htame,
      hzero⟩ :=
    exists_lowRegularity_remainder_bounds (I := I) (M := M) hDim g g hδ0 hδ hPpos hrealP
  have hD : 0 ≤ D := (norm_nonneg _).trans hzero
  have hR : 0 < lowRegularityStateRadius Ctop B1 ρout P :=
    lowRegularityStateRadius_pos hCtop hB1 hρout hPpos
  have hRP : lowRegularityStateRadius Ctop B1 ρout P ≤ P :=
    lowRegularityStateRadius_le_P hPpos.le
  have hrealR := lowRegularityMetricRealization (I := I) (M := M) g
    (Ctop := Ctop) (B1 := B1) (ρ := ρout) hPpos.le hrealP
  obtain ⟨-, hcoreN, -⟩ := houterN hR.le (hRP.trans hPN) hR le_rfl hrealR
  refine ⟨min (lowRegularityTimeHorizon Ctop B0 B1 D ρout P) (affineLiftTimeHorizon c Z),
    lt_min (lowRegularityTimeHorizon_pos hCtop hB0 hB1 hD hρout hPpos)
      (affineLiftTimeHorizon_pos hc0 hc1 hZ), ?_⟩
  intro T hT hTT₀ hT1
  obtain ⟨-, gforce, -, hball, hforce, -, -, hgf⟩ :=
    exists_lowRegularity_solution_of_remainder_bounds (I := I) (M := M) g g hδ hCtop hB0 hB1 hρout
      hPpos hrealP hcont htame hzero hT
      (hTT₀.trans (min_le_left _ _))
  set f : timeL2 (TensorHs (I := I) (M := M) g 0 2 (1 : ℝ)) T :=
    (tensorHsCongrL (I := I) (M := M) g 0 2
      (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)).compLpL 2 (timeMeasure T)
      gforce with hfdef
  have hstate : stateField (I := I) (M := M) g hT f =
      maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
        (0 : TensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2)) gforce := by
    rw [hfdef]
    exact duhamel_congr (I := I) (M := M) g
      (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num) hT gforce
  have hfae : ∀ᵐ t ∂timeMeasure T,
      f t = tensorHsCongr (I := I) (M := M) g 0 2
        (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num) (gforce t) := by
    rw [hfdef]
    exact (tensorHsCongrL (I := I) (M := M) g 0 2
      (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)).coeFn_compLpL
      (p := 2) (μ := timeMeasure T) gforce
  have hball' : ∀ᵐ t ∂timeMeasure T,
      stateField (I := I) (M := M) g hT f t ∈
        lowerState (I := I) (M := M) g 1
          (lowRegularityStateRadius Ctop B1 ρout P) := by
    rw [hstate]
    exact hball
  have hforce' : f =ᵐ[timeMeasure T] fun t =>
      tensorHsCongr (I := I) (M := M) g 0 2
        (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
        (deTurckRemainderOnLowerState (I := I) (M := M) g g hR hδ hrealR
          (aeSetLift
            (zero_mem_lowerState (I := I) (M := M) g 1 hR.le)
            (stateField (I := I) (M := M) g hT f) t)) := by
    rw [hstate]
    filter_upwards [hfae, hforce] with t h1 h2
    rw [h1, h2]
    rfl
  have hfnorm : ‖f‖ = ‖gforce‖ := by
    rw [hfdef]
    exact norm_congrLp (I := I) (M := M) g
      (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num) gforce
  have hfP : ‖f‖ ≤ P / 4 := by
    rw [hfnorm]
    refine hgf.trans ?_
    linarith
  have hkey : P * (6 * (L + 1)) ≤ 1 - c := by
    rw [← le_div_iff₀ hL1]
    exact hPc
  have hmargin : 6 * (2 * L * ‖f‖) ≤ (1 - c) / 2 := by
    have h1 : 12 * L * ‖f‖ ≤ 12 * L * (P / 4) :=
      mul_le_mul_of_nonneg_left hfP (by linarith : (0 : ℝ) ≤ 12 * L)
    linarith only [h1, hkey, hPpos]
  refine ⟨f, gforce, Ctop, B0, B1, D, ρout, P,
    hasCompatibleSecondOrderSolution_of_bounds (I := I) (M := M) hDim g hR hρ (hRP.trans hPρ)
      hδ0 hδ_le hδ hrealR hreal' hcont hcoreN hA2cont hA2core
      (mul_nonneg hC hρ.le) hA2bd hA2Hicont (mul_nonneg hC hρ.le) hA2Hibd hA2sq
      hZ hL FHi FLo hFHi hFLo hFLoCore hFHiBd hFLoBd hFComm
      hT hT1 f hball' hforce' hc0 hc1 hB2c hB2c hmargin
      (hTT₀.trans (min_le_right _ _)) (hRP.trans hPcap),
    hfae, ?_⟩
  exact isLowRegularitySolutionAt_of_remainder_bounds (I := I) (M := M) g hδ hCtop hB0 hB1 hρout hPpos
    hrealP hδ0 hδ_le hcoreN hcont htame hzero hT
    (hTT₀.trans (min_le_left _ _)) hT1 gforce hgf hforce (hRP.trans hPcap)

theorem exists_compatible_second_order_solution_at_threshold
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {Rcap : ℝ} (hRcap : 0 < Rcap)
    {thr : ℝ} (hthr : 0 < thr) (hthr3 : thr ≤ 1 / 3) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ)
      (hreal' : ∀ S : SmoothCcTensor g 0 2,
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
          gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g S) thr)
      (B2 : ℝ), 0 ≤ B2 ∧
      ∀ {c : ℝ}, B2 ≤ c → c < 1 →
        ∃ T₀ : ℝ, 0 < T₀ ∧
          ∀ {T : ℝ} (hT : 0 < T) (_ : T ≤ T₀) (hT1 : T ≤ 1),
            ∃ (f : timeL2 (TensorHs (I := I) (M := M) g 0 2 (1 : ℝ)) T)
              (fLo : timeL2 (TensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
              (Ctop B0 B1 D ρout P : ℝ),
              HasCompatibleSecondOrderSolution (I := I) (M := M) g hρ hthr.le hthr3 hreal' hT hT1 f
                  Rcap ∧
                (∀ᵐ t ∂timeMeasure T, f t =
                  tensorHsCongr (I := I) (M := M) g 0 2
                    (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num) (fLo t)) ∧
                IsLowRegularitySolutionAt (I := I) (M := M) (δ := thr) (Ctop := Ctop)
                  (B0 := B0) (B1 := B1) (D := D) (ρ := ρout) (P := P)
                  g hT hT1 fLo Rcap := by
  obtain ⟨ρ, hρ, hreal', B2, hB2, -, hsolve⟩ :=
    exists_compatible_second_order_solution_with_contraction (I := I) (M := M) hDim g hRcap hthr hthr3
  exact ⟨ρ, hρ, hreal', B2, hB2, hsolve⟩

theorem exists_compatible_second_order_solution
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {Rcap : ℝ} (hRcap : 0 < Rcap)
    {thr : ℝ} (hthr : 0 < thr) (hthr3 : thr ≤ 1 / 3) :
    ∃ (ρ δ : ℝ) (hρ : 0 < ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
      (hreal' : ∀ S : SmoothCcTensor g 0 2,
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
          gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g S) δ)
      (B2 : ℝ), 0 ≤ B2 ∧
      ∀ {c : ℝ}, B2 ≤ c → c < 1 →
        ∃ T₀ : ℝ, 0 < T₀ ∧
          ∀ {T : ℝ} (hT : 0 < T) (_ : T ≤ T₀) (hT1 : T ≤ 1),
            ∃ (f : timeL2 (TensorHs (I := I) (M := M) g 0 2 (1 : ℝ)) T)
              (fLo : timeL2 (TensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T),
              HasCompatibleSecondOrderSolution (I := I) (M := M) g hρ hδ0 hδ_le hreal' hT hT1 f
                  Rcap ∧
                (∀ᵐ t ∂timeMeasure T, f t =
                  tensorHsCongr (I := I) (M := M) g 0 2
                    (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num) (fLo t)) ∧
                IsLowRegularitySolution (I := I) (M := M) g hT fLo := by
  obtain ⟨ρ, hρ, hreal', B2, hB2, hsolve⟩ :=
    exists_compatible_second_order_solution_at_threshold (I := I) (M := M) hDim g hRcap hthr hthr3
  refine ⟨ρ, thr, hρ, hthr.le, hthr3, hreal', B2, hB2, ?_⟩
  intro c hB2c hc1
  obtain ⟨T₀, hT₀, hpack⟩ := hsolve hB2c hc1
  refine ⟨T₀, hT₀, ?_⟩
  intro T hT hTT₀ hT1
  obtain ⟨f, fLo, Ctop, B0, B1, D, ρout, P, hre, hfae, hlo⟩ :=
    hpack hT hTT₀ hT1
  exact ⟨f, fLo, hre, hfae, hlo.toIsLowRegularitySolution⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end

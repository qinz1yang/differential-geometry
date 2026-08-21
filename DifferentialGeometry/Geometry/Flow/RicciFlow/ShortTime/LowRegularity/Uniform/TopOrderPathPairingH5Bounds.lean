import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.CenteredPathPairing
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.TopOrderPairingH5Bounds

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle intervalIntegral
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Sobolev (iteratedCovGrad)
open DifferentialGeometry.Analysis.Spectral
  (operatorFieldApply ccTensorToHs deTurckMetricPrincipalDefectTotal oneMinusConnLapSmooth metricPrincipalDefectCurvCoeff)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem ricciDeTurck_remainder_path_pairing_h5_uniform_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∀ {eta : ℝ}, 0 < eta →
      ∃ delta2 R2 : ℝ,
        0 < delta2 ∧ delta2 ≤ 1 / 3 ∧ 0 < R2 ∧ R2 ≤ 1 ∧
        ∀ g : SmoothRiemannianMetric I M,
          MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
          (∀ a : ℕ, a ≤ 3 →
            MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
          ∃ G : ℝ, 0 ≤ G ∧
            ∀ (T : SmoothCcTensor g 0 2)
              (_hTsymm : ∀ (x : M) (u v : TangentSpace I x),
                ccTensorBilin (I := I) g T x u v =
                  ccTensorBilin (I := I) g T x v u)
              {delta : ℝ}, delta ≤ delta2 → 0 ≤ delta →
              ∀ (hdelta_lt : delta < 1)
                (hdelta : gFibreOpBound (I := I) (M := M) g
                  (ccTensorBilinSymm (I := I) g T) delta)
                (hdeltaZ : gFibreOpBound (I := I) (M := M) g
                  (ccTensorBilinSymm (I := I) g
                    (0 : SmoothCcTensor g 0 2)) delta)
                {R : ℝ}, 0 ≤ R → R ≤ R2 →
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
              let P0 := ricciDeTurckRemainderZeroOrderPathIntegral (I := I) (M := M) g gBase T 0
                hdelta_lt hdelta hdelta_lt hdeltaZ
              let P2 := rhsTopPathIntegral (I := I) (M := M) g T 0
                hdelta_lt hdelta hdelta_lt hdeltaZ
              let K0 := metricPrincipalDefectCurvCoeff (I := I) g g
              let LT := oneMinusConnLapSmooth (I := I) g 0 2 T
              let HT := iteratedCovGrad (I := I) g 0 2 2 T
              let HLT := iteratedCovGrad (I := I) g 0 2 2 LT
              let B02 :=
                oneMinusConnLapSmooth (I := I) g 0 2
                    (operatorFieldApply (I := I) (M := M) g 2 2 P0 T) +
                  (oneMinusConnLapSmooth (I := I) g 0 2
                      (operatorFieldApply (I := I) (M := M) g 4 2 P2 HT) -
                    operatorFieldApply (I := I) (M := M) g 4 2 P2 HLT)
              let V := oneMinusConnLapSmooth (I := I) g 0 2
                (oneMinusConnLapSmooth (I := I) g 0 2 LT)
              2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun
                    (B02 + operatorFieldApply (I := I) (M := M) g 2 2 K0 LT).toFun| ≤
                eta * ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖ ^ 2 +
                  G *
                    (‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
                      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 *
                        ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
                      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 4) := by
  intro eta heta
  obtain ⟨delta2, R2, hdelta2, hdelta2third, hR2, hR2one, hpoint⟩ :=
    ricciDeTurck_remainder_pairing_h5_uniform_bound (I := I) (M := M) hDim gBase hΛ heta
  refine ⟨delta2, R2, hdelta2, hdelta2third, hR2, hR2one, ?_⟩
  intro g hEq hjet
  obtain ⟨G, hG, hpointG⟩ := hpoint g hEq hjet
  refine ⟨G, hG, ?_⟩
  intro T hTsymm delta hdelta_le hdelta0 hdelta_lt hdelta hdeltaZ R hR hRle hT2
  let P0 := ricciDeTurckRemainderZeroOrderPathIntegral (I := I) (M := M) g gBase T 0
    hdelta_lt hdelta hdelta_lt hdeltaZ
  let P2 := rhsTopPathIntegral (I := I) (M := M) g T 0
    hdelta_lt hdelta hdelta_lt hdeltaZ
  let K0 := metricPrincipalDefectCurvCoeff (I := I) g g
  let LT := oneMinusConnLapSmooth (I := I) g 0 2 T
  let HT := iteratedCovGrad (I := I) g 0 2 2 T
  let HLT := iteratedCovGrad (I := I) g 0 2 2 LT
  let B02 :=
    oneMinusConnLapSmooth (I := I) g 0 2
        (operatorFieldApply (I := I) (M := M) g 2 2 P0 T) +
      (oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 4 2 P2 HT) -
        operatorFieldApply (I := I) (M := M) g 4 2 P2 HLT)
  let V := oneMinusConnLapSmooth (I := I) g 0 2
    (oneMinusConnLapSmooth (I := I) g 0 2 LT)
  let Js := fun s : ℝ =>
    let gs := metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s
    let R0s := rhsDecomposition0 (I := I) (M := M) g gBase T hdelta hdeltaZ s
    let Qs := fun U : SmoothCcTensor g 0 2 =>
      ricciDeTurckTopOrderBilinearPairingCoefficient (I := I) (M := M) g T U hdelta hdeltaZ
        ricciDecompositionQA ricciDecompositionQB lieDecompositionQ lieDecompositionEps s
    let Zs := operatorFieldApply (I := I) (M := M) g 2 2 (Qs T) T
    let PairComms := oneMinusConnLapSmooth (I := I) g 0 2 Zs -
      operatorFieldApply (I := I) (M := M) g 2 2 (Qs LT) T -
      operatorFieldApply (I := I) (M := M) g 2 2 (Qs T) LT + Zs
    let Cs := deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gs -
      deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g
    oneMinusConnLapSmooth (I := I) g 0 2
        (operatorFieldApply (I := I) (M := M) g 2 2 (R0s + K0) T) +
      PairComms +
      (oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 4 2 Cs HT) -
        operatorFieldApply (I := I) (M := M) g 4 2 Cs HLT) - Zs
  let Crosss := fun s : ℝ =>
    let Qs := fun U : SmoothCcTensor g 0 2 =>
      ricciDeTurckTopOrderBilinearPairingCoefficient (I := I) (M := M) g T U hdelta hdeltaZ
        ricciDecompositionQA ricciDecompositionQB lieDecompositionQ lieDecompositionEps s
    operatorFieldApply (I := I) (M := M) g 2 2 (Qs LT) T +
      operatorFieldApply (I := I) (M := M) g 2 2 (Qs T) LT
  let f : ℝ → ℝ := fun s => Inner.inner ℝ V (Js s + Crosss s)
  let Cb : ℝ :=
    eta * ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖ ^ 2 +
      G *
        (‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 *
            ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 4)
  obtain ⟨hpair, hfInt⟩ :=
    centeredPathPairing_eq_intervalIntegral_and_intervalIntegrable
      (I := I) (M := M) g gBase T V hTsymm hdelta_lt hdelta hdeltaZ
  have hfInt' : IntervalIntegrable f volume 0 1 := by
    simpa only [f, Js, Crosss, V, LT, HT, HLT, K0] using hfInt
  have hpointwise : ∀ s ∈ Set.Icc (0 : ℝ) 1, 2 * |f s| ≤ Cb := by
    intro s hs
    simpa only [f, Cb, Js, Crosss, V, LT, HT, HLT, K0,
      SmoothCcTensor.inner_def] using
      hpointG T hTsymm hdelta_le hdelta0 hdelta hdeltaZ hs hR hRle hT2
  have habs := intervalIntegral.abs_integral_le_integral_abs
    (μ := volume) (f := f) (a := (0 : ℝ)) (b := 1) (by norm_num)
  have hmono : (∫ s in (0 : ℝ)..1, 2 * |f s|) ≤
      ∫ _s in (0 : ℝ)..1, Cb := by
    exact intervalIntegral.integral_mono_on (by norm_num)
      (hfInt'.abs.const_mul 2) _root_.intervalIntegrable_const hpointwise
  change 2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun
      (B02 + operatorFieldApply (I := I) (M := M) g 2 2 K0 LT).toFun| ≤ Cb
  calc
    2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun
        (B02 + operatorFieldApply (I := I) (M := M) g 2 2 K0 LT).toFun| =
        2 * |∫ s in (0 : ℝ)..1, f s| := by
      rw [← SmoothCcTensor.inner_def]
      simpa only [f, B02, P0, P2, K0, LT, HT, HLT, V] using congrArg
        (fun z : ℝ => 2 * |z|) hpair
    _ ≤ 2 * (∫ s in (0 : ℝ)..1, |f s|) :=
      mul_le_mul_of_nonneg_left habs (by norm_num)
    _ = ∫ s in (0 : ℝ)..1, 2 * |f s| := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ ∫ _s in (0 : ℝ)..1, Cb := hmono
    _ = Cb := by
      rw [intervalIntegral.integral_const]
      norm_num

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end

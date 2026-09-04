import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Pairing.TopOrderH4Bounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Pairing.TopPathBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Action.LowerScalePathDecomposition

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle intervalIntegral
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Sobolev (iteratedCovGrad)
open DifferentialGeometry.Analysis.Spectral
  (operatorFieldApply ccTensorToHs ccTensorToHs_smul deTurckMetricPrincipalDefectTotal oneMinusConnLapSmooth
   metricPrincipalDefectCurvCoeff)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem exists_uniform_lower_scale_h4_pairing_bound_with_caps
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∀ {eta : ℝ}, 0 < eta →
      ∃ delta0 : ℝ,
        0 < delta0 ∧ delta0 ≤ 1 / 3 ∧
        ∀ {delta : ℝ}, 0 < delta → delta ≤ delta0 →
        ∃ R0 : ℝ, 0 < R0 ∧ R0 ≤ 1 ∧
        ∀ g : SmoothRiemannianMetric I M,
          MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
          (∀ a : ℕ, a ≤ 3 →
            MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
          ∃ G : ℝ, 0 ≤ G ∧
            ∀ (T : SmoothCcTensor g 0 2)
              (_hTsymm : ∀ (x : M) (u v : TangentSpace I x),
                ccTensorBilin (I := I) g T x u v =
                  ccTensorBilin (I := I) g T x v u)
              (hdelta_lt : delta < 1)
              (hdelta : gFibreOpBound (I := I) (M := M) g
                (ccTensorBilinSymm (I := I) g T) delta)
              (hdeltaZ : gFibreOpBound (I := I) (M := M) g
                (ccTensorBilinSymm (I := I) g
                  (0 : SmoothCcTensor g 0 2)) delta)
              {R : ℝ}, 0 ≤ R → R ≤ R0 →
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
              let A := lowerScaleActionCoefficients (I := I) (M := M) g gBase T
                hdelta_lt hdelta hdeltaZ
              let V := oneMinusConnLapSmooth (I := I) g 0 2
                (oneMinusConnLapSmooth (I := I) g 0 2 T)
              2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun
                    (oneMinusConnLapSmooth (I := I) g 0 2
                      (A.secondOrderAction (I := I) (M := M) T +
                        A.firstOrderAction (I := I) (M := M) T)).toFun| ≤
                eta * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
                  G * (‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 +
                    ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 4) := by
  intro eta heta
  let e : ℝ := eta / 3
  have he : 0 < e := by dsimp only [e]; positivity
  obtain ⟨delta0, Re, hdelta0, hdelta0third, hRe, hReone, hedge⟩ :=
    ricciDeTurck_remainder_path_pairing_h4_uniform_bound (I := I) (M := M) hDim gBase hΛ he
  refine ⟨delta0, hdelta0, hdelta0third, ?_⟩
  intro delta hdelta hdelta_le
  have hdeltathird : delta ≤ 1 / 3 := hdelta_le.trans hdelta0third
  have hdeltalt : delta < 1 := lt_of_le_of_lt hdeltathird (by norm_num)
  obtain ⟨Rl, Gl, hRl, hRlone, hGl, hlow⟩ :=
    low1_pair_abs_uniform (I := I) (M := M) hDim gBase hΛ
      hdelta.le hdeltalt he
  obtain ⟨Rt, hRt, htop⟩ :=
    top_pair_abs_uniform (I := I) (M := M) hDim gBase hΛ he
  let R0 : ℝ := min Re (min Rl Rt)
  have hR0 : 0 < R0 := by
    dsimp only [R0]
    exact lt_min hRe (lt_min hRl hRt)
  have hR0one : R0 ≤ 1 := by
    exact (min_le_left Re (min Rl Rt)).trans hReone
  refine ⟨R0, hR0, hR0one, ?_⟩
  intro g hEq hjet
  obtain ⟨Ge, hGe, hedgeG⟩ := hedge g hEq hjet
  let G : ℝ := Ge + Gl
  have hG : 0 ≤ G := add_nonneg hGe hGl
  refine ⟨G, hG, ?_⟩
  intro T hTsymm hdelta_lt hdeltaT hdeltaZ R hR hRR0 hT2
  let A := lowerScaleActionCoefficients (I := I) (M := M) g gBase T
    hdelta_lt hdeltaT hdeltaZ
  let P0 := ricciDeTurckRemainderZeroOrderPathIntegral (I := I) (M := M) g gBase T 0
    hdelta_lt hdeltaT hdelta_lt hdeltaZ
  let P1 := ricciDeTurckRemainderFirstOrderPathIntegral (I := I) (M := M) g gBase T 0
    hdelta_lt hdeltaT hdelta_lt hdeltaZ
  let P2 := rhsTopPathIntegral (I := I) (M := M) g T 0
    hdelta_lt hdeltaT hdelta_lt hdeltaZ
  let Φ0 := deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g
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
  let Y1 := oneMinusConnLapSmooth (I := I) g 0 2
    (operatorFieldApply (I := I) (M := M) g 3 2 P1
      (iteratedCovGrad (I := I) g 0 2 1 T))
  let Y2 := operatorFieldApply (I := I) (M := M) g 4 2 (P2 - Φ0) HLT
  let X := B02 + operatorFieldApply (I := I) (M := M) g 2 2 K0 LT
  let V := oneMinusConnLapSmooth (I := I) g 0 2 LT
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let z : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖
  have hRRe : R ≤ Re := hRR0.trans (min_le_left _ _)
  have hRRl : R ≤ Rl := hRR0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRRt : R ≤ Rt := hRR0.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hcenter := hedgeG T hTsymm (delta := delta) hdelta_le hdelta.le
    hdelta_lt hdeltaT hdeltaZ hR hRRe hT2
  have hlow1 := hlow g hEq hjet T hdeltaT hdeltaZ hR hRRl hT2
  have hzero : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
      (0 : SmoothCcTensor g 0 2)‖ ≤ R := by
    rw [show (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • (0 : SmoothCcTensor g 0 2) from (zero_smul ℝ _).symm,
      ccTensorToHs_smul, zero_smul, norm_zero]
    exact hR
  have htop2 := htop g hEq hjet T (0 : SmoothCcTensor g 0 2)
    hdelta_lt hdeltaT hdelta_lt hdeltaZ hR hRRt hT2 hzero T
  have hnf := oneMinusConnectionLaplacian_lowerScaleActionCoefficients_eq_path_terms (I := I) (M := M) g gBase T hTsymm
    hdeltathird hdelta.le hdeltaT hdeltaZ
  have hdecomp :
      oneMinusConnLapSmooth (I := I) g 0 2
          (A.secondOrderAction (I := I) (M := M) T + A.firstOrderAction (I := I) (M := M) T) =
        X + Y1 + Y2 := by
    dsimp only [A, X, Y1, Y2, B02, P0, P1, P2, Φ0, K0, LT, HT, HLT]
    dsimp only at hnf
    rw [sub_eq_iff_eq_add] at hnf
    rw [hnf]
    module
  have htri :
      2 * |Inner.inner ℝ V (X + Y1 + Y2)| ≤
        2 * |Inner.inner ℝ V X| +
          2 * |Inner.inner ℝ V Y1| +
            2 * |Inner.inner ℝ V Y2| := by
    rw [inner_add_right, inner_add_right]
    nlinarith [abs_add_le (Inner.inner ℝ V X) (Inner.inner ℝ V Y1),
      abs_add_le (Inner.inner ℝ V X + Inner.inner ℝ V Y1)
        (Inner.inner ℝ V Y2)]
  have hcenter' : 2 * |Inner.inner ℝ V X| ≤ e * z ^ 2 + Ge * (y ^ 2 + y ^ 4) := by
    simpa only [V, X, B02, P0, P2, K0, LT, HT, HLT, y, z,
      SmoothCcTensor.inner_def] using hcenter
  have hlow1' : 2 * |Inner.inner ℝ V Y1| ≤ e * z ^ 2 + Gl * y ^ 2 := by
    simpa only [V, Y1, P1, LT, y, z, SmoothCcTensor.inner_def] using hlow1
  have htop2' : 2 * |Inner.inner ℝ V Y2| ≤ e * z ^ 2 := by
    simpa only [V, Y2, P2, Φ0, LT, HLT, z, SmoothCcTensor.inner_def] using htop2
  change 2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun
      (oneMinusConnLapSmooth (I := I) g 0 2
        (A.secondOrderAction (I := I) (M := M) T + A.firstOrderAction (I := I) (M := M) T)).toFun| ≤
    eta * z ^ 2 + G * (y ^ 2 + y ^ 4)
  rw [hdecomp, ← SmoothCcTensor.inner_def]
  calc
    2 * |Inner.inner ℝ
          (oneMinusConnLapSmooth (I := I) g 0 2 LT) (X + Y1 + Y2)| ≤
        2 * |Inner.inner ℝ V X| +
          2 * |Inner.inner ℝ V Y1| + 2 * |Inner.inner ℝ V Y2| := by
      simpa only [V] using htri
    _ ≤ (e * z ^ 2 + Ge * (y ^ 2 + y ^ 4)) +
          (e * z ^ 2 + Gl * y ^ 2) + e * z ^ 2 := by
      gcongr
    _ ≤ eta * z ^ 2 + G * (y ^ 2 + y ^ 4) := by
      dsimp only [e, G]
      nlinarith [mul_nonneg hGl (sq_nonneg y), mul_nonneg hGl (by positivity)]
    _ = eta * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
          G * (‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 +
            ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 4) := by
      rfl

theorem exists_uniform_lower_scale_h4_pairing_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∀ {eta : ℝ}, 0 < eta →
      ∃ delta R0 : ℝ,
        0 < delta ∧ delta ≤ 1 / 3 ∧ 0 < R0 ∧ R0 ≤ 1 ∧
        ∀ g : SmoothRiemannianMetric I M,
          MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
          (∀ a : ℕ, a ≤ 3 →
            MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
          ∃ G : ℝ, 0 ≤ G ∧
            ∀ (T : SmoothCcTensor g 0 2)
              (_hTsymm : ∀ (x : M) (u v : TangentSpace I x),
                ccTensorBilin (I := I) g T x u v =
                  ccTensorBilin (I := I) g T x v u)
              (hdelta_lt : delta < 1)
              (hdelta : gFibreOpBound (I := I) (M := M) g
                (ccTensorBilinSymm (I := I) g T) delta)
              (hdeltaZ : gFibreOpBound (I := I) (M := M) g
                (ccTensorBilinSymm (I := I) g
                  (0 : SmoothCcTensor g 0 2)) delta)
              {R : ℝ}, 0 ≤ R → R ≤ R0 →
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
              let A := lowerScaleActionCoefficients (I := I) (M := M) g gBase T
                hdelta_lt hdelta hdeltaZ
              let V := oneMinusConnLapSmooth (I := I) g 0 2
                (oneMinusConnLapSmooth (I := I) g 0 2 T)
              2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun
                    (oneMinusConnLapSmooth (I := I) g 0 2
                      (A.secondOrderAction (I := I) (M := M) T +
                        A.firstOrderAction (I := I) (M := M) T)).toFun| ≤
                eta * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
                  G * (‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 +
                    ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 4) := by
  intro eta heta
  obtain ⟨delta, hdelta, hdeltathird, hpair⟩ :=
    exists_uniform_lower_scale_h4_pairing_bound_with_caps (I := I) (M := M) hDim gBase hΛ heta
  obtain ⟨R0, hR0, hR0one, hpair0⟩ := hpair hdelta le_rfl
  exact ⟨delta, R0, hdelta, hdeltathird, hR0, hR0one, hpair0⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end

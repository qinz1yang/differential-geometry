import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Action.CenteredTopOrderCommutator
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Pairing.MixedDerivativeH5Bounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Pairing.CurvatureCommutatorH5Bounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Pairing.TopKernelBounds

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev (iteratedCovGrad)
open DifferentialGeometry.Analysis.Spectral
  (operatorFieldApply ccTensorToHs deTurckMetricPrincipalDefectTotal metricPerturbationPathFromZero metricComparisonEndomorphism_pairing_balance oneMinusConnLapSmooth
    metricPrincipalDefectCurvCoeff slotExtend)
open DifferentialGeometry.Geometry.Curvature (pointwiseTensorCurv)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private theorem abs_add_sub_sub_sub_sub_le
    (a b c d e f : ℝ) :
    |a + b - c - d - e - f| ≤ |a| + |b| + |c| + |d| + |e| + |f| := by
  calc
    |a + b - c - d - e - f| ≤ |a + b - c - d - e| + |f| := abs_sub _ _
    _ ≤ (|a + b - c - d| + |e|) + |f| := by
      gcongr
      exact abs_sub _ _
    _ ≤ ((|a + b - c| + |d|) + |e|) + |f| := by
      gcongr
      exact abs_sub _ _
    _ ≤ (((|a + b| + |c|) + |d|) + |e|) + |f| := by
      gcongr
      exact abs_sub _ _
    _ ≤ (((|a| + |b| + |c|) + |d|) + |e|) + |f| := by
      gcongr
      exact abs_add_le a b

private theorem two_mul_le_eps {eta x y : ℝ} (heta : 0 < eta) :
    2 * x * y ≤ eta * x ^ 2 + eta⁻¹ * y ^ 2 := by
  have hinv : 0 ≤ eta⁻¹ := inv_nonneg.mpr heta.le
  have hs := mul_nonneg hinv (sq_nonneg (eta * x - y))
  have hexpand :
      eta⁻¹ * (eta * x - y) ^ 2 =
        eta * x ^ 2 - 2 * x * y + eta⁻¹ * y ^ 2 := by
    field_simp [ne_of_gt heta]
    ring
  rw [hexpand] at hs
  linarith

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] in
private theorem center_sum_h5
    (g : SmoothRiemannianMetric I M)
    (V J Cross Yc Yp Yd P20 P11L P11R : SmoothCcTensor g 0 2)
    (eta e Lc C4 Gmix Gd Gcorner G y q z : ℝ)
    (he : e = eta / 5)
    (hG : G = C4 + Gmix + Gcorner + Gd)
    (hC4 : 0 ≤ C4) (hGmix : 0 ≤ Gmix) (hGd : 0 ≤ Gd)
    (hGcorner : 0 ≤ Gcorner)
    (hnf : J + Cross = Yc + Yp - Yd - P20 - P11L - P11R)
    (hc : 2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun Yc.toFun| ≤
      e * z ^ 2 + Lc)
    (hp : 2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun Yp.toFun| ≤
      C4 * q ^ 2 + 2 * e * z ^ 2 + Gmix * y ^ 2 * q ^ 2)
    (hd : 2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun Yd.toFun| ≤
      e * z ^ 2 + Gd * y ^ 4)
    (hk : 2 * (|tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P20.toFun| +
        |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P11L.toFun| +
        |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P11R.toFun|) ≤
      e * z ^ 2 + Gcorner * y ^ 2 * q ^ 2) :
    2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun
        (J + Cross).toFun| ≤
      eta * z ^ 2 + Lc + G * (q ^ 2 + y ^ 2 * q ^ 2 + y ^ 4) := by
  have hinner :
      tensorL2Inner (I := I) (M := M) g 0 2 V.toFun (J + Cross).toFun =
        tensorL2Inner (I := I) (M := M) g 0 2 V.toFun Yc.toFun +
          tensorL2Inner (I := I) (M := M) g 0 2 V.toFun Yp.toFun -
          tensorL2Inner (I := I) (M := M) g 0 2 V.toFun Yd.toFun -
          tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P20.toFun -
          tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P11L.toFun -
          tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P11R.toFun := by
    rw [← SmoothCcTensor.inner_def (I := I) (M := M) V (J + Cross), hnf]
    simp only [inner_add_right, inner_sub_right, SmoothCcTensor.inner_def]
  have habs :
      |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun (J + Cross).toFun| ≤
        |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun Yc.toFun| +
          |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun Yp.toFun| +
          |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun Yd.toFun| +
          |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P20.toFun| +
          |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P11L.toFun| +
          |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P11R.toFun| := by
    rw [hinner]
    exact abs_add_sub_sub_sub_sub_le _ _ _ _ _ _
  calc
    2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun
        (J + Cross).toFun| ≤
        2 * (|tensorL2Inner (I := I) (M := M) g 0 2 V.toFun Yc.toFun| +
          |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun Yp.toFun| +
          |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun Yd.toFun| +
          |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P20.toFun| +
          |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P11L.toFun| +
          |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P11R.toFun|) :=
      mul_le_mul_of_nonneg_left habs (by norm_num)
    _ = 2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun Yc.toFun| +
        2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun Yp.toFun| +
        2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun Yd.toFun| +
        2 * (|tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P20.toFun| +
          |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P11L.toFun| +
          |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P11R.toFun|) := by ring
    _ ≤ (e * z ^ 2 + Lc) +
        (C4 * q ^ 2 + 2 * e * z ^ 2 + Gmix * y ^ 2 * q ^ 2) +
        (e * z ^ 2 + Gd * y ^ 4) +
        (e * z ^ 2 + Gcorner * y ^ 2 * q ^ 2) := by
      gcongr
    _ ≤ eta * z ^ 2 + Lc + G * (q ^ 2 + y ^ 2 * q ^ 2 + y ^ 4) := by
      have hlower :
          C4 * q ^ 2 + Gmix * y ^ 2 * q ^ 2 + Gd * y ^ 4 +
              Gcorner * y ^ 2 * q ^ 2 ≤
            (C4 + Gmix + Gcorner + Gd) *
              (q ^ 2 + y ^ 2 * q ^ 2 + y ^ 4) := by
        nlinarith [mul_nonneg hC4 (mul_nonneg (sq_nonneg y) (sq_nonneg q)),
          mul_nonneg hC4 (sq_nonneg (y ^ 2)),
          mul_nonneg hGmix (sq_nonneg q),
          mul_nonneg hGmix (sq_nonneg (y ^ 2)),
          mul_nonneg hGcorner (sq_nonneg q),
          mul_nonneg hGcorner (sq_nonneg (y ^ 2)),
          mul_nonneg hGd (sq_nonneg q),
          mul_nonneg hGd (mul_nonneg (sq_nonneg y) (sq_nonneg q))]
      rw [he, hG]
      calc
        _ = eta * z ^ 2 + Lc +
            (C4 * q ^ 2 + Gmix * y ^ 2 * q ^ 2 + Gd * y ^ 4 +
              Gcorner * y ^ 2 * q ^ 2) := by ring
        _ ≤ eta * z ^ 2 + Lc + (C4 + Gmix + Gcorner + Gd) *
            (q ^ 2 + y ^ 2 * q ^ 2 + y ^ 4) :=
          add_le_add le_rfl hlower

theorem ricciDeTurck_remainder_pairing_h5_bound_of_low_order_action_pairing_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Lambda : ℝ} (hLambda : 1 ≤ Lambda) :
    ∀ {eta : ℝ}, 0 < eta →
      ∃ delta2 R2 : ℝ,
        0 < delta2 ∧ delta2 ≤ 1 / 3 ∧ 0 < R2 ∧ R2 ≤ 1 ∧
        ∀ g : SmoothRiemannianMetric I M,
          MetricUniformEquivalentOn (I := I) Set.univ gBase g Lambda →
          (∀ a : ℕ, a ≤ 3 →
            MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Lambda) →
          ∃ G : ℝ, 0 ≤ G ∧
            ∀ (T : SmoothCcTensor g 0 2)
              (_hTsymm : ∀ (x : M) (u v : TangentSpace I x),
                ccTensorBilin (I := I) g T x u v =
                  ccTensorBilin (I := I) g T x v u)
              {delta : ℝ}, delta ≤ delta2 → 0 ≤ delta →
              ∀ (hdelta : gFibreOpBound (I := I) (M := M) g
                  (ccTensorBilinSymm (I := I) g T) delta)
                (hdeltaZ : gFibreOpBound (I := I) (M := M) g
                  (ccTensorBilinSymm (I := I) g
                    (0 : SmoothCcTensor g 0 2)) delta)
                {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
              ∀ {R : ℝ}, 0 ≤ R → R ≤ R2 →
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
              ∀ {Lc : ℝ},
              let gs := metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s
              let R0 := rhsDecomposition0 (I := I) (M := M) g gBase T
                hdelta hdeltaZ s
              let K0 := metricPrincipalDefectCurvCoeff (I := I) g g
              let LT := oneMinusConnLapSmooth (I := I) g 0 2 T
              let HT := iteratedCovGrad (I := I) g 0 2 2 T
              let HLT := iteratedCovGrad (I := I) g 0 2 2 LT
              let Q : SmoothCcTensor g 0 2 → SmoothCcTensor g 2 2 := fun U =>
                ricciDeTurckTopOrderBilinearPairingCoefficient (I := I) (M := M) g T U hdelta hdeltaZ
                  ricciDecompositionQA ricciDecompositionQB lieDecompositionQ lieDecompositionEps s
              let Z := operatorFieldApply (I := I) (M := M) g 2 2 (Q T) T
              let Cross :=
                operatorFieldApply (I := I) (M := M) g 2 2 (Q LT) T +
                  operatorFieldApply (I := I) (M := M) g 2 2 (Q T) LT
              let PairComm :=
                oneMinusConnLapSmooth (I := I) g 0 2 Z -
                  operatorFieldApply (I := I) (M := M) g 2 2 (Q LT) T -
                  operatorFieldApply (I := I) (M := M) g 2 2 (Q T) LT + Z
              let C : SmoothCcTensor g 4 2 :=
                deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gs -
                  deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g
              let J :=
                oneMinusConnLapSmooth (I := I) g 0 2
                    (operatorFieldApply (I := I) (M := M) g 2 2 (R0 + K0) T) +
                  PairComm +
                  (oneMinusConnLapSmooth (I := I) g 0 2
                      (operatorFieldApply (I := I) (M := M) g 4 2 C HT) -
                    operatorFieldApply (I := I) (M := M) g 4 2 C HLT) - Z
              let A := RicciDeTurckLowOrder.pathIntegrand
                  (I := I) (M := M) g gBase T hdelta hdeltaZ s + K0
              let V := oneMinusConnLapSmooth (I := I) g 0 2
                (oneMinusConnLapSmooth (I := I) g 0 2 LT)
              2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun
                    (oneMinusConnLapSmooth (I := I) g 0 2
                      (operatorFieldApply (I := I) (M := M) g 2 2 A T)).toFun| ≤
                  (eta / 5) *
                      ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖ ^ 2 +
                    Lc →
                2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun
                    (J + Cross).toFun| ≤
                  eta * ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖ ^ 2 +
                    Lc + G *
                      (‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
                        ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 *
                          ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
                        ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 4) := by
  intro eta heta
  let e : ℝ := eta / 5
  have he : 0 < e := by
    dsimp only [e]
    positivity
  obtain ⟨rhoP, C4, Cmix, C5, hrhoP, hC4, hCmix, hC5, hprincipal⟩ :=
    bcD2_pair_h5_uniform (I := I) (M := M) hDim gBase hLambda
  obtain ⟨rhoD, hrhoD, hdefect⟩ :=
    curvature_commutator_pairing_h5_young_bound (I := I) (M := M)
      hDim gBase hLambda he
  obtain ⟨rhoK, hrhoK, hcorner⟩ :=
    mixed_derivative_action_pairing_h5_uniform_bound (I := I) (M := M) hDim gBase hLambda
  let delta2 : ℝ := min (1 / 4 : ℝ) (e / (4 * (C5 + 1)))
  have hC5p : 0 < C5 + 1 := by linarith
  have hdelta2 : 0 < delta2 := lt_min (by norm_num)
    (div_pos he (mul_pos (by norm_num) hC5p))
  have hdelta2third : delta2 ≤ 1 / 3 :=
    (min_le_left _ _).trans (by norm_num)
  let R2 : ℝ := min 1 (min rhoP (min rhoD rhoK))
  have hR2 : 0 < R2 := by
    dsimp only [R2]
    exact lt_min zero_lt_one (lt_min hrhoP (lt_min hrhoD hrhoK))
  have hR2one : R2 ≤ 1 := min_le_left _ _
  refine ⟨delta2, R2, hdelta2, hdelta2third, hR2, hR2one, ?_⟩
  intro g hEq hjet
  obtain ⟨Gd, hGd, hdefectG⟩ := hdefect g hEq hjet
  obtain ⟨Gk, hGk, hcornerG⟩ := hcorner g hEq hjet
  let Gmix : ℝ := e⁻¹ * Cmix ^ 2
  let Gcorner : ℝ := e⁻¹ * Gk ^ 2
  let G : ℝ := C4 + Gmix + Gcorner + Gd
  have hGmix : 0 ≤ Gmix :=
    mul_nonneg (inv_nonneg.mpr he.le) (sq_nonneg Cmix)
  have hGcorner : 0 ≤ Gcorner :=
    mul_nonneg (inv_nonneg.mpr he.le) (sq_nonneg Gk)
  have hG : 0 ≤ G := by
    dsimp only [G]
    positivity
  refine ⟨G, hG, ?_⟩
  intro T hTsymm delta hdelta_le hdelta0 hdelta hdeltaZ s hs
    R hR hRle hT2 Lc
  dsimp only
  let gs := metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s
  let R0 := rhsDecomposition0 (I := I) (M := M) g gBase T hdelta hdeltaZ s
  let K0 := metricPrincipalDefectCurvCoeff (I := I) g g
  let LT := oneMinusConnLapSmooth (I := I) g 0 2 T
  let HT := iteratedCovGrad (I := I) g 0 2 2 T
  let HLT := iteratedCovGrad (I := I) g 0 2 2 LT
  let Q : SmoothCcTensor g 0 2 → SmoothCcTensor g 2 2 := fun U =>
    ricciDeTurckTopOrderBilinearPairingCoefficient (I := I) (M := M) g T U hdelta hdeltaZ
      ricciDecompositionQA ricciDecompositionQB lieDecompositionQ lieDecompositionEps s
  let Z := operatorFieldApply (I := I) (M := M) g 2 2 (Q T) T
  let Cross := operatorFieldApply (I := I) (M := M) g 2 2 (Q LT) T +
    operatorFieldApply (I := I) (M := M) g 2 2 (Q T) LT
  let PairComm := oneMinusConnLapSmooth (I := I) g 0 2 Z -
    operatorFieldApply (I := I) (M := M) g 2 2 (Q LT) T -
    operatorFieldApply (I := I) (M := M) g 2 2 (Q T) LT + Z
  let C : SmoothCcTensor g 4 2 :=
    deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gs -
      deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g
  let J := oneMinusConnLapSmooth (I := I) g 0 2
      (operatorFieldApply (I := I) (M := M) g 2 2 (R0 + K0) T) +
    PairComm +
    (oneMinusConnLapSmooth (I := I) g 0 2
        (operatorFieldApply (I := I) (M := M) g 4 2 C HT) -
      operatorFieldApply (I := I) (M := M) g 4 2 C HLT) - Z
  let A := RicciDeTurckLowOrder.pathIntegrand
      (I := I) (M := M) g gBase T hdelta hdeltaZ s + K0
  let B : SmoothCcTensor g 4 2 :=
    lieDecomposition2 (I := I) (M := M) g T hdelta hdeltaZ s + C +
      (-2 * s : ℝ) • RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient
        (I := I) (M := M) g gs T
  let Gcurv := covGrad (I := I) (M := M) g 0 3
      (pointwiseTensorCurv (I := I) (M := M) g 2 T) +
    pointwiseTensorCurv (I := I) (M := M) g 3
      (covGrad (I := I) (M := M) g 0 2 T)
  let V := oneMinusConnLapSmooth (I := I) g 0 2
    (oneMinusConnLapSmooth (I := I) g 0 2 LT)
  let Tr := DifferentialGeometry.Analysis.Spectral.DeTurck.cometricDoubleTraceField
    (I := I) g 2
  let P20 := operatorFieldApply (I := I) (M := M) g 4 2 Tr
      (operatorFieldApply (I := I) (M := M) g 4 4
        (covGrad (I := I) (M := M) g 4 3
          (covGrad (I := I) (M := M) g 4 2 B)) HT)
  let P11L := operatorFieldApply (I := I) (M := M) g 4 2 Tr
      (operatorFieldApply (I := I) (M := M) g 5 4
        (slotExtend (I := I) (M := M) g 4 3
          (covGrad (I := I) (M := M) g 4 2 B))
        (covGrad (I := I) (M := M) g 0 4 HT))
  let P11R := operatorFieldApply (I := I) (M := M) g 4 2 Tr
      (operatorFieldApply (I := I) (M := M) g 5 4
        (covGrad (I := I) (M := M) g 5 3
          (slotExtend (I := I) (M := M) g 4 2 B))
        (covGrad (I := I) (M := M) g 0 4 HT))
  let Yc := oneMinusConnLapSmooth (I := I) g 0 2
    (operatorFieldApply (I := I) (M := M) g 2 2 A T)
  let Yp := operatorFieldApply (I := I) (M := M) g 4 2 (B - C) HLT
  let Yd := operatorFieldApply (I := I) (M := M) g 4 2 B Gcurv
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let q : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖
  let z : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖
  intro hcarrier
  have hy : 0 ≤ y := norm_nonneg _
  have hq : 0 ≤ q := norm_nonneg _
  have hz : 0 ≤ z := norm_nonneg _
  have hdelta_quarter : delta ≤ 1 / 4 :=
    hdelta_le.trans (min_le_left _ _)
  have hdelta_third : delta ≤ 1 / 3 := hdelta_le.trans hdelta2third
  have hbase : 0 < 1 - delta := by linarith
  have hsquare : (1 / 2 : ℝ) ≤ (1 - delta) ^ 2 := by
    nlinarith [sq_nonneg delta]
  let rate : ℝ := delta / (1 - delta) ^ 2
  have hrate : rate ≤ 2 * delta := by
    dsimp only [rate]
    rw [div_le_iff₀ (sq_pos_of_pos hbase)]
    nlinarith [mul_le_mul_of_nonneg_left hsquare hdelta0]
  have hdelta_frac : delta ≤ e / (4 * (C5 + 1)) :=
    hdelta_le.trans (min_le_right _ _)
  have hdelta_scaled : delta * (4 * (C5 + 1)) ≤ e :=
    (le_div_iff₀ (mul_pos (by norm_num) hC5p)).mp hdelta_frac
  have hC5rate : 2 * C5 * rate ≤ e := by
    have h1 : 2 * C5 * rate ≤ 4 * C5 * delta := by
      calc
        2 * C5 * rate ≤ 2 * C5 * (2 * delta) :=
          mul_le_mul_of_nonneg_left hrate (mul_nonneg (by norm_num) hC5)
        _ = 4 * C5 * delta := by ring
    have h2 : 4 * C5 * delta ≤ e := by
      calc
        4 * C5 * delta ≤ 4 * (C5 + 1) * delta := by
          apply mul_le_mul_of_nonneg_right _ hdelta0
          nlinarith
        _ ≤ e := by nlinarith
    exact h1.trans h2
  have hRrhoP : R ≤ rhoP :=
    hRle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRrhoD : R ≤ rhoD :=
    hRle.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hRrhoK : R ≤ rhoK :=
    hRle.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hp := hprincipal g hEq hjet T hTsymm hdelta_third hdelta0
    hdelta hdeltaZ (hT2.trans hRrhoP) hs T
  have hd := hdefectG T hTsymm hdelta_third hdelta0 hdelta hdeltaZ
    (hT2.trans hRrhoD) hs
  have hk := hcornerG T hTsymm hdelta_third hdelta0 hdelta hdeltaZ
    (hT2.trans hRrhoK) hs
  have hprincipal' :
      2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun Yp.toFun| ≤
        C4 * q ^ 2 + 2 * e * z ^ 2 + Gmix * y ^ 2 * q ^ 2 := by
    have hlow : 2 * C4 * rate * q ^ 2 ≤ C4 * q ^ 2 := by
      have hratehalf : 2 * rate ≤ 1 := by
        calc
          2 * rate ≤ 2 * (2 * delta) :=
            mul_le_mul_of_nonneg_left hrate (by norm_num)
          _ = 4 * delta := by ring
          _ ≤ 4 * (1 / 4 : ℝ) :=
            mul_le_mul_of_nonneg_left hdelta_quarter (by norm_num)
          _ = 1 := by norm_num
      calc
        2 * C4 * rate * q ^ 2 = (C4 * (2 * rate)) * q ^ 2 := by ring
        _ ≤ (C4 * 1) * q ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hratehalf hC4) (sq_nonneg q)
        _ = C4 * q ^ 2 := by ring
    have hmix : 2 * Cmix * y * z * q ≤
        e * z ^ 2 + Gmix * y ^ 2 * q ^ 2 := by
      calc
        2 * Cmix * y * z * q = 2 * z * (Cmix * y * q) := by ring
        _ ≤ e * z ^ 2 + e⁻¹ * (Cmix * y * q) ^ 2 := two_mul_le_eps he
        _ = e * z ^ 2 + Gmix * y ^ 2 * q ^ 2 := by
          dsimp only [Gmix]
          ring
    have htop : 2 * C5 * rate * z ^ 2 ≤ e * z ^ 2 :=
      mul_le_mul_of_nonneg_right hC5rate (sq_nonneg z)
    have hp' :
        |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun Yp.toFun| ≤
          C4 * rate * q ^ 2 + Cmix * y * z * q + C5 * rate * z ^ 2 := by
      have hYp : Yp = operatorFieldApply (I := I) (M := M) g 4 2
          (lieDecomposition2 (I := I) (M := M) g T hdelta hdeltaZ s +
            (-2 * s : ℝ) • RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient
              (I := I) (M := M) g gs T) HLT := by
        dsimp only [Yp, B]
        congr 1
        module
      rw [hYp]
      simpa only [V, LT, HLT, gs, rate, y, q, z] using hp
    calc
      2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun Yp.toFun| ≤
          2 * (C4 * rate * q ^ 2 + Cmix * y * z * q +
            C5 * rate * z ^ 2) :=
        mul_le_mul_of_nonneg_left hp' (by norm_num)
      _ = 2 * C4 * rate * q ^ 2 + 2 * Cmix * y * z * q +
          2 * C5 * rate * z ^ 2 := by ring
      _ ≤ C4 * q ^ 2 + (e * z ^ 2 + Gmix * y ^ 2 * q ^ 2) +
          e * z ^ 2 := add_le_add (add_le_add hlow hmix) htop
      _ = C4 * q ^ 2 + 2 * e * z ^ 2 + Gmix * y ^ 2 * q ^ 2 := by ring
  have hdefect' :
      2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun Yd.toFun| ≤
        e * z ^ 2 + Gd * y ^ 4 := by
    simpa only [Yd, B, C, Gcurv, V, LT, gs, y, z] using hd
  have hcorner' :
      2 * (|tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P20.toFun| +
          |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P11L.toFun| +
          |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P11R.toFun|) ≤
        e * z ^ 2 + Gcorner * y ^ 2 * q ^ 2 := by
    have hk' :
        2 * (|tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P20.toFun| +
            |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P11L.toFun| +
            |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P11R.toFun|) ≤
          Gk * y * q * z := by
      simpa only [P20, P11L, P11R, Tr, HT, B, gs, V, LT, y, q, z] using hk
    calc
      _ ≤ Gk * y * q * z := hk'
      _ = 2 * z * ((Gk * y * q) / 2) := by ring
      _ ≤ e * z ^ 2 + e⁻¹ * ((Gk * y * q) / 2) ^ 2 := two_mul_le_eps he
      _ ≤ e * z ^ 2 + Gcorner * y ^ 2 * q ^ 2 := by
        refine add_le_add le_rfl ?_
        calc
          e⁻¹ * ((Gk * y * q) / 2) ^ 2 =
              (1 / 4 : ℝ) * (Gcorner * y ^ 2 * q ^ 2) := by
            dsimp only [Gcorner]
            ring
          _ ≤ 1 * (Gcorner * y ^ 2 * q ^ 2) :=
            mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
          _ = Gcorner * y ^ 2 * q ^ 2 := one_mul _
  have hpeel := ricciDeTurck_remainder_centered_commutator_decomposition (I := I) (M := M) g gBase T hTsymm
    (lt_of_le_of_lt hdelta_third (by norm_num)) hdelta hdeltaZ s hs
  have hgs : metricPerturbationPathFromZero (I := I) (M := M) g T hdelta s = gs :=
    metricComparisonEndomorphism_pairing_balance (I := I) (M := M) g T
      (lt_of_le_of_lt hdelta_third (by norm_num)) hdelta hdeltaZ hs
  dsimp only at hpeel
  rw [hgs] at hpeel
  have hpeel' : J = Yc + Yp - Yd - P20 - P11L - P11R - Cross := by
    simpa only [J, Cross, Yc, Yp, Yd, A, B, C, Gcurv, P20, P11L, P11R,
      Tr, PairComm, Z, Q, HLT, HT, LT, K0, R0, gs] using hpeel
  have hnf : J + Cross = Yc + Yp - Yd - P20 - P11L - P11R := by
    rw [hpeel']
    module
  have hcarrier' :
      2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun Yc.toFun| ≤
        e * z ^ 2 + Lc := by
    simpa only [Yc, V, A, LT, e, z] using hcarrier
  have hfinal := center_sum_h5 (I := I) (M := M) g V J Cross Yc Yp Yd
    P20 P11L P11R eta e Lc C4 Gmix Gd Gcorner G y q z rfl rfl
    hC4 hGmix hGd hGcorner hnf hcarrier' hprincipal' hdefect' hcorner'
  generalize hleft :
      2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun (J + Cross).toFun| = lhs
      at hfinal ⊢
  generalize hright :
      eta * z ^ 2 + Lc + G * (q ^ 2 + y ^ 2 * q ^ 2 + y ^ 4) = rhs
      at hfinal ⊢
  exact hfinal

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end

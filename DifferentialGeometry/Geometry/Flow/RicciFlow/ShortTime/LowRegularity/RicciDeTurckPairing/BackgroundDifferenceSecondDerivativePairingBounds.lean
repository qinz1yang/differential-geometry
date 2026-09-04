import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Action.CenteredTopOrderCommutator
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Pairing.MixedDerivativeH4Bounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Pairing.CurvatureCommutatorH4Bounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Pairing.TopKernelBounds

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.CheegerGromovCompactness
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

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

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

theorem edge_center_pairing_abs_of_carrier_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∀ {eta : ℝ}, 0 < eta →
      ∃ delta2 R2 : ℝ,
        0 < delta2 ∧ delta2 ≤ 1 / 3 ∧ 0 < R2 ∧ R2 ≤ 1 ∧
        ∀ g : SmoothRiemannianMetric I M,
          MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
          (∀ a : ℕ, a ≤ 3 →
            MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
          ∃ Gd : ℝ, 0 ≤ Gd ∧
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
              let V := oneMinusConnLapSmooth (I := I) g 0 2 LT
              2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun
                    (oneMinusConnLapSmooth (I := I) g 0 2
                      (operatorFieldApply (I := I) (M := M) g 2 2 A T)).toFun| ≤
                  (eta / 4) *
                      ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
                    Lc →
                2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun
                    (J + Cross).toFun| ≤
                  eta * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
                    Lc + Gd *
                      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 := by
  intro eta heta
  let e : ℝ := eta / 4
  have he : 0 < e := by
    dsimp only [e]
    positivity
  obtain ⟨delta2, hdelta2, hdelta2third, hprincipal⟩ :=
    bcD2_pair_abs_uniform (I := I) (M := M) gBase hΛ he
  obtain ⟨rho, Ccorner, hrho, hCcorner, hcorner⟩ :=
    mixed_derivative_action_pairing_h4_uniform_bound (I := I) (M := M) hDim gBase hΛ
  let R2 : ℝ := min 1 (min rho (e / (Ccorner + 1)))
  have hden : 0 < Ccorner + 1 := by linarith
  have hR2 : 0 < R2 := by
    dsimp only [R2]
    exact lt_min zero_lt_one (lt_min hrho (div_pos he hden))
  have hR2one : R2 ≤ 1 := min_le_left _ _
  refine ⟨delta2, R2, hdelta2, hdelta2third, hR2, hR2one, ?_⟩
  intro g hEq hjet
  obtain ⟨Gd, hGd, hdefect⟩ :=
    curvature_commutator_pairing_h4_uniform_bound (I := I) (M := M) gBase hΛ he g hEq hjet
  refine ⟨Gd, hGd, ?_⟩
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
  let G := covGrad (I := I) (M := M) g 0 3
      (pointwiseTensorCurv (I := I) (M := M) g 2 T) +
    pointwiseTensorCurv (I := I) (M := M) g 3
      (covGrad (I := I) (M := M) g 0 2 T)
  let V := oneMinusConnLapSmooth (I := I) g 0 2 LT
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
  let Yd := operatorFieldApply (I := I) (M := M) g 4 2 B G
  intro hcarrier
  have hdelta_third : delta ≤ 1 / 3 := hdelta_le.trans hdelta2third
  have hRrho : R ≤ rho :=
    hRle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRsmall : R ≤ e / (Ccorner + 1) :=
    hRle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hCR : Ccorner * R ≤ e := by
    have hfrac : Ccorner / (Ccorner + 1) ≤ 1 :=
      (div_le_one hden).2 (by linarith)
    calc
      Ccorner * R ≤ Ccorner * (e / (Ccorner + 1)) :=
        mul_le_mul_of_nonneg_left hRsmall hCcorner
      _ = e * (Ccorner / (Ccorner + 1)) := by
        simp only [div_eq_mul_inv]
        ring
      _ ≤ e * 1 := mul_le_mul_of_nonneg_left hfrac he.le
      _ = e := mul_one _
  have hp := hprincipal g hEq hjet T hTsymm hdelta_le hdelta0
    hdelta hdeltaZ hs T
  have hd := hdefect T hTsymm hdelta_third hdelta0 hdelta hdeltaZ hs
  have hk := hcorner g hEq hjet T hTsymm hdelta_third hdelta0
    hdelta hdeltaZ hs hR hRrho hT2
  have hcorners :
      2 * (|tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P20.toFun| +
          |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P11L.toFun| +
          |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P11R.toFun|) ≤
        e * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 := by
    calc
      _ ≤ Ccorner * R *
          ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 := by
        simpa only [B, C, gs, HT, V, Tr, P20, P11L, P11R] using hk
      _ ≤ e * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hCR (sq_nonneg _)
  have hpeel := ricciDeTurck_remainder_centered_commutator_decomposition (I := I) (M := M) g gBase T hTsymm
    (lt_of_le_of_lt hdelta_third (by norm_num)) hdelta hdeltaZ s hs
  have hgs : metricPerturbationPathFromZero (I := I) (M := M) g T hdelta s = gs :=
    metricComparisonEndomorphism_pairing_balance (I := I) (M := M) g T
      (lt_of_le_of_lt hdelta_third (by norm_num)) hdelta hdeltaZ hs
  dsimp only at hpeel
  rw [hgs] at hpeel
  have hpeel' : J = Yc + Yp - Yd - P20 - P11L - P11R - Cross := by
    simpa only [J, Cross, Yc, Yp, Yd, A, B, C, G, P20, P11L, P11R,
      Tr, PairComm, Z, Q, HLT, HT, LT, K0, R0, gs] using hpeel
  have hnf : J + Cross = Yc + Yp - Yd - P20 - P11L - P11R := by
    rw [hpeel']
    module
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
  have hYp : Yp = operatorFieldApply (I := I) (M := M) g 4 2
      (lieDecomposition2 (I := I) (M := M) g T hdelta hdeltaZ s +
        (-2 * s : ℝ) • RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient
          (I := I) (M := M) g gs T) HLT := by
    dsimp only [Yp, B]
    congr 1
    module
  have hp' :
      2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun Yp.toFun| ≤
        e * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 := by
    rw [hYp]
    simpa only [V, LT, HLT, gs] using hp
  have hd' :
      2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun Yd.toFun| ≤
        e * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
          Gd * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 := by
    simpa only [Yd, B, C, G, V, LT, gs] using hd
  have hc' :
      2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun Yc.toFun| ≤
        e * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
          Lc := by
    simpa only [Yc, V, A, K0, LT, e] using hcarrier
  have hfirst :
      2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun
        (J + Cross).toFun| ≤ 2 *
        (|tensorL2Inner (I := I) (M := M) g 0 2 V.toFun Yc.toFun| +
          |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun Yp.toFun| +
          |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun Yd.toFun| +
          |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P20.toFun| +
          |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P11L.toFun| +
          |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P11R.toFun|) :=
    mul_le_mul_of_nonneg_left habs (by norm_num)
  have hsecond :
      2 *
        (|tensorL2Inner (I := I) (M := M) g 0 2 V.toFun Yc.toFun| +
          |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun Yp.toFun| +
          |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun Yd.toFun| +
          |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P20.toFun| +
          |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P11L.toFun| +
          |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun P11R.toFun|) ≤
        (e + e + e + e) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
        Lc + Gd *
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 := by
    nlinarith only [hc', hp', hd', hcorners]
  have hthird :
      (e + e + e + e) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
        Lc + Gd *
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 =
        eta * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
        Lc + Gd *
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 := by
    dsimp only [e]
    ring
  have hfinal := hfirst.trans (hsecond.trans_eq hthird)
  simpa only [V, LT, J, R0, K0, PairComm, Z, Q, C, gs, Cross] using hfinal

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end

import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.CenteredTopOrderDecomposition
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RemainderAction

noncomputable section


open Bundle Manifold Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff RealInnerProductSpace BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
      [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
private theorem operatorFieldApplication_sub_right_ec
    (g : SmoothRiemannianMetric I M) (r s : Nat)
    (Phi : SmoothCcTensor g r s) (W1 W2 : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) g r s Phi (W1 - W2) =
      operatorFieldApply (I := I) (M := M) g r s Phi W1 -
        operatorFieldApply (I := I) (M := M) g r s Phi W2 := by
  have h : operatorFieldApply (I := I) (M := M) g r s Phi (W1 - W2) +
      operatorFieldApply (I := I) (M := M) g r s Phi W2 =
        operatorFieldApply (I := I) (M := M) g r s Phi W1 := by
    rw [← operatorFieldApplication_add_right]
    congr 1
    abel
  exact eq_sub_of_add_eq h

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem centered_commutator_finish
    {g : SmoothRiemannianMetric I M}
    (J LA LB BH CH BC BG P20 P11L P11R Cross : SmoothCcTensor g 0 2)
    (hJ : J = LA + LB - CH - Cross)
    (hLtop : LB = BH - BG - P20 - P11L - P11R)
    (hsub : BC = BH - CH) :
    J = LA + BC - BG - P20 - P11L - P11R - Cross := by
  rw [hJ, hLtop, hsub]
  module

omit [SigmaCompactSpace M] in
theorem ricciDeTurck_remainder_centered_commutator_decomposition
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g T x v w =
        ccTensorBilin (I := I) g T x w v)
    {delta : Real} (hdelta_lt : delta < 1)
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) delta)
    (s : Real) (hs : s ∈ Set.Icc (0 : Real) 1) :
    let gs : SmoothRiemannianMetric I M :=
      metricPerturbationPathFromZero (I := I) (M := M) g T hdelta s
    let R0 : SmoothCcTensor g 2 2 :=
      rhsDecomposition0 (I := I) (M := M) g g_bg T hdelta hdeltaZ s
    let K0 : SmoothCcTensor g 2 2 := metricPrincipalDefectCurvCoeff (I := I) g g
    let LT : SmoothCcTensor g 0 2 := oneMinusConnLapSmooth (I := I) g 0 2 T
    let HT : SmoothCcTensor g 0 4 := iteratedCovGrad (I := I) g 0 2 2 T
    let HLT : SmoothCcTensor g 0 4 := iteratedCovGrad (I := I) g 0 2 2 LT
    let Q : SmoothCcTensor g 0 2 → SmoothCcTensor g 2 2 := fun U =>
      ricciDeTurckTopOrderBilinearPairingCoefficient (I := I) (M := M) g T U hdelta hdeltaZ
        ricciDecompositionQA ricciDecompositionQB lieDecompositionQ lieDecompositionEps s
    let Z : SmoothCcTensor g 0 2 :=
      operatorFieldApply (I := I) (M := M) g 2 2 (Q T) T
    let Cross : SmoothCcTensor g 0 2 :=
      operatorFieldApply (I := I) (M := M) g 2 2 (Q LT) T +
        operatorFieldApply (I := I) (M := M) g 2 2 (Q T) LT
    let PairComm : SmoothCcTensor g 0 2 :=
      oneMinusConnLapSmooth (I := I) g 0 2 Z -
        operatorFieldApply (I := I) (M := M) g 2 2 (Q LT) T -
        operatorFieldApply (I := I) (M := M) g 2 2 (Q T) LT + Z
    let C : SmoothCcTensor g 4 2 :=
      deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gs -
        deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g
    let J : SmoothCcTensor g 0 2 :=
      oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 2 2 (R0 + K0) T) +
        PairComm +
        (oneMinusConnLapSmooth (I := I) g 0 2
            (operatorFieldApply (I := I) (M := M) g 4 2 C HT) -
          operatorFieldApply (I := I) (M := M) g 4 2 C HLT) - Z
    let A : SmoothCcTensor g 2 2 :=
      RicciDeTurckLowOrder.pathIntegrand
          (I := I) (M := M) g g_bg T hdelta hdeltaZ s + K0
    let B : SmoothCcTensor g 4 2 :=
      lieDecomposition2 (I := I) (M := M) g T hdelta hdeltaZ s + C +
        (-2 * s : Real) • RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient
          (I := I) (M := M) g gs T
    let G : SmoothCcTensor g 0 4 :=
      covGrad (I := I) (M := M) g 0 3
          (pointwiseTensorCurv (I := I) (M := M) g 2 T) +
        pointwiseTensorCurv (I := I) (M := M) g 3
          (covGrad (I := I) (M := M) g 0 2 T)
    let Tr : SmoothCcTensor g 4 2 :=
      DeTurck.cometricDoubleTraceField (I := I) g 2
    let P20 : SmoothCcTensor g 0 2 :=
      operatorFieldApply (I := I) (M := M) g 4 2 Tr
        (operatorFieldApply (I := I) (M := M) g 4 4
          (covGrad (I := I) (M := M) g 4 3
            (covGrad (I := I) (M := M) g 4 2 B)) HT)
    let P11L : SmoothCcTensor g 0 2 :=
      operatorFieldApply (I := I) (M := M) g 4 2 Tr
        (operatorFieldApply (I := I) (M := M) g 5 4
          (slotExtend (I := I) (M := M) g 4 3
            (covGrad (I := I) (M := M) g 4 2 B))
          (covGrad (I := I) (M := M) g 0 4 HT))
    let P11R : SmoothCcTensor g 0 2 :=
      operatorFieldApply (I := I) (M := M) g 4 2 Tr
        (operatorFieldApply (I := I) (M := M) g 5 4
          (covGrad (I := I) (M := M) g 5 3
            (slotExtend (I := I) (M := M) g 4 2 B))
          (covGrad (I := I) (M := M) g 0 4 HT))
    J =
      oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 2 2 A T) +
        operatorFieldApply (I := I) (M := M) g 4 2 (B - C) HLT -
        operatorFieldApply (I := I) (M := M) g 4 2 B G -
        P20 - P11L - P11R - Cross := by
  classical
  let gs : SmoothRiemannianMetric I M :=
    metricPerturbationPathFromZero (I := I) (M := M) g T hdelta s
  let R0 : SmoothCcTensor g 2 2 :=
    rhsDecomposition0 (I := I) (M := M) g g_bg T hdelta hdeltaZ s
  let K0 : SmoothCcTensor g 2 2 := metricPrincipalDefectCurvCoeff (I := I) g g
  let LT : SmoothCcTensor g 0 2 := oneMinusConnLapSmooth (I := I) g 0 2 T
  let HT : SmoothCcTensor g 0 4 := iteratedCovGrad (I := I) g 0 2 2 T
  let HLT : SmoothCcTensor g 0 4 := iteratedCovGrad (I := I) g 0 2 2 LT
  let Q : SmoothCcTensor g 0 2 → SmoothCcTensor g 2 2 := fun U =>
    ricciDeTurckTopOrderBilinearPairingCoefficient (I := I) (M := M) g T U hdelta hdeltaZ
      ricciDecompositionQA ricciDecompositionQB lieDecompositionQ lieDecompositionEps s
  let Z : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 2 2 (Q T) T
  let Cross : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 2 2 (Q LT) T +
      operatorFieldApply (I := I) (M := M) g 2 2 (Q T) LT
  let PairComm : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 Z -
      operatorFieldApply (I := I) (M := M) g 2 2 (Q LT) T -
      operatorFieldApply (I := I) (M := M) g 2 2 (Q T) LT + Z
  let C : SmoothCcTensor g 4 2 :=
    deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gs -
      deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g
  let J : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2
        (operatorFieldApply (I := I) (M := M) g 2 2 (R0 + K0) T) +
      PairComm +
      (oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 4 2 C HT) -
        operatorFieldApply (I := I) (M := M) g 4 2 C HLT) - Z
  let A : SmoothCcTensor g 2 2 :=
    RicciDeTurckLowOrder.pathIntegrand
        (I := I) (M := M) g g_bg T hdelta hdeltaZ s + K0
  let B : SmoothCcTensor g 4 2 :=
    lieDecomposition2 (I := I) (M := M) g T hdelta hdeltaZ s + C +
      (-2 * s : Real) • RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient
        (I := I) (M := M) g gs T
  let G : SmoothCcTensor g 0 4 :=
    covGrad (I := I) (M := M) g 0 3
        (pointwiseTensorCurv (I := I) (M := M) g 2 T) +
      pointwiseTensorCurv (I := I) (M := M) g 3
        (covGrad (I := I) (M := M) g 0 2 T)
  let Tr : SmoothCcTensor g 4 2 :=
    DeTurck.cometricDoubleTraceField (I := I) g 2
  let P20 : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 4 2 Tr
      (operatorFieldApply (I := I) (M := M) g 4 4
        (covGrad (I := I) (M := M) g 4 3
          (covGrad (I := I) (M := M) g 4 2 B)) HT)
  let P11L : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 4 2 Tr
      (operatorFieldApply (I := I) (M := M) g 5 4
        (slotExtend (I := I) (M := M) g 4 3
          (covGrad (I := I) (M := M) g 4 2 B))
        (covGrad (I := I) (M := M) g 0 4 HT))
  let P11R : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 4 2 Tr
      (operatorFieldApply (I := I) (M := M) g 5 4
        (covGrad (I := I) (M := M) g 5 3
          (slotExtend (I := I) (M := M) g 4 2 B))
        (covGrad (I := I) (M := M) g 0 4 HT))
  have hself :
      operatorFieldApply (I := I) (M := M) g 2 2 R0 T =
        operatorFieldApply (I := I) (M := M) g 2 2
            (RicciDeTurckLowOrder.pathIntegrand
              (I := I) (M := M) g g_bg T hdelta hdeltaZ s) T +
          operatorFieldApply (I := I) (M := M) g 4 2
            (RicciDeTurckLowOrder.ricciDeTurckSelfTopOrderCoefficient
              (I := I) (M := M) g T hdelta hdeltaZ s) HT := by
    dsimp only [R0, HT]
    exact RicciDeTurckLowOrder.self_remainder_decomposition
      (I := I) (M := M) g g_bg T hTsymm
        hdelta_lt hdelta hdeltaZ hs
  have hQ :
      Z = operatorFieldApply (I := I) (M := M) g 4 2
        (rhsDecomposition2 (I := I) (M := M) g T hdelta hdeltaZ s) HT := by
    dsimp only [Z, Q, HT]
    rw [ricciDeTurckTopOrderBilinearPairingCoefficient_eq_coefficientForJet]
    simpa only [rhsDecomposition2, ricciDecomposition2, lieDecomposition2] using
      ricciDeTurckTopOrderPairingCoefficientForJet_apply (I := I) (M := M) g T
        (iteratedCovGrad (I := I) g 0 2 2 T) hdelta hdeltaZ
          ricciDecompositionQA ricciDecompositionQB lieDecompositionQ lieDecompositionEps s
  have hB :
      rhsDecomposition2 (I := I) (M := M) g T hdelta hdeltaZ s +
          RicciDeTurckLowOrder.ricciDeTurckSelfTopOrderCoefficient
            (I := I) (M := M) g T hdelta hdeltaZ s + C = B := by
    have hmetric := metricComparisonEndomorphism_pairing_balance (I := I) (M := M) g T
      hdelta_lt hdelta hdeltaZ hs
    have hkernel := RicciDeTurckLowOrder.topKernel_eq
      (I := I) (M := M) g T hdelta hdeltaZ s
    dsimp only [B, C, gs]
    rw [hmetric]
    dsimp only at hkernel
    rw [← hkernel]
    simp only [rhsDecompositionTop]
    module
  have hBapp := congrArg
    (fun F : SmoothCcTensor g 4 2 =>
      operatorFieldApply (I := I) (M := M) g 4 2 F HT) hB
  simp only [operatorFieldApplication_add_left] at hBapp
  have hinside :
      operatorFieldApply (I := I) (M := M) g 2 2 (R0 + K0) T + Z +
          operatorFieldApply (I := I) (M := M) g 4 2 C HT =
        operatorFieldApply (I := I) (M := M) g 2 2 A T +
          operatorFieldApply (I := I) (M := M) g 4 2 B HT := by
    dsimp only [A]
    simp only [operatorFieldApplication_add_left]
    have hself' :
        operatorFieldApply (I := I) (M := M) g 2 2 R0 T =
          operatorFieldApply (I := I) (M := M) g 2 2
              (RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
                g g_bg T hdelta hdeltaZ s) T +
            operatorFieldApply (I := I) (M := M) g 4 2
              (RicciDeTurckLowOrder.ricciDeTurckSelfTopOrderCoefficient (I := I) (M := M)
                g T hdelta hdeltaZ s) HT := hself
    rw [hself', hQ]
    rw [← hBapp]
    module
  have hJ :
      J =
        oneMinusConnLapSmooth (I := I) g 0 2
            (operatorFieldApply (I := I) (M := M) g 2 2 A T) +
          oneMinusConnLapSmooth (I := I) g 0 2
            (operatorFieldApply (I := I) (M := M) g 4 2 B HT) -
          operatorFieldApply (I := I) (M := M) g 4 2 C HLT - Cross := by
    dsimp only [J, PairComm]
    calc
      oneMinusConnLapSmooth (I := I) g 0 2
            (operatorFieldApply (I := I) (M := M) g 2 2 (R0 + K0) T) +
          (oneMinusConnLapSmooth (I := I) g 0 2 Z -
              operatorFieldApply (I := I) (M := M) g 2 2 (Q LT) T -
              operatorFieldApply (I := I) (M := M) g 2 2 (Q T) LT + Z) +
          (oneMinusConnLapSmooth (I := I) g 0 2
              (operatorFieldApply (I := I) (M := M) g 4 2 C HT) -
            operatorFieldApply (I := I) (M := M) g 4 2 C HLT) - Z =
        (oneMinusConnLapSmooth (I := I) g 0 2
            (operatorFieldApply (I := I) (M := M) g 2 2 (R0 + K0) T) +
          oneMinusConnLapSmooth (I := I) g 0 2 Z +
          oneMinusConnLapSmooth (I := I) g 0 2
            (operatorFieldApply (I := I) (M := M) g 4 2 C HT)) -
          operatorFieldApply (I := I) (M := M) g 4 2 C HLT - Cross := by
            dsimp only [Cross]
            module
      _ = oneMinusConnLapSmooth (I := I) g 0 2
            (operatorFieldApply (I := I) (M := M) g 2 2 (R0 + K0) T + Z +
              operatorFieldApply (I := I) (M := M) g 4 2 C HT) -
          operatorFieldApply (I := I) (M := M) g 4 2 C HLT - Cross := by
            rw [oneMinusConn_add (I := I) (M := M) g 0 2,
              oneMinusConn_add (I := I) (M := M) g 0 2]
      _ = oneMinusConnLapSmooth (I := I) g 0 2
            (operatorFieldApply (I := I) (M := M) g 2 2 A T +
              operatorFieldApply (I := I) (M := M) g 4 2 B HT) -
          operatorFieldApply (I := I) (M := M) g 4 2 C HLT - Cross := by
            rw [hinside]
      _ = oneMinusConnLapSmooth (I := I) g 0 2
              (operatorFieldApply (I := I) (M := M) g 2 2 A T) +
            oneMinusConnLapSmooth (I := I) g 0 2
              (operatorFieldApply (I := I) (M := M) g 4 2 B HT) -
          operatorFieldApply (I := I) (M := M) g 4 2 C HLT - Cross := by
            rw [oneMinusConn_add (I := I) (M := M) g 0 2]
  have hHLT :
      HLT = HT - iteratedCovGrad (I := I) g 0 2 2
        (rawTensorConnLapSmooth (I := I) g 0 2 T) := by
    dsimp only [HLT, HT, LT, oneMinusConnLapSmooth]
    rw [iteratedCovGrad_sub]
  have hprod := rawTensorConnLap_operatorFieldApplication_comm_of_rank
    (I := I) (M := M) g 4 2 B HT
  have harg := rawConnLap_iteratedCovGrad_two_comm
    (I := I) (M := M) g 2 T
  have hLtop :
      oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 4 2 B HT) =
        operatorFieldApply (I := I) (M := M) g 4 2 B HLT -
          operatorFieldApply (I := I) (M := M) g 4 2 B G -
          P20 - P11L - P11R := by
    dsimp only [oneMinusConnLapSmooth]
    rw [hprod, harg]
    simp only [operatorFieldApplication_add_right]
    rw [hHLT, operatorFieldApplication_sub_right_ec]
    dsimp only [G, P20, P11L, P11R, Tr]
    simp only [operatorFieldApplication_add_right]
    module
  have hsub :
      operatorFieldApply (I := I) (M := M) g 4 2 (B - C) HLT =
        operatorFieldApply (I := I) (M := M) g 4 2 B HLT -
          operatorFieldApply (I := I) (M := M) g 4 2 C HLT :=
    operatorFieldApplication_sub_left (I := I) (M := M) g 4 2 B C HLT
  have hfinal := centered_commutator_finish J
    (oneMinusConnLapSmooth (I := I) g 0 2
      (operatorFieldApply (I := I) (M := M) g 2 2 A T))
    (oneMinusConnLapSmooth (I := I) g 0 2
      (operatorFieldApply (I := I) (M := M) g 4 2 B HT))
    (operatorFieldApply (I := I) (M := M) g 4 2 B HLT)
    (operatorFieldApply (I := I) (M := M) g 4 2 C HLT)
    (operatorFieldApply (I := I) (M := M) g 4 2 (B - C) HLT)
    (operatorFieldApply (I := I) (M := M) g 4 2 B G)
    P20 P11L P11R Cross hJ hLtop hsub
  simpa only [gs, R0, K0, LT, HT, HLT, Q, Z, Cross, PairComm, C, J,
    A, B, G, Tr, P20, P11L, P11R] using hfinal

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end

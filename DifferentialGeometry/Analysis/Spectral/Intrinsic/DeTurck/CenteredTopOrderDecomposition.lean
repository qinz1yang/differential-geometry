import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.TopOrderPairingPolarization
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHSZeroDecomposition
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ConnLapPairing
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.RoughLaplacianOperatorFieldApplicationCommutation

noncomputable section


open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open Bundle Manifold Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff RealInnerProductSpace BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

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

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem ricciDeTurckTopOrderBilinearPairingCoefficient_eq_six_term_sum
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) delta)
    (s : Real) :
    let gm := metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s
    let G := iteratedCovGrad (I := I) g 0 2 2 U
    ricciDeTurckTopOrderBilinearPairingCoefficient (I := I) (M := M) g T U hdelta hdeltaZ
        ricciDecompositionQA ricciDecompositionQB lieDecompositionQ lieDecompositionEps s =
      (s / 2) •
        (topOrderPairingCoefficient (I := I) (M := M) g gm G (ricciDecompositionQA 1) +
          topOrderPairingCoefficient (I := I) (M := M) g gm G (ricciDecompositionQB 1) -
          topOrderPairingCoefficient (I := I) (M := M) g gm G (ricciDecompositionQA 3) -
          topOrderPairingCoefficient (I := I) (M := M) g gm G (ricciDecompositionQB 3) -
          topOrderPairingCoefficient (I := I) (M := M) g gm G (lieDecompositionQ 1) -
          topOrderPairingCoefficient (I := I) (M := M) g gm G
            ((lieDecompositionQ 1).trans (Equiv.swap (0 : Fin 4) 1))) := by
  classical
  have hB0 : ricciDecompositionQB 0 = lieDecompositionQ 0 := by
    apply Equiv.ext
    intro i
    fin_cases i <;> rfl
  have hA0 : ricciDecompositionQA 0 =
      (lieDecompositionQ 0).trans (Equiv.swap (0 : Fin 4) 1) := by
    apply Equiv.ext
    intro i
    fin_cases i <;> rfl
  have hA2 : ricciDecompositionQA 2 = lieDecompositionQ 2 := by
    apply Equiv.ext
    intro i
    fin_cases i <;> rfl
  have hB2 : ricciDecompositionQB 2 =
      (lieDecompositionQ 2).trans (Equiv.swap (0 : Fin 4) 1) := by
    apply Equiv.ext
    intro i
    fin_cases i <;> rfl
  simp only [ricciDeTurckTopOrderBilinearPairingCoefficient, ricciDeTurckTopOrderPairingCoefficientForJet, riemannTopOrderPairingCoefficient, Fin.sum_univ_three]
  rw [hB0, hA0, hA2, hB2]
  simp [lieDecompositionEps]
  module

omit [BoundarylessManifold I M] in
omit [I.Boundaryless] in
theorem ricciDeTurckTopOrderPairingCoefficientForJet_apply_eq_secondOrderDecomposition
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (G : SmoothCcTensor g 0 4) {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) delta)
    (s : Real) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (ricciDeTurckTopOrderPairingCoefficientForJet (I := I) (M := M) g T G hdelta hdeltaZ
          ricciDecompositionQA ricciDecompositionQB lieDecompositionQ lieDecompositionEps s) T =
      operatorFieldApply (I := I) (M := M) g 4 2
        (rhsDecomposition2 (I := I) (M := M) g T hdelta hdeltaZ s) G := by
  simpa only [rhsDecomposition2, ricciDecomposition2, lieDecomposition2] using
    ricciDeTurckTopOrderPairingCoefficientForJet_apply (I := I) (M := M) g T G hdelta hdeltaZ
      ricciDecompositionQA ricciDecompositionQB lieDecompositionQ lieDecompositionEps s

theorem ricciDeTurckTopOrderPairingCoefficientForJet_connLaplacian_identity
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) delta)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real)
    (s : Real) :
    ricciDeTurckTopOrderPairingCoefficientForJet (I := I) (M := M) g T
        (rawTensorConnLapSmooth (I := I) g 0 4
          (iteratedCovGrad (I := I) g 0 2 2 U))
        hdelta hdeltaZ qA qB q epsilon s =
      ricciDeTurckTopOrderPairingCoefficientForJet (I := I) (M := M) g T
        (iteratedCovGrad (I := I) g 0 2 2
            (rawTensorConnLapSmooth (I := I) g 0 2 U) +
          covGrad (I := I) (M := M) g 0 3
            (pointwiseTensorCurv (I := I) (M := M) g 2 U) +
          pointwiseTensorCurv (I := I) (M := M) g 3
            (covGrad (I := I) (M := M) g 0 2 U))
        hdelta hdeltaZ qA qB q epsilon s := by
  rw [rawConnLap_iteratedCovGrad_two_comm (I := I) (M := M) g 2 U]

theorem deTurckMetricPrincipalDefect_cometricDoubleTrace_commutator
    (g₀ g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) :
    let Φd : SmoothCcTensor g₀ 4 2 :=
      deTurckMetricPrincipalDefectTotal (I := I) (M := M) g₀ g -
        cometricDoubleTraceCoefficient (I := I) (M := M) g₀ g
    let K : SmoothCcTensor g₀ 2 2 :=
      metricPrincipalDefectCurvCoeff (I := I) g₀ g
    oneMinusConnLapSmooth (I := I) g₀ 0 2
          (operatorFieldApply (I := I) (M := M) g₀ 4 2 Φd
            (iteratedCovGrad (I := I) g₀ 0 2 2 S)) -
        operatorFieldApply (I := I) (M := M) g₀ 4 2 Φd
          (iteratedCovGrad (I := I) g₀ 0 2 2
            (oneMinusConnLapSmooth (I := I) g₀ 0 2 S)) =
      oneMinusConnLapSmooth (I := I) g₀ 0 2
          (operatorFieldApply (I := I) (M := M) g₀ 2 2 K S) -
        operatorFieldApply (I := I) (M := M) g₀ 2 2 K
          (oneMinusConnLapSmooth (I := I) g₀ 0 2 S) := by
  dsimp only
  have hS :
      operatorFieldApply (I := I) (M := M) g₀ 4 2
          (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g₀ g -
            cometricDoubleTraceCoefficient (I := I) (M := M) g₀ g)
          (iteratedCovGrad (I := I) g₀ 0 2 2 S) =
        operatorFieldApply (I := I) (M := M) g₀ 2 2
          (metricPrincipalDefectCurvCoeff (I := I) g₀ g)
          (iteratedCovGrad (I := I) g₀ 0 2 0 S) :=
    metricPrincipalDefect_curv_fold (I := I) (M := M) g₀ g S
  have hLS :
      operatorFieldApply (I := I) (M := M) g₀ 4 2
          (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g₀ g -
            cometricDoubleTraceCoefficient (I := I) (M := M) g₀ g)
          (iteratedCovGrad (I := I) g₀ 0 2 2
            (oneMinusConnLapSmooth (I := I) g₀ 0 2 S)) =
        operatorFieldApply (I := I) (M := M) g₀ 2 2
          (metricPrincipalDefectCurvCoeff (I := I) g₀ g)
          (iteratedCovGrad (I := I) g₀ 0 2 0
            (oneMinusConnLapSmooth (I := I) g₀ 0 2 S)) :=
    metricPrincipalDefect_curv_fold (I := I) (M := M) g₀ g
      (oneMinusConnLapSmooth (I := I) g₀ 0 2 S)
  rw [hS, hLS]
  simp only [iteratedCovGrad_zero]

theorem ricciDeTurck_remainder_centered_operator_decomposition
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
    let Ks : SmoothCcTensor g 2 2 := metricPrincipalDefectCurvCoeff (I := I) g gs
    let E0 : SmoothCcTensor g 2 2 := backgroundZeroOrderCoefficient (I := I) (M := M) g g_bg +
      metricDependentZeroOrderCoefficient (I := I) (M := M) g gs g_bg
    let Ds : SmoothCcTensor g 0 2 → SmoothCcTensor g 0 2 := fun W =>
      deTurckPrincipalCometricArm (I := I) (M := M) g gs W
    let LT : SmoothCcTensor g 0 2 := oneMinusConnLapSmooth (I := I) g 0 2 T
    let Q : SmoothCcTensor g 0 2 → SmoothCcTensor g 2 2 := fun U =>
      ricciDeTurckTopOrderBilinearPairingCoefficient (I := I) (M := M) g T U hdelta hdeltaZ
        ricciDecompositionQA ricciDecompositionQB lieDecompositionQ lieDecompositionEps s
    let Z : SmoothCcTensor g 0 2 := operatorFieldApply (I := I) (M := M) g 2 2 (Q T) T
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
            (operatorFieldApply (I := I) (M := M) g 4 2 C
              (iteratedCovGrad (I := I) g 0 2 2 T)) -
          operatorFieldApply (I := I) (M := M) g 4 2 C
            (iteratedCovGrad (I := I) g 0 2 2 LT)) - Z
    J =
      oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 2 2 E0 T) +
        (oneMinusConnLapSmooth (I := I) g 0 2 (Ds T) - Ds LT) -
        operatorFieldApply (I := I) (M := M) g 2 2 (Ks - K0) LT - Cross := by
  classical
  let gs : SmoothRiemannianMetric I M :=
    metricPerturbationPathFromZero (I := I) (M := M) g T hdelta s
  let A0 : SmoothCcTensor g 2 2 := DeTurckCoefficients.ricciDeTurckRemainderZeroOrderCoefficient
    (I := I) (M := M) g g_bg T 0 hdelta hdeltaZ s
  let R0 : SmoothCcTensor g 2 2 :=
    rhsDecomposition0 (I := I) (M := M) g g_bg T hdelta hdeltaZ s
  let K0 : SmoothCcTensor g 2 2 := metricPrincipalDefectCurvCoeff (I := I) g g
  let Ks : SmoothCcTensor g 2 2 := metricPrincipalDefectCurvCoeff (I := I) g gs
  let E0 : SmoothCcTensor g 2 2 := backgroundZeroOrderCoefficient (I := I) (M := M) g g_bg +
    metricDependentZeroOrderCoefficient (I := I) (M := M) g gs g_bg
  let Ds : SmoothCcTensor g 0 2 → SmoothCcTensor g 0 2 := fun W =>
    deTurckPrincipalCometricArm (I := I) (M := M) g gs W
  let LT : SmoothCcTensor g 0 2 := oneMinusConnLapSmooth (I := I) g 0 2 T
  let Q : SmoothCcTensor g 0 2 → SmoothCcTensor g 2 2 := fun U =>
    ricciDeTurckTopOrderBilinearPairingCoefficient (I := I) (M := M) g T U hdelta hdeltaZ
      ricciDecompositionQA ricciDecompositionQB lieDecompositionQ lieDecompositionEps s
  let Z : SmoothCcTensor g 0 2 := operatorFieldApply (I := I) (M := M) g 2 2 (Q T) T
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
          (operatorFieldApply (I := I) (M := M) g 4 2 C
            (iteratedCovGrad (I := I) g 0 2 2 T)) -
        operatorFieldApply (I := I) (M := M) g 4 2 C
          (iteratedCovGrad (I := I) g 0 2 2 LT)) - Z
  have hQdiag :
      Z = operatorFieldApply (I := I) (M := M) g 4 2
        (rhsDecomposition2 (I := I) (M := M) g T hdelta hdeltaZ s)
        (iteratedCovGrad (I := I) g 0 2 2 T) := by
    dsimp only [Z, Q]
    change operatorFieldApply (I := I) (M := M) g 2 2
        (ricciDeTurckTopOrderPairingCoefficient (I := I) (M := M) g T hdelta hdeltaZ
          ricciDecompositionQA ricciDecompositionQB lieDecompositionQ lieDecompositionEps s) T = _
    simpa only [rhsDecomposition2, ricciDecomposition2, lieDecomposition2] using
      ricciDeTurckTopOrderPairingCoefficient_apply (I := I) (M := M) g T hdelta hdeltaZ
        ricciDecompositionQA ricciDecompositionQB lieDecompositionQ lieDecompositionEps s
  have hdecomposition :
      operatorFieldApply (I := I) (M := M) g 2 2 A0 T =
        operatorFieldApply (I := I) (M := M) g 2 2 R0 T + Z := by
    dsimp only [A0, R0]
    rw [hQdiag]
    exact rhsLow0_decomposition (I := I) (M := M) g g_bg T hTsymm
      hdelta_lt hdelta hdeltaZ hs
  have hlow : A0 + Ks = E0 := by
    have hmetric := metricComparisonEndomorphism_pairing_balance (I := I) (M := M) g T
      hdelta_lt hdelta hdeltaZ hs
    dsimp only [A0, Ks, E0, gs]
    rw [hmetric]
    simpa only [DeTurckCoefficients.ricciDeTurckRemainderZeroOrderCoefficient,
      linearizedRicciConnectionDifferenceOrder0Coeff] using
        lowOrderZeroCoefficient_eq_background_add_metricDependent (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s) g_bg
  have htop (W : SmoothCcTensor g 0 2) :
      operatorFieldApply (I := I) (M := M) g 4 2 C
          (iteratedCovGrad (I := I) g 0 2 2 W) =
        Ds W + operatorFieldApply (I := I) (M := M) g 2 2 (Ks - K0) W := by
    have hgs := principalCoefficientAction_decomposition (I := I) (M := M) g gs W
    have hg := principalCoefficientAction_decomposition (I := I) (M := M) g g W
    simp only [deTurckPrincipalCometricArm,
      deTurckPrincipalCometricCoeff, sub_self, operatorFieldApplication_zero_left, add_zero] at hg
    dsimp only [C, Ds, Ks, K0]
    change operatorFieldApply (I := I) (M := M) g 4 2
        (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gs -
          deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g)
        (iteratedCovGrad (I := I) g 0 2 2 W) =
      deTurckPrincipalCometricArm (I := I) (M := M) g gs W +
        operatorFieldApply (I := I) (M := M) g 2 2
          (metricPrincipalDefectCurvCoeff (I := I) g gs -
            metricPrincipalDefectCurvCoeff (I := I) g g) W
    rw [operatorFieldApplication_sub_left, hgs, hg, operatorFieldApplication_sub_left]
    module
  have hlowApp := congrArg
    (fun F : SmoothCcTensor g 2 2 =>
      operatorFieldApply (I := I) (M := M) g 2 2 F T) hlow
  simp only [operatorFieldApplication_add_left] at hlowApp
  change operatorFieldApply (I := I) (M := M) g 2 2 A0 T =
      operatorFieldApply (I := I) (M := M) g 2 2 R0 T + Z at hdecomposition
  change operatorFieldApply (I := I) (M := M) g 2 2 A0 T +
      operatorFieldApply (I := I) (M := M) g 2 2 Ks T =
        operatorFieldApply (I := I) (M := M) g 2 2 E0 T at hlowApp
  have hinside :
      operatorFieldApply (I := I) (M := M) g 2 2 (R0 + K0) T + Z +
          operatorFieldApply (I := I) (M := M) g 4 2 C
            (iteratedCovGrad (I := I) g 0 2 2 T) =
        operatorFieldApply (I := I) (M := M) g 2 2 E0 T + Ds T := by
    rw [htop T]
    simp only [operatorFieldApplication_add_left, operatorFieldApplication_sub_left]
    rw [← hlowApp, hdecomposition]
    module
  change J =
    oneMinusConnLapSmooth (I := I) g 0 2
        (operatorFieldApply (I := I) (M := M) g 2 2 E0 T) +
      (oneMinusConnLapSmooth (I := I) g 0 2 (Ds T) - Ds LT) -
      operatorFieldApply (I := I) (M := M) g 2 2 (Ks - K0) LT - Cross
  dsimp only [J, PairComm]
  calc
    oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 2 2 (R0 + K0) T) +
        (oneMinusConnLapSmooth (I := I) g 0 2 Z -
            operatorFieldApply (I := I) (M := M) g 2 2 (Q LT) T -
            operatorFieldApply (I := I) (M := M) g 2 2 (Q T) LT + Z) +
        (oneMinusConnLapSmooth (I := I) g 0 2
            (operatorFieldApply (I := I) (M := M) g 4 2 C
              (iteratedCovGrad (I := I) g 0 2 2 T)) -
          operatorFieldApply (I := I) (M := M) g 4 2 C
            (iteratedCovGrad (I := I) g 0 2 2 LT)) - Z =
      (oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 2 2 (R0 + K0) T) +
        oneMinusConnLapSmooth (I := I) g 0 2 Z +
        oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 4 2 C
            (iteratedCovGrad (I := I) g 0 2 2 T))) -
        operatorFieldApply (I := I) (M := M) g 4 2 C
          (iteratedCovGrad (I := I) g 0 2 2 LT) - Cross := by
            dsimp only [Cross]
            module
    _ = oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 2 2 (R0 + K0) T + Z +
            operatorFieldApply (I := I) (M := M) g 4 2 C
              (iteratedCovGrad (I := I) g 0 2 2 T)) -
        operatorFieldApply (I := I) (M := M) g 4 2 C
          (iteratedCovGrad (I := I) g 0 2 2 LT) - Cross := by
            rw [oneMinusConn_add (I := I) (M := M) g 0 2,
              oneMinusConn_add (I := I) (M := M) g 0 2]
    _ = oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 2 2 E0 T + Ds T) -
        operatorFieldApply (I := I) (M := M) g 4 2 C
          (iteratedCovGrad (I := I) g 0 2 2 LT) - Cross := by
            rw [hinside]
    _ = oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 2 2 E0 T + Ds T) -
        (Ds LT + operatorFieldApply (I := I) (M := M) g 2 2 (Ks - K0) LT) -
        Cross := by
            rw [htop LT]
    _ = oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 2 2 E0 T) +
        (oneMinusConnLapSmooth (I := I) g 0 2 (Ds T) - Ds LT) -
        operatorFieldApply (I := I) (M := M) g 2 2 (Ks - K0) LT - Cross := by
            rw [oneMinusConn_add (I := I) (M := M) g 0 2]
            module

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end

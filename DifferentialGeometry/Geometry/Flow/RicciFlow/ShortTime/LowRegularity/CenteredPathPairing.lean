import DifferentialGeometry.Analysis.Integration.L2.PathIntegralCoeffFieldPairing
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.LowerScalePathDecomposition

noncomputable section
set_option autoImplicit false
open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle intervalIntegral
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace
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
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Spectral.MetricRealization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem inner_oneMinusConnLap_pathIntegral_data
    (g : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g 0 2) (Φ : ℝ → SmoothCcTensor g 0 2)
    (S : Set ℝ) (hS : IsOpen S) (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hΦ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun x : M => TensorRSSpace 0 2 I x) p.1
        ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    let P := pathIntegralCoeffField (I := I) (M := M) g 0 2 Φ S hS hSI hΦ
    (Inner.inner ℝ V (oneMinusConnLapSmooth (I := I) g 0 2 P) =
        ∫ t in (0 : ℝ)..1,
          Inner.inner ℝ V (oneMinusConnLapSmooth (I := I) g 0 2 (Φ t))) ∧
      IntervalIntegrable
        (fun t : ℝ =>
          Inner.inner ℝ V (oneMinusConnLapSmooth (I := I) g 0 2 (Φ t)))
        volume 0 1 := by
  dsimp only
  let LV := oneMinusConnLapSmooth (I := I) g 0 2 V
  let P := pathIntegralCoeffField (I := I) (M := M) g 0 2 Φ S hS hSI hΦ
  have hbase := DifferentialGeometry.Integral.L2.inner_pathIntegralCoeffField_eq_intervalIntegral
    (I := I) (M := M) g LV Φ S hS hSI hΦ
  have hbaseInt := DifferentialGeometry.Integral.L2.intervalIntegrable_inner_of_jointContMDiffOn
    (I := I) (M := M) g LV Φ S hS hSI hΦ
  have hmove : Inner.inner ℝ V (oneMinusConnLapSmooth (I := I) g 0 2 P) =
      Inner.inner ℝ LV P := by
    calc
      Inner.inner ℝ V (oneMinusConnLapSmooth (I := I) g 0 2 P) =
          Inner.inner ℝ (oneMinusConnLapSmooth (I := I) g 0 2 P) V := real_inner_comm _ _
      _ = Inner.inner ℝ P LV := by
        simpa only [SmoothCcTensor.inner_def, LV] using
          oneMinusConnLapSmooth_l2Inner_selfAdjoint (I := I) (M := M) g 0 2 P V
      _ = Inner.inner ℝ LV P := real_inner_comm _ _
  have hpoint : ∀ t : ℝ,
      Inner.inner ℝ V (oneMinusConnLapSmooth (I := I) g 0 2 (Φ t)) =
        Inner.inner ℝ LV (Φ t) := by
    intro t
    calc
      Inner.inner ℝ V (oneMinusConnLapSmooth (I := I) g 0 2 (Φ t)) =
          Inner.inner ℝ (oneMinusConnLapSmooth (I := I) g 0 2 (Φ t)) V := real_inner_comm _ _
      _ = Inner.inner ℝ (Φ t) LV := by
        simpa only [SmoothCcTensor.inner_def, LV] using
          oneMinusConnLapSmooth_l2Inner_selfAdjoint (I := I) (M := M) g 0 2 (Φ t) V
      _ = Inner.inner ℝ LV (Φ t) := real_inner_comm _ _
  have hfun : (fun t : ℝ =>
      Inner.inner ℝ V (oneMinusConnLapSmooth (I := I) g 0 2 (Φ t))) =
      fun t : ℝ => Inner.inner ℝ LV (Φ t) := by
    funext t
    exact hpoint t
  refine ⟨?_, ?_⟩
  · rw [hmove, show P = pathIntegralCoeffField (I := I) (M := M)
      g 0 2 Φ S hS hSI hΦ from rfl, hbase, hfun]
  · rw [hfun]
    exact hbaseInt

private theorem inner_centered_pathIntegral_data
    (g : SmoothRiemannianMetric I M) (V : SmoothCcTensor g 0 2)
    (A B C D : ℝ → SmoothCcTensor g 0 2)
    (S : Set ℝ) (hS : IsOpen S) (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun x : M => TensorRSSpace 0 2 I x) p.1 ((A p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun x : M => TensorRSSpace 0 2 I x) p.1 ((B p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    (hC : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun x : M => TensorRSSpace 0 2 I x) p.1 ((C p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    (hD : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun x : M => TensorRSSpace 0 2 I x) p.1 ((D p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    let PA := pathIntegralCoeffField (I := I) (M := M) g 0 2 A S hS hSI hA
    let PB := pathIntegralCoeffField (I := I) (M := M) g 0 2 B S hS hSI hB
    let PC := pathIntegralCoeffField (I := I) (M := M) g 0 2 C S hS hSI hC
    let PD := pathIntegralCoeffField (I := I) (M := M) g 0 2 D S hS hSI hD
    (Inner.inner ℝ V
        (oneMinusConnLapSmooth (I := I) g 0 2 PA +
          oneMinusConnLapSmooth (I := I) g 0 2 PB +
          oneMinusConnLapSmooth (I := I) g 0 2 PC - PD) =
      ∫ t in (0 : ℝ)..1, Inner.inner ℝ V
        (oneMinusConnLapSmooth (I := I) g 0 2 (A t) +
          oneMinusConnLapSmooth (I := I) g 0 2 (B t) +
          oneMinusConnLapSmooth (I := I) g 0 2 (C t) - D t)) ∧
      IntervalIntegrable (fun t : ℝ => Inner.inner ℝ V
        (oneMinusConnLapSmooth (I := I) g 0 2 (A t) +
          oneMinusConnLapSmooth (I := I) g 0 2 (B t) +
          oneMinusConnLapSmooth (I := I) g 0 2 (C t) - D t)) volume 0 1 := by
  dsimp only
  obtain ⟨hAe, hAi⟩ := inner_oneMinusConnLap_pathIntegral_data
    (I := I) (M := M) g V A S hS hSI hA
  obtain ⟨hBe, hBi⟩ := inner_oneMinusConnLap_pathIntegral_data
    (I := I) (M := M) g V B S hS hSI hB
  obtain ⟨hCe, hCi⟩ := inner_oneMinusConnLap_pathIntegral_data
    (I := I) (M := M) g V C S hS hSI hC
  have hDe := DifferentialGeometry.Integral.L2.inner_pathIntegralCoeffField_eq_intervalIntegral
    (I := I) (M := M) g V D S hS hSI hD
  have hDi := DifferentialGeometry.Integral.L2.intervalIntegrable_inner_of_jointContMDiffOn
    (I := I) (M := M) g V D S hS hSI hD
  refine ⟨?_, ?_⟩
  · rw [inner_sub_right, inner_add_right, inner_add_right, hAe, hBe, hCe, hDe]
    rw [← intervalIntegral.integral_add hAi hBi,
      ← intervalIntegral.integral_add (hAi.add hBi) hCi,
      ← intervalIntegral.integral_sub ((hAi.add hBi).add hCi) hDi]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [inner_sub_right, inner_add_right, inner_add_right]
  · have hi := ((hAi.add hBi).add hCi).sub hDi
    have hfun : (fun t : ℝ =>
        Inner.inner ℝ V (oneMinusConnLapSmooth (I := I) g 0 2 (A t)) +
          Inner.inner ℝ V (oneMinusConnLapSmooth (I := I) g 0 2 (B t)) +
          Inner.inner ℝ V (oneMinusConnLapSmooth (I := I) g 0 2 (C t)) -
          Inner.inner ℝ V (D t)) =
        fun t : ℝ => Inner.inner ℝ V
          (oneMinusConnLapSmooth (I := I) g 0 2 (A t) +
            oneMinusConnLapSmooth (I := I) g 0 2 (B t) +
            oneMinusConnLapSmooth (I := I) g 0 2 (C t) - D t) := by
      funext t
      rw [inner_sub_right, inner_add_right, inner_add_right]
    rw [← hfun]
    exact hi

theorem centeredPathPairing_eq_intervalIntegral_and_intervalIntegrable
    (g g_bg : SmoothRiemannianMetric I M) (T V : SmoothCcTensor g 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g T x v w = ccTensorBilin (I := I) g T x w v)
    {delta : ℝ} (hdelta_lt : delta < 1)
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta) :
    let P0 := ricciDeTurckRemainderZeroOrderPathIntegral (I := I) (M := M) g g_bg T 0
      hdelta_lt hdelta hdelta_lt hdeltaZ
    let P2 := rhsTopPathIntegral (I := I) (M := M) g T 0
      hdelta_lt hdelta hdelta_lt hdeltaZ
    let Φ0 := deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g
    let K0 := metricPrincipalDefectCurvCoeff (I := I) g g
    let LT := oneMinusConnLapSmooth (I := I) g 0 2 T
    let HT := iteratedCovGrad (I := I) g 0 2 2 T
    let HLT := iteratedCovGrad (I := I) g 0 2 2 LT
    let B02 := oneMinusConnLapSmooth (I := I) g 0 2
        (operatorFieldApply (I := I) (M := M) g 2 2 P0 T) +
      (oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 4 2 P2 HT) -
        operatorFieldApply (I := I) (M := M) g 4 2 P2 HLT)
    let Js := fun s : ℝ =>
      let gs := metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s
      let R0s := rhsDecomposition0 (I := I) (M := M) g g_bg T hdelta hdeltaZ s
      let Qs := fun U : SmoothCcTensor g 0 2 =>
        ricciDeTurckTopOrderBilinearPairingCoefficient (I := I) (M := M) g T U hdelta hdeltaZ
          ricciDecompositionQA ricciDecompositionQB lieDecompositionQ lieDecompositionEps s
      let Zs := operatorFieldApply (I := I) (M := M) g 2 2 (Qs T) T
      let PairComms := oneMinusConnLapSmooth (I := I) g 0 2 Zs -
        operatorFieldApply (I := I) (M := M) g 2 2 (Qs LT) T -
        operatorFieldApply (I := I) (M := M) g 2 2 (Qs T) LT + Zs
      let Cs := deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gs - Φ0
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
    (Inner.inner ℝ V (B02 + operatorFieldApply (I := I) (M := M) g 2 2 K0 LT) =
        ∫ s in (0 : ℝ)..1, Inner.inner ℝ V (Js s + Crosss s)) ∧
      IntervalIntegrable (fun s : ℝ =>
        Inner.inner ℝ V (Js s + Crosss s)) volume 0 1 := by
  classical
  dsimp only
  let S : Set ℝ := metricPerturbationPathDomain (δ := delta) (δ' := delta)
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ S := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hdelta_lt hdelta_lt
  let R : ℝ → SmoothCcTensor g 2 2 :=
    rhsDecomposition0 (I := I) (M := M) g g_bg T hdelta hdeltaZ
  let K0 : SmoothCcTensor g 2 2 := metricPrincipalDefectCurvCoeff (I := I) g g
  let Φ : ℝ → SmoothCcTensor g 4 2 := fun s =>
    deTurckMetricPrincipalDefectTotal (I := I) (M := M) g
      (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s)
  let Φ0 : SmoothCcTensor g 4 2 :=
    deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g
  let LT := oneMinusConnLapSmooth (I := I) g 0 2 T
  let HT := iteratedCovGrad (I := I) g 0 2 2 T
  let HLT := iteratedCovGrad (I := I) g 0 2 2 LT
  let Q : ℝ → SmoothCcTensor g 2 2 := fun s =>
    ricciDeTurckTopOrderBilinearPairingCoefficient (I := I) (M := M) g T T hdelta hdeltaZ
      ricciDecompositionQA ricciDecompositionQB lieDecompositionQ lieDecompositionEps s
  let A0 : ℝ → SmoothCcTensor g 0 2 := fun s =>
    operatorFieldApply (I := I) (M := M) g 2 2 (R s + K0) T
  let Z0 : ℝ → SmoothCcTensor g 0 2 := fun s =>
    operatorFieldApply (I := I) (M := M) g 2 2 (Q s) T
  let CHT : ℝ → SmoothCcTensor g 0 2 := fun s =>
    operatorFieldApply (I := I) (M := M) g 4 2 (Φ s - Φ0) HT
  let CHLT : ℝ → SmoothCcTensor g 0 2 := fun s =>
    operatorFieldApply (I := I) (M := M) g 4 2 (Φ s - Φ0) HLT
  have hR : linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g 2 R
      (δ := delta) (δ' := delta) := by
    simpa only [R] using rhsDecomposition0_joint (I := I) (M := M)
      g g_bg T hdelta hdeltaZ
  have hRK : linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g 2
      (fun s => R s + K0) (δ := delta) (δ' := delta) :=
    covariantJetJoint_add (I := I) (M := M) g R (fun _ => K0) hR
      (covariantJetJoint_const (I := I) (M := M) g K0)
  have hA0 := operatorFieldApplication_fixed_jointContMDiffOn (I := I) (M := M)
    g (fun s => R s + K0) T S hRK
  have hQ : linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g 2 Q
      (δ := delta) (δ' := delta) := by
    rw [linearizedRicciCovariantJetJointSmoothness]
    simpa only [Q] using ricciDeTurckTopOrderPairingCoefficient_joint_contDiff (I := I) (M := M)
      g T T hdelta hdeltaZ ricciDecompositionQA ricciDecompositionQB lieDecompositionQ lieDecompositionEps
  have hZ0 := operatorFieldApplication_fixed_jointContMDiffOn (I := I) (M := M) g Q T S hQ
  have hC : linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g 4
      (fun s => Φ s - Φ0) (δ := delta) (δ' := delta) := by
    simpa only [Φ, Φ0] using phi_dev_joint (I := I) (M := M)
      g T (0 : SmoothCcTensor g 0 2) hdelta hdeltaZ
  have hCHT := operatorFieldApplication_fixed_jointContMDiffOn (I := I) (M := M)
    g (fun s => Φ s - Φ0) HT S hC
  have hCHLT := operatorFieldApplication_fixed_jointContMDiffOn (I := I) (M := M)
    g (fun s => Φ s - Φ0) HLT S hC
  have hRKInt : rhsDecomposition0Int (I := I) (M := M) g g_bg T
        hdelta_lt hdelta hdeltaZ + K0 =
      pathIntegralCoeffField (I := I) (M := M) g 2 2
        (fun s => R s + K0) S metricPerturbationPathDomain_isOpen hSI hRK := by
    change pathIntegralCoeffField (I := I) (M := M) g 2 2 R S
        metricPerturbationPathDomain_isOpen hSI hR + K0 = _
    simpa only [K0] using pathIntegralCoeffField_add_const
      (I := I) (M := M) g R K0 S metricPerturbationPathDomain_isOpen hSI hR hRK
  have hA0Int : operatorFieldApply (I := I) (M := M) g 2 2
        (rhsDecomposition0Int (I := I) (M := M) g g_bg T
          hdelta_lt hdelta hdeltaZ + K0) T =
      pathIntegralCoeffField (I := I) (M := M) g 0 2 A0 S
        metricPerturbationPathDomain_isOpen hSI (by
          simpa only [A0, operatorFieldComposition_zero_eq_operatorFieldApply] using hA0) := by
    rw [hRKInt]
    simpa only [A0, operatorFieldComposition_zero_eq_operatorFieldApply] using
      operatorFieldApplication_pathIntegralCoeffField (I := I) (M := M) g
        (fun s => R s + K0) T S metricPerturbationPathDomain_isOpen hSI hRK
  have hZ0Int : operatorFieldApply (I := I) (M := M) g 2 2
        (ricciDeTurckTopOrderPathIntegralCoefficient (I := I) (M := M) g T T hdelta_lt hdelta hdeltaZ
          ricciDecompositionQA ricciDecompositionQB lieDecompositionQ lieDecompositionEps) T =
      pathIntegralCoeffField (I := I) (M := M) g 0 2 Z0 S
        metricPerturbationPathDomain_isOpen hSI (by
          simpa only [Z0, operatorFieldComposition_zero_eq_operatorFieldApply] using hZ0) := by
    simpa only [Z0, Q, S, operatorFieldComposition_zero_eq_operatorFieldApply] using
      ricciDeTurckTopOrderPathIntegralCoefficient_apply (I := I) (M := M) g T T T hdelta_lt hdelta hdeltaZ
        ricciDecompositionQA ricciDecompositionQB lieDecompositionQ lieDecompositionEps
  have hCInt : rhsTopPathIntegral (I := I) (M := M) g T 0
        hdelta_lt hdelta hdelta_lt hdeltaZ - Φ0 =
      pathIntegralCoeffField (I := I) (M := M) g 4 2
        (fun s => Φ s - Φ0) S metricPerturbationPathDomain_isOpen hSI hC := by
    have hΦlin := rhs_top_path_joint (I := I) (M := M)
      g T (0 : SmoothCcTensor g 0 2) hdelta hdeltaZ
    have hΦneg := covariantJetJoint_add (I := I) (M := M) g Φ (fun _ => -Φ0)
      (by simpa only [Φ] using hΦlin)
      (covariantJetJoint_const (I := I) (M := M) g (-Φ0))
    have hΦ := hΦlin
    have hΦneg' := hΦneg
    rw [linearizedRicciCovariantJetJointSmoothness] at hΦ hΦneg'
    unfold rhsTopPathIntegral
    simpa only [Φ, Φ0, S, sub_eq_add_neg] using
      pathIntegralCoeffField_add_const (I := I) (M := M)
        g Φ (-Φ0) S metricPerturbationPathDomain_isOpen hSI
          (by simpa only [Φ, S] using hΦ) (by simpa only [Φ, Φ0, S] using hΦneg')
  have hCHTInt : operatorFieldApply (I := I) (M := M) g 4 2
        (rhsTopPathIntegral (I := I) (M := M) g T 0
          hdelta_lt hdelta hdelta_lt hdeltaZ - Φ0) HT =
      pathIntegralCoeffField (I := I) (M := M) g 0 2 CHT S
        metricPerturbationPathDomain_isOpen hSI (by
          simpa only [CHT, operatorFieldComposition_zero_eq_operatorFieldApply] using hCHT) := by
    rw [hCInt]
    simpa only [CHT, operatorFieldComposition_zero_eq_operatorFieldApply] using
      operatorFieldApplication_pathIntegralCoeffField (I := I) (M := M) g
        (fun s => Φ s - Φ0) HT S metricPerturbationPathDomain_isOpen hSI hC
  have hCHLTInt : operatorFieldApply (I := I) (M := M) g 4 2
        (rhsTopPathIntegral (I := I) (M := M) g T 0
          hdelta_lt hdelta hdelta_lt hdeltaZ - Φ0) HLT =
      pathIntegralCoeffField (I := I) (M := M) g 0 2 CHLT S
        metricPerturbationPathDomain_isOpen hSI (by
          simpa only [CHLT, operatorFieldComposition_zero_eq_operatorFieldApply] using hCHLT) := by
    rw [hCInt]
    simpa only [CHLT, operatorFieldComposition_zero_eq_operatorFieldApply] using
      operatorFieldApplication_pathIntegralCoeffField (I := I) (M := M) g
        (fun s => Φ s - Φ0) HLT S metricPerturbationPathDomain_isOpen hSI hC
  have hpath := inner_centered_pathIntegral_data (I := I) (M := M)
    g V A0 Z0 CHT CHLT S metricPerturbationPathDomain_isOpen hSI
      (by simpa only [A0, operatorFieldComposition_zero_eq_operatorFieldApply] using hA0)
      (by simpa only [Z0, operatorFieldComposition_zero_eq_operatorFieldApply] using hZ0)
      (by simpa only [CHT, operatorFieldComposition_zero_eq_operatorFieldApply] using hCHT)
      (by simpa only [CHLT, operatorFieldComposition_zero_eq_operatorFieldApply] using hCHLT)
  rw [← hA0Int, ← hZ0Int, ← hCHTInt, ← hCHLTInt] at hpath
  have hcenter := lowerScaleZerothSecondOrderTerms_eq_centered_commutator_decomposition (I := I) (M := M)
    g g_bg T hTsymm hdelta_lt hdelta hdeltaZ
  dsimp only at hcenter
  have hInt :
      oneMinusConnLapSmooth (I := I) g 0 2
            (operatorFieldApply (I := I) (M := M) g 2 2
              (ricciDeTurckRemainderZeroOrderPathIntegral (I := I) (M := M) g g_bg T 0
                hdelta_lt hdelta hdelta_lt hdeltaZ) T) +
          (oneMinusConnLapSmooth (I := I) g 0 2
              (operatorFieldApply (I := I) (M := M) g 4 2
                (rhsTopPathIntegral (I := I) (M := M) g T 0
                  hdelta_lt hdelta hdelta_lt hdeltaZ) HT) -
            operatorFieldApply (I := I) (M := M) g 4 2
              (rhsTopPathIntegral (I := I) (M := M) g T 0
                hdelta_lt hdelta hdelta_lt hdeltaZ) HLT) +
          operatorFieldApply (I := I) (M := M) g 2 2 K0 LT =
        oneMinusConnLapSmooth (I := I) g 0 2
            (operatorFieldApply (I := I) (M := M) g 2 2
              (rhsDecomposition0Int (I := I) (M := M) g g_bg T
                hdelta_lt hdelta hdeltaZ + K0) T) +
          oneMinusConnLapSmooth (I := I) g 0 2
            (operatorFieldApply (I := I) (M := M) g 2 2
              (ricciDeTurckTopOrderPathIntegralCoefficient (I := I) (M := M) g T T hdelta_lt hdelta hdeltaZ
                ricciDecompositionQA ricciDecompositionQB lieDecompositionQ lieDecompositionEps) T) +
          oneMinusConnLapSmooth (I := I) g 0 2
            (operatorFieldApply (I := I) (M := M) g 4 2
              (rhsTopPathIntegral (I := I) (M := M) g T 0
                hdelta_lt hdelta hdelta_lt hdeltaZ - Φ0) HT) -
          operatorFieldApply (I := I) (M := M) g 4 2
            (rhsTopPathIntegral (I := I) (M := M) g T 0
              hdelta_lt hdelta hdelta_lt hdeltaZ - Φ0) HLT := by
    rw [hcenter]
    module
  have hpoint : ∀ s : ℝ,
      (let gs := metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s
       let R0s := rhsDecomposition0 (I := I) (M := M) g g_bg T hdelta hdeltaZ s
       let Qs := fun U : SmoothCcTensor g 0 2 =>
         ricciDeTurckTopOrderBilinearPairingCoefficient (I := I) (M := M) g T U hdelta hdeltaZ
           ricciDecompositionQA ricciDecompositionQB lieDecompositionQ lieDecompositionEps s
       let Zs := operatorFieldApply (I := I) (M := M) g 2 2 (Qs T) T
       let PairComms := oneMinusConnLapSmooth (I := I) g 0 2 Zs -
         operatorFieldApply (I := I) (M := M) g 2 2 (Qs LT) T -
         operatorFieldApply (I := I) (M := M) g 2 2 (Qs T) LT + Zs
       let Cs := deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gs - Φ0
       oneMinusConnLapSmooth (I := I) g 0 2
           (operatorFieldApply (I := I) (M := M) g 2 2 (R0s + K0) T) +
         PairComms +
         (oneMinusConnLapSmooth (I := I) g 0 2
             (operatorFieldApply (I := I) (M := M) g 4 2 Cs HT) -
           operatorFieldApply (I := I) (M := M) g 4 2 Cs HLT) - Zs) +
      (let Qs := fun U : SmoothCcTensor g 0 2 =>
         ricciDeTurckTopOrderBilinearPairingCoefficient (I := I) (M := M) g T U hdelta hdeltaZ
           ricciDecompositionQA ricciDecompositionQB lieDecompositionQ lieDecompositionEps s
       operatorFieldApply (I := I) (M := M) g 2 2 (Qs LT) T +
         operatorFieldApply (I := I) (M := M) g 2 2 (Qs T) LT) =
      oneMinusConnLapSmooth (I := I) g 0 2 (A0 s) +
        oneMinusConnLapSmooth (I := I) g 0 2 (Z0 s) +
        oneMinusConnLapSmooth (I := I) g 0 2 (CHT s) - CHLT s := by
    intro s
    dsimp only [A0, Z0, CHT, CHLT, R, K0, Q, Φ, Φ0]
    module
  refine ⟨?_, ?_⟩
  · calc
      Inner.inner ℝ V
        (oneMinusConnLapSmooth (I := I) g 0 2
              (operatorFieldApply (I := I) (M := M) g 2 2
                (ricciDeTurckRemainderZeroOrderPathIntegral (I := I) (M := M) g g_bg T 0
                  hdelta_lt hdelta hdelta_lt hdeltaZ) T) +
            (oneMinusConnLapSmooth (I := I) g 0 2
                (operatorFieldApply (I := I) (M := M) g 4 2
                  (rhsTopPathIntegral (I := I) (M := M) g T 0
                    hdelta_lt hdelta hdelta_lt hdeltaZ) HT) -
              operatorFieldApply (I := I) (M := M) g 4 2
                (rhsTopPathIntegral (I := I) (M := M) g T 0
                  hdelta_lt hdelta hdelta_lt hdeltaZ) HLT) +
            operatorFieldApply (I := I) (M := M) g 2 2 K0 LT) =
        Inner.inner ℝ V
          (oneMinusConnLapSmooth (I := I) g 0 2
              (operatorFieldApply (I := I) (M := M) g 2 2
                (rhsDecomposition0Int (I := I) (M := M) g g_bg T
                  hdelta_lt hdelta hdeltaZ + K0) T) +
            oneMinusConnLapSmooth (I := I) g 0 2
              (operatorFieldApply (I := I) (M := M) g 2 2
                (ricciDeTurckTopOrderPathIntegralCoefficient (I := I) (M := M) g T T hdelta_lt
                  hdelta hdeltaZ ricciDecompositionQA ricciDecompositionQB
                    lieDecompositionQ lieDecompositionEps) T) +
            oneMinusConnLapSmooth (I := I) g 0 2
              (operatorFieldApply (I := I) (M := M) g 4 2
                (rhsTopPathIntegral (I := I) (M := M) g T 0
                  hdelta_lt hdelta hdelta_lt hdeltaZ - Φ0) HT) -
            operatorFieldApply (I := I) (M := M) g 4 2
              (rhsTopPathIntegral (I := I) (M := M) g T 0
                hdelta_lt hdelta hdelta_lt hdeltaZ - Φ0) HLT) :=
      congrArg (Inner.inner ℝ V) hInt
      _ = ∫ s in (0 : ℝ)..1, Inner.inner ℝ V
          (oneMinusConnLapSmooth (I := I) g 0 2 (A0 s) +
            oneMinusConnLapSmooth (I := I) g 0 2 (Z0 s) +
            oneMinusConnLapSmooth (I := I) g 0 2 (CHT s) - CHLT s) := hpath.1
      _ = _ := by
        refine intervalIntegral.integral_congr (fun s _ => ?_)
        rw [hpoint s]
  · have hfun : (fun s : ℝ =>
        Inner.inner ℝ V
          ((let gs := metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s
            let R0s := rhsDecomposition0 (I := I) (M := M) g g_bg T hdelta hdeltaZ s
            let Qs := fun U : SmoothCcTensor g 0 2 =>
              ricciDeTurckTopOrderBilinearPairingCoefficient (I := I) (M := M) g T U hdelta hdeltaZ
                ricciDecompositionQA ricciDecompositionQB lieDecompositionQ lieDecompositionEps s
            let Zs := operatorFieldApply (I := I) (M := M) g 2 2 (Qs T) T
            let PairComms := oneMinusConnLapSmooth (I := I) g 0 2 Zs -
              operatorFieldApply (I := I) (M := M) g 2 2 (Qs LT) T -
              operatorFieldApply (I := I) (M := M) g 2 2 (Qs T) LT + Zs
            let Cs := deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gs - Φ0
            oneMinusConnLapSmooth (I := I) g 0 2
                (operatorFieldApply (I := I) (M := M) g 2 2 (R0s + K0) T) +
              PairComms +
              (oneMinusConnLapSmooth (I := I) g 0 2
                  (operatorFieldApply (I := I) (M := M) g 4 2 Cs HT) -
                operatorFieldApply (I := I) (M := M) g 4 2 Cs HLT) - Zs) +
            (let Qs := fun U : SmoothCcTensor g 0 2 =>
              ricciDeTurckTopOrderBilinearPairingCoefficient (I := I) (M := M) g T U hdelta hdeltaZ
                ricciDecompositionQA ricciDecompositionQB lieDecompositionQ lieDecompositionEps s
             operatorFieldApply (I := I) (M := M) g 2 2 (Qs LT) T +
               operatorFieldApply (I := I) (M := M) g 2 2 (Qs T) LT))) =
      fun s : ℝ => Inner.inner ℝ V
        (oneMinusConnLapSmooth (I := I) g 0 2 (A0 s) +
          oneMinusConnLapSmooth (I := I) g 0 2 (Z0 s) +
          oneMinusConnLapSmooth (I := I) g 0 2 (CHT s) - CHLT s) := by
      funext s
      rw [hpoint s]
    rw [hfun]
    exact hpath.2

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
end

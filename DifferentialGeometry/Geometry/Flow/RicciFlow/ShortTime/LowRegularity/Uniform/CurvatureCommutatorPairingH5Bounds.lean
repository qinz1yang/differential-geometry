import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.AllOrderGardingConstant
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.MixedDerivativePairingH5Bounds

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Sobolev
  (iteratedCovGrad iteratedCovGrad_succ iteratedCovGrad_zero)
open DifferentialGeometry.Analysis.Elliptic
  (exists_iteratedCovGrad_pointwiseTensorCurv_l2Norm_le)
open DifferentialGeometry.Analysis.Spectral
  (operatorFieldApply operatorFieldComposition_zero_eq_operatorFieldApply ccTensorToHs cc_h1_jet_sq deTurckMetricPrincipalDefectTotal smooth_cc_tensor_h1_norm_sq_eq_covariant_jet hsJet_le
    iteratedCovGrad_comp_norm norm_ccHs_eq_smoothHs oneMinusConnLapSmooth one_minus_connection_laplacian_squared_pairing_h3_h1_bound
    smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap)
open DifferentialGeometry.Geometry.Curvature (pointwiseTensorCurv)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem defect_arg_h1_fixed
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : SmoothCcTensor g 0 2,
        let GT : SmoothCcTensor g 0 4 :=
          covGrad (I := I) (M := M) g 0 3
              (pointwiseTensorCurv (I := I) (M := M) g 2 T) +
            pointwiseTensorCurv (I := I) (M := M) g 3
              (covGrad (I := I) (M := M) g 0 2 T)
        ‖(⟨GT⟩ : SmoothCcTensorH1 g 0 4)‖ ≤
          C * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ := by
  classical
  obtain ⟨K2, hK2, hcurv2⟩ :=
    exists_iteratedCovGrad_pointwiseTensorCurv_l2Norm_le
      (I := I) (M := M) g 2
  obtain ⟨K3, hK3, hcurv3⟩ :=
    exists_iteratedCovGrad_pointwiseTensorCurv_l2Norm_le
      (I := I) (M := M) g 3
  obtain ⟨CJ, hCJ, hjet3⟩ := hsJet_le (I := I) (M := M) g 2 3
  let K : ℝ := K2 1 + K2 2 + K3 0 + K3 1
  let C : ℝ := K * CJ
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact add_nonneg (add_nonneg (add_nonneg (hK2 1) (hK2 2)) (hK3 0))
      (hK3 1)
  have hC : 0 ≤ C := mul_nonneg hK hCJ
  refine ⟨C, hC, ?_⟩
  intro T
  let R2 : SmoothCcTensor g 0 3 :=
    pointwiseTensorCurv (I := I) (M := M) g 2 T
  let DT : SmoothCcTensor g 0 3 :=
    covGrad (I := I) (M := M) g 0 2 T
  let A : SmoothCcTensor g 0 4 :=
    covGrad (I := I) (M := M) g 0 3 R2
  let B : SmoothCcTensor g 0 4 :=
    pointwiseTensorCurv (I := I) (M := M) g 3 DT
  let GT : SmoothCcTensor g 0 4 := A + B
  let S : ℝ := ∑ j ∈ Finset.range 4,
    ‖iteratedCovGrad (I := I) g 0 2 j T‖
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  have hS : S ≤ CJ * y := by
    have h := hjet3 T
    have hthree : ((3 : ℕ) : ℝ) = (3 : ℝ) := by norm_num
    rw [hthree] at h
    simpa only [S, y] using h
  have hS3 :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 2 j T‖) ≤ S := by
    dsimp only [S]
    simp only [Finset.sum_range_succ]
    exact le_add_of_nonneg_right (norm_nonneg _)
  have hDT_eq : DT = iteratedCovGrad (I := I) g 0 2 1 T := by
    simp only [DT, iteratedCovGrad_succ, iteratedCovGrad_zero, Nat.add_zero]
  have hDT0 :
      ‖iteratedCovGrad (I := I) g 0 3 0 DT‖ =
        ‖iteratedCovGrad (I := I) g 0 2 1 T‖ := by
    rw [hDT_eq]
    simpa only [Nat.reduceAdd] using
      (iteratedCovGrad_comp_norm (I := I) (M := M) g 2 1 0 T)
  have hDT1 :
      ‖iteratedCovGrad (I := I) g 0 3 1 DT‖ =
        ‖iteratedCovGrad (I := I) g 0 2 2 T‖ := by
    rw [hDT_eq]
    simpa only [Nat.reduceAdd] using
      (iteratedCovGrad_comp_norm (I := I) (M := M) g 2 1 1 T)
  have hDT0' : ‖DT‖ =
      ‖iteratedCovGrad (I := I) g 0 2 1 T‖ := by
    simpa only [iteratedCovGrad_zero] using hDT0
  have hDT2' :
      ‖iteratedCovGrad (I := I) g 0 3 2 DT‖ =
        ‖iteratedCovGrad (I := I) g 0 2 3 T‖ := by
    rw [hDT_eq]
    simpa only [Nat.reduceAdd] using
      (iteratedCovGrad_comp_norm (I := I) (M := M) g 2 1 2 T)
  have hDT2 :
      (∑ j ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g 0 3 j DT‖) ≤ S := by
    dsimp only [S]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      iteratedCovGrad_zero]
    rw [hDT0', hDT1]
    nlinarith [norm_nonneg T,
      norm_nonneg (iteratedCovGrad (I := I) g 0 2 3 T)]
  have hDT3 :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 3 j DT‖) ≤ S := by
    dsimp only [S]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      iteratedCovGrad_zero]
    rw [hDT0', hDT1, hDT2']
    nlinarith [norm_nonneg T]
  have hA0 : ‖A‖ ≤ K2 1 * S := by
    have hAeq : A = iteratedCovGrad (I := I) g 0 3 1 R2 := by
      simp only [A, iteratedCovGrad_succ, iteratedCovGrad_zero, Nat.add_zero]
    calc
      _ ≤ K2 1 * ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ := by
        rw [hAeq]
        simpa only [R2, Nat.reduceAdd] using hcurv2 1 T
      _ ≤ K2 1 * S := mul_le_mul_of_nonneg_left hS3 (hK2 1)
  have hA1 :
      ‖covGrad (I := I) (M := M) g 0 4 A‖ ≤ K2 2 * S := by
    have hAeq : A = iteratedCovGrad (I := I) g 0 3 1 R2 := by
      simp only [A, iteratedCovGrad_succ, iteratedCovGrad_zero, Nat.add_zero]
    have houter : covGrad (I := I) (M := M) g 0 4 A =
        iteratedCovGrad (I := I) g 0 4 1 A := by
      simp only [iteratedCovGrad_succ, iteratedCovGrad_zero, Nat.add_zero]
    calc
      _ = ‖iteratedCovGrad (I := I) g 0 3 2 R2‖ := by
        rw [houter, hAeq]
        simpa only [Nat.reduceAdd] using iteratedCovGrad_comp_norm
          (I := I) (M := M) g 3 1 1 R2
      _ ≤ K2 2 * S := by simpa only [R2] using hcurv2 2 T
  have hB0 : ‖B‖ ≤ K3 0 * S := by
    calc
      _ ≤ K3 0 * ∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g 0 3 j DT‖ := by
        simpa only [B, iteratedCovGrad_zero, Nat.reduceAdd] using hcurv3 0 DT
      _ ≤ K3 0 * S := mul_le_mul_of_nonneg_left hDT2 (hK3 0)
  have hB1 :
      ‖covGrad (I := I) (M := M) g 0 4 B‖ ≤ K3 1 * S := by
    have houter : covGrad (I := I) (M := M) g 0 4 B =
        iteratedCovGrad (I := I) g 0 4 1 B := by
      simp only [iteratedCovGrad_succ, iteratedCovGrad_zero, Nat.add_zero]
    calc
      _ ≤ K3 1 * ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 3 j DT‖ := by
        rw [houter]
        simpa only [B, Nat.reduceAdd] using hcurv3 1 DT
      _ ≤ K3 1 * S := mul_le_mul_of_nonneg_left hDT3 (hK3 1)
  have hGT0 : ‖GT‖ ≤ (K2 1 + K3 0) * S := by
    calc
      _ ≤ ‖A‖ + ‖B‖ := by simpa only [GT] using norm_add_le A B
      _ ≤ K2 1 * S + K3 0 * S := add_le_add hA0 hB0
      _ = _ := by ring
  have hGT1 :
      ‖covGrad (I := I) (M := M) g 0 4 GT‖ ≤
        (K2 2 + K3 1) * S := by
    calc
      _ = ‖covGrad (I := I) (M := M) g 0 4 A +
          covGrad (I := I) (M := M) g 0 4 B‖ := by
        dsimp only [GT]
        rw [covGrad_add]
      _ ≤ ‖covGrad (I := I) (M := M) g 0 4 A‖ +
          ‖covGrad (I := I) (M := M) g 0 4 B‖ := norm_add_le _ _
      _ ≤ K2 2 * S + K3 1 * S := add_le_add hA1 hB1
      _ = _ := by ring
  have hroot : ‖(⟨GT⟩ : SmoothCcTensorH1 g 0 4)‖ ≤
      ‖GT‖ + ‖covGrad (I := I) (M := M) g 0 4 GT‖ := by
    have hsq := smooth_cc_tensor_h1_norm_sq_eq_covariant_jet (I := I) (M := M) g 0 4 GT
    refine le_of_sq_le_sq ?_ (add_nonneg (norm_nonneg _) (norm_nonneg _))
    rw [hsq]
    nlinarith [mul_nonneg (norm_nonneg GT)
      (norm_nonneg (covGrad (I := I) (M := M) g 0 4 GT))]
  calc
    _ ≤ ‖GT‖ + ‖covGrad (I := I) (M := M) g 0 4 GT‖ := hroot
    _ ≤ (K2 1 + K3 0) * S + (K2 2 + K3 1) * S :=
      add_le_add hGT0 hGT1
    _ = K * S := by dsimp only [K]; ring
    _ ≤ K * (CJ * y) := mul_le_mul_of_nonneg_left hS hK
    _ = C * y := by dsimp only [C]; ring

theorem curvature_commutator_pairing_h5_uniform_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ rho : ℝ, 0 < rho ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ b : ℕ, b ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ b g gBase Λ) →
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ (T : SmoothCcTensor g 0 2)
            (_hTsymm : ∀ (x : M) (u v : TangentSpace I x),
              ccTensorBilin (I := I) g T x u v =
                ccTensorBilin (I := I) g T x v u)
            {delta : ℝ}, delta ≤ 1 / 3 → 0 ≤ delta →
            ∀ (hdelta : gFibreOpBound (I := I) (M := M) g
                (ccTensorBilinSymm (I := I) g T) delta)
              (hdeltaZ : gFibreOpBound (I := I) (M := M) g
                (ccTensorBilinSymm (I := I) g
                  (0 : SmoothCcTensor g 0 2)) delta),
            ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ rho →
            ∀ {a : ℝ}, a ∈ Set.Icc (0 : ℝ) 1 →
            let gm := metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ a
            let B : SmoothCcTensor g 4 2 :=
              lieDecomposition2 (I := I) (M := M) g T hdelta hdeltaZ a +
                (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gm -
                  deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g) +
                (-2 * a : ℝ) •
                  RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T
            let GT : SmoothCcTensor g 0 4 :=
              covGrad (I := I) (M := M) g 0 3
                  (pointwiseTensorCurv (I := I) (M := M) g 2 T) +
                pointwiseTensorCurv (I := I) (M := M) g 3
                  (covGrad (I := I) (M := M) g 0 2 T)
            let V : SmoothCcTensor g 0 2 :=
              oneMinusConnLapSmooth (I := I) g 0 2
                (oneMinusConnLapSmooth (I := I) g 0 2
                  (oneMinusConnLapSmooth (I := I) g 0 2 T))
            2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun
                (operatorFieldApply (I := I) (M := M) g 4 2 B GT).toFun| ≤
              C * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 *
                ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖ := by
  classical
  obtain ⟨rho, CB, hrho, hCB, hedge⟩ :=
    ricciDeTurckTopOrderCoefficient_h3_uniform_bound (I := I) (M := M) hDim gBase hΛ
  obtain ⟨Capp, hCapp, happ⟩ :=
    operatorFieldComposition_h2_uniform_bound (I := I) (M := M) hDim gBase hΛ 0 4 2
  refine ⟨rho, hrho, ?_⟩
  intro g hEq hjet
  obtain ⟨Cg, hCg, hGT⟩ := defect_arg_h1_fixed (I := I) (M := M) g
  let C : ℝ := 2 * Capp * CB * Cg
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro T hTsymm delta hdelta_le hdelta0 hdelta hdeltaZ hT2 a ha
  let gm : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ a
  let B : SmoothCcTensor g 4 2 :=
    lieDecomposition2 (I := I) (M := M) g T hdelta hdeltaZ a +
      (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gm -
        deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g) +
      (-2 * a : ℝ) •
        RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T
  let GT : SmoothCcTensor g 0 4 :=
    covGrad (I := I) (M := M) g 0 3
        (pointwiseTensorCurv (I := I) (M := M) g 2 T) +
      pointwiseTensorCurv (I := I) (M := M) g 3
        (covGrad (I := I) (M := M) g 0 2 T)
  let Y : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 4 2 B GT
  let W : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 T
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let z : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖
  have hB4 :
      (∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 4 2 j B‖ ^ 2) ≤ (CB * y) ^ 2 := by
    simpa only [B, gm, y] using
      hedge g hEq hjet T hTsymm hdelta_le hdelta0 hdelta hdeltaZ hT2 ha
  have hB3 :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 4 2 j B‖ ^ 2) ≤ (CB * y) ^ 2 := by
    simp only [Finset.sum_range_succ] at hB4 ⊢
    nlinarith [hB4, sq_nonneg
      ‖iteratedCovGrad (I := I) g 4 2 3 B‖]
  have hGTh1 : ‖(⟨GT⟩ : SmoothCcTensorH1 g 0 4)‖ ≤ Cg * y := by
    simpa only [GT, y] using hGT T
  have hGTjet :
      (∑ j ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g 0 4 j GT‖ ^ 2) ≤ (Cg * y) ^ 2 := by
    calc
      _ = ‖(⟨GT⟩ : SmoothCcTensorH1 g 0 4)‖ ^ 2 := by
        simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
          iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.zero_add,
          Nat.add_zero] using
            (smooth_cc_tensor_h1_norm_sq_eq_covariant_jet (I := I) (M := M) g 0 4 GT).symm
      _ ≤ (Cg * y) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hGTh1 2
  have hjet1 := hjet 1 (by norm_num)
  have hjet2 := hjet 2 (by norm_num)
  have hY : ‖(⟨Y⟩ : SmoothCcTensorH1 g 0 2)‖ ≤
      Capp * (CB * y) * (Cg * y) := by
    simpa only [Y, operatorFieldComposition_zero_eq_operatorFieldApply] using
      happ g hEq hjet1 hjet2 B GT (CB * y) (Cg * y)
        (mul_nonneg hCB (norm_nonneg _))
        (mul_nonneg hCg (norm_nonneg _)) hB3 hGTjet
  have hspec :
      ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) Y‖ =
        ‖(⟨Y⟩ : SmoothCcTensorH1 g 0 2)‖ := by
    have hspectral := cc_h1_jet_sq (I := I) (M := M) g Y
    have hintrinsic := smooth_cc_tensor_h1_norm_sq_eq_covariant_jet (I := I) (M := M) g 0 2 Y
    nlinarith [norm_nonneg
      (ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) Y),
      norm_nonneg (⟨Y⟩ : SmoothCcTensorH1 g 0 2)]
  have hshift :
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W‖ = z := by
    dsimp only [z]
    rw [norm_ccHs_eq_smoothHs, norm_ccHs_eq_smoothHs]
    have h := (smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap
      (I := I) (M := M) g 3 T).symm
    have hthree : ((3 : ℕ) : ℝ) = (3 : ℝ) := by norm_num
    have hfive : (((3 + 2 : ℕ) : ℝ)) = (5 : ℝ) := by norm_num
    rw [hthree, hfive] at h
    simpa only [W] using h
  have hpair := one_minus_connection_laplacian_squared_pairing_h3_h1_bound
    (I := I) (M := M) g W Y
  change
    |tensorL2Inner (I := I) (M := M) g 0 2
      (oneMinusConnLapSmooth (I := I) g 0 2
        (oneMinusConnLapSmooth (I := I) g 0 2 W)).toFun Y.toFun| ≤ _ at hpair
  rw [hshift, hspec] at hpair
  have hz : 0 ≤ z := norm_nonneg _
  have hscaled : z * ‖(⟨Y⟩ : SmoothCcTensorH1 g 0 2)‖ ≤
      z * (Capp * (CB * y) * (Cg * y)) :=
    mul_le_mul_of_nonneg_left hY hz
  dsimp only [C, B, gm, GT, Y, W, y, z] at hpair hscaled ⊢
  nlinarith

theorem curvature_commutator_pairing_h5_young_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∀ {eta : ℝ}, 0 < eta →
      ∃ rho : ℝ, 0 < rho ∧
        ∀ g : SmoothRiemannianMetric I M,
          MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
          (∀ b : ℕ, b ≤ 3 →
            MetricCovDerivOrderBoundOn (I := I) Set.univ b g gBase Λ) →
          ∃ G : ℝ, 0 ≤ G ∧
            ∀ (T : SmoothCcTensor g 0 2)
              (_hTsymm : ∀ (x : M) (u v : TangentSpace I x),
                ccTensorBilin (I := I) g T x u v =
                  ccTensorBilin (I := I) g T x v u)
              {delta : ℝ}, delta ≤ 1 / 3 → 0 ≤ delta →
              ∀ (hdelta : gFibreOpBound (I := I) (M := M) g
                  (ccTensorBilinSymm (I := I) g T) delta)
                (hdeltaZ : gFibreOpBound (I := I) (M := M) g
                  (ccTensorBilinSymm (I := I) g
                    (0 : SmoothCcTensor g 0 2)) delta),
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ rho →
              ∀ {a : ℝ}, a ∈ Set.Icc (0 : ℝ) 1 →
              let gm := metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ a
              let B : SmoothCcTensor g 4 2 :=
                lieDecomposition2 (I := I) (M := M) g T hdelta hdeltaZ a +
                  (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gm -
                    deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g) +
                  (-2 * a : ℝ) •
                    RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T
              let GT : SmoothCcTensor g 0 4 :=
                covGrad (I := I) (M := M) g 0 3
                    (pointwiseTensorCurv (I := I) (M := M) g 2 T) +
                  pointwiseTensorCurv (I := I) (M := M) g 3
                    (covGrad (I := I) (M := M) g 0 2 T)
              let V : SmoothCcTensor g 0 2 :=
                oneMinusConnLapSmooth (I := I) g 0 2
                  (oneMinusConnLapSmooth (I := I) g 0 2
                    (oneMinusConnLapSmooth (I := I) g 0 2 T))
              2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun
                  (operatorFieldApply (I := I) (M := M) g 4 2 B GT).toFun| ≤
                eta *
                    ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖ ^ 2 +
                  G *
                    ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 4 := by
  intro eta heta
  obtain ⟨rho, hrho, hraw⟩ :=
    curvature_commutator_pairing_h5_uniform_bound (I := I) (M := M) hDim gBase hΛ
  refine ⟨rho, hrho, ?_⟩
  intro g hEq hjet
  obtain ⟨C, hC, hpair⟩ := hraw g hEq hjet
  let G : ℝ := eta⁻¹ * C ^ 2
  have hG : 0 ≤ G := mul_nonneg (inv_nonneg.mpr heta.le) (sq_nonneg C)
  have hetaG : eta * G = C ^ 2 := by
    dsimp only [G]
    field_simp
  refine ⟨G, hG, ?_⟩
  intro T hTsymm delta hdelta_le hdelta0 hdelta hdeltaZ hT2 a ha
  have hp := hpair T hTsymm hdelta_le hdelta0 hdelta hdeltaZ hT2 ha
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let z : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖
  have hyoung : C * y ^ 2 * z ≤ eta * z ^ 2 + G * y ^ 4 := by
    apply (mul_le_mul_iff_of_pos_left heta).mp
    have hrhs :
        eta * (eta * z ^ 2 + G * y ^ 4) =
          (eta * z) ^ 2 + (C * y ^ 2) ^ 2 := by
      calc
        _ = eta ^ 2 * z ^ 2 + (eta * G) * y ^ 4 := by ring
        _ = eta ^ 2 * z ^ 2 + C ^ 2 * y ^ 4 := by rw [hetaG]
        _ = _ := by ring
    rw [hrhs]
    nlinarith [two_mul_le_add_sq (eta * z) (C * y ^ 2)]
  dsimp only [y, z] at hyoung
  exact hp.trans hyoung

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end

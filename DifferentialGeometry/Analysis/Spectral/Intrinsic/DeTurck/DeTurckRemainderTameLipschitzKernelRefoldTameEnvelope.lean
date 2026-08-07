import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzKernelRefoldTopSeparatedBounds
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
  (chartRiemannTensor extChartAt_target_subset_interior_of_boundaryless)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (covGrad unitModel smoothCcTensor_ext_of_unitModel unitTensor pathIntegralCoeffField
  pathIntegralCoeffField_appCc_eq pathIntegralCoeffField_toSection linearizedRicciThreeArmHjoint
  linearizedRicciThreeArmHcont linearizedRicciThreeArmHjoint_zero
  exists_linearizedRicci_threeArm_coeffFields ricciTensor_realize_sub_eq_threeArm_appCc
  linearizedRicciArm0Field linearizedRicciArm1Field linearizedRicciArm2FieldLichnerowicz
  linearizedRicciArm0BaseCoeff linearizedRicciArm0CorrField linearizedRicciArm1BaseCoeff
  linearizedRicciArm1CorrField ricciArmPrincipalCoeff traceHessianCoeff
  linearizedRicci_arm0Field_jointSmooth linearizedRicci_arm1Field_jointSmooth
  linearizedRicci_arm2FieldLichnerowicz_jointSmooth ricciArmOrder1KoszulCoeff
  exists_arm1Koszul_realizedFam_rfns_ballUniform continuousBilinearMap_basis_expand
  unitModel_basis_expand_two unitModel_eq_ccTensorBilin_local appCc_zero_left_local ccTensor02Symm
  symmS_sub ccTensorBilin_symmS iteratedCovGrad_symmS_eq domDomCongrSection
  riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection)
open DifferentialGeometry.PDE.DeTurck (deTurckVF)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (realizedSmallSet realizedSmallSet_isOpen Icc_subset_realizedSmallSet linearizedRicciAt
  ricciTensor_realized_sub_eq_integral_linearizedRicci linearizedRicciAt_eq_deriv_chartSum_on_Ioo
  realizedRicciChartSum jointContMDiff_toModel_continuous_slice
  hasDerivAt_realizedRicciChartSum_general realizedFam)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (symmAbsorbedCoeff symmAbsorbedCoeff_appCc_eq exists_iteratedCovGrad_unitModel_domDomCongrSection
  symmAbsorbedCoeff_riemannianFiberNormSq_le symmAbsorbedCoeff_jet_le)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]

private local instance instCompleteSpaceE_tame : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

open DifferentialGeometry.Analysis.Spectral.DeTurck (cometricLmodel)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (lieDeTurckChartSlope deriv_realizedFam_chartLieDeTurckComp_eq_chartSlope)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (deTurckLieArm2PrincipalCoeff deTurckLieArm1Coeff deTurckLieCoeffField
  deTurckLieArm2PrincipalCoeff_realizedFam_jointSmooth deTurckLieArm1Coeff_realizedFam_jointSmooth
  deTurckLieCoeffField_realizedFam_jointSmooth)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (reindexCoeffGen reindexCoeffFibGen reindexCoeffFibGen_apply reindexCoeffGen_toSection
  deTurckLieTraceCoeff deTurckLieTraceCoeff_toSection deTurckLieTraceFib traceHessianFib
  domDomCongrFibPerm_apply domDomCongrFib_apply traceHessianSlotPerm deTurckLieArm2DivSlotPermA
  deTurckLieArm2DivSlotPermAT traceHessianCoeff_toSection)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (convexPerturbation convexPerturbation_gFibreOpBound realizedFam_inner_of_mem)
open Analysis.Parabolic.TensorSpectral

set_option backward.isDefEq.respectTransparency false

set_option backward.isDefEq.respectTransparency false in

private theorem rfns_iteratedCovGrad_linRicciOrder0RiemannHalfComb_topSeparated_budgetDualCap_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (hδ₀half : δ₀ ≤ 1 / 2) :
    ∃ ε : ℝ, 0 ≤ ε ∧
      27 * Real.sqrt (Module.finrank ℝ E) * (1 - δ₀) * ε ≤
        2 * (32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
          28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2) ∧
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P)
          δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
                  (I := I) (M := M) g₀ g₁
                + (1 / 2 : ℝ) •
                  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                    (I := I) (M := M) g₀ g₁)).toSection x) ≤
          ε ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)
            + C i * Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  by_cases hn1 : Module.finrank ℝ E = 1
  · refine ⟨0, le_refl 0, ?_, fun _ => 0, fun _ => le_refl 0, ?_⟩
    · rw [mul_zero]
      rw [rfns_tl_fibreConst_one hn1]
      norm_num
    · intro g₁ P htie δ hδ_le hδ0 hbound i x
      have hS :
        Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
            (I := I) (M := M) g₀ g₁
          + (1 / 2 : ℝ) •
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
              (I := I) (M := M) g₀ g₁ = (0 : SmoothCcTensor g₀ 2 2) := by
        rw [dim1_linearizedRicciConnDiffOrder0CoeffField_eq_zero (I := I) (M := M) hn1 g₀ g₁,
          dim1_ricciArmOrder0RiemannCoeff_eq_zero (I := I) (M := M) hn1 g₀ g₁]
        rw [smul_zero, add_zero]
      rw [hS]
      rw [rfns_tl_icg_zero (I := I) g₀ 2 2 i]
      rw [rfns_tl_toSection_zero (I := I) g₀ 2 (2 + i) x]
      rw [riemannianFiberNormSq_zero (I := I) (M := M) g₀ 2 (2 + i) x]
      rw [show ((0 : ℝ)) ^ 2 = 0 from by norm_num, zero_mul, zero_mul, add_zero]
  · have hn2 : 2 ≤ Module.finrank ℝ E := by
      have h1 : Module.finrank ℝ E ≠ 0 := NeZero.ne _
      omega
    obtain ⟨KC, hKC_nn, hKC⟩ :=
      riemannianFiberNormSq_iteratedCovGrad_linearizedRicciConnDiffOrder0CoeffField_topAmplitude_le
      (I := I) (M := M) g₀ hδ₀ hδ₀half
    obtain ⟨KR, hKR_nn, hKR⟩ :=
      riemannianFiberNormSq_iteratedCovGrad_refoldKernelContr_symmSecondCovGrad_topAmplitude_le
      (I := I) (M := M) g₀ hδ₀ hδ₀half
    obtain ⟨KA, hKA_nn, hKA⟩ :=
      exists_riemannianFiberNormSq_iteratedCovGrad_ricciArmOrder0AACommCoeffField_window
        (I := I) (M := M) g₀ hδ₀
    obtain ⟨KB, hKB_nn, hKB⟩ :=
      riemannianFiberNormSq_iteratedCovGrad_bgRDiffRefoldRemainderField_boundedFactorGridWindow_le
      (I := I) (M := M) g₀ hδ₀
    obtain ⟨KM, hKM_nn, hKM⟩ := b1_fixedField_jet_bound (I := I) (M := M) g₀ 2 2
      ((1 / 2 : ℝ) •
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
          (I := I) (M := M) g₀ g₀)
    refine ⟨(804 / 125 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2,
      by positivity,
      rfns_tl_budgetDualCap (Module.finrank ℝ E) hn2 hδ₀ hδ₀half
        (by norm_num) (by norm_num),
      fun i => 505 * (KC i + KR i + KA i + KB i + KM i),
      fun i => by
        have h1 := hKC_nn i
        have h2 := hKR_nn i
        have h3 := hKA_nn i
        have h4 := hKB_nn i
        have h5 := hKM_nn i
        positivity, ?_⟩
    intro g₁ P htie δ hδ_le hδ0 hbound i x
    have hQsymm : ∀ (y : M) (v w : TangentSpace I y),
        smoothCcTensorBilinForm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ P) y v w =
        smoothCcTensorBilinForm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ P) y w v := by
      intro y v w
      rw [ccTensorBilin_symmS (I := I) (M := M) g₀ P y v w,
        ccTensorBilin_symmS (I := I) (M := M) g₀ P y w v,
        ccTensorBilinSymm_apply, ccTensorBilinSymm_apply]
      ring
    have htie' : ∀ (y : M) (v w : TangentSpace I y),
        g₁.inner y v w = g₀.inner y v w +
          ccTensorBilinSymm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ P) y v w := by
      intro y v w
      rw [show ccTensorBilinSymm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ P) y v w =
          (1 / 2 : ℝ) * (smoothCcTensorBilinForm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ P)
            y v w
            + smoothCcTensorBilinForm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ P) y w v)
              from by
        rw [ccTensorBilinSymm_apply]]
      rw [ccTensorBilin_symmS (I := I) (M := M) g₀ P y v w,
        ccTensorBilin_symmS (I := I) (M := M) g₀ P y w v,
        ccTensorBilinSymm_apply, ccTensorBilinSymm_apply, htie y v w,
        ccTensorBilinSymm_apply]
      ring
    have hhalf := b1_halfRiemannBackgroundDifference_eq_residualFieldSum_add_kernelContraction
      (I := I) (M := M) g₀ g₁ (ccTensor02Symm (I := I) (M := M) g₀ P) htie' hQsymm
    have hdec :
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
          (I := I) (M := M) g₀ g₁
        + (1 / 2 : ℝ) •
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
            (I := I) (M := M) g₀ g₁ =
        (((Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
            (I := I) (M := M) g₀ g₁
          + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0AACommCoeffField
              (I := I) (M := M) g₀ g₁)
          + Analysis.Parabolic.TensorSpectral.backgroundRicciCommutatorDiffRefoldRemainderField
              (I := I) (M := M) g₀ g₁)
          + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
              (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
              (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1)
          + (1 / 2 : ℝ) •
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
              (I := I) (M := M) g₀ g₀ := by
      have hgoal :
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0AACommCoeffField
            (I := I) (M := M) g₀ g₁
          + Analysis.Parabolic.TensorSpectral.backgroundRicciCommutatorDiffRefoldRemainderField
              (I := I) (M := M) g₀ g₁
          + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
              (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
              (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 =
          (1 / 2 : ℝ) •
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
              (I := I) (M := M) g₀ g₁
          - (1 / 2 : ℝ) •
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
              (I := I) (M := M) g₀ g₀ := by
        rw [← hhalf]
        rw [smul_sub]
      have hstep :
        (((Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
            (I := I) (M := M) g₀ g₁
          + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0AACommCoeffField
              (I := I) (M := M) g₀ g₁)
          + Analysis.Parabolic.TensorSpectral.backgroundRicciCommutatorDiffRefoldRemainderField
              (I := I) (M := M) g₀ g₁)
          + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
              (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
              (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1)
          =
          Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
            (I := I) (M := M) g₀ g₁
          + ((1 / 2 : ℝ) •
              DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                (I := I) (M := M) g₀ g₁
            - (1 / 2 : ℝ) •
              DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                (I := I) (M := M) g₀ g₀) := by
        rw [show
          (((Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
            (I := I) (M := M) g₀ g₁
          + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0AACommCoeffField
              (I := I) (M := M) g₀ g₁)
          + Analysis.Parabolic.TensorSpectral.backgroundRicciCommutatorDiffRefoldRemainderField
              (I := I) (M := M) g₀ g₁)
          + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
              (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
              (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1)
          =
          Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
            (I := I) (M := M) g₀ g₁
          + (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0AACommCoeffField
              (I := I) (M := M) g₀ g₁
            + Analysis.Parabolic.TensorSpectral.backgroundRicciCommutatorDiffRefoldRemainderField
              (I := I) (M := M) g₀ g₁
            + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
              (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
              (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1) from by abel]
        rw [hgoal]
      rw [hstep]
      abel
    rw [hdec]
    rw [iteratedCovGrad_add (I := I) g₀ 2 2 i, iteratedCovGrad_add (I := I) g₀ 2 2 i,
      iteratedCovGrad_add (I := I) g₀ 2 2 i, iteratedCovGrad_add (I := I) g₀ 2 2 i]
    rw [b1_toSection_add (I := I) (M := M) g₀ 2 (2 + i), b1_toSection_add (I := I) (M := M) g₀ 2
      (2 + i),
      b1_toSection_add (I := I) (M := M) g₀ 2 (2 + i), b1_toSection_add (I := I) (M := M) g₀ 2
        (2 + i)]
    have hb_nn : ∀ l, (0 : ℝ) ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) :=
      fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
    have hw_nn : (0 : ℝ) ≤ Combinatorics.boundedFactorGridWindow
        (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) :=
      Combinatorics.boundedFactorGridWindow_nonneg _ hb_nn (i + 1) (i + 3)
    have hw_one : (1 : ℝ) ≤ Combinatorics.boundedFactorGridWindow
        (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) :=
      Combinatorics.one_le_boundedFactorGridWindow _ hb_nn (by omega)
    have hL0b := hKC g₁ P htie hδ_le hδ0 hbound i x
    have hRb := hKR g₁ P htie hδ_le hδ0 hbound i x
    have hAb := hKA g₁ P htie hδ_le hδ0 hbound i x
    have hBb := hKB g₁ P htie hδ_le hδ0 hbound i x
    have hMb : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          ((1 / 2 : ℝ) •
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
              (I := I) (M := M) g₀ g₀)).toSection x) ≤
        KM i * Combinatorics.boundedFactorGridWindow
          (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
      refine le_trans (hKM i x) ?_
      nlinarith [hw_one, hKM_nn i]
    set T1 : TensorRSSpace 2 (2 + i) I x := (iteratedCovGrad (I := I) g₀ 2 2 i
      (Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
        (I := I) (M := M) g₀ g₁)).toSection x with hT1_def
    set T2 : TensorRSSpace 2 (2 + i) I x := (iteratedCovGrad (I := I) g₀ 2 2 i
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0AACommCoeffField
        (I := I) (M := M) g₀ g₁)).toSection x with hT2_def
    set T3 : TensorRSSpace 2 (2 + i) I x := (iteratedCovGrad (I := I) g₀ 2 2 i
      (Analysis.Parabolic.TensorSpectral.backgroundRicciCommutatorDiffRefoldRemainderField
        (I := I) (M := M) g₀ g₁)).toSection x with hT3_def
    set T4 : TensorRSSpace 2 (2 + i) I x := (iteratedCovGrad (I := I) g₀ 2 2 i
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
        (I := I) (M := M) g₀ g₁
        (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
        (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
        (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1)).toSection x with hT4_def
    set T5 : TensorRSSpace 2 (2 + i) I x := (iteratedCovGrad (I := I) g₀ 2 2 i
      ((1 / 2 : ℝ) •
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
          (I := I) (M := M) g₀ g₀)).toSection x with hT5_def
    set btop : ℝ := riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
      ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) with hbtop_def
    set w : ℝ := Combinatorics.boundedFactorGridWindow
      (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) with hw_def
    have hsq_chain : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((((T1 + T2) + T3) + T4) + T5)) ≤
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x T1)
        + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x T2)
        + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x T3)
        + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x T4)
        + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x T5) := by
      have h4 := b1_sqrt_rfns_add_le (I := I) (M := M) g₀ 2 (2 + i) x
        (((T1 + T2) + T3) + T4) T5
      have h3 := b1_sqrt_rfns_add_le (I := I) (M := M) g₀ 2 (2 + i) x
        ((T1 + T2) + T3) T4
      have h2 := b1_sqrt_rfns_add_le (I := I) (M := M) g₀ 2 (2 + i) x (T1 + T2) T3
      have h1 := b1_sqrt_rfns_add_le (I := I) (M := M) g₀ 2 (2 + i) x T1 T2
      linarith [h1, h2, h3, h4]
    have hsp1 : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x T1) ≤
        ((21 / 4 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2) * Real.sqrt btop
        + Real.sqrt (KC i * w) :=
      b1_sqrt_head_split (by positivity) (hb_nn (i + 2)) (hKC_nn i) hw_nn hL0b
    have hsp4 : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x T4) ≤
        ((23 / 20 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2) * Real.sqrt btop
        + Real.sqrt (KR i * w) :=
      b1_sqrt_head_split (by positivity) (hb_nn (i + 2)) (hKR_nn i) hw_nn hRb
    have hsp2 : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x T2) ≤
        Real.sqrt (KA i * w) := b1_sqrt_le_of_le hAb
    have hsp3 : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x T3) ≤
        Real.sqrt (KB i * w) := b1_sqrt_le_of_le hBb
    have hsp5 : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x T5) ≤
        Real.sqrt (KM i * w) := b1_sqrt_le_of_le hMb
    have hTsum : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((((T1 + T2) + T3) + T4) + T5)) ≤
        (((23 / 20 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2)
          + ((21 / 4 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2)) * Real.sqrt btop
        + (Real.sqrt (KC i * w) + Real.sqrt (KR i * w) + Real.sqrt (KA i * w)
          + Real.sqrt (KB i * w) + Real.sqrt (KM i * w)) := by
      have hexp : (((23 / 20 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2)
          + ((21 / 4 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2)) * Real.sqrt btop =
          ((23 / 20 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2) * Real.sqrt btop
          + ((21 / 4 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2) * Real.sqrt btop := by
        ring
      rw [hexp]
      linarith [hsq_chain, hsp1, hsp2, hsp3, hsp4, hsp5]
    have hfin := b1_young_assembly (hb_nn (i + 2)) hw_nn
      (by positivity : (0 : ℝ) ≤ (23 / 20 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2)
      (by positivity : (0 : ℝ) ≤ (21 / 4 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2)
      (hKC_nn i) (hKR_nn i) (hKA_nn i) (hKB_nn i) (hKM_nn i)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + i) x
        ((((T1 + T2) + T3) + T4) + T5)) hTsum
    have hEamp : (((201 : ℝ) / 200) *
        (((23 / 20 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2)
          + ((21 / 4 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2))) ^ 2 =
        ((804 / 125 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2) ^ 2 := by
      ring
    rw [hEamp] at hfin
    exact hfin

set_option backward.isDefEq.respectTransparency false in

private theorem
    linearizedRicciConnDiffOrder0RiemannHalfComb_perOrder_l2_topArm_tameEnvelope_highOrder
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (hδ₀half : δ₀ ≤ 1 / 2) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
    ∃ ε : ℝ, 0 ≤ ε ∧
      27 * Real.sqrt (Module.finrank ℝ E) * (1 - δ₀) * ε ≤
        2 * (32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
          28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), a < i →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
                  (I := I) (M := M) g₀ g₁
                + (1 / 2 : ℝ) •
                  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                    (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
              ε ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 := by
  classical
  obtain ⟨ε, hε_nn, hε_cap, C, hC_nn, hC⟩ :=
    rfns_iteratedCovGrad_linRicciOrder0RiemannHalfComb_topSeparated_budgetDualCap_le
      (I := I) (M := M) g₀ hδ₀ hδ₀half
  obtain ⟨Kflat, hKflat_nn, hKflat⟩ :=
    boundedFactorGridWindow_integral_ballUniform_flat_allOrders
      (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => C i * Kflat i, fun i => mul_nonneg (hC_nn i) (hKflat_nn i),
    ε, hε_nn, hε_cap, ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
    have hδ0 : 0 ≤ δ := by
      obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
        haveI : Nontrivial (TangentSpace I x₀) := by
          have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
            have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
            rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
          exact Module.nontrivial_of_finrank_pos hfr
        exact exists_ne 0
      have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
      have hbound := hδ x₀ v v
      have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ P x₀ v v| := abs_nonneg _
      by_contra hδc
      have hδc' : δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 := mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    obtain ⟨hWint, hWbound⟩ := hKflat P hPball i
    have hbint : MeasureTheory.Integrable
        (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      DifferentialGeometry.Analysis.Elliptic.integrable_riemannianFiberNormSq_toSection
        (I := I) (M := M) g₀ 0 (2 + (i + 2)) (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P)
    have hF_int : MeasureTheory.Integrable
        (fun x => ε ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)
          + C i * Combinatorics.boundedFactorGridWindow
              (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      MeasureTheory.Integrable.add (hbint.const_mul (ε ^ 2)) (hWint.const_mul (C i))
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
            (I := I) (M := M) g₀ g₁
          + (1 / 2 : ℝ) •
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
              (I := I) (M := M) g₀ g₁))
      (fun x => ε ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)
        + C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3))
      hF_int
      (fun x => hC g₁ P htie hδ_le hδ0 hδ i x)
    refine le_trans key ?_
    rw [MeasureTheory.integral_add (hbint.const_mul (ε ^ 2)) (hWint.const_mul (C i)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have hPtop : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
        ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 := by
      rw [SmoothCcTensor.norm_def (I := I) (M := M) (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P),
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 0
          (2 + (i + 2)) (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P)]
    rw [hPtop]
    have h2 : C i * (∫ x, Combinatorics.boundedFactorGridWindow
        (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        (C i * Kflat i) * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
      calc C i * (∫ x, Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
          ≤ C i * (Kflat i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left hWbound (hC_nn i)
        _ = (C i * Kflat i) * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by ring
    linarith
  · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
    have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
            (I := I) (M := M) g₀ g₁
          + (1 / 2 : ℝ) •
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
              (I := I) (M := M) g₀ g₁)‖ = 0 := by
      rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
        MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
    rw [hz]
    have hwin_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hK_nn : (0 : ℝ) ≤ C i * Kflat i := mul_nonneg (hC_nn i) (hKflat_nn i)
    have h1 : (0 : ℝ) ≤ (C i * Kflat i) * (1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) :=
      mul_nonneg hK_nn (by linarith)
    have h2 : (0 : ℝ) ≤ ε ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 :=
      mul_nonneg (sq_nonneg ε) (sq_nonneg _)
    nlinarith

set_option backward.isDefEq.respectTransparency false in

theorem exists_linearizedRicciArm0CorrField_realizedFam_jetL2_topArm_tameEnvelope_highOrder
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (hδ₀half : δ₀ ≤ 1 / 2) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
    ∃ ε : ℝ, 0 ≤ ε ∧
      27 * Real.sqrt (Module.finrank ℝ E) * (1 - δ₀) * ε ≤
        2 * (32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
          28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), a < i → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0Coeff
                  (I := I) g₀ T T' hδ hδ' s
                - linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s
                + (3 / 2 : ℝ) •
                  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                    (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)
                - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0CurvCoeff
                    (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) +
              ε ^ 2 * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) := by
  classical
  obtain ⟨K, hK_nn, ε, hε_nn, hε_cap, hK⟩ :=
    linearizedRicciConnDiffOrder0RiemannHalfComb_perOrder_l2_topArm_tameEnvelope_highOrder
      (I := I) (M := M) g₀ a ha_super hR hδ₀ hδ₀half
  refine ⟨K, hK_nn, ε, hε_nn, hε_cap, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hδP : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s))
      ((1 - s) * δ' + s * δ) :=
    convexPerturbation_gFibreOpBound (I := I) (M := M) g₀ T T' hδ hδ' hs0 hs1
  have hδP_le : (1 - s) * δ' + s * δ ≤ δ₀ := by
    have e1 : (1 - s) * δ' ≤ (1 - s) * δ₀ := mul_le_mul_of_nonneg_left hδ'_le h1ms
    have e2 : s * δ ≤ s * δ₀ := mul_le_mul_of_nonneg_left hδ_le hs0
    have e3 : (1 - s) * δ₀ + s * δ₀ = δ₀ := by ring
    linarith [e1, e2, e3]
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (realizedFam (I := I) g₀ T T' hδ hδ' s).inner y v w =
        g₀.inner y v w +
          ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) y v w :=
    fun y v w =>
      realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ'
        (Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs) y v w
  have hnorm_le : ∀ j : ℕ,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ≤
        (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
          + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
    intro j
    have heq : iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)
        = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
          + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
      rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
        iteratedCovGrad_add, iteratedCovGrad_smul', iteratedCovGrad_smul']
    rw [heq]
    calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
            + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
        ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
      _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg h1ms, abs_of_nonneg hs0]
  have hPball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ≤ R := by
    intro j hj
    calc ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖
        ≤ (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := hnorm_le j
      _ ≤ (1 - s) * R + s * R :=
          add_le_add (mul_le_mul_of_nonneg_left (hT'ball j hj) h1ms)
            (mul_le_mul_of_nonneg_left (hTball j hj) hs0)
      _ = R := by ring
  have hwin_ineq : ∀ j : ℕ,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2 := by
    intro j
    have hnorm := hnorm_le j
    have hy_nn : 0 ≤ (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
        + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ :=
      add_nonneg (mul_nonneg h1ms (norm_nonneg _)) (mul_nonneg hs0 (norm_nonneg _))
    nlinarith [mul_le_mul hnorm hnorm (norm_nonneg
        (iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s))) hy_nn,
      mul_nonneg (mul_nonneg hs0 h1ms)
        (sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ -
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖)),
      mul_nonneg h1ms (sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖),
      mul_nonneg hs0 (sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖)]
  rw
    [Analysis.Parabolic.TensorSpectral.corrArm0Combination_eq_order0_add_halfRiemann
    (I := I) (M := M) g₀ T T' hδ hδ' s]
  have hmain := hK (realizedFam (I := I) g₀ T T' hδ hδ' s)
    (convexPerturbation (I := I) g₀ T T' s) hδP_le hδP htie hPball i hi
  have hwinsum : ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
      ∑ j ∈ Finset.range (i + 2),
        (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
    Finset.sum_le_sum (fun j _ => hwin_ineq j)
  have h1 : K i * (1 + ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2) ≤
      K i * (1 + ∑ j ∈ Finset.range (i + 2),
        (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) :=
    mul_le_mul_of_nonneg_left (by linarith) (hK_nn i)
  have h2 : ε ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2)
        (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
      ε ^ 2 * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) :=
    mul_le_mul_of_nonneg_left (hwin_ineq (i + 2)) (sq_nonneg ε)
  linarith

set_option backward.isDefEq.respectTransparency false in

theorem linearizedRicciArm0CorrField_allOrder_tameEnvelope_interface
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (hδ₀half : δ₀ ≤ 1 / 2) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
    ∃ ε : ℝ, 0 ≤ ε ∧
      27 * Real.sqrt (Module.finrank ℝ E) * (1 - δ₀) * ε ≤
        2 * (32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
          28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (linearizedRicciArm0CorrField (I := I) g₀ T T' hδ hδ' s
                + (3 / 2 : ℝ) •
                  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                    (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)
                - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0CurvCoeff
                    (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) +
              ε ^ 2 * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) := by
  classical
  obtain ⟨Kle, hKle_nn, hKle⟩ :=
    Analysis.Parabolic.TensorSpectral.exists_corrArm0Field_realizedFam_jetL2_tameEnvelope
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Kgt, hKgt_nn, ε, hε_nn, hε_cap, hKgt⟩ :=
    exists_linearizedRicciArm0CorrField_realizedFam_jetL2_topArm_tameEnvelope_highOrder
      (I := I) (M := M) g₀ a ha_super hR hδ₀ hδ₀half
  refine ⟨fun i => Kle i + Kgt i, fun i => add_nonneg (hKle_nn i) (hKgt_nn i),
    ε, hε_nn, hε_cap, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i s hs
  have hid :=
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_arm0_arm1_corrField_data
      (I := I) g₀ T T' hδ hδ').choose_spec.choose_spec.2.2.2.2.1
  rw [show linearizedRicciArm0CorrField (I := I) g₀ T T' hδ hδ' s =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0Coeff
          (I := I) g₀ T T' hδ hδ' s
        - linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s from hid s]
  have hwin_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
      (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
    Finset.sum_nonneg fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _)
  have htop_nn : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
      ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hdist : (Kle i + Kgt i) * (1 + ∑ j ∈ Finset.range (i + 2),
      (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) =
      Kle i * (1 + ∑ j ∈ Finset.range (i + 2),
        (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) +
      Kgt i * (1 + ∑ j ∈ Finset.range (i + 2),
        (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := add_mul _ _ _
  rcases le_or_gt i a with hia | hia
  · have hb := hKle T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hia s hs
    have h1 : (0 : ℝ) ≤ Kgt i * (1 + ∑ j ∈ Finset.range (i + 2),
        (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) :=
      mul_nonneg (hKgt_nn i) (by linarith)
    have h2 : (0 : ℝ) ≤ ε ^ 2 * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) :=
      mul_nonneg (sq_nonneg ε) htop_nn
    linarith
  · have hb := hKgt T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hia s hs
    have h1 : (0 : ℝ) ≤ Kle i * (1 + ∑ j ∈ Finset.range (i + 2),
        (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) :=
      mul_nonneg (hKle_nn i) (by linarith)
    linarith

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
theorem linearizedRicciThreeArmHjoint_add [SigmaCompactSpace M] (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (A B : ℝ → SmoothCcTensor g₀ r 2) {δ δ' : ℝ}
    (hA : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r A (δ := δ) (δ' := δ'))
    (hB : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r B (δ := δ) (δ' := δ')) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r
      (fun s => A s + B s) (δ := δ) (δ' := δ') := by
  have hadd := jointTotalSpaceRS_add_fw (I := I) (r := r) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (A p.2).toSection p.1)
    (fun p : M × ℝ => (B p.2).toSection p.1)
    hA hB
  refine hadd.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r 2 I z) p.1 t) ?_
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
theorem linearizedRicciThreeArmHjoint_add_smul [SigmaCompactSpace M] (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (c : ℝ) (A B : ℝ → SmoothCcTensor g₀ r 2) {δ δ' : ℝ}
    (hA : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r A (δ := δ) (δ' := δ'))
    (hB : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r B (δ := δ) (δ' := δ')) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r
      (fun s => A s + c • B s) (δ := δ) (δ' := δ') := by
  have hsmul := lieArm_jointRS_const_smul_local (I := I) (r := r) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) c
    (fun p : M × ℝ => (B p.2).toSection p.1) hB
  have hadd := jointTotalSpaceRS_add_fw (I := I) (r := r) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (A p.2).toSection p.1)
    (fun p : M × ℝ => c • (B p.2).toSection p.1)
    hA hsmul
  refine hadd.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r 2 I z) p.1 t) ?_
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private theorem threeArmHjoint_const_smul_fw [SigmaCompactSpace M] (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (c : ℝ) (B : ℝ → SmoothCcTensor g₀ r 2) {δ δ' : ℝ}
    (hB : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r B (δ := δ) (δ' := δ')) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r
      (fun s => c • B s) (δ := δ) (δ' := δ') := by
  have hsmul := lieArm_jointRS_const_smul_local (I := I) (r := r) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) c
    (fun p : M × ℝ => (B p.2).toSection p.1) hB
  refine hsmul.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r 2 I z) p.1 t) ?_
  rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]

set_option backward.isDefEq.respectTransparency false in

theorem exists_riemannPalatini_curvatureRefold_data
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (hδ₀_half : δ₀ ≤ 1 / 2) :
    ∃ Λra : ℝ, 0 ≤ Λra ∧ ∃ Kra : ℕ → ℝ, (∀ i, 0 ≤ Kra i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (_hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∃ (C0ra : ℝ → SmoothCcTensor g₀ 2 2) (C2ra : ℝ → SmoothCcTensor g₀ 4 2),
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 C0ra (δ := δ) (δ' := δ) ∧
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 C2ra (δ := δ) (δ' := δ) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            operatorFieldApply (I := I) (M := M) g₀ 2 2
                (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                  (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
                (iteratedCovGrad (I := I) g₀ 0 2 0 T) =
              operatorFieldApply (I := I) (M := M) g₀ 2 2 (C0ra s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 T) +
                operatorFieldApply (I := I) (M := M) g₀ 4 2 (C2ra s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 T)) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((C0ra s).toSection x) ≤
              Λra ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x) ≤ Λra ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x ((C2ra s).toSection x) ≤
              (max (8 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) 0) ^ 2) ∧
          (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            ‖iteratedCovGrad (I := I) g₀ 2 2 i (C0ra s)‖ ^ 2 ≤
              Kra i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) ∧
          (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            ‖iteratedCovGrad (I := I) g₀ 4 2 i (C2ra s)‖ ^ 2 ≤
              Kra i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) :=
  by
    classical
    obtain ⟨Λid, hΛid_nn, Kid, hKid_nn, qA, qB, hqAB, hID⟩ :=
      Analysis.Parabolic.TensorSpectral.exists_riemannPalatini_refold_identity_data
        (I := I) (M := M) g₀ a ha_super hR hδ₀
    obtain ⟨Λrm, hΛrm_nn, hRm⟩ :=
      exists_ricciArmOrder0RiemannCoeff_realizedFam_riemannianFiberNormSq_ballUniform_sq
        (I := I) (M := M) g₀ a ha_super hR hδ₀
    obtain ⟨Kwin, hKwin_nn, hWin⟩ :=
      Analysis.Parabolic.TensorSpectral.exists_riemannPalatiniRefoldC2Family_l2JetWindow
        (I := I) (M := M) g₀ a ha_super hR hδ₀ qA qB hqAB
    have hsum_nn : (0 : ℝ) ≤ Λid ^ 2 + Λrm ^ 2 := by positivity
    refine ⟨Real.sqrt (Λid ^ 2 + Λrm ^ 2), Real.sqrt_nonneg _,
      fun i => Kid i + Kwin i,
      fun i => by
        have h1 := hKid_nn i
        have h2 := hKwin_nn i
        linarith, ?_⟩
    intro T hTsymm δ hδ_le hδ hδZ hTjets
    have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
    have hδ_half : δ ≤ 1 / 2 := hδ_le.trans hδ₀_half
    obtain ⟨C0ra, hjC0, hidRA, hsupC0, henvC0⟩ := hID T hTsymm hδ_le hδ hδZ hTjets
    obtain ⟨-, henvC2⟩ := hWin T hδ_le hδ_half hδ hδZ hTjets
    refine ⟨C0ra,
      fun s => (2 : ℝ) •
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannPalatiniRefoldC2Family
          (I := I) (M := M) g₀ T hδ hδZ qA qB s,
      hjC0,
      threeArmHjoint_const_smul_fw (I := I) (M := M) g₀ 4 (2 : ℝ) _
        (Analysis.Parabolic.TensorSpectral.riemannPalatiniRefoldC2Family_threeArmHjoint
          (I := I) (M := M) g₀ T hδ hδZ qA qB),
      hidRA, ?_, ?_,
      Analysis.Parabolic.TensorSpectral.riemannPalatiniRefoldC2Family_riemannianFiberNormSq_le
        (I := I) (M := M) g₀ T hδ_lt hδ_half hδ hδZ qA qB hqAB,
      ?_, ?_⟩
    · intro s hs x
      have h := hsupC0 s hs x
      have h2 := sq_nonneg Λrm
      rw [Real.sq_sqrt hsum_nn]
      linarith
    · intro s hs x
      have h := hRm T hδ_le hδ hδZ hTjets s hs x
      have h1 := sq_nonneg Λid
      rw [Real.sq_sqrt hsum_nn]
      linarith
    · intro i s hs
      try dsimp only
      have h := henvC0 i s hs
      have hX : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 := by positivity
      nlinarith [mul_nonneg (hKwin_nn i) hX]
    · intro i s hs
      try dsimp only
      have h := henvC2 i s hs
      have hX : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 := by positivity
      nlinarith [mul_nonneg (hKid_nn i) hX]

end DifferentialGeometry.Analysis.Spectral

end

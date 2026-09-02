import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Sobolev.MoserTameProduct
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergProductTwoArm
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradParametricJointSmooth
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovariantBilinearLeibniz
import DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.FiberNormUniformBound
import DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.FiberNormRawComponentBound
import DifferentialGeometry.Analysis.Integration.Measure.FamilyDecomposition
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RawComponentEuclideanBridge
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChartDeTurckRicciRHSRealizeJet
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHSSectionChartComponentIdentity
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.InverseMetricDifferenceSlotCoefficient
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckCurvatureArmCoeffField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldApplicationDropIteratedGrid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckLinearization
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRHSSectionRealizeUnitModel
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmOperatorFieldApplication
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.PathIntegralFibreNormTransfer
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.ArmCoefficient.ReindexingNorm
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciDeTurck.Remainder.Coefficient.L2JetMoser
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SymmAbsorbedCoeffInputReindexBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckPrincipalCoefficientBackgroundJetBound
import DifferentialGeometry.Analysis.Sobolev.Embedding.ContinuousSobolevRealization
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieHigherOrderCoeffField
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.MetricPerturbationPathChartLieDerivative
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.LieDeTurckRemainderOrderSplit
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.Kernel.L2JetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieCoeffOperatorFieldApplicationValue
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.GramDerivativeChartEvaluation
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.Coefficient.L2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.ArmOne.L2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.ArmTwo.L2JetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.PalatiniDecomposition.TameEstimates
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzArmConnLapJetBounds
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzRicciArmCoeffBallUniform
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LieCorrectionTameBounds
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle
    ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev
    DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
  (chartRiemannTensor extChartAt_target_subset_interior_of_boundaryless)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (covGrad unitModel smoothCcTensor_ext_of_unitModel unitTensor pathIntegralCoeffField
  pathIntegralCoeffField_operatorFieldApplication_eq pathIntegralCoeffField_toSection linearizedRicciThreeArmHjoint
  linearizedRicciThreeArmHcont linearizedRicciThreeArmHjoint_zero
  exists_linearizedRicci_threeArm_coeffFields ricciTensor_realize_sub_eq_threeArm_operatorFieldApply
  linearizedRicciArm0Field linearizedRicciArm1Field linearizedRicciArm2FieldLichnerowicz
  linearizedRicciArm0BaseCoeff linearizedRicciArm0CorrField linearizedRicciArm1BaseCoeff
  linearizedRicciArm1CorrField ricciDeTurckPrincipalCoefficient traceHessianCoeff
  linearizedRicci_arm0Field_jointSmooth linearizedRicci_arm1Field_jointSmooth
  linearizedRicci_arm2FieldLichnerowicz_jointSmooth ricciArmOrder1KoszulCoeff
  exists_arm1Koszul_metricPerturbationPath_riemannianFiberNormSq_ballUniform continuousBilinearMap_basis_expand
  unitModel_basis_expand_two unitModel_eq_ccTensorBilin_local operatorFieldApplication_zero_left_local ccTensor02Symm
  symmS_sub ccTensorBilin_symmS iteratedCovGrad_symmS_eq domDomCongrSection
  riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection)
open DifferentialGeometry.PDE.DeTurck (deTurckVF)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (metricPerturbationPathDomain metricPerturbationPathDomain_isOpen Icc_subset_metricPerturbationPathDomain linearizedRicciAt
  ricciTensor_realized_sub_eq_integral_linearizedRicci linearizedRicciAt_eq_deriv_chartSum_on_Ioo
  realizedRicciChartSum
  hasDerivAt_realizedRicciChartSum_general metricPerturbationPath)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (symmAbsorbedCoeff symmAbsorbedCoeff_operatorFieldApplication_eq exists_iteratedCovGrad_unitModel_domDomCongrSection
  symmAbsorbedCoeff_riemannianFiberNormSq_le symmAbsorbedCoeff_jet_le)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance instCompleteSpaceE_tame : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

open DifferentialGeometry.Analysis.Spectral.DeTurck (cometricLmodel)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (lieDeTurckChartSlope deriv_metricPerturbationPath_chartLieDeTurckComp_eq_chartSlope)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (deTurckLieArm2PrincipalCoeff deTurckLieArm1Coeff deTurckLieCoeffField
  deTurckLieArm2PrincipalCoeff_metricPerturbationPath_jointSmooth deTurckLieArm1Coeff_metricPerturbationPath_jointSmooth
  deTurckLieCoeffField_metricPerturbationPath_jointSmooth)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (reindexCoeffGen reindexCoeffFibGen reindexCoeffFibGen_apply reindexCoeffGen_toSection
  deTurckLieTraceCoeff deTurckLieTraceCoeff_toSection deTurckLieTraceFib traceHessianFib
  domDomCongrFibPerm_apply domDomCongrFib_apply traceHessianSlotPerm deTurckLieArm2DivSlotPermA
  deTurckLieArm2DivSlotPermAT traceHessianCoeff_toSection)

open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (convexPerturbation convexPerturbation_gFibreOpBound metricPerturbationPath_inner_of_mem)


lemma pAO_range_subset {m n : ℕ} (h : m ≤ n) :
    Finset.range m ⊆ Finset.range n := by
  intro x hx
  exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) h)

private theorem inverseMetricDifferenceSlotCoefficient_jetL2_allOrder_tame (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδP : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ j : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 2 2 j (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁)‖ ^ 2 ≤
            K j * (1 + ∑ q ∈ Finset.range (j + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2) := by
  classical
  obtain ⟨C, hC_nn, hCp⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_inverseMetricDifferenceSlotCoefficient_diagonalProductGrid_le (I := I) (M := M)
      g₀ hδ₀
  obtain ⟨Kt, hKt_nn, hKt⟩ :=
    antidiagonalTupleGrid_integral_ballUniform_tameWindow (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun j => C j * Kt j, fun j => mul_nonneg (hC_nn j) (hKt_nn j), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδP hPball j
  obtain ⟨hint, hbound⟩ := hKt P hPball j
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + j)
    (iteratedCovGrad (I := I) g₀ 2 2 j (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁))
    (fun x => C j * ∑ n ∈ Finset.range (j + 1),
      ∑ e ∈ Finset.Nat.antidiagonalTuple n j,
        ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
    (hint.const_mul (C j))
    (fun x => hCp g₁ P htie hδ_le hδ0 hδP j x)
  refine le_trans key ?_
  rw [MeasureTheory.integral_const_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (le_trans hbound (le_of_eq rfl)) (hC_nn j)

theorem pAO_traceHessian_jetSum_tame (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Q : ℕ → ℝ, (∀ i, 0 ≤ Q i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδP : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ i : ℕ,
          ∑ n ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 4 2 n
              (traceHessianCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
            Q i * (1 + ∑ q ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2) := by
  classical
  obtain ⟨Cth, hCth_nn, hCth⟩ :=
    traceHessianCoeff_sub_background_jetL2_le_inverseMetricDifferenceSlotCoefficient_jetL2 (I := I) (M := M) g₀
  obtain ⟨Kg, hKg_nn, hKg⟩ :=
    inverseMetricDifferenceSlotCoefficient_jetL2_allOrder_tame (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => 2 * (∑ n ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 4 2 n
          (traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2)
      + 2 * (∑ n ∈ Finset.range (i + 1), Cth n) * (∑ q ∈ Finset.range (i + 1), Kg q),
    fun i => by
      have h1 : (0 : ℝ) ≤ ∑ n ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 n
            (traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 :=
        Finset.sum_nonneg fun n _ => sq_nonneg _
      have h2 : (0 : ℝ) ≤ ∑ n ∈ Finset.range (i + 1), Cth n :=
        Finset.sum_nonneg fun n _ => hCth_nn n
      have h3 : (0 : ℝ) ≤ ∑ q ∈ Finset.range (i + 1), Kg q :=
        Finset.sum_nonneg fun q _ => hKg_nn q
      positivity, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδP hPball i
  set W : ℝ := 1 + ∑ q ∈ Finset.range (i + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2 with hW_def
  have hW1 : (1 : ℝ) ≤ W := by
    rw [hW_def]
    have : (0 : ℝ) ≤ ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  have hW_nn : (0 : ℝ) ≤ W := le_trans zero_le_one hW1
  have hgterm : ∀ q ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g₀ 2 2 q (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁)‖ ^ 2 ≤
        Kg q * W := by
    intro q hq
    have hq_le : q + 1 ≤ i + 1 := by
      have := Finset.mem_range.mp hq; omega
    refine le_trans (hKg g₁ P htie hδ_le hδ0 hδP hPball q) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hKg_nn q)
    rw [hW_def]
    have hmono : ∑ q' ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 q' P‖ ^ 2 ≤
        ∑ q' ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 q' P‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (pAO_range_subset hq_le) (fun _ _ _ => sq_nonneg _)
    linarith
  have hgsum : ∑ q ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g₀ 2 2 q (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁)‖ ^ 2 ≤
      (∑ q ∈ Finset.range (i + 1), Kg q) * W := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum hgterm
  have hterm : ∀ n ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g₀ 4 2 n (traceHessianCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
        2 * ‖iteratedCovGrad (I := I) g₀ 4 2 n
            (traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2
          + 2 * Cth n * ∑ j ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 j (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁)‖ ^ 2 := by
    intro n hn
    have hn_le : n + 1 ≤ i + 1 := by
      have := Finset.mem_range.mp hn; omega
    have hsplit : traceHessianCoeff (I := I) (M := M) g₀ g₁ =
        (traceHessianCoeff (I := I) (M := M) g₀ g₁
          - traceHessianCoeff (I := I) (M := M) g₀ g₀)
        + traceHessianCoeff (I := I) (M := M) g₀ g₀ := by
      rw [sub_add_cancel]
    have hadd := lieArm1_normSq_iteratedCovGrad_add_le (I := I) (M := M) g₀ 4 2 n
      (traceHessianCoeff (I := I) (M := M) g₀ g₁
        - traceHessianCoeff (I := I) (M := M) g₀ g₀)
      (traceHessianCoeff (I := I) (M := M) g₀ g₀)
    have hdiff := hCth g₁ n
    have hdiff_wide : ‖iteratedCovGrad (I := I) g₀ 4 2 n
        (traceHessianCoeff (I := I) (M := M) g₀ g₁
          - traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤
        Cth n * ∑ j ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 2 2 j (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁)‖ ^ 2 := by
      refine le_trans hdiff ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCth_nn n)
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (pAO_range_subset hn_le) (fun _ _ _ => sq_nonneg _)
    calc ‖iteratedCovGrad (I := I) g₀ 4 2 n
            (traceHessianCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2
        = ‖iteratedCovGrad (I := I) g₀ 4 2 n
            ((traceHessianCoeff (I := I) (M := M) g₀ g₁
              - traceHessianCoeff (I := I) (M := M) g₀ g₀)
            + traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 := by rw [← hsplit]
      _ ≤ 2 * ‖iteratedCovGrad (I := I) g₀ 4 2 n
            (traceHessianCoeff (I := I) (M := M) g₀ g₁
              - traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2
          + 2 * ‖iteratedCovGrad (I := I) g₀ 4 2 n
            (traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 := hadd
      _ ≤ 2 * ‖iteratedCovGrad (I := I) g₀ 4 2 n
            (traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2
          + 2 * Cth n * ∑ j ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 j (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁)‖ ^ 2 := by
          linarith [hdiff_wide]
  have hgsum_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g₀ 2 2 j (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc ∑ n ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 4 2 n
          (traceHessianCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2
      ≤ ∑ n ∈ Finset.range (i + 1),
          (2 * ‖iteratedCovGrad (I := I) g₀ 4 2 n
              (traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2
            + 2 * Cth n * ∑ j ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 2 2 j (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁)‖ ^ 2) :=
        Finset.sum_le_sum hterm
    _ = 2 * (∑ n ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 n
            (traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2)
        + 2 * (∑ n ∈ Finset.range (i + 1), Cth n)
          * ∑ j ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 j (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁)‖ ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ 2 * (∑ n ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 n
            (traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2)
        + 2 * (∑ n ∈ Finset.range (i + 1), Cth n)
          * ((∑ q ∈ Finset.range (i + 1), Kg q) * W) := by
        have h2c : (0 : ℝ) ≤ 2 * (∑ n ∈ Finset.range (i + 1), Cth n) := by
          have : (0 : ℝ) ≤ ∑ n ∈ Finset.range (i + 1), Cth n :=
            Finset.sum_nonneg fun n _ => hCth_nn n
          linarith
        have := mul_le_mul_of_nonneg_left hgsum h2c
        linarith
    _ ≤ (2 * (∑ n ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 n
            (traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2)
        + 2 * (∑ n ∈ Finset.range (i + 1), Cth n)
          * (∑ q ∈ Finset.range (i + 1), Kg q)) * W := by
        have h1 : (0 : ℝ) ≤ ∑ n ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 4 2 n
              (traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 :=
          Finset.sum_nonneg fun n _ => sq_nonneg _
        have h2 : (0 : ℝ) ≤ ∑ n ∈ Finset.range (i + 1), Cth n :=
          Finset.sum_nonneg fun n _ => hCth_nn n
        have h3 : (0 : ℝ) ≤ ∑ q ∈ Finset.range (i + 1), Kg q :=
          Finset.sum_nonneg fun q _ => hKg_nn q
        have e1 : (∑ n ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 4 2 n
              (traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2) ≤
            (∑ n ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 4 2 n
                (traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2) * W :=
          le_mul_of_one_le_right h1 hW1
        nlinarith [e1]

theorem pAO_connectionDifferenceSection_jetL2_tame (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ F : ℕ → ℝ, (∀ l, 0 ≤ F l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδP : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ l : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 1 2 l (connectionDifferenceSection (I := I) g₁ g₀)‖ ^ 2 ≤
            F l * (1 + ∑ q ∈ Finset.range (l + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    exists_riemannianFiberNormSq_iteratedCovGrad_connectionDifferenceSection_tgrid (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kt, hKt_nn, hKt⟩ :=
    antidiagonalTupleGrid_integral_ballUniform_tameWindow (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun l => CA l * ∑ k ∈ Finset.range (l + 2), Kt k,
    fun l => mul_nonneg (hCA_nn l)
      (Finset.sum_nonneg fun k _ => hKt_nn k), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδP hPball l
  set W : ℝ := 1 + ∑ q ∈ Finset.range (l + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2 with hW_def
  have hW1 : (1 : ℝ) ≤ W := by
    rw [hW_def]
    have : (0 : ℝ) ≤ ∑ q ∈ Finset.range (l + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  have hint_all : ∀ k ∈ Finset.range (l + 2), MeasureTheory.Integrable
      (fun x => ∑ n ∈ Finset.range (k + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
          ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    fun k _ => (hKt P hPball k).1
  have hptw : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 1 2 l
          (connectionDifferenceSection (I := I) g₁ g₀)).toSection x) ≤
      CA l * ∑ k ∈ Finset.range (l + 2),
        Combinatorics.antidiagonalTupleGrid
          (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
            ((iteratedCovGrad (I := I) g₀ 0 2 j' P).toSection x)) k :=
    fun x => hCA g₁ P htie hδ_le hδ0 hδP l x
  have hgrid_eq : ∀ (x : M) (k : ℕ),
      Combinatorics.antidiagonalTupleGrid
        (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
          ((iteratedCovGrad (I := I) g₀ 0 2 j' P).toSection x)) k =
      ∑ n ∈ Finset.range (k + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
          ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) :=
    fun x k => rfl
  have hint : MeasureTheory.Integrable
      (fun x => CA l * ∑ k ∈ Finset.range (l + 2),
        Combinatorics.antidiagonalTupleGrid
          (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
            ((iteratedCovGrad (I := I) g₀ 0 2 j' P).toSection x)) k)
      (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    refine MeasureTheory.Integrable.const_mul ?_ (CA l)
    have : (fun x => ∑ k ∈ Finset.range (l + 2),
        Combinatorics.antidiagonalTupleGrid
          (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
            ((iteratedCovGrad (I := I) g₀ 0 2 j' P).toSection x)) k) =
        (fun x => ∑ k ∈ Finset.range (l + 2),
          ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
      funext x
      exact Finset.sum_congr rfl (fun k _ => hgrid_eq x k)
    rw [this]
    exact MeasureTheory.integrable_finsetSum (Finset.range (l + 2)) hint_all
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 1 (2 + l)
    (iteratedCovGrad (I := I) g₀ 1 2 l (connectionDifferenceSection (I := I) g₁ g₀))
    (fun x => CA l * ∑ k ∈ Finset.range (l + 2),
      Combinatorics.antidiagonalTupleGrid
        (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
          ((iteratedCovGrad (I := I) g₀ 0 2 j' P).toSection x)) k)
    hint hptw
  refine le_trans key ?_
  rw [MeasureTheory.integral_const_mul]
  have hsum_int_eq : (∫ x, ∑ k ∈ Finset.range (l + 2),
      Combinatorics.antidiagonalTupleGrid
        (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
          ((iteratedCovGrad (I := I) g₀ 0 2 j' P).toSection x)) k
      ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
      ∑ k ∈ Finset.range (l + 2), ∫ x,
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [show (fun x => ∑ k ∈ Finset.range (l + 2),
        Combinatorics.antidiagonalTupleGrid
          (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
            ((iteratedCovGrad (I := I) g₀ 0 2 j' P).toSection x)) k) =
        (fun x => ∑ k ∈ Finset.range (l + 2),
          ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) from by
      funext x
      exact Finset.sum_congr rfl (fun k _ => hgrid_eq x k)]
    exact MeasureTheory.integral_finsetSum (Finset.range (l + 2)) hint_all
  rw [hsum_int_eq, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (hCA_nn l)
  rw [Finset.sum_mul]
  refine le_trans (Finset.sum_le_sum (fun k hk => (hKt P hPball k).2)) ?_
  refine Finset.sum_le_sum (fun k hk => ?_)
  refine mul_le_mul_of_nonneg_left ?_ (hKt_nn k)
  have hk2 : k + 1 ≤ l + 2 := by
    have := Finset.mem_range.mp hk; omega
  rw [hW_def]
  have hmono : ∑ q ∈ Finset.range (k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2 ≤
      ∑ q ∈ Finset.range (l + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (pAO_range_subset hk2) (fun _ _ _ => sq_nonneg _)
  linarith

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
private lemma pAO_connectionDifference_self_zero (gA : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    PDE.DeTurck.connectionDifference (I := I) gA gA x u v = 0 := by
  have h := PDE.DeTurck.connectionDifference_cocycle (I := I) gA gA gA x u v
  have h2 : PDE.DeTurck.connectionDifference (I := I) gA gA x u v +
      PDE.DeTurck.connectionDifference (I := I) gA gA x u v =
      PDE.DeTurck.connectionDifference (I := I) gA gA x u v + 0 := by
    rw [add_zero]
    exact h.symm
  exact add_left_cancel h2

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
private lemma pAO_connectionDifference_antisymm (gA gB : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    PDE.DeTurck.connectionDifference (I := I) gA gB x u v =
      -PDE.DeTurck.connectionDifference (I := I) gB gA x u v := by
  have h := PDE.DeTurck.connectionDifference_cocycle (I := I) gB gA gA x u v
  rw [pAO_connectionDifference_self_zero (I := I) (M := M) gA x u v] at h
  exact eq_neg_of_add_eq_zero_left h.symm

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (metricLoweredConnectionDifferenceField) in
omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma pAO_lieArm1Kappa_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (x : M) (m : Fin 3 → E) :
    unitModel (I := I) (M := M) g₀ 3 (deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg) x m =
      g₁.inner x (PDE.DeTurck.connectionDifference (I := I) g_bg g₁ x
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 1)))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 2)) := by
  rw [unitModel]
  change Tensor0SSpace.toModel
      (((deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg).toSection x)
        (unitTensor (I := I) (M := M) x)) m =
    g₁.inner x (PDE.DeTurck.connectionDifference (I := I) g_bg g₁ x
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0))
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 1)))
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 2))
  rw [show ((deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg).toSection x)
      (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (metricLoweredConnectionDifferenceField (I := I) g₁ g_bg x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma pAO_lieArm1Kappa_eq_neg_lieCorrectionZeroKappa (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg =
      -(lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g_bg) := by
  rw [show -(lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g_bg) =
      lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g_bg -
        (lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g_bg + lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g_bg)
      from by abel]
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  rw [unitModel_sub_local (I := I) (M := M) g₀ 3 (lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g_bg)
      (lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g_bg + lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g_bg) x,
    unitModel_add_local (I := I) (M := M) g₀ 3 (lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g_bg)
      (lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g_bg) x]
  rw [sub_apply, add_apply]
  rw [pAO_lieArm1Kappa_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x m,
    lieCorrectionZeroKappa_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x m]
  rw [pAO_connectionDifference_antisymm (I := I) (M := M) g_bg g₁ x
    ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0))
    ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 1))]
  rw [map_neg (g₁.inner x), neg_apply]
  ring

omit [NeZero (Module.finrank ℝ E)] in
private lemma pAO_normSq_iteratedCovGrad_lieArm1Kappa_eq (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (q : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 3 q
        (deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 0 3 q (lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 := by
  rw [pAO_lieArm1Kappa_eq_neg_lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g_bg,
    iteratedCovGrad_neg, norm_neg]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma pAO_riemannianFiberNormSq_lieArm1Kappa_eq (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
        ((deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
        ((lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g_bg).toSection x) := by
  have hsec : (deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      -((lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g_bg).toSection x) := by
    rw [pAO_lieArm1Kappa_eq_neg_lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g_bg,
      SmoothCcTensor.toSection_neg]
    rfl
  rw [hsec]
  exact riemannianFiberNormSq_neg_value (I := I) (M := M) g₀ 0 3 x _

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (cometricRaiseSlot0Field riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq) in
omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma pAO_riemannianFiberNormSq_iteratedCovGrad_raiseDomDom_eq (g₀ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 3)) (κ' : SmoothCcTensor g₀ 0 3) (n : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
            (domDomCongrSection (I := I) g₀ σ κ'))).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n κ').toSection x) := by
  rw [riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 1
    (domDomCongrSection (I := I) g₀ σ κ') n x]
  exact riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    σ κ' n x

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (cometricRaiseSlot0Field) in
omit [NeZero (Module.finrank ℝ E)] in
private lemma pAO_normSq_iteratedCovGrad_raiseDomDom_eq (g₀ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 3)) (κ' : SmoothCcTensor g₀ 0 3) (n : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 1 2 n
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ σ κ'))‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 0 3 n κ'‖ ^ 2 := by
  rw [lieCorrectionZerob_normSq_eq_integral, lieCorrectionZerob_normSq_eq_integral]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact pAO_riemannianFiberNormSq_iteratedCovGrad_raiseDomDom_eq (I := I) (M := M) g₀ σ κ' n x

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (sharpFlatEndoCc) in
theorem pAO_sharpFlat_jetSum_tame (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ F : ℕ → ℝ, (∀ l, 0 ≤ F l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδP : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ l : ℕ,
          ∑ q ∈ Finset.range (l + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2 ≤
            F l * (1 + ∑ q ∈ Finset.range (l + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2) := by
  classical
  obtain ⟨Cb, hCb_nn, hCb⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_metricComparisonDifferenceEndomorphism_diagGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kt, hKt_nn, hKt⟩ :=
    antidiagonalTupleGrid_integral_ballUniform_tameWindow (I := I) (M := M) g₀ a ha_super hR
  set IdIns : SmoothCcTensor g₀ 1 1 :=
    endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
      (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀) with hIdIns_def
  refine ⟨fun l => ∑ q ∈ Finset.range (l + 1),
      (2 * (Cb q * Kt q) + 2 * ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ ^ 2),
    fun l => Finset.sum_nonneg fun q _ => add_nonneg
      (mul_nonneg (by norm_num) (mul_nonneg (hCb_nn q) (hKt_nn q)))
      (mul_nonneg (by norm_num) (sq_nonneg _)), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδP hPball l
  set W : ℝ := 1 + ∑ q ∈ Finset.range (l + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2 with hW_def
  have hW1 : (1 : ℝ) ≤ W := by
    rw [hW_def]
    have : (0 : ℝ) ≤ ∑ q ∈ Finset.range (l + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  set DiffIns : SmoothCcTensor g₀ 1 1 :=
    endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)
    with hDiffIns_def
  have hdecomp : sharpFlatEndoCc (I := I) g₀ g₁ = DiffIns + IdIns := by
    rw [lieCorrectionZerob_sharpFlat_eq_slotInsert_fullRaised (I := I) (M := M) g₀ g₁,
      lieCorrectionZerob_fullRaised_diff_split (I := I) (M := M) g₀ g₁,
      lieCorrectionZerob_slotInsert_add (I := I) (M := M) g₀ 0]
  have hterm : ∀ q ∈ Finset.range (l + 1),
      ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2 ≤
        (2 * (Cb q * Kt q) + 2 * ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ ^ 2) * W := by
    intro q hq
    have hq_le : q + 1 ≤ l + 2 := by have := Finset.mem_range.mp hq; omega
    obtain ⟨hgi, hgb⟩ := hKt P hPball q
    have hDq : ‖iteratedCovGrad (I := I) g₀ 1 1 q DiffIns‖ ^ 2 ≤ Cb q * Kt q * W := by
      have hint : MeasureTheory.Integrable
          (fun x => Cb q *
            (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
              ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) := hgi.const_mul _
      have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
        1 (1 + q) (iteratedCovGrad (I := I) g₀ 1 1 q DiffIns) _ hint
        (fun x => hCb g₁ P htie hδ_le hδ0 hδP q x)
      refine le_trans hkey ?_
      rw [MeasureTheory.integral_const_mul]
      have hwin : Kt q * (1 + ∑ j ∈ Finset.range (q + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ Kt q * W := by
        refine mul_le_mul_of_nonneg_left ?_ (hKt_nn q)
        rw [hW_def]
        have hmono : ∑ j ∈ Finset.range (q + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤
            ∑ j ∈ Finset.range (l + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (pAO_range_subset hq_le)
            (fun _ _ _ => sq_nonneg _)
        linarith
      refine le_trans (mul_le_mul_of_nonneg_left hgb (hCb_nn q)) ?_
      refine le_trans (mul_le_mul_of_nonneg_left hwin (hCb_nn q)) (le_of_eq (by ring))
    have hsplit : ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2 ≤
        2 * ‖iteratedCovGrad (I := I) g₀ 1 1 q DiffIns‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ ^ 2 := by
      rw [hdecomp]
      exact lieCorrectionZerob_normSq_iteratedCovGrad_add_le (I := I) (M := M) g₀ 1 1 q DiffIns IdIns
    have hexp : (2 * (Cb q * Kt q) + 2 * ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ ^ 2) * W =
        2 * (Cb q * Kt q * W) + 2 * ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ ^ 2 * W := by
      ring
    have hIdW : ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ ^ 2 ≤
        ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ ^ 2 * W :=
      le_mul_of_one_le_right (sq_nonneg _) hW1
    linarith [hsplit, hDq, hIdW, hexp]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul]

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (metricLoweredConnectionDifferenceCoefficient cometricRaiseSlot0Field) in
theorem pAO_kappa_jetSum_tame (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ F : ℕ → ℝ, (∀ l, 0 ≤ F l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδP : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ l : ℕ,
          ∑ q ∈ Finset.range (l + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 3 q
              (lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
            F l * (1 + ∑ q ∈ Finset.range (l + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2) := by
  classical
  obtain ⟨Fcd, hFcd_nn, hFcd⟩ :=
    pAO_connectionDifferenceSection_jetL2_tame (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Λcd, Fcdtr, hΛcd_nn, hFcdtr_nn, hcd⟩ :=
    lieCorrectionZerob_cds_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Λlow, hΛlow_nn, hΛlow⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 0 3
      (lieCorrectionZeroLowFix (I := I) (M := M) g₀ g_bg)
  obtain ⟨Λfx, hΛfx_nn, hΛfx⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 1 2
      (lieCorrectionZeroFixCd (I := I) (M := M) g₀ g_bg)
  obtain ⟨C2b, hC2b_nn, hC2b⟩ := lieCorrectionZerob_twoArm_fn (I := I) (M := M) g₀ 1 1 2 1
  set nQ : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * max δ₀ 0 ^ 2 with hnQ_def
  have hnQ_nn : 0 ≤ nQ := by rw [hnQ_def]; positivity
  set FB : ℕ → ℝ := fun l => ∑ q ∈ Finset.range (l + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 3 q (lieCorrectionZeroLowFix (I := I) (M := M) g₀ g_bg)‖ ^ 2
    with hFB_def
  have hFB_nn : ∀ l, 0 ≤ FB l := fun l => Finset.sum_nonneg fun q _ => sq_nonneg _
  set Ffx : ℕ → ℝ := fun q => ∑ j ∈ Finset.range (q + 1),
    ‖iteratedCovGrad (I := I) g₀ 1 2 j (lieCorrectionZeroFixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2
    with hFfx_def
  have hFfx_nn : ∀ q, 0 ≤ Ffx q := fun q => Finset.sum_nonneg fun j _ => sq_nonneg _
  set FcdS : ℕ → ℝ := fun q => ∑ n ∈ Finset.range (q + 1), Fcd n with hFcdS_def
  have hFcdS_nn : ∀ q, 0 ≤ FcdS q := fun q => Finset.sum_nonneg fun n _ => hFcd_nn n
  set FC : ℕ → ℝ := fun l => ∑ q ∈ Finset.range (l + 1),
    diagonalGridGrowthFactor (E := E) q * (C2b q * (nQ * FcdS q + Λcd)) with hFC_def
  have hFC_nn : ∀ l, 0 ≤ FC l := fun l =>
    Finset.sum_nonneg fun q _ => mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2b_nn q) (add_nonneg (mul_nonneg hnQ_nn (hFcdS_nn q)) hΛcd_nn))
  set FD : ℕ → ℝ := fun l => ∑ q ∈ Finset.range (l + 1),
    diagonalGridGrowthFactor (E := E) q * (C2b q * (nQ * Ffx q + Λfx)) with hFD_def
  have hFD_nn : ∀ l, 0 ≤ FD l := fun l =>
    Finset.sum_nonneg fun q _ => mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2b_nn q) (add_nonneg (mul_nonneg hnQ_nn (hFfx_nn q)) hΛfx_nn))
  refine ⟨fun l => 8 * FcdS l + 8 * FB l + 4 * FC l + 2 * FD l,
    fun l => by
      have := hFcdS_nn l
      have := hFB_nn l
      have := hFC_nn l
      have := hFD_nn l
      linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδP hPball l
  set W : ℝ := 1 + ∑ q ∈ Finset.range (l + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2 with hW_def
  have hW1 : (1 : ℝ) ≤ W := by
    rw [hW_def]
    have : (0 : ℝ) ≤ ∑ q ∈ Finset.range (l + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  have hW_nn : (0 : ℝ) ≤ W := le_trans zero_le_one hW1
  obtain ⟨hWB0, _⟩ := lieCorrectionZerob_WB_feed (I := I) (M := M) g₀ a P hδ_le hδ0 hδP hPball
  obtain ⟨hcd0, _⟩ := hcd g₁ P htie hδ_le hδ0 hδP hPball
  have hκeq := lieCorrectionZerob_kappa_decomp (I := I) (M := M) g₀ g₁ g_bg P htie
  have hΨcC : ∀ x : M, (connectionDifferenceSection (I := I) g₁ g₀).toSection x =
      connectionDifferenceFib (I := I) g₁ g₀ x := fun x => rfl
  have hΨcD : ∀ x : M, (lieCorrectionZeroFixCd (I := I) (M := M) g₀ g_bg).toSection x =
      connectionDifferenceFib (I := I) g₀ g_bg x := fun x => rfl
  have hWBsum : ∀ q : ℕ, q ≤ l →
      ∑ j ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 1 j
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (ccTensor02Symm (I := I) (M := M) g₀ P))‖ ^ 2 ≤ W := by
    intro q hq
    have hstep : ∀ j ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 1 j
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (ccTensor02Symm (I := I) (M := M) g₀ P))‖ ^ 2 ≤
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
      intro j _
      rw [lieCorrectionZerob_normSq_iteratedCovGrad_raise_eq (I := I) (M := M) g₀ 0 (ccTensor02Symm (I := I) (M := M) g₀ P) j]
      exact lieCorrectionZerob_normSq_iteratedCovGrad_symmS_le (I := I) (M := M) g₀ P j
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [hW_def]
    have hmono : ∑ j ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤
        ∑ j ∈ Finset.range (l + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (pAO_range_subset (by omega : q + 1 ≤ l + 2))
        (fun _ _ _ => sq_nonneg _)
    linarith
  have hcdsum : ∀ q : ℕ, q ≤ l →
      ∑ n ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 2 n (connectionDifferenceSection (I := I) g₁ g₀)‖ ^ 2 ≤
        FcdS q * W := by
    intro q hq
    have hstep : ∀ n ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 2 n (connectionDifferenceSection (I := I) g₁ g₀)‖ ^ 2 ≤
          Fcd n * W := by
      intro n hn
      refine le_trans (hFcd g₁ P htie hδ_le hδ0 hδP hPball n) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hFcd_nn n)
      rw [hW_def]
      have hnle : n + 2 ≤ l + 2 := by
        have h1 := Finset.mem_range.mp hn
        omega
      have hmono : ∑ q' ∈ Finset.range (n + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 q' P‖ ^ 2 ≤
          ∑ q' ∈ Finset.range (l + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 q' P‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (pAO_range_subset hnle)
          (fun _ _ _ => sq_nonneg _)
      linarith
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [hFcdS_def, Finset.sum_mul]
  have hstep : ∀ q ∈ Finset.range (l + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 3 q (lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
      8 * ‖iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)‖ ^ 2 +
        8 * ‖iteratedCovGrad (I := I) g₀ 0 3 q (lieCorrectionZeroLowFix (I := I) (M := M) g₀ g_bg)‖ ^ 2 +
        4 * ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (lieCorrectionZeroPbLow (I := I) (M := M) g₀ P g₁ g₀)‖ ^ 2 +
        2 * ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (lieCorrectionZeroPbLow (I := I) (M := M) g₀ P g₀ g_bg)‖ ^ 2 := by
    intro q _
    have hnorm : ‖iteratedCovGrad (I := I) g₀ 0 3 q
        (lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 =
        ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁ + lieCorrectionZeroLowFix (I := I) (M := M) g₀ g_bg
            + lieCorrectionZeroPbLow (I := I) (M := M) g₀ P g₁ g₀
            + lieCorrectionZeroPbLow (I := I) (M := M) g₀ P g₀ g_bg)‖ ^ 2 := by
      rw [hκeq]
    rw [hnorm]
    have k1 := lieCorrectionZerob_normSq_iteratedCovGrad_add_le (I := I) (M := M) g₀ 0 3 q
      (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁ + lieCorrectionZeroLowFix (I := I) (M := M) g₀ g_bg
        + lieCorrectionZeroPbLow (I := I) (M := M) g₀ P g₁ g₀)
      (lieCorrectionZeroPbLow (I := I) (M := M) g₀ P g₀ g_bg)
    have k2 := lieCorrectionZerob_normSq_iteratedCovGrad_add_le (I := I) (M := M) g₀ 0 3 q
      (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁ + lieCorrectionZeroLowFix (I := I) (M := M) g₀ g_bg)
      (lieCorrectionZeroPbLow (I := I) (M := M) g₀ P g₁ g₀)
    have k3 := lieCorrectionZerob_normSq_iteratedCovGrad_add_le (I := I) (M := M) g₀ 0 3 q
      (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) (lieCorrectionZeroLowFix (I := I) (M := M) g₀ g_bg)
    linarith [k1, k2, k3]
  refine le_trans (Finset.sum_le_sum hstep) ?_
  have hsplit : ∑ q ∈ Finset.range (l + 1),
      (8 * ‖iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)‖ ^ 2 +
        8 * ‖iteratedCovGrad (I := I) g₀ 0 3 q (lieCorrectionZeroLowFix (I := I) (M := M) g₀ g_bg)‖ ^ 2 +
        4 * ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (lieCorrectionZeroPbLow (I := I) (M := M) g₀ P g₁ g₀)‖ ^ 2 +
        2 * ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (lieCorrectionZeroPbLow (I := I) (M := M) g₀ P g₀ g_bg)‖ ^ 2) =
      8 * ∑ q ∈ Finset.range (l + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)‖ ^ 2 +
        8 * ∑ q ∈ Finset.range (l + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 3 q (lieCorrectionZeroLowFix (I := I) (M := M) g₀ g_bg)‖ ^ 2 +
        4 * ∑ q ∈ Finset.range (l + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 3 q (lieCorrectionZeroPbLow (I := I) (M := M) g₀ P g₁ g₀)‖ ^ 2 +
        2 * ∑ q ∈ Finset.range (l + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 3 q (lieCorrectionZeroPbLow (I := I) (M := M) g₀ P g₀ g_bg)‖ ^ 2 := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hsplit]
  have hAsum : ∑ q ∈ Finset.range (l + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)‖ ^ 2 ≤
      FcdS l * W := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun q _ =>
      lieCorrectionZerob_normSq_iteratedCovGrad_lowered_eq (I := I) (M := M) g₀ g₁ q)) ?_
    exact hcdsum l le_rfl
  have hBsum : ∑ q ∈ Finset.range (l + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 3 q (lieCorrectionZeroLowFix (I := I) (M := M) g₀ g_bg)‖ ^ 2 ≤
      FB l * W := by
    have : FB l ≤ FB l * W := le_mul_of_one_le_right (hFB_nn l) hW1
    rw [hFB_def] at this ⊢
    exact this
  have hCsum : ∑ q ∈ Finset.range (l + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 3 q (lieCorrectionZeroPbLow (I := I) (M := M) g₀ P g₁ g₀)‖ ^ 2 ≤
      FC l * W := by
    rw [hFC_def, Finset.sum_mul]
    refine Finset.sum_le_sum fun q hq => ?_
    have hq_le : q ≤ l := by have := Finset.mem_range.mp hq; omega
    rw [lieCorrectionZerob_normSq_iteratedCovGrad_pbLow_eq (I := I) (M := M) g₀ P g₁ g₀
      (connectionDifferenceSection (I := I) g₁ g₀) hΨcC q]
    refine le_trans (lieCorrectionZerob_operatorFieldComposition_normSq_le (I := I) (M := M) g₀ 1 1 2
      (connectionDifferenceSection (I := I) g₁ g₀)
      (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 (ccTensor02Symm (I := I) (M := M) g₀ P)) q
      (C2b q) Λcd nQ (FcdS q * W) W
      (hC2b_nn q) hΛcd_nn hnQ_nn hcd0 hWB0 (hcdsum q hq_le) (hWBsum q hq_le)
      (hC2b q)) ?_
    exact le_of_eq (by ring)
  have hDsum : ∑ q ∈ Finset.range (l + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 3 q (lieCorrectionZeroPbLow (I := I) (M := M) g₀ P g₀ g_bg)‖ ^ 2 ≤
      FD l * W := by
    rw [hFD_def, Finset.sum_mul]
    refine Finset.sum_le_sum fun q hq => ?_
    have hq_le : q ≤ l := by have := Finset.mem_range.mp hq; omega
    rw [lieCorrectionZerob_normSq_iteratedCovGrad_pbLow_eq (I := I) (M := M) g₀ P g₀ g_bg
      (lieCorrectionZeroFixCd (I := I) (M := M) g₀ g_bg) hΨcD q]
    refine le_trans (lieCorrectionZerob_operatorFieldComposition_normSq_le (I := I) (M := M) g₀ 1 1 2
      (lieCorrectionZeroFixCd (I := I) (M := M) g₀ g_bg)
      (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 (ccTensor02Symm (I := I) (M := M) g₀ P)) q
      (C2b q) Λfx nQ (Ffx q) W
      (hC2b_nn q) hΛfx_nn hnQ_nn hΛfx hWB0 le_rfl (hWBsum q hq_le)
      (hC2b q)) ?_
    have hgd := operatorFieldApplicationGdiag_nonneg (E := E) q
    have hbase : nQ * Ffx q ≤ nQ * Ffx q * W :=
      le_mul_of_one_le_right (mul_nonneg hnQ_nn (hFfx_nn q)) hW1
    have hfac : (0 : ℝ) ≤ diagonalGridGrowthFactor (E := E) q * C2b q :=
      mul_nonneg hgd (hC2b_nn q)
    have hin : nQ * Ffx q + Λfx * W ≤ (nQ * Ffx q + Λfx) * W := by
      have : (nQ * Ffx q + Λfx) * W = nQ * Ffx q * W + Λfx * W := by ring
      linarith [hbase, this]
    calc diagonalGridGrowthFactor (E := E) q * (C2b q * (nQ * Ffx q + Λfx * W))
        = diagonalGridGrowthFactor (E := E) q * C2b q * (nQ * Ffx q + Λfx * W) := by ring
      _ ≤ diagonalGridGrowthFactor (E := E) q * C2b q * ((nQ * Ffx q + Λfx) * W) :=
          mul_le_mul_of_nonneg_left hin hfac
      _ = diagonalGridGrowthFactor (E := E) q * (C2b q * (nQ * Ffx q + Λfx)) * W := by ring
  have hexp : (8 * FcdS l + 8 * FB l + 4 * FC l + 2 * FD l) * W =
      8 * (FcdS l * W) + 8 * (FB l * W) + 4 * (FC l * W) + 2 * (FD l * W) := by ring
  linarith [hAsum, hBsum, hCsum, hDsum, hexp]

theorem pAO_deTurckLieArmOneBackgroundCoefficient_jetL2_tame (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ F : ℕ → ℝ, (∀ l, 0 ≤ F l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδP : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ l : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 1 2 l
              (deTurckLieArmOneBackgroundCoefficient (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
            F l * (1 + ∑ q ∈ Finset.range (l + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2) := by
  classical
  obtain ⟨Λκ, Fκtr, hΛκ_nn, hFκtr_nn, hκ⟩ :=
    lieCorrectionZerob_kappa_feed (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨Λsf, Fsftr, hΛsf_nn, hFsftr_nn, hsf⟩ :=
    lieCorrectionZerob_sharpFlat_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Fκt, hFκt_nn, hκt⟩ :=
    pAO_kappa_jetSum_tame (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨Fsft, hFsft_nn, hsft⟩ :=
    pAO_sharpFlat_jetSum_tame (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨C2b, hC2b_nn, hC2b⟩ := lieCorrectionZerob_twoArm_fn (I := I) (M := M) g₀ 1 1 2 1
  refine ⟨fun l => diagonalGridGrowthFactor (E := E) l * (C2b l * (Λsf * Fκt l + Λκ * Fsft l)),
    fun l => mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) l)
      (mul_nonneg (hC2b_nn l) (add_nonneg (mul_nonneg hΛsf_nn (hFκt_nn l))
        (mul_nonneg hΛκ_nn (hFsft_nn l)))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδP hPball l
  obtain ⟨hκ0, _⟩ := hκ g₁ P htie hδ_le hδ0 hδP hPball
  obtain ⟨hsf0, _⟩ := hsf g₁ P htie hδ_le hδ0 hδP hPball
  have hκtW := hκt g₁ P htie hδ_le hδ0 hδP hPball l
  have hsftW := hsft g₁ P htie hδ_le hδ0 hδP hPball l
  have hdef : deTurckLieArmOneBackgroundCoefficient (I := I) (M := M) g₀ g₁ g_bg =
      ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 2
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricRaiseSlot0Field (I := I)
          (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
            (deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)))
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc (I := I) g₀ g₁) :=
          rfl
  have hA0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
      ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricRaiseSlot0Field (I := I)
        (M := M) g₀ 1
        (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
          (deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg))).toSection x) ≤ Λκ := by
    intro x
    have h := pAO_riemannianFiberNormSq_iteratedCovGrad_raiseDomDom_eq (I := I) (M := M) g₀ lieArm1RhoSlot0
      (deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg) 0 x
    simp only [iteratedCovGrad_zero] at h
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
          ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricRaiseSlot0Field (I := I)
            (M := M) g₀ 1
            (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
              (deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg))).toSection x)
        = riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
            ((deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg).toSection x) := h
      _ = riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
            ((lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g_bg).toSection x) :=
          pAO_riemannianFiberNormSq_lieArm1Kappa_eq (I := I) (M := M) g₀ g₁ g_bg x
      _ ≤ Λκ := hκ0 x
  have hAL2 : ∑ n ∈ Finset.range (l + 1),
      ‖iteratedCovGrad (I := I) g₀ 1 2 n
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricRaiseSlot0Field (I := I)
          (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
            (deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)))‖ ^ 2 ≤
      Fκt l * (1 + ∑ q ∈ Finset.range (l + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2) := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun n _ => ?_)) hκtW
    rw [pAO_normSq_iteratedCovGrad_raiseDomDom_eq (I := I) (M := M) g₀ lieArm1RhoSlot0
        (deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg) n,
      pAO_normSq_iteratedCovGrad_lieArm1Kappa_eq (I := I) (M := M) g₀ g₁ g_bg n]
  rw [hdef]
  refine le_trans (lieCorrectionZerob_operatorFieldComposition_normSq_le (I := I) (M := M) g₀ 1 1 2
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricRaiseSlot0Field (I := I)
      (M := M) g₀ 1
      (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
        (deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)))
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc (I := I) g₀ g₁) l
    (C2b l) Λκ Λsf
    (Fκt l * (1 + ∑ q ∈ Finset.range (l + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2))
    (Fsft l * (1 + ∑ q ∈ Finset.range (l + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2))
    (hC2b_nn l) hΛκ_nn hΛsf_nn hA0 hsf0 hAL2 hsftW
    (hC2b l)) (le_of_eq (by ring))

end DifferentialGeometry.Analysis.Spectral

end

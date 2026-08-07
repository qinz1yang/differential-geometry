import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalCometricExtraction
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalArmSpectralGarding
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderHigherOrderTame
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricInverseDifferenceMultiplier
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.ConnLapCommutatorCoefficientTame
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingSharpC0JetSum
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.ChartH2GardingConstant
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.IntegratedOrder2Weitzenbock
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Analysis.Sobolev.RiemannianFiberNormSq.PointwiseToL2Packaging
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.HomFieldActionIteratedCovGradWindow
import DifferentialGeometry.Analysis.Integration.L2.FiniteProductHolderFiberNorm
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricPathResolventFactorization
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.IntegratedOrder2WeitzenbockRS
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseTensorCurvatureRS
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.HomFieldCurvatureJetDecomposition
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderPrincipalArmOpNormCometricCoeffFibreSup
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderPrincipalArmOpNormArmFieldPathIntegralJetL2
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderPrincipalArmOpNormConnLapIterateJetLadder
open DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Tensor.Auxiliary
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Tensor.Auxiliary
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Tensor.Auxiliary
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Tensor.Auxiliary
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Tensor.Auxiliary
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature


noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private lemma six_twelve_mul_le {A B C D S : ℝ}
    (hA : A ≤ C * S) (hB : B ≤ D * S) :
    6 * A + 12 * B ≤ (6 * C + 12 * D) * S := by
  linear_combination 6 * hA + 12 * hB

private lemma norm_add_sq_le_two {V : Type*} [SeminormedAddCommGroup V] (x y : V) :
    ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have hn := norm_add_le x y
  have hxy : 0 ≤ ‖x + y‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖x‖ - ‖y‖), mul_le_mul hn hn hxy (by positivity),
    norm_nonneg x, norm_nonneg y]

private lemma sq_le_two_bounds_of_le_add {x y z Y Z : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hxyz : x ≤ y + z)
    (hy2 : y ^ 2 ≤ Y) (hz2 : z ^ 2 ≤ Z) :
    x ^ 2 ≤ 2 * Y + 2 * Z := by
  nlinarith [sq_nonneg (y - z), mul_le_mul hxyz hxyz hx (add_nonneg hy hz)]

private lemma sq_le_three_of_le_add_add_two {x y z w : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hxyz : x ≤ y + z + 2 * w) :
    x ^ 2 ≤ 3 * y ^ 2 + 3 * z ^ 2 + 12 * w ^ 2 := by
  nlinarith [mul_le_mul hxyz hxyz hx (by positivity), sq_nonneg (y - z),
    sq_nonneg (y - 2 * w), sq_nonneg (z - 2 * w)]

theorem smoothCcToTensorHs_rawTensorConnLapSmooth_le
    (g₀ : SmoothRiemannianMetric I M) (σ : ℝ) (T : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T)‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (σ + 2) T‖ := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcompact_def
  set lam : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun i => DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
      (I := I) (M := M) i with hlam_def
  set c : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun i => tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 T) i
    with hc_def
  have hnn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (σ + 2) T‖ := norm_nonneg _
  have hlam_nn : ∀ i, 0 ≤ lam i := fun i =>
    DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensor_lambda_nonneg
      (I := I) (M := M) i
  have hLHS_term : ∀ i,
      tensorSobolevWeight (I := I) (M := M) i σ *
          (tensorL2Coeff (I := I) (M := M) h_compact
            (SmoothCcTensor.toL2 (rawTensorConnLapSmooth (I := I) g₀ 0 2 T)) i) ^ 2 =
        tensorSobolevWeight (I := I) (M := M) i σ * (lam i) ^ 2 * (c i) ^ 2 := by
    intro i
    rw [tensorL2Coeff_ofCompact_rawTensorConnLapSmooth (I := I) (M := M) g₀ h_compact T i]
    rw [show (- lam i * c i) ^ 2 = (lam i) ^ 2 * (c i) ^ 2 by ring]
    ring
  have hRHS_term : ∀ i,
      tensorSobolevWeight (I := I) (M := M) i (σ + 2) * (c i) ^ 2 =
        tensorSobolevWeight (I := I) (M := M) i σ * (1 + lam i) ^ 2 * (c i) ^ 2 := by
    intro i
    rw [tensorHs.tensorSobolevWeight_add (I := I) (M := M) i σ 2]
    have hw2 : tensorSobolevWeight (I := I) (M := M) i (2 : ℝ) = (1 + lam i) ^ 2 := by
      unfold tensorSobolevWeight
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hw2]
  have hsummable_RHS : Summable (fun i =>
      tensorSobolevWeight (I := I) (M := M) i σ * (1 + lam i) ^ 2 * (c i) ^ 2) := by
    have hw := (ccSpectralEmbed (I := I) (M := M) g₀ (σ + 2) T).weighted_summable
    refine hw.congr (fun i => ?_)
    rw [ccSpectralEmbed_coeff,
      show tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 T) i = c i from rfl]
    exact hRHS_term i
  have hsummable_LHS : Summable (fun i =>
      tensorSobolevWeight (I := I) (M := M) i σ * (lam i) ^ 2 * (c i) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hsummable_RHS
    · have := tensorSobolevWeight_pos (I := I) (M := M) i σ
      have := hlam_nn i
      positivity
    · have hwpos : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ :=
        le_of_lt (tensorSobolevWeight_pos (I := I) (M := M) i σ)
      have hbase : (lam i) ^ 2 ≤ (1 + lam i) ^ 2 := by
        have := hlam_nn i; nlinarith
      have hc2 : 0 ≤ (c i) ^ 2 := sq_nonneg _
      nlinarith [mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hbase hwpos) hc2]
  have hsq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T)‖ ^ 2 ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (σ + 2) T‖ ^ 2 := by
    rw [tensorHs.norm_sq_eq_tsum, tensorHs.norm_sq_eq_tsum]
    rw [show (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          ((smoothCcToTensorHs (I := I) (M := M) g₀ σ
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 T)).coeff i) ^ 2) =
        fun i => tensorSobolevWeight (I := I) (M := M) i σ * (lam i) ^ 2 * (c i) ^ 2 by
      funext i
      rw [smoothCcToTensorHs_coeff, ← hcompact_def]
      exact hLHS_term i]
    rw [show (fun i => tensorSobolevWeight (I := I) (M := M) i (σ + 2) *
          ((smoothCcToTensorHs (I := I) (M := M) g₀ (σ + 2) T).coeff i) ^ 2) =
        fun i => tensorSobolevWeight (I := I) (M := M) i σ * (1 + lam i) ^ 2 * (c i) ^ 2 by
      funext i
      rw [smoothCcToTensorHs_coeff, ← hcompact_def,
        show tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 T) i = c i from rfl]
      exact hRHS_term i]
    refine Summable.tsum_le_tsum (fun i => ?_) hsummable_LHS hsummable_RHS
    have hwpos : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ :=
      le_of_lt (tensorSobolevWeight_pos (I := I) (M := M) i σ)
    have hbase : (lam i) ^ 2 ≤ (1 + lam i) ^ 2 := by
      have := hlam_nn i; nlinarith
    have hc2 : 0 ≤ (c i) ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbase hwpos) hc2]
  exact le_of_sq_le_sq hsq hnn

theorem exists_smoothCcToTensorHs_deTurckPrincipalCometricArm_opNorm_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ Clower : ℕ → ℝ, (∀ m, 0 ≤ Clower m) ∧
      ∀ (m : ℕ) (T₀ : SmoothCcTensor g₀ 0 2)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀
              (tensorSectionRealizeMetric (I := I) g₀ T₀
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                (hδ_fibre T₀ hball)) T₀)‖ ≤
          deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ +
            Clower m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T₀‖ := by
  classical
  obtain ⟨Clower, hClower_nn, hbound⟩ :=
    exists_smoothCcToTensorHs_deTurckPrincipalCometricArm_principal_le
      (I := I) (M := M) g₀ a ha_super hR₀ hδ_le hδ_fibre
  refine ⟨Clower, hClower_nn, fun m T₀ hball => ?_⟩
  rcases isEmpty_or_nonempty M with hM | hM
  · have hzero : ∀ (τ : ℝ) (X : SmoothCcTensor g₀ 0 2),
        smoothCcToTensorHs (I := I) (M := M) g₀ τ X = 0 := by
      intro τ X
      have hL2norm : ‖SmoothCcTensor.toL2 X‖ = 0 := by
        rw [SmoothCcTensor.norm_toL2, SmoothCcTensor.norm_def,
          DifferentialGeometry.Integral.L2.tensorL2Norm,
          DifferentialGeometry.Integral.L2.tensorL2Inner,
          MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
      have hL2 : SmoothCcTensor.toL2 X = 0 := norm_eq_zero.mp hL2norm
      refine tensorHs.ext (funext fun i => ?_)
      rw [smoothCcToTensorHs_coeff, tensorHs.zero_coeff,
        hL2, tensorL2Coeff_eq_inner, inner_zero_right]
    rw [hzero, hzero, hzero]
    simp
  · have hδ_nn : 0 ≤ δ :=
      delta_nonneg_of_ball_gFibreOpBound (I := I) (M := M) g₀ a hR₀ hδ_fibre
    have hδ_lt1 : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
    have hκ_nn : 0 ≤ δ / (1 - δ) := div_nonneg hδ_nn (by linarith)
    have hCEκ_nn : 0 ≤ deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) :=
      mul_nonneg (deTurckArmFibreConst_nonneg _) hκ_nn
    refine le_trans (hbound m T₀ hball) ?_
    have hshift : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ ≤
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ :=
      smoothCcToTensorHs_rawTensorConnLapSmooth_le (I := I) (M := M) g₀ (m : ℝ) T₀
    have htop : deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ ≤
        deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ :=
      mul_le_mul_of_nonneg_left hshift hCEκ_nn
    linarith

theorem exists_coeffAction_iteratedCovGrad_l2_dataJetWindow_le
    (g₀ : SmoothRiemannianMetric I M) (m : ℕ) :
    ∃ Cgrid : ℕ → ℝ, (∀ q, 0 ≤ Cgrid q) ∧
      ∀ (q : ℕ) (C : SmoothCcTensor g₀ (2 + m) 2) (Kc : ℝ) (T₀ : SmoothCcTensor g₀ 0 2),
        0 ≤ Kc →
        (∀ (i : ℕ), i ≤ q → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) (2 + i) x
            ((iteratedCovGrad (I := I) g₀ (2 + m) 2 i C).toSection x) ≤ Kc ^ 2) →
        ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 C
              (iteratedCovGrad (I := I) g₀ 0 2 m T₀))‖ ≤
          Cgrid q * Kc * Real.sqrt (∑ i ∈ Finset.range (q + m + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
  classical
  refine ⟨fun q => Real.sqrt (diagonalGridGrowthFactor (E := E) q * ((q : ℝ) + 1)) *
      Real.sqrt ((q + m + 1 : ℕ) : ℝ),
    fun q => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
    fun q C Kc T₀ hKc hjet => ?_⟩
  have hG_nn : 0 ≤ diagonalGridGrowthFactor (E := E) q := appCcGdiag_nonneg (E := E) q
  have hGq_nn : 0 ≤ diagonalGridGrowthFactor (E := E) q * ((q : ℝ) + 1) :=
    mul_nonneg hG_nn (by positivity)
  set Cpk : ℝ := Kc * Real.sqrt (diagonalGridGrowthFactor (E := E) q * ((q : ℝ) + 1)) with hCpk_def
  have hCpk_nn : 0 ≤ Cpk := mul_nonneg hKc (Real.sqrt_nonneg _)
  have hCpksq : Cpk ^ 2 = Kc ^ 2 * (diagonalGridGrowthFactor (E := E) q * ((q : ℝ) + 1)) := by
    rw [hCpk_def, mul_pow, Real.sq_sqrt hGq_nn]
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
          ((iteratedCovGrad (I := I) g₀ 0 2 q
            (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 C
              (iteratedCovGrad (I := I) g₀ 0 2 m T₀))).toSection x) ≤
        Cpk ^ 2 * ∑ i ∈ Finset.range (q + m + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i T₀).toSection x) := by
    intro x
    set Sfull : ℝ := ∑ i ∈ Finset.range (q + m + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i T₀).toSection x) with hSfull_def
    have hshift : ∀ (F : ℕ → ℝ), (∀ i, 0 ≤ F i) →
        (∑ l ∈ Finset.range (q + 1), F (m + l)) ≤ ∑ i ∈ Finset.range (q + m + 1), F i := by
      intro F hF
      have hinj : ∀ l₁ ∈ Finset.range (q + 1), ∀ l₂ ∈ Finset.range (q + 1),
          m + l₁ = m + l₂ → l₁ = l₂ := fun l₁ _ l₂ _ h => by omega
      have himg : (Finset.range (q + 1)).image (fun l => m + l) ⊆
          Finset.range (q + m + 1) := by
        intro i hi
        rw [Finset.mem_image] at hi
        obtain ⟨l, hl, rfl⟩ := hi
        rw [Finset.mem_range] at hl ⊢; omega
      calc (∑ l ∈ Finset.range (q + 1), F (m + l))
          = ∑ i ∈ (Finset.range (q + 1)).image (fun l => m + l), F i :=
            (Finset.sum_image hinj).symm
        _ ≤ ∑ i ∈ Finset.range (q + m + 1), F i :=
            Finset.sum_le_sum_of_subset_of_nonneg himg (fun i _ _ => hF i)
    have hWfull : (∑ l ∈ Finset.range (q + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
              (iteratedCovGrad (I := I) g₀ 0 2 m T₀)).toSection x)) ≤ Sfull := by
      rw [show (∑ l ∈ Finset.range (q + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                (iteratedCovGrad (I := I) g₀ 0 2 m T₀)).toSection x)) =
          ∑ l ∈ Finset.range (q + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (m + l)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (m + l) T₀).toSection x) from
        Finset.sum_congr rfl (fun l _ =>
          riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 m l T₀ x)]
      rw [hSfull_def]
      exact hshift (fun i => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i T₀).toSection x))
        (fun i => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + i) x _)
    have hterm : ∀ i ∈ Finset.range (q + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) (2 + i) x
            ((iteratedCovGrad (I := I) g₀ (2 + m) 2 i C).toSection x) *
          ∑ l ∈ Finset.range (q + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                (iteratedCovGrad (I := I) g₀ 0 2 m T₀)).toSection x) ≤
          Kc ^ 2 * Sfull := by
      intro i hi
      have hi_le : i ≤ q := by rw [Finset.mem_range] at hi; omega
      have hgC := hjet i hi_le x
      have hsub : Finset.range (q + 1 - i) ⊆ Finset.range (q + 1) :=
        Finset.range_mono (by omega)
      have hWi : (∑ l ∈ Finset.range (q + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                (iteratedCovGrad (I := I) g₀ 0 2 m T₀)).toSection x)) ≤
          ∑ l ∈ Finset.range (q + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                (iteratedCovGrad (I := I) g₀ 0 2 m T₀)).toSection x) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun l _ _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 ((2 + m) + l) x _)
      have hWi_nn : 0 ≤ ∑ l ∈ Finset.range (q + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
              (iteratedCovGrad (I := I) g₀ 0 2 m T₀)).toSection x) :=
        Finset.sum_nonneg (fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 ((2 + m) + l) x _)
      exact mul_le_mul hgC (le_trans hWi hWfull) hWi_nn (sq_nonneg Kc)
    have hmono : (∑ i ∈ Finset.range (q + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) (2 + i) x
              ((iteratedCovGrad (I := I) g₀ (2 + m) 2 i C).toSection x) *
            ∑ l ∈ Finset.range (q + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
                ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                  (iteratedCovGrad (I := I) g₀ 0 2 m T₀)).toSection x)) ≤
        ((q : ℝ) + 1) * (Kc ^ 2 * Sfull) := by
      refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    refine le_trans
      (riemannianFiberNormSq_iteratedCovGrad_comp_diagonalProductGrid_le (I := I) (M := M) g₀
        (2 + m) 2 C
        (iteratedCovGrad (I := I) g₀ 0 2 m T₀) q x) ?_
    refine le_trans (mul_le_mul_of_nonneg_left hmono hG_nn) ?_
    rw [hCpksq]
    apply le_of_eq; ring
  have hpack := tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum (I := I) (M := M) g₀
    (q + m + 1) (fun i => 2 + i) (fun i => iteratedCovGrad (I := I) g₀ 0 2 i T₀)
    (iteratedCovGrad (I := I) g₀ 0 2 q
      (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 C (iteratedCovGrad (I := I) g₀ 0 2 m T₀)))
    Cpk hCpk_nn hpt
  refine le_trans hpack ?_
  have hCS : ∑ i ∈ Finset.range (q + m + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ≤
      Real.sqrt ((q + m + 1 : ℕ) : ℝ) *
        Real.sqrt (∑ i ∈ Finset.range (q + m + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
    have hcs0 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (q + m + 1))
      (fun _ => (1 : ℝ)) (fun i => ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one] at hcs0
    have hsum_nn : 0 ≤ ∑ i ∈ Finset.range (q + m + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    rw [← Real.sqrt_sq hsum_nn,
      show Real.sqrt ((q + m + 1 : ℕ) : ℝ) *
          Real.sqrt (∑ i ∈ Finset.range (q + m + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) =
        Real.sqrt (((q + m + 1 : ℕ) : ℝ) *
          ∑ i ∈ Finset.range (q + m + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) from
        (Real.sqrt_mul (by positivity) _).symm]
    exact Real.sqrt_le_sqrt hcs0
  refine le_trans (mul_le_mul_of_nonneg_left hCS hCpk_nn) ?_
  rw [hCpk_def]
  apply le_of_eq; ring

theorem exists_smoothCcToTensorHs_real_le_of_iteratedCovGrad_jet_window
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha : 1 ≤ a)
    (Clow : ℕ → ℝ) (hClow_nn : ∀ q, 0 ≤ Clow q) :
    ∃ Ctame : ℕ → ℝ, (∀ k, 0 ≤ Ctame k) ∧
      ∀ (k : ℕ) (U V : SmoothCcTensor g₀ 0 2),
        (∀ q : ℕ, ‖iteratedCovGrad (I := I) g₀ 0 2 q U‖ ≤
          Clow q * Real.sqrt (∑ i ∈ Finset.range (q + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i V‖ ^ 2)) →
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) U‖ ≤
          Ctame k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) V‖ := by
  classical
  set C1 : ℕ → ℝ := fun k =>
    (exists_smoothCcToTensorHs_le_iteratedCovGrad_sum_general (I := I) (M := M) g₀
      (a + k - 1)).choose with hC1_def
  set C2 : ℕ → ℝ := fun k =>
    (exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀
      (a + k - 1 + 1)).choose with hC2_def
  have hC1_spec : ∀ k, 0 ≤ C1 k ∧ ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + k - 1 : ℕ) : ℝ) S‖ ≤
        C1 k * ∑ j ∈ Finset.range (a + k - 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ :=
    fun k => (exists_smoothCcToTensorHs_le_iteratedCovGrad_sum_general (I := I) (M := M) g₀
      (a + k - 1)).choose_spec
  have hC2_spec : ∀ k, 0 ≤ C2 k ∧ ∀ S : SmoothCcTensor g₀ 0 2,
      ∑ j ∈ Finset.range (a + k - 1 + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤
        C2 k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + k - 1 + 1 : ℕ) : ℝ) S‖ :=
    fun k => (exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀
      (a + k - 1 + 1)).choose_spec
  refine ⟨fun k => C1 k * (∑ j ∈ Finset.range (a + k - 1 + 1), Clow j) * C2 k,
    fun k => ?_, fun k U V hU => ?_⟩
  · exact mul_nonneg (mul_nonneg (hC1_spec k).1
      (Finset.sum_nonneg (fun j _ => hClow_nn j))) (hC2_spec k).1
  · have hUexp : (a : ℝ) + (k : ℝ) - 1 = ((a + k - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (show 1 ≤ a + k by omega)]; push_cast; ring
    have hVexp : (a : ℝ) + (k : ℝ) = ((a + k - 1 + 1 : ℕ) : ℝ) := by
      rw [show a + k - 1 + 1 = a + k by omega]; push_cast; ring
    rw [hUexp, hVexp]
    set SV : ℝ := ∑ i ∈ Finset.range (a + k - 1 + 1 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 i V‖ with hSV_def
    have hSV_nn : 0 ≤ SV := Finset.sum_nonneg (fun i _ => norm_nonneg _)
    have hsq_le : ∑ i ∈ Finset.range (a + k - 1 + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i V‖ ^ 2 ≤ SV ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => norm_nonneg _)
    have hsqrtV_le : Real.sqrt (∑ i ∈ Finset.range (a + k - 1 + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i V‖ ^ 2) ≤ SV :=
      le_trans (Real.sqrt_le_sqrt hsq_le) (le_of_eq (Real.sqrt_sq hSV_nn))
    have hUj : ∀ j ∈ Finset.range (a + k - 1 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j U‖ ≤ Clow j * SV := by
      intro j hj
      have hj_le : j ≤ a + k - 1 := by rw [Finset.mem_range] at hj; omega
      refine le_trans (hU j) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hClow_nn j)
      have hsub : Finset.range (j + 1 + 1) ⊆ Finset.range (a + k - 1 + 1 + 1) :=
        Finset.range_mono (by omega)
      have hwin : ∑ i ∈ Finset.range (j + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i V‖ ^ 2 ≤
          ∑ i ∈ Finset.range (a + k - 1 + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i V‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => sq_nonneg _)
      exact le_trans (Real.sqrt_le_sqrt hwin) hsqrtV_le
    have hUsum : ∑ j ∈ Finset.range (a + k - 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j U‖ ≤
        (∑ j ∈ Finset.range (a + k - 1 + 1), Clow j) * SV := by
      refine le_trans (Finset.sum_le_sum hUj) ?_
      rw [Finset.sum_mul]
    have hb1 := (hC1_spec k).2 U
    have hb2 := (hC2_spec k).2 V
    have hSV_le : SV ≤ C2 k *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + k - 1 + 1 : ℕ) : ℝ) V‖ := hb2
    calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + k - 1 : ℕ) : ℝ) U‖
        ≤ C1 k * ∑ j ∈ Finset.range (a + k - 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j U‖ := hb1
      _ ≤ C1 k * ((∑ j ∈ Finset.range (a + k - 1 + 1), Clow j) * SV) :=
          mul_le_mul_of_nonneg_left hUsum (hC1_spec k).1
      _ ≤ C1 k * ((∑ j ∈ Finset.range (a + k - 1 + 1), Clow j) *
            (C2 k * ‖smoothCcToTensorHs (I := I) (M := M) g₀
              ((a + k - 1 + 1 : ℕ) : ℝ) V‖)) := by
          refine mul_le_mul_of_nonneg_left ?_ (hC1_spec k).1
          exact mul_le_mul_of_nonneg_left hSV_le
            (Finset.sum_nonneg (fun j _ => hClow_nn j))
      _ = C1 k * (∑ j ∈ Finset.range (a + k - 1 + 1), Clow j) * C2 k *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + k - 1 + 1 : ℕ) : ℝ) V‖ := by
          ring

def deTurckArmContractionThreshold' (n : ℕ) : ℝ :=
  1 / (1 + 2 * (deTurckArmFibreConst n + deTurckArmFibreConst n ^ 3))

lemma deTurckArmContractionThreshold'_le {n : ℕ} (hn : 1 ≤ n) :
    deTurckArmContractionThreshold' n ≤ deTurckArmContractionThreshold n := by
  have hC := one_le_deTurckArmFibreConst hn
  unfold deTurckArmContractionThreshold' deTurckArmContractionThreshold
  have hC3 : 0 ≤ deTurckArmFibreConst n ^ 3 := by positivity
  apply one_div_le_one_div_of_le (by linarith)
  linarith

lemma deTurckArmContractionThreshold'_le_third {n : ℕ} (hn : 1 ≤ n) :
    deTurckArmContractionThreshold' n ≤ 1 / 3 :=
  le_trans (deTurckArmContractionThreshold'_le hn)
    (deTurckArmContractionThreshold_le_third hn)

lemma deTurckArmContractionThreshold'_lt_one {n : ℕ} (hn : 1 ≤ n) :
    deTurckArmContractionThreshold' n < 1 :=
  lt_of_le_of_lt (deTurckArmContractionThreshold'_le_third hn)
    (by norm_num : (1 : ℝ) / 3 < 1)

lemma deTurckArmContractionThreshold'_le_third' (n : ℕ) [NeZero n] :
    deTurckArmContractionThreshold' n ≤ 1 / 3 :=
  deTurckArmContractionThreshold'_le_third (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))

lemma deTurckArmContractionThreshold'_lt_one' (n : ℕ) [NeZero n] :
    deTurckArmContractionThreshold' n < 1 :=
  deTurckArmContractionThreshold'_lt_one (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))

lemma deTurckArmFibreConst_cube_mul_div_le {n : ℕ} (hn : 1 ≤ n) {δ : ℝ}
    (hδ_le : δ ≤ deTurckArmContractionThreshold' n) :
    deTurckArmFibreConst n ^ 3 * (δ / (1 - δ)) ≤
      deTurckArmFibreConst n ^ 2 / (2 * (1 + deTurckArmFibreConst n ^ 2)) := by
  have hC := one_le_deTurckArmFibreConst hn
  set C := deTurckArmFibreConst n with hC_def
  set K : ℝ := C + C ^ 3 with hK_def
  have hC3_nn : (0 : ℝ) ≤ C ^ 3 := by positivity
  have hK1 : 1 ≤ K := by rw [hK_def]; linarith
  have hden : (0 : ℝ) < 1 + 2 * K := by linarith
  have hthr_lt : deTurckArmContractionThreshold' n < 1 :=
    deTurckArmContractionThreshold'_lt_one hn
  have hδ_lt1 : δ < 1 := lt_of_le_of_lt hδ_le hthr_lt
  have h1δ_pos : (0 : ℝ) < 1 - δ := by linarith
  have hRHS_pos : (0 : ℝ) <
      C ^ 2 / (2 * (1 + C ^ 2)) := by positivity
  by_cases hδ0 : δ ≤ 0
  · have hratio_np : δ / (1 - δ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hδ0 h1δ_pos.le
    have : C ^ 3 * (δ / (1 - δ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hratio_np
    linarith
  · have hδ_mul : δ * (1 + 2 * K) ≤ 1 := by
      have := (le_div_iff₀ hden).mp
        (show δ ≤ 1 / (1 + 2 * K) from hδ_le)
      linarith
    have hratio : δ / (1 - δ) ≤ 1 / (2 * K) := by
      rw [div_le_div_iff₀ h1δ_pos (by linarith : (0 : ℝ) < 2 * K)]
      nlinarith
    have hkey : C ^ 3 / (2 * K) = C ^ 2 / (2 * (1 + C ^ 2)) := by
      rw [hK_def]
      have hCpos : (0 : ℝ) < C := by linarith
      rw [div_eq_div_iff (by positivity) (by positivity)]
      ring
    calc C ^ 3 * (δ / (1 - δ)) ≤ C ^ 3 * (1 / (2 * K)) :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = C ^ 3 / (2 * K) := by ring
      _ = C ^ 2 / (2 * (1 + C ^ 2)) := hkey

lemma deTurckBudget_half_add_lt_one (n : ℕ) :
    (1 / 2 : ℝ) + deTurckArmFibreConst n ^ 2 / (2 * (1 + deTurckArmFibreConst n ^ 2)) < 1 := by
  have hC2 : (0 : ℝ) ≤ deTurckArmFibreConst n ^ 2 := sq_nonneg _
  have hden : (0 : ℝ) < 2 * (1 + deTurckArmFibreConst n ^ 2) := by linarith
  have hlt : deTurckArmFibreConst n ^ 2 / (2 * (1 + deTurckArmFibreConst n ^ 2)) <
      1 / 2 := by
    rw [div_lt_div_iff₀ hden (by norm_num : (0:ℝ) < 2)]
    linarith
  linarith

lemma deTurckArmFibreConst_cube_mul_div_le_thirtyTwo {n : ℕ} (hn : 1 ≤ n) {δ : ℝ}
    (hδ_le : δ ≤ deTurckArmContractionThresholdSharp n) :
    32 * deTurckArmFibreConst n ^ 3 * (δ / (1 - δ)) ≤
      32 * deTurckArmFibreConst n ^ 2 / (2 * (1 + 32 * deTurckArmFibreConst n ^ 2)) := by
  have hC := one_le_deTurckArmFibreConst hn
  set C := deTurckArmFibreConst n with hC_def
  set K : ℝ := C + 32 * C ^ 3 with hK_def
  have hC3_nn : (0 : ℝ) ≤ C ^ 3 := by positivity
  have hK1 : 1 ≤ K := by rw [hK_def]; nlinarith
  have hden : (0 : ℝ) < 1 + 2 * K := by linarith
  have hthr_lt : deTurckArmContractionThresholdSharp n < 1 :=
    deTurckArmContractionThreshold''_lt_one hn
  have hδ_lt1 : δ < 1 := lt_of_le_of_lt hδ_le hthr_lt
  have h1δ_pos : (0 : ℝ) < 1 - δ := by linarith
  by_cases hδ0 : δ ≤ 0
  · have hratio_np : δ / (1 - δ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hδ0 h1δ_pos.le
    have hL : 32 * C ^ 3 * (δ / (1 - δ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hratio_np
    have hR : (0 : ℝ) ≤ 32 * C ^ 2 / (2 * (1 + 32 * C ^ 2)) := by positivity
    linarith
  · have hδ_mul : δ * (1 + 2 * K) ≤ 1 := by
      have := (le_div_iff₀ hden).mp
        (show δ ≤ 1 / (1 + 2 * K) from hδ_le)
      linarith
    have hratio : δ / (1 - δ) ≤ 1 / (2 * K) := by
      rw [div_le_div_iff₀ h1δ_pos (by linarith : (0 : ℝ) < 2 * K)]
      nlinarith
    have hkey : 32 * C ^ 3 / (2 * K) = 32 * C ^ 2 / (2 * (1 + 32 * C ^ 2)) := by
      rw [hK_def]
      have hCpos : (0 : ℝ) < C := by linarith
      rw [div_eq_div_iff (by positivity) (by positivity)]
      ring
    calc 32 * C ^ 3 * (δ / (1 - δ)) ≤ 32 * C ^ 3 * (1 / (2 * K)) :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = 32 * C ^ 3 / (2 * K) := by ring
      _ = 32 * C ^ 2 / (2 * (1 + 32 * C ^ 2)) := hkey

lemma deTurckBudget_half_add_thirtyTwo_lt_one (n : ℕ) :
    (1 / 2 : ℝ) + 32 * deTurckArmFibreConst n ^ 2 /
        (2 * (1 + 32 * deTurckArmFibreConst n ^ 2)) < 1 := by
  have hC2 : (0 : ℝ) ≤ 32 * deTurckArmFibreConst n ^ 2 := by positivity
  have hden : (0 : ℝ) < 2 * (1 + 32 * deTurckArmFibreConst n ^ 2) := by linarith
  have hlt : 32 * deTurckArmFibreConst n ^ 2 /
      (2 * (1 + 32 * deTurckArmFibreConst n ^ 2)) < 1 / 2 := by
    rw [div_lt_div_iff₀ hden (by norm_num : (0:ℝ) < 2)]
    linarith
  linarith

set_option backward.isDefEq.respectTransparency false in
open DifferentialGeometry.Integral.Measure in
theorem exists_gInvDiffSlotCoeff_grid_l2_jetLinear_highOrder
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ Kg : ℕ → ℝ, (∀ i, 0 ≤ Kg i) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        ∀ (i : ℕ),
          (∫ x, (∑ n' ∈ Finset.range (i + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n' i,
                ∏ m : Fin n',
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x))
            ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g₀)) ≤
          Kg i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨C2, hC2_nn, hC2⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ (a + 2)
  set B : ℝ := C2 * R₀ with hB_def
  have hB_nn : 0 ≤ B := mul_nonneg hC2_nn hR₀
  obtain ⟨Cemb, hCemb_nn, hCemb⟩ :=
    deTurckSmoothRemainderDiff_supercritical_pointwise_jet_le_fixedWindow
      (I := I) (M := M) g₀ a ha_super
  set Λ₀ : ℝ := Cemb * Real.sqrt ((a + 1 + 1 : ℕ) : ℝ) * B with hΛ₀_def
  have hΛ₀_nn : 0 ≤ Λ₀ := by rw [hΛ₀_def]; positivity
  set L : ℝ := max (Λ₀ ^ 2) 1 with hL_def
  have hL_one : (1 : ℝ) ≤ L := le_max_right _ _
  have hL_nn : (0 : ℝ) ≤ L := le_trans zero_le_one hL_one
  set Cgn : ℕ → ℝ := fun k =>
    if h : 1 ≤ k then
      (Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 2 k h).choose
    else 0 with hCgn_def
  set Cg1 : ℕ → ℝ := fun k => max (Cgn k) 1 with hCg1_def
  have hCg1_one : ∀ k, (1 : ℝ) ≤ Cg1 k := fun k => le_max_right _ _
  have hCgL_one : ∀ k, (1 : ℝ) ≤ Cg1 k * L :=
    fun k => le_trans (hCg1_one k) (le_mul_of_one_le_right
      (le_trans zero_le_one (hCg1_one k)) hL_one)
  set Cbig : ℕ → ℝ := fun k => L ^ k * (Cg1 k * L) ^ k with hCbig_def
  have hCbig_nn : ∀ k, 0 ≤ Cbig k := fun k =>
    mul_nonneg (pow_nonneg hL_nn k)
      (pow_nonneg (le_trans zero_le_one (hCgL_one k)) k)
  set vol : ℝ := ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal
    with hvol_def
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  refine ⟨fun k => (∑ n' ∈ Finset.range (k + 1),
      ((Finset.Nat.antidiagonalTuple n' k).card : ℝ)) * Cbig k + vol, ?_, ?_⟩
  · intro k
    exact add_nonneg
      (mul_nonneg (Finset.sum_nonneg fun n' _ => Nat.cast_nonneg _) (hCbig_nn k)) hvol_nn
  · intro T₀ hball i
    have hS_nn : 0 ≤ ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 :=
      Finset.sum_nonneg fun j _ => sq_nonneg _
    have h1S : (1 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by linarith
    have hPball : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤ B := by
      intro j hj
      have hsum := hC2 T₀
      have hcast : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 2 : ℕ) : ℝ) T₀‖ =
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ :=
        smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
      rw [hcast] at hsum
      have hsumB : ∑ l ∈ Finset.range (a + 2 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ≤ B := by
        rw [hB_def]
        exact le_trans hsum (mul_le_mul_of_nonneg_left hball hC2_nn)
      exact le_trans
        (Finset.single_le_sum
          (f := fun l => ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖)
          (fun l _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))) hsumB
    have hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        (T₀.toSection x) ≤ Λ₀ ^ 2 := by
      intro x
      have hsum_le : ∑ j ∈ Finset.range (a + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 ≤ ((a + 1 + 1 : ℕ) : ℝ) * B ^ 2 := by
        calc ∑ j ∈ Finset.range (a + 1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2
            ≤ ∑ j ∈ Finset.range (a + 1 + 1), B ^ 2 := by
              apply Finset.sum_le_sum
              intro j hj
              have hjle : j ≤ a + 2 := by have := Finset.mem_range.mp hj; omega
              nlinarith [norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 j T₀),
                hPball j hjle, hB_nn]
          _ = ((a + 1 + 1 : ℕ) : ℝ) * B ^ 2 := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hsingle : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T₀.toSection x) ≤
          ∑ m ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 m T₀).toSection x) := by
        have h0mem : (0 : ℕ) ∈ Finset.range 3 := by norm_num
        have hsl := Finset.single_le_sum
          (f := fun m => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 m T₀).toSection x))
          (fun m _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + m) x _) h0mem
        simpa using hsl
      have hLam2 : Λ₀ ^ 2 = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * B ^ 2 := by
        rw [hΛ₀_def, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
      have hchain : ∑ m ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 m T₀).toSection x) ≤ Λ₀ ^ 2 := by
        refine le_trans (hCemb T₀ x) ?_
        rw [hLam2]
        calc Cemb ^ 2 * ∑ j ∈ Finset.range (a + 1 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2
            ≤ Cemb ^ 2 * (((a + 1 + 1 : ℕ) : ℝ) * B ^ 2) :=
              mul_le_mul_of_nonneg_left hsum_le (by positivity)
          _ = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * B ^ 2 := by ring
      exact le_trans hsingle hchain
    by_cases hi0 : i = 0
    · subst hi0
      have hgrid0 : (fun x => ∑ n' ∈ Finset.range (0 + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n' 0, ∏ m : Fin n',
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)) =
          (fun _ : M => (1 : ℝ)) := by
        funext x
        simp only [Nat.zero_add, Finset.sum_range_one, Finset.Nat.antidiagonalTuple_zero_zero,
          Finset.sum_singleton, Finset.univ_eq_empty, Finset.prod_empty]
      rw [hgrid0, MeasureTheory.integral_const, smul_eq_mul, mul_one,
        MeasureTheory.measureReal_def, ← hvol_def]
      have hvolKg : vol ≤ (∑ n' ∈ Finset.range (0 + 1),
          ((Finset.Nat.antidiagonalTuple n' 0).card : ℝ)) * Cbig 0 + vol :=
        le_add_of_nonneg_left
          (mul_nonneg (Finset.sum_nonneg fun n' _ => Nat.cast_nonneg _) (hCbig_nn 0))
      calc vol = vol * 1 := (mul_one _).symm
        _ ≤ ((∑ n' ∈ Finset.range (0 + 1),
              ((Finset.Nat.antidiagonalTuple n' 0).card : ℝ)) * Cbig 0 + vol) *
            (1 + ∑ j ∈ Finset.range (0 + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) :=
          mul_le_mul hvolKg h1S zero_le_one
            (add_nonneg (mul_nonneg (Finset.sum_nonneg fun n' _ => Nat.cast_nonneg _)
              (hCbig_nn 0)) hvol_nn)
    · have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
      have hiR_pos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hi0
      have hN2_le : ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 ≤
          1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by
        have hmem : i ∈ Finset.range (i + 2) := Finset.mem_range.mpr (by omega)
        have := Finset.single_le_sum
          (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)
          (fun j _ => sq_nonneg _) hmem
        linarith
      have hGNspec :=
        (Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 2 i hi1).choose_spec.2
      have hCgn_i :
        (Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
          (I := I) (M := M) g₀ 0 2 i hi1).choose = Cgn i := by
        rw [hCgn_def]; simp only [dif_pos hi1]
      have hLbound : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 2 → Λ₀ ^ θ ≤ L := by
        intro θ hθ0 hθ2
        rcases le_or_gt 1 Λ₀ with hΛ1 | hΛ1
        · calc Λ₀ ^ θ ≤ Λ₀ ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hΛ1 hθ2
            _ = Λ₀ ^ 2 := Real.rpow_two Λ₀
            _ ≤ L := le_max_left _ _
        · calc Λ₀ ^ θ ≤ 1 := Real.rpow_le_one hΛ₀_nn (le_of_lt hΛ1) hθ0
            _ ≤ L := hL_one
      have hcont_prod : ∀ (n' : ℕ) (e : Fin n' → ℕ), Continuous (fun x : M =>
          ∏ m : Fin n', riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)) := by
        intro n' e
        refine continuous_finset_prod _ fun m _ => ?_
        have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
          (iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀)
        refine hc.congr fun x => ?_
        rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x),
          ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
            (iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀) x]
      have hint_prod : ∀ (n' : ℕ) (e : Fin n' → ℕ), MeasureTheory.Integrable
          (fun x : M => ∏ m : Fin n',
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
        fun n' e => integrable_of_continuous_compactSpace (I := I) (M := M) g₀
          (hcont_prod n' e)
      have hPT : ∀ n' ∈ Finset.range (i + 1), ∀ e ∈ Finset.Nat.antidiagonalTuple n' i,
          (∫ x, ∏ m : Fin n',
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
          Cbig i * ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 := by
        intro n' hn' e he
        have hn'_le : n' ≤ i := by have := Finset.mem_range.mp hn'; omega
        have hsum_univ : ∑ m, e m = i := Finset.Nat.mem_antidiagonalTuple.mp he
        have hem_le : ∀ m : Fin n', e m ≤ i := by
          intro m
          have h1 := Finset.single_le_sum (f := fun m' => e m')
            (fun m' _ => Nat.zero_le (e m')) (Finset.mem_univ m)
          rw [hsum_univ] at h1
          exact h1
        have hΛzero : ∀ m ∈ (Finset.univ : Finset (Fin n')), e m = 0 → ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x) ≤ Λ₀ ^ 2 := by
          intro m _ hm0 x
          revert hm0
          generalize e m = j
          intro hj
          subst hj
          simpa [iteratedCovGrad_zero] using hsup x
        have hHold := holder_integral_prod_riemannianFiberNormSq_natWeight_le_of_sup_bound
          (I := I) (M := M) g₀ (Finset.univ : Finset (Fin n')) (fun _ => 0)
          (fun m => 2 + e m) (fun m => iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀) e i
          hi1 hsum_univ (fun _ => Λ₀ ^ 2) (fun m _ _ => sq_nonneg _) hΛzero
        beta_reduce at hHold
        have hsum_pos_nat : ∑ m ∈ Finset.univ.filter (fun m : Fin n' => 0 < e m), e m = i := by
          rw [← hsum_univ]
          refine Finset.sum_subset (Finset.filter_subset _ _) fun m _ hm => ?_
          by_contra h0
          exact hm (Finset.mem_filter.mpr ⟨Finset.mem_univ m, Nat.pos_of_ne_zero h0⟩)
        have h2sum : ∑ m ∈ Finset.univ.filter (fun m : Fin n' => 0 < e m),
            (2 * (e m : ℝ) / (i : ℝ)) = 2 := by
          have hterm : ∀ m ∈ Finset.univ.filter (fun m : Fin n' => 0 < e m),
              2 * (e m : ℝ) / (i : ℝ) = (e m : ℝ) * (2 / (i : ℝ)) := fun m _ => by ring
          rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Nat.cast_sum, hsum_pos_nat]
          field_simp
        have hposcard : (Finset.univ.filter (fun m : Fin n' => 0 < e m)).card ≤ i := by
          calc (Finset.univ.filter (fun m : Fin n' => 0 < e m)).card
              ≤ (Finset.univ : Finset (Fin n')).card := Finset.card_filter_le _ _
            _ = n' := by simp
            _ ≤ i := hn'_le
        have hzercard : (Finset.univ.filter (fun m : Fin n' => e m = 0)).card ≤ i := by
          calc (Finset.univ.filter (fun m : Fin n' => e m = 0)).card
              ≤ (Finset.univ : Finset (Fin n')).card := Finset.card_filter_le _ _
            _ = n' := by simp
            _ ≤ i := hn'_le
        have hFG : ∀ m ∈ Finset.univ.filter (fun m : Fin n' => 0 < e m),
            (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)
                  ^ ((i : ℝ) / (e m : ℝ))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((e m : ℝ) / (i : ℝ)) ≤
            Cg1 i * L * ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖
              ^ (2 * (e m : ℝ) / (i : ℝ)) := by
          intro m hm
          have hem_pos : 0 < e m := (Finset.mem_filter.mp hm).2
          rcases eq_or_lt_of_le (hem_le m) with hemi | hemi
          · subst hemi
            have hd1 : ((e m : ℝ) / (e m : ℝ)) = 1 := div_self (ne_of_gt hiR_pos)
            rw [hd1, Real.rpow_one, mul_div_assoc, hd1, mul_one, Real.rpow_two]
            simp only [Real.rpow_one]
            have hbr := tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
              (I := I) (M := M) g₀ 0 (2 + e m)
              (iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀)
            rw [← SmoothCcTensor.norm_def] at hbr
            rw [← hbr]
            have h1 : (1 : ℝ) ≤ Cg1 (e m) * L := hCgL_one (e m)
            nlinarith [sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀‖]
          · have hb := hGNspec T₀ Λ₀ hΛ₀_nn hsup (e m) hem_pos hemi
            rw [hCgn_i] at hb
            refine le_trans hb ?_
            have hnorm : Integral.L2.tensorL2Norm (I := I) g₀ 0 (2 + i)
                (iteratedCovGrad (I := I) g₀ 0 2 i T₀).toFun =
                ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ :=
              (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 i T₀)).symm
            rw [hnorm]
            have hθL_nn : (0 : ℝ) ≤ 2 * (1 - (e m : ℝ) / (i : ℝ)) := by
              have : (e m : ℝ) / (i : ℝ) ≤ 1 :=
                (div_le_one hiR_pos).mpr (by exact_mod_cast hem_le m)
              linarith
            have hθL_le2 : 2 * (1 - (e m : ℝ) / (i : ℝ)) ≤ 2 := by
              have : (0 : ℝ) ≤ (e m : ℝ) / (i : ℝ) := by positivity
              linarith
            have hΛfac : Λ₀ ^ (2 * (1 - (e m : ℝ) / (i : ℝ))) ≤ L :=
              hLbound _ hθL_nn hθL_le2
            have hNfac_nn : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖
                ^ (2 * (e m : ℝ) / (i : ℝ)) :=
              Real.rpow_nonneg (norm_nonneg _) _
            calc Cgn i * Λ₀ ^ (2 * (1 - (e m : ℝ) / (i : ℝ))) *
                  ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ (2 * (e m : ℝ) / (i : ℝ))
                ≤ Cg1 i * Λ₀ ^ (2 * (1 - (e m : ℝ) / (i : ℝ))) *
                  ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ (2 * (e m : ℝ) / (i : ℝ)) := by
                  refine mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right (le_max_left _ _)
                      (Real.rpow_nonneg hΛ₀_nn _)) hNfac_nn
              _ ≤ Cg1 i * L * ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖
                  ^ (2 * (e m : ℝ) / (i : ℝ)) := by
                  refine mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hΛfac
                      (le_trans zero_le_one (hCg1_one i))) hNfac_nn
        have hF_nn : ∀ m ∈ Finset.univ.filter (fun m : Fin n' => 0 < e m),
            (0 : ℝ) ≤ (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)
                  ^ ((i : ℝ) / (e m : ℝ))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((e m : ℝ) / (i : ℝ)) :=
          fun m _ => Real.rpow_nonneg
            (MeasureTheory.integral_nonneg fun x => Real.rpow_nonneg
              (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + e m) x _) _) _
        have hprodF_le : (∏ m ∈ Finset.univ.filter (fun m : Fin n' => 0 < e m),
            (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)
                  ^ ((i : ℝ) / (e m : ℝ))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((e m : ℝ) / (i : ℝ))) ≤
            ∏ m ∈ Finset.univ.filter (fun m : Fin n' => 0 < e m),
              (Cg1 i * L * ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖
                ^ (2 * (e m : ℝ) / (i : ℝ))) :=
          Finset.prod_le_prod hF_nn hFG
        have hprodG : (∏ m ∈ Finset.univ.filter (fun m : Fin n' => 0 < e m),
            (Cg1 i * L * ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖
              ^ (2 * (e m : ℝ) / (i : ℝ)))) =
            (Cg1 i * L) ^ (Finset.univ.filter (fun m : Fin n' => 0 < e m)).card *
              ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ (2 : ℝ) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const,
            ← Real.rpow_sum_of_nonneg (norm_nonneg _) (fun m _ => by positivity), h2sum]
        have hzer_le : ((Λ₀ ^ 2) ^ (Finset.univ.filter
            (fun m : Fin n' => e m = 0)).card : ℝ) ≤ L ^ i :=
          le_trans (pow_le_pow_left₀ (sq_nonneg _) (le_max_left _ _) _)
            (pow_le_pow_right₀ hL_one hzercard)
        have hpos_le : ((Cg1 i * L) ^ (Finset.univ.filter
            (fun m : Fin n' => 0 < e m)).card : ℝ) ≤ (Cg1 i * L) ^ i :=
          pow_le_pow_right₀ (hCgL_one i) hposcard
        calc (∫ x, ∏ m : Fin n',
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
            ≤ (∏ _m ∈ Finset.univ.filter (fun m : Fin n' => e m = 0), Λ₀ ^ 2) *
              ∏ m ∈ Finset.univ.filter (fun m : Fin n' => 0 < e m),
                (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)
                      ^ ((i : ℝ) / (e m : ℝ))
                  ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((e m : ℝ) / (i : ℝ)) :=
            hHold
          _ ≤ (∏ _m ∈ Finset.univ.filter (fun m : Fin n' => e m = 0), Λ₀ ^ 2) *
              ((Cg1 i * L) ^ (Finset.univ.filter (fun m : Fin n' => 0 < e m)).card *
                ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ (2 : ℝ)) := by
            refine mul_le_mul_of_nonneg_left (le_of_le_of_eq hprodF_le hprodG) ?_
            exact Finset.prod_nonneg fun _ _ => sq_nonneg _
          _ = (Λ₀ ^ 2) ^ (Finset.univ.filter (fun m : Fin n' => e m = 0)).card *
              ((Cg1 i * L) ^ (Finset.univ.filter (fun m : Fin n' => 0 < e m)).card *
                ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
            rw [Finset.prod_const, Real.rpow_two]
          _ ≤ L ^ i * ((Cg1 i * L) ^ i *
                ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
            refine mul_le_mul hzer_le
              (mul_le_mul_of_nonneg_right hpos_le (sq_nonneg _))
              (mul_nonneg (pow_nonneg (le_trans zero_le_one (hCgL_one i)) _)
                (sq_nonneg _))
              (pow_nonneg hL_nn i)
          _ = Cbig i * ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 := by
            simp only [hCbig_def]
            ring
      rw [MeasureTheory.integral_finset_sum _
        (fun n' _ => MeasureTheory.integrable_finset_sum _ (fun e _ => hint_prod n' e))]
      have hinner : ∀ n' ∈ Finset.range (i + 1),
          (∫ x, ∑ e ∈ Finset.Nat.antidiagonalTuple n' i, ∏ m : Fin n',
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)
            ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g₀)) =
          ∑ e ∈ Finset.Nat.antidiagonalTuple n' i,
            ∫ x, ∏ m : Fin n',
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)
            ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g₀) :=
        fun n' _ => MeasureTheory.integral_finset_sum _ (fun e _ => hint_prod n' e)
      rw [Finset.sum_congr rfl hinner]
      have hle1 : ∑ n' ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n' i,
            (∫ x, ∏ m : Fin n',
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)
            ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g₀)) ≤
          ∑ n' ∈ Finset.range (i + 1), ∑ _e ∈ Finset.Nat.antidiagonalTuple n' i,
            (Cbig i * ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
        refine Finset.sum_le_sum fun n' hn' => Finset.sum_le_sum fun e he => ?_
        exact hPT n' hn' e he
      refine le_trans hle1 ?_
      have heq2 : ∑ n' ∈ Finset.range (i + 1), ∑ _e ∈ Finset.Nat.antidiagonalTuple n' i,
          (Cbig i * ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) =
          (∑ n' ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n' i).card : ℝ)) *
            (Cbig i * ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun n' _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [heq2]
      have hcard_nn : (0 : ℝ) ≤ ∑ n' ∈ Finset.range (i + 1),
          ((Finset.Nat.antidiagonalTuple n' i).card : ℝ) :=
        Finset.sum_nonneg fun n' _ => Nat.cast_nonneg _
      calc (∑ n' ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n' i).card : ℝ)) *
            (Cbig i * ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2)
          = ((∑ n' ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n' i).card : ℝ)) *
              Cbig i) * ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 := by ring
        _ ≤ ((∑ n' ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n' i).card : ℝ)) *
              Cbig i) * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hN2_le (mul_nonneg hcard_nn (hCbig_nn i))
        _ ≤ ((∑ n' ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n' i).card : ℝ)) *
              Cbig i + vol) * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) :=
            mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hvol_nn)
              (le_trans zero_le_one h1S)

set_option backward.isDefEq.respectTransparency false in
open DifferentialGeometry.Integral.Measure in
theorem exists_deTurckPrincipalCometricCoeff_realize_coeffJetEnvelope_le
    (g₀ _g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2),
        (∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T₀ x v w = smoothCcTensorBilinForm (I := I) g₀ T₀ x w
            v) →
        ∀ (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
              (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
                  (tensorSectionRealizeMetric (I := I) g₀ T₀
                    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                    (hδ_fibre T₀ hball)))‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) := by
  classical
  have hrsub : ∀ k l : ℕ, k ≤ l → Finset.range k ⊆ Finset.range l :=
    fun k l hkl x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hkl)
  obtain ⟨Kg, hKg_nn, hKg⟩ :=
    exists_gInvDiffSlotCoeff_grid_l2_jetLinear_highOrder (I := I) (M := M) g₀ a ha_super hR₀
  obtain ⟨Cd, hCd_nn, hCd⟩ :=
    deTurckPrincipalCometricCoeff_perOrder_rfns_le_gInvDiffSlotCoeff (I := I) (M := M) g₀
  obtain ⟨C2, hC2_nn, hC2⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ (a + 2)
  set B : ℝ := C2 * R₀ with hB_def
  have hB_nn : 0 ≤ B := mul_nonneg hC2_nn hR₀
  obtain ⟨Klo, hKlo_nn, hKlo⟩ :=
    gInvDiffSlotCoeff_perOrder_l2_ballUniform_generic (I := I) (M := M) g₀ a ha_super hB_nn
      (by norm_num : (1 : ℝ) / 3 < 1)
  obtain ⟨Cg, hCg_nn, hCg⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_gInvDiffSlotCoeff_diagonalProductGrid_le (I := I) (M := M)
      g₀
      (by norm_num : (1 : ℝ) / 3 < 1)
  set KcF : ℕ → ℝ := fun i => Cd i * ∑ j ∈ Finset.range (i + 1),
    (Klo j + Cg j * Kg j) with hKcF_def
  have hKcF_nn : ∀ i, 0 ≤ KcF i := fun i =>
    mul_nonneg (hCd_nn i) (Finset.sum_nonneg fun j _ =>
      add_nonneg (hKlo_nn j) (mul_nonneg (hCg_nn j) (hKg_nn j)))
  refine ⟨KcF, hKcF_nn, ?_⟩
  intro T₀ hTsymm hball i
  set g₁ : SmoothRiemannianMetric I M := tensorSectionRealizeMetric (I := I) g₀ T₀
    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) with hg₁_def
  have hS_nn : 0 ≤ ∑ l ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 :=
    Finset.sum_nonneg fun l _ => sq_nonneg _
  have h1S_nn : (0 : ℝ) ≤ 1 + ∑ l ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 := by linarith
  rcases isEmpty_or_nonempty M with hM | hM
  · have hzero : ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
        (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)‖ = 0 := by
      rw [SmoothCcTensor.norm_def, DifferentialGeometry.Integral.L2.tensorL2Norm,
        DifferentialGeometry.Integral.L2.tensorL2Inner, MeasureTheory.integral_of_isEmpty,
        Real.sqrt_zero]
    rw [hzero]
    have hpos : (0 : ℝ) ≤ KcF i * (1 + ∑ l ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := mul_nonneg (hKcF_nn i) h1S_nn
    simpa using hpos
  · have hδ0 : 0 ≤ δ :=
      delta_nonneg_of_ball_gFibreOpBound (I := I) (M := M) g₀ a hR₀ hδ_fibre
    have htie : ∀ (y : M) (v w : TangentSpace I y),
        g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₀ y v w := by
      intro y v w
      rw [hg₁_def]
      exact tensorSectionRealizeMetric_inner (I := I) g₀ T₀
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) y v w
    have hPball : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤ B := by
      intro j hj
      have hsum := hC2 T₀
      have hcast : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 2 : ℕ) : ℝ) T₀‖ =
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ :=
        smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
      rw [hcast] at hsum
      have hsumB : ∑ l ∈ Finset.range (a + 2 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ≤ B := by
        rw [hB_def]
        exact le_trans hsum (mul_le_mul_of_nonneg_left hball hC2_nn)
      have hsingle : ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
          ∑ l ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ :=
        Finset.single_le_sum
          (f := fun l => ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖)
          (fun l _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
      exact le_trans hsingle hsumB
    have hint_slot : ∀ j : ℕ, MeasureTheory.Integrable
        (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 2 2 j
            (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      fun j => integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 2 (2 + j) _
    have hL2trans : ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
        (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
        Cd i * ∑ j ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 := by
      have hF_int : MeasureTheory.Integrable
          (fun x => Cd i * ∑ j ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 2 2 j
                (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
        (MeasureTheory.integrable_finset_sum _ (fun j _ => hint_slot j)).const_mul (Cd i)
      have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
        (2 + 2) (2 + i)
        (iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁))
        (fun x => Cd i * ∑ j ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 2 2 j
              (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x))
        hF_int (fun x => hCd g₁ i x)
      refine le_trans hkey ?_
      rw [MeasureTheory.integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (hCd_nn i)
      rw [MeasureTheory.integral_finset_sum _ (fun j _ => hint_slot j)]
      refine Finset.sum_le_sum fun j _ => ?_
      have hbr := tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M)
        g₀ 2 (2 + j) (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁))
      rw [← SmoothCcTensor.norm_def] at hbr
      exact le_of_eq hbr.symm
    have hslot : ∀ j : ℕ, j ≤ i →
        ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 ≤
          (Klo j + Cg j * Kg j) * (1 + ∑ l ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
      intro j hj
      have h1S_ge : (1 : ℝ) ≤ 1 + ∑ l ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 := by linarith
      rcases le_or_gt j a with hja | hja
      · have hlo := hKlo g₁ T₀ hδ_le (hδ_fibre T₀ hball) htie hPball j hja
        calc ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2
            ≤ Klo j := hlo
          _ = Klo j * 1 := (mul_one _).symm
          _ ≤ Klo j * (1 + ∑ l ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) :=
            mul_le_mul_of_nonneg_left h1S_ge (hKlo_nn j)
          _ ≤ (Klo j + Cg j * Kg j) * (1 + ∑ l ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
            refine mul_le_mul_of_nonneg_right ?_ h1S_nn
            exact le_add_of_nonneg_right (mul_nonneg (hCg_nn j) (hKg_nn j))
      · have hpt : ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 2 2 j
                (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) ≤
            Cg j * ∑ n' ∈ Finset.range (j + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                ∏ m : Fin n',
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x) :=
          fun x => hCg g₁ T₀ htie hδ_le hδ0 (hδ_fibre T₀ hball) j x
        have hcont_grid : Continuous (fun x : M =>
            ∑ n' ∈ Finset.range (j + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                ∏ m : Fin n',
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)) := by
          refine continuous_finset_sum _ fun n' _ => continuous_finset_sum _ fun e _ =>
            continuous_finset_prod _ fun m _ => ?_
          have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
            (iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀)
          refine hc.congr fun x => ?_
          rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x),
            ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
              (iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀) x]
        have hint_grid : MeasureTheory.Integrable
            (fun x : M => ∑ n' ∈ Finset.range (j + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                ∏ m : Fin n',
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
          integrable_of_continuous_compactSpace (I := I) (M := M) g₀ hcont_grid
        have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
          2 (2 + j)
          (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁))
          (fun x => Cg j * ∑ n' ∈ Finset.range (j + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
              ∏ m : Fin n',
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x))
          (hint_grid.const_mul (Cg j)) hpt
        have hgridE := hKg T₀ hball j
        have hwin : ∑ l ∈ Finset.range (j + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 ≤
            ∑ l ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (hrsub _ _ (by omega))
            (fun l _ _ => sq_nonneg _)
        calc ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2
            ≤ ∫ x, (Cg j * ∑ n' ∈ Finset.range (j + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                  ∏ m : Fin n',
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := hkey
          _ = Cg j * ∫ x, (∑ n' ∈ Finset.range (j + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                  ∏ m : Fin n',
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
            rw [MeasureTheory.integral_const_mul]
          _ ≤ Cg j * (Kg j * (1 + ∑ l ∈ Finset.range (j + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left hgridE (hCg_nn j)
          _ ≤ Cg j * (Kg j * (1 + ∑ l ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2)) := by
            refine mul_le_mul_of_nonneg_left ?_ (hCg_nn j)
            refine mul_le_mul_of_nonneg_left ?_ (hKg_nn j)
            linarith
          _ = Cg j * Kg j * (1 + ∑ l ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by ring
          _ ≤ (Klo j + Cg j * Kg j) * (1 + ∑ l ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
            refine mul_le_mul_of_nonneg_right ?_ h1S_nn
            exact le_add_of_nonneg_left (hKlo_nn j)
    calc ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2
        ≤ Cd i * ∑ j ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 :=
          hL2trans
      _ ≤ Cd i * ∑ j ∈ Finset.range (i + 1),
            ((Klo j + Cg j * Kg j) * (1 + ∑ l ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2)) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_) (hCd_nn i)
          exact hslot j (by have := Finset.mem_range.mp hj; omega)
      _ = KcF i * (1 + ∑ l ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
          simp only [hKcF_def]
          rw [← Finset.sum_mul]
          ring

set_option backward.isDefEq.respectTransparency false in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem pje_icg_smul (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) =
      c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
set_option backward.isDefEq.respectTransparency false in
private lemma riemannianFiberNormSq_toSection_smul (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (V : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r s x ((c • V).toSection x) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x (V.toSection x) := by
  rw [show ((c • V).toSection x) = c • (V.toSection x) from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x
      (c • V.toSection x),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (V.toSection x)]
  rw [Tensor0SBundle.TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left,
    tensorInnerPointwise_smul_right]
  ring

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private theorem pje_normSq_icg_reindex_eq (g₀ : SmoothRiemannianMetric I M)
    (R : SmoothCcTensor g₀ 4 2) (ρ : Equiv.Perm (Fin 4)) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (reindexCoeffGen (I := I) (M := M) g₀ 4 2 R ρ)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 4 2 i R‖ ^ 2 := by
  have h1 := tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M)
    g₀ 4 (2 + i)
    (iteratedCovGrad (I := I) g₀ 4 2 i (reindexCoeffGen (I := I) (M := M) g₀ 4 2 R ρ))
  have h2 := tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M)
    g₀ 4 (2 + i) (iteratedCovGrad (I := I) g₀ 4 2 i R)
  rw [← SmoothCcTensor.norm_def] at h1 h2
  rw [h1, h2]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 4 2 R ρ i x

set_option backward.isDefEq.respectTransparency false in
open DifferentialGeometry.PDE.DeTurck.RicciLinearization in
open DifferentialGeometry.Integral.Measure in
theorem exists_deTurckPhiTotPathIntegral_sub_background_coeffJetEnvelope_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2),
        (∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T₀ x v w = smoothCcTensorBilinForm (I := I) g₀ T₀ x w
            v) →
        ∀ (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
              (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
                  (0 : SmoothCcTensor g₀ 0 2)
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                  (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                    (by
                      rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                          from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                        tensorHs_norm_smul]
                      simpa using hR₀)) -
                deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) := by
  classical
  have hrsub : ∀ k l : ℕ, k ≤ l → Finset.range k ⊆ Finset.range l :=
    fun k l hkl x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hkl)
  obtain ⟨Kg, hKg_nn, hKg⟩ :=
    exists_gInvDiffSlotCoeff_grid_l2_jetLinear_highOrder (I := I) (M := M) g₀ a ha_super hR₀
  obtain ⟨Cth, hCth_nn, hCth⟩ :=
    traceHessianCoeff_sub_background_jetL2_le_gInvDiffSlotCoeff_jetL2 (I := I) (M := M) g₀
  obtain ⟨Cr, hCr_nn, hCr⟩ :=
    ricciArmPrincipalCoeff_sub_background_jetL2_le_gInvDiffSlotCoeff_jetL2 (I := I) (M := M) g₀
  obtain ⟨C2, hC2_nn, hC2⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ (a + 2)
  set B : ℝ := C2 * R₀ with hB_def
  have hB_nn : 0 ≤ B := mul_nonneg hC2_nn hR₀
  obtain ⟨Klo, hKlo_nn, hKlo⟩ :=
    gInvDiffSlotCoeff_perOrder_l2_ballUniform_generic (I := I) (M := M) g₀ a ha_super hB_nn
      (by norm_num : (1 : ℝ) / 3 < 1)
  obtain ⟨Cg, hCg_nn, hCg⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_gInvDiffSlotCoeff_diagonalProductGrid_le (I := I) (M := M)
      g₀
      (by norm_num : (1 : ℝ) / 3 < 1)
  set KdevF : ℕ → ℝ := fun i => (6 * Cth i + 12 * Cr i) * ∑ j ∈ Finset.range (i + 1),
    (Klo j + Cg j * Kg j) with hKdevF_def
  have hKdevF_nn : ∀ i, 0 ≤ KdevF i := fun i =>
    mul_nonneg (by have := hCth_nn i; have := hCr_nn i; linarith)
      (Finset.sum_nonneg fun j _ =>
        add_nonneg (hKlo_nn j) (mul_nonneg (hCg_nn j) (hKg_nn j)))
  set cB : ℕ → ℝ := fun i =>
    ‖iteratedCovGrad (I := I) g₀ 4 2 i
      (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ^ 2 with hcB_def
  have hcB_nn : ∀ i, 0 ≤ cB i := fun i => sq_nonneg _
  refine ⟨fun i => 4 * KdevF i + 6 * cB i,
    fun i => by have := hKdevF_nn i; have := hcB_nn i; linarith, ?_⟩
  intro T₀ hTsymm hball i
  change ‖iteratedCovGrad (I := I) g₀ 4 2 i
      (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
          (0 : SmoothCcTensor g₀ 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
            (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀)) -
        deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ^ 2 ≤
    (4 * KdevF i + 6 * cB i) * (1 + ∑ l ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2)
  have hS_nn : 0 ≤ ∑ l ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 :=
    Finset.sum_nonneg fun l _ => sq_nonneg _
  have h1S_nn : (0 : ℝ) ≤ 1 + ∑ l ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 := by linarith
  have h1S_ge : (1 : ℝ) ≤ 1 + ∑ l ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 := by linarith
  rcases isEmpty_or_nonempty M with hM | hM
  · have hzero : ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
            (0 : SmoothCcTensor g₀ 0 2)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
              (by
                rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                    from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                  tensorHs_norm_smul]
                simpa using hR₀)) -
          deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ = 0 := by
      rw [SmoothCcTensor.norm_def, DifferentialGeometry.Integral.L2.tensorL2Norm,
        DifferentialGeometry.Integral.L2.tensorL2Inner, MeasureTheory.integral_of_isEmpty,
        Real.sqrt_zero]
    rw [hzero]
    have hpos : (0 : ℝ) ≤ (4 * KdevF i + 6 * cB i) * (1 + ∑ l ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) :=
      mul_nonneg (by have := hKdevF_nn i; have := hcB_nn i; linarith) h1S_nn
    simpa using hpos
  · have hδ0 : 0 ≤ δ :=
      delta_nonneg_of_ball_gFibreOpBound (I := I) (M := M) g₀ a hR₀ hδ_fibre
    have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
    have hZn : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (0 : SmoothCcTensor g₀ 0 2)‖ ≤ R₀ := by
      rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
          from (zero_smul _ _).symm, smoothCcToTensorHs_smul, tensorHs_norm_smul]
      simpa using hR₀
    have hSI : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ) := by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_realizedSmallSet hδ_lt hδ_lt
    have hSopen : IsOpen (realizedSmallSet (δ := δ) (δ' := δ)) := realizedSmallSet_isOpen
    have hj2 := deTurckPhiMetTotal_jointSmooth_along_realizedFam (I := I) (M := M) g₀ g_bg T₀
      (0 : SmoothCcTensor g₀ 0 2) (hδ_fibre T₀ hball) (hδ_fibre 0 hZn)
    have hTball : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤ B := by
      intro j hj
      have hsum := hC2 T₀
      have hcast : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 2 : ℕ) : ℝ) T₀‖ =
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ :=
        smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
      rw [hcast] at hsum
      have hsumB : ∑ l ∈ Finset.range (a + 2 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ≤ B := by
        rw [hB_def]
        exact le_trans hsum (mul_le_mul_of_nonneg_left hball hC2_nn)
      have hsingle : ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
          ∑ l ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ :=
        Finset.single_le_sum
          (f := fun l => ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖)
          (fun l _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
      exact le_trans hsingle hsumB
    let Φ : ℝ → SmoothCcTensor g₀ 4 2 := fun s =>
      deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
        (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
          (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s)
    let Φbg : SmoothCcTensor g₀ 4 2 :=
      deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀
    have hdev : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedCovGrad (I := I) g₀ 4 2 i (Φ s - Φbg)‖ ^ 2 ≤
        KdevF i * (1 + ∑ l ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
      intro s hs
      set g₁ : SmoothRiemannianMetric I M :=
        realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
          (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s with hg₁_def
      have hsmem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
        Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
      have htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀
              (convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) s) y v w := by
        intro y v w
        rw [hg₁_def]
        exact realizedFam_inner_of_mem (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
          (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) hsmem y v w
      have hcp : convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) s = s • T₀ := by
        simp [convexPerturbation, smul_zero, zero_add]
      have hs0 : (0 : ℝ) ≤ s := hs.1
      have hs1 : s ≤ 1 := hs.2
      have hδP : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀
            (convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) s)) δ := by
        have h := convexPerturbation_gFibreOpBound (I := I) (M := M) g₀ T₀
          (0 : SmoothCcTensor g₀ 0 2) (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) hs0 hs1
        rwa [show (1 - s) * δ + s * δ = δ by ring] at h
      have hPball : ∀ j : ℕ, j ≤ a + 2 →
          ‖iteratedCovGrad (I := I) g₀ 0 2 j
            (convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) s)‖ ≤ B := by
        intro j hj
        rw [hcp, pje_icg_smul (I := I) g₀ 0 2 j s T₀, norm_smul]
        have habs : ‖s‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hs0]; exact hs1
        calc ‖s‖ * ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖
            ≤ 1 * B := mul_le_mul habs (hTball j hj) (norm_nonneg _) zero_le_one
          _ = B := one_mul B
      have hslot : ∀ j : ℕ, j ≤ i →
          ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 ≤
            (Klo j + Cg j * Kg j) * (1 + ∑ l ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
        intro j hj
        rcases le_or_gt j a with hja | hja
        · have hlo := hKlo g₁ (convexPerturbation (I := I) g₀ T₀
            (0 : SmoothCcTensor g₀ 0 2) s) hδ_le hδP htie hPball j hja
          calc ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2
              ≤ Klo j := hlo
            _ = Klo j * 1 := (mul_one _).symm
            _ ≤ Klo j * (1 + ∑ l ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) :=
              mul_le_mul_of_nonneg_left h1S_ge (hKlo_nn j)
            _ ≤ (Klo j + Cg j * Kg j) * (1 + ∑ l ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
              refine mul_le_mul_of_nonneg_right ?_ h1S_nn
              exact le_add_of_nonneg_right (mul_nonneg (hCg_nn j) (hKg_nn j))
        · have hpt0 : ∀ x : M,
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
                ((iteratedCovGrad (I := I) g₀ 2 2 j
                  (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) ≤
              Cg j * ∑ n' ∈ Finset.range (j + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                  ∏ m : Fin n',
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m)
                        (convexPerturbation (I := I) g₀ T₀
                          (0 : SmoothCcTensor g₀ 0 2) s)).toSection x) :=
            fun x => hCg g₁ (convexPerturbation (I := I) g₀ T₀
              (0 : SmoothCcTensor g₀ 0 2) s) htie hδ_le hδ0 hδP j x
          have hgm : ∀ x : M,
              (∑ n' ∈ Finset.range (j + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                  ∏ m : Fin n',
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m)
                        (convexPerturbation (I := I) g₀ T₀
                          (0 : SmoothCcTensor g₀ 0 2) s)).toSection x)) ≤
              ∑ n' ∈ Finset.range (j + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                  ∏ m : Fin n',
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x) := by
            intro x
            refine Finset.sum_le_sum fun n' _ => Finset.sum_le_sum fun e _ => ?_
            have hfac : ∀ m : Fin n',
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m)
                    (convexPerturbation (I := I) g₀ T₀
                      (0 : SmoothCcTensor g₀ 0 2) s)).toSection x) =
                s ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x) := by
              intro m
              rw [hcp, pje_icg_smul (I := I) g₀ 0 2 (e m) s T₀,
                riemannianFiberNormSq_toSection_smul (I := I) (M := M) g₀ 0 (2 + e m) s
                  (iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀) x]
            calc (∏ m : Fin n',
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m)
                      (convexPerturbation (I := I) g₀ T₀
                        (0 : SmoothCcTensor g₀ 0 2) s)).toSection x))
                = ∏ m : Fin n', (s ^ 2 *
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)) :=
                  Finset.prod_congr rfl fun m _ => hfac m
              _ = (s ^ 2) ^ (n' : ℕ) * ∏ m : Fin n',
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x) := by
                  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
                    Fintype.card_fin]
              _ ≤ 1 * ∏ m : Fin n',
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x) := by
                  refine mul_le_mul_of_nonneg_right ?_
                    (Finset.prod_nonneg fun m _ =>
                      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + e m) x _)
                  exact pow_le_one₀ (sq_nonneg s) (by nlinarith)
              _ = ∏ m : Fin n',
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x) := one_mul _
          have hpt : ∀ x : M,
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
                ((iteratedCovGrad (I := I) g₀ 2 2 j
                  (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) ≤
              Cg j * ∑ n' ∈ Finset.range (j + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                  ∏ m : Fin n',
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x) :=
            fun x => le_trans (hpt0 x) (mul_le_mul_of_nonneg_left (hgm x) (hCg_nn j))
          have hcont_grid : Continuous (fun x : M =>
              ∑ n' ∈ Finset.range (j + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                  ∏ m : Fin n',
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)) := by
            refine continuous_finset_sum _ fun n' _ => continuous_finset_sum _ fun e _ =>
              continuous_finset_prod _ fun m _ => ?_
            have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
              (iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀)
            refine hc.congr fun x => ?_
            rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x),
              ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
                (iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀) x]
          have hint_grid : MeasureTheory.Integrable
              (fun x : M => ∑ n' ∈ Finset.range (j + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                  ∏ m : Fin n',
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
            integrable_of_continuous_compactSpace (I := I) (M := M) g₀ hcont_grid
          have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
            2 (2 + j)
            (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁))
            (fun x => Cg j * ∑ n' ∈ Finset.range (j + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                ∏ m : Fin n',
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x))
            (hint_grid.const_mul (Cg j)) hpt
          have hgridE := hKg T₀ hball j
          have hwin : ∑ l ∈ Finset.range (j + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 ≤
              ∑ l ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (hrsub _ _ (by omega))
              (fun l _ _ => sq_nonneg _)
          calc ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2
              ≤ ∫ x, (Cg j * ∑ n' ∈ Finset.range (j + 1),
                  ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                    ∏ m : Fin n',
                      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x))
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := hkey
            _ = Cg j * ∫ x, (∑ n' ∈ Finset.range (j + 1),
                  ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                    ∏ m : Fin n',
                      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x))
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
                rw [MeasureTheory.integral_const_mul]
            _ ≤ Cg j * (Kg j * (1 + ∑ l ∈ Finset.range (j + 2),
                  ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2)) :=
              mul_le_mul_of_nonneg_left hgridE (hCg_nn j)
            _ ≤ Cg j * (Kg j * (1 + ∑ l ∈ Finset.range (i + 2),
                  ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2)) := by
                refine mul_le_mul_of_nonneg_left ?_ (hCg_nn j)
                refine mul_le_mul_of_nonneg_left ?_ (hKg_nn j)
                linarith
            _ = Cg j * Kg j * (1 + ∑ l ∈ Finset.range (i + 2),
                  ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by ring
            _ ≤ (Klo j + Cg j * Kg j) * (1 + ∑ l ∈ Finset.range (i + 2),
                  ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
                refine mul_le_mul_of_nonneg_right ?_ h1S_nn
                exact le_add_of_nonneg_left (hKlo_nn j)
      have hslotSum : ∑ j ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 ≤
          (∑ j ∈ Finset.range (i + 1), (Klo j + Cg j * Kg j)) *
            (1 + ∑ l ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
        calc (∑ j ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2)
            ≤ ∑ j ∈ Finset.range (i + 1), ((Klo j + Cg j * Kg j) *
                (1 + ∑ l ∈ Finset.range (i + 2),
                  ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2)) :=
              Finset.sum_le_sum fun j hj =>
                hslot j (by have := Finset.mem_range.mp hj; omega)
          _ = (∑ j ∈ Finset.range (i + 1), (Klo j + Cg j * Kg j)) *
                (1 + ∑ l ∈ Finset.range (i + 2),
                  ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
              rw [Finset.sum_mul]
      have hdev_eq :
          deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₁ -
            deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ =
          reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA)
            + reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT)
            - ((ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
                - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)
              + (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
                - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)) := by
        rw [deTurckPhiMetTotal_eq_reindex_decomp_fw (I := I) (M := M) g₀ g_bg g₁,
          deTurckPhiMetTotal_eq_reindex_decomp_fw (I := I) (M := M) g₀ g_bg g₀,
          reindexCoeffGen_map_sub (I := I) (M := M) g₀ _ _
            (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA),
          reindexCoeffGen_map_sub (I := I) (M := M) g₀ _ _
            (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT)]
        abel
      have hreiA := pje_normSq_icg_reindex_eq (I := I) (M := M) g₀
        (traceHessianCoeff (I := I) (M := M) g₀ g₁
          - traceHessianCoeff (I := I) (M := M) g₀ g₀)
        (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA) i
      have hreiB := pje_normSq_icg_reindex_eq (I := I) (M := M) g₀
        (traceHessianCoeff (I := I) (M := M) g₀ g₁
          - traceHessianCoeff (I := I) (M := M) g₀ g₀)
        (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT) i
      have hth := hCth g₁ i
      have hr := hCr g₁ i
      have htri : ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₁ -
            deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ≤
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA))‖ +
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT))‖ +
          2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
              - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)‖ := by
        rw [hdev_eq, iteratedCovGrad_sub, iteratedCovGrad_add, iteratedCovGrad_add]
        have h1 := norm_sub_le
          (iteratedCovGrad (I := I) g₀ 4 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA)) +
            iteratedCovGrad (I := I) g₀ 4 2 i
              (reindexCoeffGen (I := I) (M := M) g₀ 4 2
                (traceHessianCoeff (I := I) (M := M) g₀ g₁
                  - traceHessianCoeff (I := I) (M := M) g₀ g₀)
                (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT)))
          (iteratedCovGrad (I := I) g₀ 4 2 i
            (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
              - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀) +
           iteratedCovGrad (I := I) g₀ 4 2 i
            (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
              - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀))
        have h2 := norm_add_le
          (iteratedCovGrad (I := I) g₀ 4 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA)))
          (iteratedCovGrad (I := I) g₀ 4 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT)))
        have h3 := norm_add_le
          (iteratedCovGrad (I := I) g₀ 4 2 i
            (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
              - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀))
          (iteratedCovGrad (I := I) g₀ 4 2 i
            (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
              - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀))
        linarith
      have hsq : ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₁ -
            deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ^ 2 ≤
          3 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA))‖ ^ 2 +
          3 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT))‖ ^ 2 +
          12 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
              - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 := by
        exact sq_le_three_of_le_add_add_two
          (norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
            (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₁ -
              deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)))
          (norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA))))
          (norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT))))
          (norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
            (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
              - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀))) htri
      calc ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₁ -
              deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ^ 2
          ≤ 3 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (reindexCoeffGen (I := I) (M := M) g₀ 4 2
                (traceHessianCoeff (I := I) (M := M) g₀ g₁
                  - traceHessianCoeff (I := I) (M := M) g₀ g₀)
                (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA))‖ ^ 2 +
            3 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (reindexCoeffGen (I := I) (M := M) g₀ 4 2
                (traceHessianCoeff (I := I) (M := M) g₀ g₁
                  - traceHessianCoeff (I := I) (M := M) g₀ g₀)
                (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT))‖ ^ 2 +
            12 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
                - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 := hsq
        _ = 6 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 +
            12 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
                - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 := by
            rw [hreiA, hreiB]; ring
        _ ≤ (6 * Cth i + 12 * Cr i) * (∑ j ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 2 2 j
                (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2) := by
            exact six_twelve_mul_le hth hr
        _ ≤ (6 * Cth i + 12 * Cr i) * ((∑ j ∈ Finset.range (i + 1), (Klo j + Cg j * Kg j)) *
              (1 + ∑ l ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left hslotSum
              (add_nonneg (mul_nonneg (by norm_num) (hCth_nn i))
                (mul_nonneg (by norm_num) (hCr_nn i)))
        _ = KdevF i * (1 + ∑ l ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
            simp only [hKdevF_def]; ring
    have hbare : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedCovGrad (I := I) g₀ 4 2 i (Φ s)‖ ^ 2 ≤
        (2 * KdevF i + 2 * cB i) * (1 + ∑ l ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
      intro s hs
      have hsplit1 : ‖iteratedCovGrad (I := I) g₀ 4 2 i (Φ s)‖ ≤
          ‖iteratedCovGrad (I := I) g₀ 4 2 i (Φ s - Φbg)‖ +
            ‖iteratedCovGrad (I := I) g₀ 4 2 i Φbg‖ := by
        calc ‖iteratedCovGrad (I := I) g₀ 4 2 i (Φ s)‖
            = ‖iteratedCovGrad (I := I) g₀ 4 2 i ((Φ s - Φbg) + Φbg)‖ := by
                rw [sub_add_cancel]
          _ = ‖iteratedCovGrad (I := I) g₀ 4 2 i (Φ s - Φbg) +
                iteratedCovGrad (I := I) g₀ 4 2 i Φbg‖ := by rw [iteratedCovGrad_add]
          _ ≤ _ := norm_add_le _ _
      have hd := hdev s hs
      have hcBi : cB i = ‖iteratedCovGrad (I := I) g₀ 4 2 i
          Φbg‖ ^ 2 := rfl
      have hcmul : cB i * 1 ≤ cB i * (1 + ∑ l ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h1S_ge (hcB_nn i)
      have hb2 : ‖iteratedCovGrad (I := I) g₀ 4 2 i
          Φbg‖ ^ 2 ≤
          cB i * (1 + ∑ l ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
        rw [← hcBi]
        simpa only [mul_one] using hcmul
      have hsq := sq_le_two_bounds_of_le_add
        (norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i (Φ s)))
        (norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i (Φ s - Φbg)))
        (norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i Φbg))
        hsplit1 hd hb2
      calc ‖iteratedCovGrad (I := I) g₀ 4 2 i (Φ s)‖ ^ 2
          ≤ 2 * (KdevF i * (1 + ∑ l ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2)) +
            2 * (cB i * (1 + ∑ l ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2)) := hsq
        _ = (2 * KdevF i + 2 * cB i) * (1 + ∑ l ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by ring
    have hprod2_nn : (0 : ℝ) ≤ (2 * KdevF i + 2 * cB i) * (1 + ∑ l ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) :=
      mul_nonneg (by have := hKdevF_nn i; have := hcB_nn i; linarith) h1S_nn
    let B₂ : ℝ := Real.sqrt ((2 * KdevF i + 2 * cB i) *
      (1 + ∑ l ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2))
    have hB₂_sq : B₂ ^ 2 = (2 * KdevF i + 2 * cB i) *
        (1 + ∑ l ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
      change Real.sqrt ((2 * KdevF i + 2 * cB i) *
        (1 + ∑ l ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2)) ^ 2 = _
      exact Real.sq_sqrt hprod2_nn
    have hj2' : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 Φ
        (δ := δ) (δ' := δ) := by
      simpa only [Φ] using hj2
    have hΦjet : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedCovGrad (I := I) g₀ 4 2 i (Φ s)‖ ^ 2 ≤ B₂ ^ 2 := by
      intro s hs
      rw [hB₂_sq]
      exact hbare s hs
    have htower := armField_pathIntegral_jetL2_perOrder_le (I := I) (M := M) g₀ 4 Φ
      hSI hSopen hj2' i (B := B₂) (Real.sqrt_nonneg _) hΦjet
    rw [hB₂_sq] at htower
    have hPeq : deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
        (0 : SmoothCcTensor g₀ 0 2)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
          (by
            rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
              tensorHs_norm_smul]
            simpa using hR₀)) =
        pathIntegralCoeffField (I := I) (M := M) g₀ 4 2 Φ
          (realizedSmallSet (δ := δ) (δ' := δ)) hSopen hSI hj2 := rfl
    have htower' : ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
          (0 : SmoothCcTensor g₀ 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
            (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀)))‖ ^ 2 ≤
        (2 * KdevF i + 2 * cB i) * (1 + ∑ l ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
      rw [hPeq]; exact htower
    have hsplit : ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
            (0 : SmoothCcTensor g₀ 0 2)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
              (by
                rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                    from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                  tensorHs_norm_smul]
                simpa using hR₀)) -
          deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ^ 2 ≤
        2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
            (0 : SmoothCcTensor g₀ 0 2)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
              (by
                rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                    from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                  tensorHs_norm_smul]
                simpa using hR₀)))‖ ^ 2 +
        2 * cB i := by
      have h := norm_sub_le
        (iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
            (0 : SmoothCcTensor g₀ 0 2)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
              (by
                rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                    from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                  tensorHs_norm_smul]
                simpa using hR₀))))
        (iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀))
      rw [← iteratedCovGrad_sub] at h
      have hcBi : cB i = ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ^ 2 := rfl
      have hs := sq_le_two_bounds_of_le_add
        (norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
              (0 : SmoothCcTensor g₀ 0 2)
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
              (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                (by
                  rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                      from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                    tensorHs_norm_smul]
                  simpa using hR₀)) -
            deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)))
        (norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
            (0 : SmoothCcTensor g₀ 0 2)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
              (by
                rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                    from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                  tensorHs_norm_smul]
                simpa using hR₀)))))
        (norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀))) h (le_refl _) (le_refl _)
      rw [← hcBi] at hs
      exact hs
    have hcmul : cB i * 1 ≤ cB i * (1 + ∑ l ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h1S_ge (hcB_nn i)
    linear_combination hsplit + 2 * htower' + 2 * hcmul

theorem
    exists_deTurckPhiTotPathIntegral_sub_background_sub_principalCometricCoeff_coeffJetEnvelope_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2),
        (∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T₀ x v w = smoothCcTensorBilinForm (I := I) g₀ T₀ x w
            v) →
        ∀ (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
              (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
                  (0 : SmoothCcTensor g₀ 0 2)
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                  (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                    (by
                      rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                          from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                        tensorHs_norm_smul]
                      simpa using hR₀)) -
                deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ -
                deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
                  (tensorSectionRealizeMetric (I := I) g₀ T₀
                    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                    (hδ_fibre T₀ hball)))‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) := by
  classical
  obtain ⟨K1, hK1_nn, h1⟩ :=
    exists_deTurckPhiTotPathIntegral_sub_background_coeffJetEnvelope_le
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  obtain ⟨K2, hK2_nn, h2⟩ :=
    exists_deTurckPrincipalCometricCoeff_realize_coeffJetEnvelope_le
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  refine ⟨fun i => 2 * K1 i + 2 * K2 i,
    fun i => by have := hK1_nn i; have := hK2_nn i; linarith,
    fun T₀ hTsymm hball i => ?_⟩
  have hsub := iteratedCovGrad_sub (I := I) g₀ (2 + 2) 2 i
    (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
        (0 : SmoothCcTensor g₀ 0 2)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
          (by
            rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
              tensorHs_norm_smul]
            simpa using hR₀)) -
      deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)
    (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
      (tensorSectionRealizeMetric (I := I) g₀ T₀
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        (hδ_fibre T₀ hball)))
  rw [show (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
        (0 : SmoothCcTensor g₀ 0 2)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
          (by
            rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
              tensorHs_norm_smul]
            simpa using hR₀)) -
      deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ -
      deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
        (tensorSectionRealizeMetric (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre T₀ hball))) =
    (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
        (0 : SmoothCcTensor g₀ 0 2)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
          (by
            rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
              tensorHs_norm_smul]
            simpa using hR₀)) -
      deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀) -
      deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
        (tensorSectionRealizeMetric (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre T₀ hball)) from rfl, hsub]
  have hA := h1 T₀ hTsymm hball i
  have hB := h2 T₀ hTsymm hball i
  set nA := ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
    (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
        (0 : SmoothCcTensor g₀ 0 2)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
          (by
            rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
              tensorHs_norm_smul]
            simpa using hR₀)) -
      deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ with hnA
  set nB := ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
    (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
      (tensorSectionRealizeMetric (I := I) g₀ T₀
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        (hδ_fibre T₀ hball)))‖ with hnB
  have hnA_nn : 0 ≤ nA := by rw [hnA]; exact norm_nonneg _
  have hnB_nn : 0 ≤ nB := by rw [hnB]; exact norm_nonneg _
  have hn : ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
      (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
          (0 : SmoothCcTensor g₀ 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
            (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀)) -
        deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀) -
      iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
        (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
          (tensorSectionRealizeMetric (I := I) g₀ T₀
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre T₀ hball)))‖ ≤ nA + nB :=
    norm_sub_le _ _
  have hsq : ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
      (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
          (0 : SmoothCcTensor g₀ 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
            (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀)) -
        deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀) -
      iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
        (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
          (tensorSectionRealizeMetric (I := I) g₀ T₀
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre T₀ hball)))‖ ^ 2 ≤ 2 * nA ^ 2 + 2 * nB ^ 2 := by
    have hlhs_nn : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
        (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
            (0 : SmoothCcTensor g₀ 0 2)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
              (by
                rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                    from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                  tensorHs_norm_smul]
                simpa using hR₀)) -
          deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀) -
        iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
            (tensorSectionRealizeMetric (I := I) g₀ T₀
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
              (hδ_fibre T₀ hball)))‖ := norm_nonneg _
    nlinarith [sq_nonneg (nA - nB), mul_le_mul hn hn hlhs_nn (by linarith : (0:ℝ) ≤ nA + nB)]
  refine le_trans hsq ?_
  have hSig_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by positivity
  nlinarith [hA, hB, hSig_nn, hK1_nn i, hK2_nn i]

theorem
    exists_deTurckPhiTotPathIntegral_sub_bg_sub_principalCometricCoeff_fibreSmall_coeffJetEnvelope
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ εCD : ℝ, 0 ≤ εCD ∧
      (0 ≤ δ → εCD ≤ 3 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) ∧
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2),
        (∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T₀ x v w = smoothCcTensorBilinForm (I := I) g₀ T₀ x w
            v) →
        ∀ (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x
            ((deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
                  (0 : SmoothCcTensor g₀ 0 2)
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                  (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                    (by
                      rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                          from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                        tensorHs_norm_smul]
                      simpa using hR₀)) -
                deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ -
                deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
                  (tensorSectionRealizeMetric (I := I) g₀ T₀
                    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                    (hδ_fibre T₀ hball))).toSection x) ≤ εCD ^ 2) ∧
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
              (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
                  (0 : SmoothCcTensor g₀ 0 2)
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                  (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                    (by
                      rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                          from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                        tensorHs_norm_smul]
                      simpa using hR₀)) -
                deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ -
                deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
                  (tensorSectionRealizeMetric (I := I) g₀ T₀
                    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                    (hδ_fibre T₀ hball)))‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) := by
  classical
  obtain ⟨εCD, hεCD_nn, hεCD_cap, hsup⟩ :=
    exists_deTurckPhiTotPathIntegral_sub_background_sub_principalCometricCoeff_fibreSup_le
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  obtain ⟨Kc, hKc_nn, henv⟩ :=
    exists_deTurckPhiTotPathIntegral_sub_background_sub_principalCometricCoeff_coeffJetEnvelope_le
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  exact ⟨εCD, hεCD_nn, hεCD_cap, Kc, hKc_nn, fun T₀ hTsymm hball =>
    ⟨hsup T₀ hTsymm hball, henv T₀ hTsymm hball⟩⟩

theorem exists_deTurckSmoothRemainderDiff_sub_principalCometricArm_endpointResidual_coeffJetEnvelope
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ εCr : ℝ, 0 ≤ εCr ∧
      (0 ≤ δ → εCr ≤ 19 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) ∧
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
    ∃ εa : ℝ, 0 ≤ εa ∧
      2 * Real.sqrt (Module.finrank ℝ E) * εa ≤
        32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
          28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 ∧
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2),
        (∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T₀ x v w = smoothCcTensorBilinForm (I := I) g₀ T₀ x w
            v) →
        ∀ (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ∃ (C₀ : SmoothCcTensor g₀ (2 + 0) 2) (C₁ : SmoothCcTensor g₀ (2 + 1) 2)
          (C₂r : SmoothCcTensor g₀ (2 + 2) 2),
          (deTurckSmoothRemainder (I := I) g₀ g_bg T₀
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) -
              deTurckSmoothRemainder (I := I) g₀ g_bg
                (0 : SmoothCcTensor g₀ 0 2)
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                  (by
                    rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                        from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                      tensorHs_norm_smul]
                    simpa using hR₀)) -
              deTurckPrincipalCometricArm (I := I) (M := M) g₀
                (tensorSectionRealizeMetric (I := I) g₀ T₀
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                  (hδ_fibre T₀ hball)) T₀) =
            operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀
              (iteratedCovGrad (I := I) g₀ 0 2 0 T₀) +
              operatorFieldApply (I := I) (M := M) g₀ (2 + 1) 2 C₁
                (iteratedCovGrad (I := I) g₀ 0 2 1 T₀) +
              operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
                ((deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
                      (0 : SmoothCcTensor g₀ 0 2)
                      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
                      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                      (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                        (by
                          rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) •
                            (0 : SmoothCcTensor g₀ 0 2)
                              from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                            tensorHs_norm_smul]
                          simpa using hR₀)) -
                    deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ -
                    deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
                      (tensorSectionRealizeMetric (I := I) g₀ T₀
                        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                        (hδ_fibre T₀ hball))) + C₂r)
                (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x (C₂r.toSection x) ≤
              εCr ^ 2) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 0) 2 x (C₀.toSection x) ≤
              Λ ^ 2) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 1) 2 x (C₁.toSection x) ≤
              Λ ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
                εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 1) 2 i C₁‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂r‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) := by
  classical
  obtain ⟨εCr, hεCr_nn, hεCr_cap, Kc1, hKc1_nn, εar, hεar_nn, hεar_cap, Λ₁, hΛ₁_nn, harm⟩ :=
    exists_deTurckRHSArmDiff_zero_canonicalTop_curvatureRefold_coeffSup_jetEnvelope_of_symm
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  obtain ⟨K₀, hK₀fold⟩ :=
    exists_deTurckPhiMetTotal_background_curvatureFold_of_symm (I := I) (M := M) g₀ g_bg
  obtain ⟨ΛK, hΛK_nn, hΛK⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 2 K₀
  have hεa_cap : 2 * Real.sqrt (Module.finrank ℝ E) * ((3 : ℝ) / 2 * εar) ≤
      32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
        28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 := by
    calc 2 * Real.sqrt (Module.finrank ℝ E) * ((3 : ℝ) / 2 * εar)
        = 3 * Real.sqrt (Module.finrank ℝ E) * εar := by ring
      _ ≤ 32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
          28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 := hεar_cap
  refine ⟨εCr, hεCr_nn, hεCr_cap,
    fun i => 2 * Kc1 i + 2 * ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀‖ ^ 2,
    fun i => add_nonneg (mul_nonneg (by norm_num) (hKc1_nn i)) (by positivity),
    (3 : ℝ) / 2 * εar, by linarith, hεa_cap,
    Real.sqrt (2 * Λ₁ ^ 2 + 2 * ΛK) + Λ₁,
    add_nonneg (Real.sqrt_nonneg _) hΛ₁_nn,
    fun T₀ hTsymm hball => ?_⟩
  obtain ⟨C₀k, C₁k, C₂r, hidArm, hC₀sup, hC₁sup, hC₂rsup, hC₀env, hC₁env, hC₂renv⟩ :=
    harm T₀ hTsymm hball
  have hsqA : Real.sqrt (2 * Λ₁ ^ 2 + 2 * ΛK) ^ 2 = 2 * Λ₁ ^ 2 + 2 * ΛK :=
    Real.sq_sqrt (by nlinarith [hΛ₁_nn, hΛK_nn])
  refine ⟨C₀k + K₀, C₁k, C₂r, ?_, hC₂rsup, ?_, ?_, ?_, ?_, ?_⟩
  · have h884 := deTurckSmoothRemainderDiff_eq_armDiff_sub_connLapDiff (I := I) g₀ g_bg T₀
      (0 : SmoothCcTensor g₀ 0 2)
      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
      (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
        (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀))
    rw [sub_zero] at h884
    have hidArm' : deTurckRHSArmG0 (I := I) g₀ g_bg T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) -
        deTurckRHSArmG0 (I := I) g₀ g_bg (0 : SmoothCcTensor g₀ 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
            (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀)) =
        operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀k (iteratedCovGrad (I := I) g₀ 0 2 0 T₀)
          +
          operatorFieldApply (I := I) (M := M) g₀ (2 + 1) 2 C₁k
            (iteratedCovGrad (I := I) g₀ 0 2 1 T₀) +
          operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
            (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
              (0 : SmoothCcTensor g₀ 0 2)
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
              (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀)))
            (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) +
          operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂r
            (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) :=
      hidArm
    have hfold := hK₀fold T₀ hTsymm
    have hfold' : operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)
          (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) -
        operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
            (I := I) (M := M) g₀ g₀)
          (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) =
        operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 K₀
          (iteratedCovGrad (I := I) g₀ 0 2 0 T₀) := by
      rw [← appCc_sub_left]
      exact hfold
    have hlift : rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀ =
        operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
            (I := I) (M := M) g₀ g₀)
          (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) := by
      apply smoothCcTensor_ext_of_unitModel
      intro x
      apply ContinuousMultilinearMap.ext
      intro v
      exact
        rawTensorConnLapSmooth_eq_appCc_cometricDoubleTrace
          (I := I) (M := M) g₀ T₀ x v
    have hArm : deTurckPrincipalCometricArm (I := I) (M := M) g₀
        (tensorSectionRealizeMetric (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre T₀ hball)) T₀ =
        operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
            (tensorSectionRealizeMetric (I := I) g₀ T₀
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
              (hδ_fibre T₀ hball)))
          (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) := rfl
    have hPCC : deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
        (tensorSectionRealizeMetric (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre T₀ hball)) =
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
          (I := I) (M := M) g₀
          (tensorSectionRealizeMetric (I := I) g₀ T₀
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre T₀ hball)) -
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
          (I := I) (M := M) g₀ g₀ := rfl
    rw [h884, hlift, hArm, hidArm']
    rw [appCc_add_left (I := I) (M := M) g₀ (2 + 0) 2 C₀k K₀
      (iteratedCovGrad (I := I) g₀ 0 2 0 T₀)]
    rw [appCc_add_left (I := I) (M := M) g₀ (2 + 2) 2 _ C₂r
      (iteratedCovGrad (I := I) g₀ 0 2 2 T₀)]
    rw [show (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
          (0 : SmoothCcTensor g₀ 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
            (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀)) -
        deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ -
        deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
          (tensorSectionRealizeMetric (I := I) g₀ T₀
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre T₀ hball))) =
      (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
          (0 : SmoothCcTensor g₀ 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
            (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀)) -
        deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀) -
      deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
        (tensorSectionRealizeMetric (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre T₀ hball)) from rfl]
    rw [appCc_sub_left (I := I) (M := M) g₀ (2 + 2) 2 _
      (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
        (tensorSectionRealizeMetric (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre T₀ hball)))
      (iteratedCovGrad (I := I) g₀ 0 2 2 T₀)]
    rw [appCc_sub_left (I := I) (M := M) g₀ (2 + 2) 2 _
      (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)
      (iteratedCovGrad (I := I) g₀ 0 2 2 T₀)]
    rw [hPCC]
    rw [appCc_sub_left (I := I) (M := M) g₀ (2 + 2) 2 _
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
        (I := I) (M := M) g₀ g₀)
      (iteratedCovGrad (I := I) g₀ 0 2 2 T₀)]
    rw [← hfold']
    abel
  · intro x
    have hsec : ((C₀k + K₀).toSection x) = C₀k.toSection x + K₀.toSection x := by
      rw [SmoothCcTensor.toSection_add]; rfl
    rw [hsec]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ (2 + 0) 2 x _ _) ?_
    have h1 := hC₀sup x
    have h2 := hΛK x
    nlinarith [Real.sqrt_nonneg (2 * Λ₁ ^ 2 + 2 * ΛK), hΛ₁_nn, hsqA]
  · intro x
    have h1 := hC₁sup x
    have hle : Λ₁ ≤ Real.sqrt (2 * Λ₁ ^ 2 + 2 * ΛK) + Λ₁ :=
      le_add_of_nonneg_left (Real.sqrt_nonneg _)
    have := pow_le_pow_left₀ hΛ₁_nn hle 2
    linarith
  · intro i
    have hdist := iteratedCovGrad_add (I := I) g₀ (2 + 0) 2 i C₀k K₀
    rw [hdist]
    have htri : ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀k +
          iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀‖ ^ 2 ≤
        2 * ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀k‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀‖ ^ 2 :=
      norm_add_sq_le_two _ _
    refine le_trans htri ?_
    have hD := hC₀env i
    have hSig_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 :=
      Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have hKW : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀‖ ^ 2 *
        (∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) :=
      mul_nonneg (sq_nonneg _) hSig_nn
    have hεX : (0 : ℝ) ≤ εar ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    linear_combination 2 * hD + 2 * hKW + (1 / 4 : ℝ) * hεX
  · intro i
    refine le_trans (hC₁env i) ?_
    have hSig_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by
      have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (i + 2)) =>
        sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖)
      linarith
    refine mul_le_mul_of_nonneg_right ?_ hSig_nn
    have h1 := hKc1_nn i
    have h2 : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀‖ ^ 2 := sq_nonneg _
    linarith
  · intro i
    refine le_trans (hC₂renv i) ?_
    have hSig_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by
      have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (i + 2)) =>
        sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖)
      linarith
    refine mul_le_mul_of_nonneg_right ?_ hSig_nn
    have h1 := hKc1_nn i
    have h2 : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀‖ ^ 2 := sq_nonneg _
    linarith

theorem
    exists_deTurckSmoothRemainderDiff_sub_principalCometricArm_threeArmCoeffAction_coeffJetEnvelope
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ εC : ℝ, 0 ≤ εC ∧
      (0 ≤ δ → εC ≤ 32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 * (δ / (1 - δ))) ∧
      (0 ≤ δ → εC ≤ 28 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) ∧
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
    ∃ εa : ℝ, 0 ≤ εa ∧
      2 * Real.sqrt (Module.finrank ℝ E) * εa ≤
        32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
          28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 ∧
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2),
        (∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T₀ x v w = smoothCcTensorBilinForm (I := I) g₀ T₀ x w
            v) →
        ∀ (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ∃ (C₀ : SmoothCcTensor g₀ (2 + 0) 2) (C₁ : SmoothCcTensor g₀ (2 + 1) 2)
          (C₂ : SmoothCcTensor g₀ (2 + 2) 2),
          (deTurckSmoothRemainder (I := I) g₀ g_bg T₀
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) -
              deTurckSmoothRemainder (I := I) g₀ g_bg
                (0 : SmoothCcTensor g₀ 0 2)
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                  (by
                    rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                        from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                      tensorHs_norm_smul]
                    simpa using hR₀)) -
              deTurckPrincipalCometricArm (I := I) (M := M) g₀
                (tensorSectionRealizeMetric (I := I) g₀ T₀
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                  (hδ_fibre T₀ hball)) T₀) =
            operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀
              (iteratedCovGrad (I := I) g₀ 0 2 0 T₀) +
              operatorFieldApply (I := I) (M := M) g₀ (2 + 1) 2 C₁
                (iteratedCovGrad (I := I) g₀ 0 2 1 T₀) +
              operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
                (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x (C₂.toSection x) ≤
              εC ^ 2) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 0) 2 x (C₀.toSection x) ≤
              Λ ^ 2) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 1) 2 x (C₁.toSection x) ≤
              Λ ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
                εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 1) 2 i C₁‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) := by
  classical
  obtain ⟨εCD, hεCD_nn, hεCD_cap, KcD, hKcD_nn, hK2⟩ :=
    exists_deTurckPhiTotPathIntegral_sub_bg_sub_principalCometricCoeff_fibreSmall_coeffJetEnvelope
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  obtain ⟨εCr, hεCr_nn, hεCr_cap, Kc1, hKc1_nn, εa, hεa_nn, hεa_cap, Λ1, hΛ1_nn, hK1⟩ :=
    exists_deTurckSmoothRemainderDiff_sub_principalCometricArm_endpointResidual_coeffJetEnvelope
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  have hn1 : 1 ≤ Module.finrank ℝ E :=
    Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Module.finrank ℝ E))
  have hC1 : (1 : ℝ) ≤ deTurckArmFibreConst (Module.finrank ℝ E) :=
    one_le_deTurckArmFibreConst hn1
  refine ⟨Real.sqrt (2 * εCD ^ 2 + 2 * εCr ^ 2), Real.sqrt_nonneg _,
    fun hδ_nn => ?_, fun hδ_nn => ?_,
    fun i => 3 * Kc1 i + 2 * KcD i,
    fun i => by have := hKc1_nn i; have := hKcD_nn i; linarith,
    εa, hεa_nn, hεa_cap,
    Λ1, hΛ1_nn, fun T₀ hTsymm hball => ?_⟩
  · have hδ_lt1 : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
    have hκ_nn : 0 ≤ δ / (1 - δ) := div_nonneg hδ_nn (by linarith)
    set C : ℝ := deTurckArmFibreConst (Module.finrank ℝ E) with hC_def
    set κ : ℝ := δ / (1 - δ) with hκ_def
    have hd := hεCD_cap hδ_nn
    have hr := hεCr_cap hδ_nn
    have hsq : (2 * εCD ^ 2 + 2 * εCr ^ 2) ≤ (32 * C ^ 2 * κ) ^ 2 := by
      have hεCD_sq : εCD ^ 2 ≤ (3 * C * κ) ^ 2 := by nlinarith
      have hεCr_sq : εCr ^ 2 ≤ (19 * C * κ) ^ 2 := by nlinarith
      have hC2 : (1 : ℝ) ≤ C ^ 2 := by nlinarith
      nlinarith [sq_nonneg (C * κ), sq_nonneg κ]
    calc Real.sqrt (2 * εCD ^ 2 + 2 * εCr ^ 2)
        ≤ Real.sqrt ((32 * C ^ 2 * κ) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = 32 * C ^ 2 * κ := Real.sqrt_sq (by positivity)
      _ = 32 * C ^ 2 * (δ / (1 - δ)) := by rw [hκ_def]
  · have hδ_lt1 : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
    have hκ_nn : 0 ≤ δ / (1 - δ) := div_nonneg hδ_nn (by linarith)
    have hC_nn : 0 ≤ deTurckArmFibreConst (Module.finrank ℝ E) :=
      deTurckArmFibreConst_nonneg _
    have hd := hεCD_cap hδ_nn
    have hr := hεCr_cap hδ_nn
    have h28_nn : (0 : ℝ) ≤
        28 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) := by positivity
    have hsq : 2 * εCD ^ 2 + 2 * εCr ^ 2 ≤
        (28 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) ^ 2 := by
      nlinarith [hd, hr, hεCD_nn, hεCr_nn, mul_nonneg hC_nn hκ_nn]
    calc Real.sqrt (2 * εCD ^ 2 + 2 * εCr ^ 2)
        ≤ Real.sqrt ((28 * deTurckArmFibreConst (Module.finrank ℝ E) *
            (δ / (1 - δ))) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = 28 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) :=
          Real.sqrt_sq h28_nn
  obtain ⟨hDsup, hDenv⟩ := hK2 T₀ hTsymm hball
  obtain ⟨C₀, C₁, C₂r, hid, hC₂r_sup, hC₀sup, hC₁sup, hC₀env, hC₁env, hC₂r_env⟩ :=
    hK1 T₀ hTsymm hball
  have hεC_sq : Real.sqrt (2 * εCD ^ 2 + 2 * εCr ^ 2) ^ 2 =
      2 * εCD ^ 2 + 2 * εCr ^ 2 := Real.sq_sqrt (by positivity)
  refine ⟨C₀, C₁,
    (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
        (0 : SmoothCcTensor g₀ 0 2)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
          (by
            rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
              tensorHs_norm_smul]
            simpa using hR₀)) -
      deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ -
      deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
        (tensorSectionRealizeMetric (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre T₀ hball))) + C₂r,
    hid, ?_, hC₀sup, hC₁sup, ?_, ?_, ?_⟩
  · intro x
    rw [hεC_sq]
    have hsec : ((deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
          (0 : SmoothCcTensor g₀ 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
            (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀)) -
        deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ -
        deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
          (tensorSectionRealizeMetric (I := I) g₀ T₀
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre T₀ hball))) + C₂r).toSection x =
        (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
          (0 : SmoothCcTensor g₀ 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
            (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀)) -
        deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ -
        deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
          (tensorSectionRealizeMetric (I := I) g₀ T₀
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre T₀ hball))).toSection x + C₂r.toSection x := by
      rw [SmoothCcTensor.toSection_add]; rfl
    rw [hsec]
    refine le_trans
      (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ (2 + 2) 2 x _ _) ?_
    have h1 := hDsup x
    have h2 := hC₂r_sup x
    linarith
  · intro i
    refine le_trans (hC₀env i) ?_
    have hSig_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by
      have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (i + 2)) =>
        sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖)
      linarith
    have hmono : Kc1 i * (1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) ≤
        (3 * Kc1 i + 2 * KcD i) * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) := by
      refine mul_le_mul_of_nonneg_right ?_ hSig_nn
      have := hKc1_nn i; have := hKcD_nn i
      linarith
    linarith
  · intro i
    refine le_trans (hC₁env i) ?_
    have hSig_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by
      have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (i + 2)) =>
        sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖)
      linarith
    refine mul_le_mul_of_nonneg_right ?_ hSig_nn
    have := hKc1_nn i; have := hKcD_nn i
    linarith
  · intro i
    have hdist := iteratedCovGrad_add (I := I) g₀ (2 + 2) 2 i
      (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
          (0 : SmoothCcTensor g₀ 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
            (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀)) -
        deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ -
        deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
          (tensorSectionRealizeMetric (I := I) g₀ T₀
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre T₀ hball)))
      C₂r
    rw [hdist]
    refine le_trans (norm_add_sq_le_two _ _) ?_
    have hD := hDenv i
    have hr := hC₂r_env i
    have hSig_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by
      have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (i + 2)) =>
        sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖)
      linarith
    have hKc1i := hKc1_nn i
    have hextra := mul_nonneg hKc1i hSig_nn
    linear_combination 2 * hD + 2 * hr + hextra

end Spectral
end Analysis
end DifferentialGeometry

end

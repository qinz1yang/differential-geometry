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
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseToL2Packaging
import DifferentialGeometry.Geometry.Connection.TensorNabla.HomFieldActionIteratedCovGradWindow
import DifferentialGeometry.Analysis.Integration.L2.FiniteProductHolderFiberNorm
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricPathResolventFactorization
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.IntegratedOrder2WeitzenbockRS
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseTensorCurvatureRS
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.HomFieldCurvatureJetDecomposition

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

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
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
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

theorem exists_appCc_iteratedCovGrad_l2_dataJetWindow_le
    (g₀ : SmoothRiemannianMetric I M) (m : ℕ) :
    ∃ Cgrid : ℕ → ℝ, (∀ q, 0 ≤ Cgrid q) ∧
      ∀ (q : ℕ) (C : SmoothCcTensor g₀ (2 + m) 2) (Kc : ℝ) (T₀ : SmoothCcTensor g₀ 0 2),
        0 ≤ Kc →
        (∀ (i : ℕ), i ≤ q → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) (2 + i) x
            ((iteratedCovGrad (I := I) g₀ (2 + m) 2 i C).toSection x) ≤ Kc ^ 2) →
        ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (appCc (I := I) (M := M) g₀ (2 + m) 2 C
              (iteratedCovGrad (I := I) g₀ 0 2 m T₀))‖ ≤
          Cgrid q * Kc * Real.sqrt (∑ i ∈ Finset.range (q + m + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
  classical
  refine ⟨fun q => Real.sqrt (appCcGdiag (E := E) q * ((q : ℝ) + 1)) *
      Real.sqrt ((q + m + 1 : ℕ) : ℝ),
    fun q => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
    fun q C Kc T₀ hKc hjet => ?_⟩
  have hG_nn : 0 ≤ appCcGdiag (E := E) q := appCcGdiag_nonneg (E := E) q
  have hGq_nn : 0 ≤ appCcGdiag (E := E) q * ((q : ℝ) + 1) :=
    mul_nonneg hG_nn (by positivity)
  set Cpk : ℝ := Kc * Real.sqrt (appCcGdiag (E := E) q * ((q : ℝ) + 1)) with hCpk_def
  have hCpk_nn : 0 ≤ Cpk := mul_nonneg hKc (Real.sqrt_nonneg _)
  have hCpksq : Cpk ^ 2 = Kc ^ 2 * (appCcGdiag (E := E) q * ((q : ℝ) + 1)) := by
    rw [hCpk_def, mul_pow, Real.sq_sqrt hGq_nn]
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
          ((iteratedCovGrad (I := I) g₀ 0 2 q
            (appCc (I := I) (M := M) g₀ (2 + m) 2 C
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
          rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 m l T₀ x)]
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
      (appCc_iteratedCovGrad_diagonalProductGrid_le (I := I) (M := M) g₀ (2 + m) 2 C
        (iteratedCovGrad (I := I) g₀ 0 2 m T₀) q x) ?_
    refine le_trans (mul_le_mul_of_nonneg_left hmono hG_nn) ?_
    rw [hCpksq]
    apply le_of_eq; ring
  have hpack := tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum (I := I) (M := M) g₀
    (q + m + 1) (fun i => 2 + i) (fun i => iteratedCovGrad (I := I) g₀ 0 2 i T₀)
    (iteratedCovGrad (I := I) g₀ 0 2 q
      (appCc (I := I) (M := M) g₀ (2 + m) 2 C (iteratedCovGrad (I := I) g₀ 0 2 m T₀)))
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
    (hδ_le : δ ≤ deTurckArmContractionThreshold'' n) :
    32 * deTurckArmFibreConst n ^ 3 * (δ / (1 - δ)) ≤
      32 * deTurckArmFibreConst n ^ 2 / (2 * (1 + 32 * deTurckArmFibreConst n ^ 2)) := by
  have hC := one_le_deTurckArmFibreConst hn
  set C := deTurckArmFibreConst n with hC_def
  set K : ℝ := C + 32 * C ^ 3 with hK_def
  have hC3_nn : (0 : ℝ) ≤ C ^ 3 := by positivity
  have hK1 : 1 ≤ K := by rw [hK_def]; nlinarith
  have hden : (0 : ℝ) < 1 + 2 * K := by linarith
  have hthr_lt : deTurckArmContractionThreshold'' n < 1 :=
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

section

open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma kscr_g1_inner_injective (g₁ : SmoothRiemannianMetric I M) (x : M)
    {a b : TangentSpace I x} (hab : ∀ u : TangentSpace I x, g₁.inner x a u = g₁.inner x b u) :
    a = b := by
  by_contra hne
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hpos := g₁.pos x (a - b) hsub
  have hzero : g₁.inner x (a - b) (a - b) = 0 := by
    have hsplit : g₁.inner x (a - b) (a - b)
        = g₁.inner x (a - b) a - g₁.inner x (a - b) b := by rw [← map_sub]
    rw [hsplit, g₁.symm x (a - b) a, g₁.symm x (a - b) b, hab (a - b)]
    ring
  exact absurd hzero (ne_of_gt hpos)

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma kscr_cometricLmodel_covectorOfCLM_inner_loc
    (g₁ : SmoothRiemannianMetric I M) (y : M)
    (φ : E →L[ℝ] ℝ) (u : TangentSpace I y) :
    g₁.inner y (cometricLmodel (I := I) g₁ y
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ)) u = φ (u : E) := by
  have h1 : cometricLmodel (I := I) g₁ y
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ) =
      inverseMetricSharpFib (I := I) g₁ y
        ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 y).symm
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ)) := rfl
  rw [h1, inverseMetricSharpFib_inner (I := I) g₁ y _ u, cotangentToDualLinear_apply,
    cotangentToDual_apply]
  change (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ)
      (fun _ : Fin 1 => (u : E)) = φ (u : E)
  rw [Tensor0SBundle.model_covectorOfCLM_apply]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma kscr_cometricLmodel_covOf_g0flat_eq (g₀ : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    cometricLmodel (I := I) g₀ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((g₀.inner x v).toLinearMap.toContinuousLinearMap)) = v := by
  apply kscr_g1_inner_injective (I := I) g₀ x
  intro u
  rw [kscr_cometricLmodel_covectorOfCLM_inner_loc (I := I) g₀ x
    ((g₀.inner x v).toLinearMap.toContinuousLinearMap) u]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma kscr_flatRecon_eq_basisVec (g₀ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (b : Fin n) :
    ∑ k : Fin (Module.finrank ℝ E),
        (g₀.inner x (e b) ((Module.finBasis ℝ E) k) : ℝ) •
          cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)) = e b := by
  classical
  have hsmul : ∀ k : Fin (Module.finrank ℝ E),
      (g₀.inner x (e b) ((Module.finBasis ℝ E) k) : ℝ) •
          cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k))
        = cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((g₀.inner x (e b) ((Module.finBasis ℝ E) k) : ℝ) •
                ((Module.finBasis ℝ E).cDualBasis k))) := by
    intro k
    rw [map_smul, map_smul]
  rw [Finset.sum_congr rfl (fun k _ => hsmul k)]
  rw [← map_sum, ← map_sum]
  have hcoe : ∀ k : Fin (Module.finrank ℝ E),
      ((Module.finBasis ℝ E).cDualBasis k)
        = LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord k) := by
    intro k
    rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
    congr 1
    exact congrFun (Module.Basis.coe_dualBasis (Module.finBasis ℝ E)) k
  have hsum : (∑ k : Fin (Module.finrank ℝ E),
        (g₀.inner x (e b) ((Module.finBasis ℝ E) k) : ℝ) •
          ((Module.finBasis ℝ E).cDualBasis k))
      = (g₀.inner x (e b)).toLinearMap.toContinuousLinearMap := by
    have hrepr := cdual_sum_repr (Module.finBasis ℝ E)
      ((g₀.inner x (e b)).toLinearMap.toContinuousLinearMap)
    refine Eq.trans ?_ hrepr
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hcoe k]
    congr 1
  rw [hsum]
  exact kscr_cometricLmodel_covOf_g0flat_eq (I := I) g₀ x (e b)

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma kscr_deTurckCoeff_toModel_eq (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (w : Tensor0SSpace 4 I x) (m : Fin 2 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁).toSection x) w) m =
      ∑ k : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel w)
          (Fin.cons
            ((gInvDiffRaisedEndo (I := I) g₀ g₁ x
              (cometricLmodel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))) : TangentSpace I x) : E)
            (Fin.cons (((Module.finBasis ℝ E) k : E)) m)) := by
  classical
  rw [deTurckPrincipalCometricCoeff_toSection_clm_eq (I := I) (M := M) g₀ g₁ x,
    ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
    ContinuousMultilinearMap.sub_apply,
    cometricDoubleTraceFib_toModel, cometricDoubleTraceFib_toModel,
    modelDoubleTrace_apply, modelDoubleTrace_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  set wm : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ := Tensor0SSpace.toModel w with hwm
  set tail : Fin 3 → E := Fin.cons (((Module.finBasis ℝ E) k : E)) m with htail
  have hcurry : ∀ z : TangentSpace I x,
      wm (Fin.cons ((z : E)) tail)
        = ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 4 => E) ℝ) wm
            ((z : TangentSpace I x) : E)) tail := by
    intro z; rw [continuousMultilinearCurryLeftEquiv_apply]
  rw [hcurry (cometricLmodel (I := I) g₁ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))),
    hcurry (cometricLmodel (I := I) g₀ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))),
    hcurry (gInvDiffRaisedEndo (I := I) g₀ g₁ x
        (cometricLmodel (I := I) g₀ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k))))]
  rw [← ContinuousMultilinearMap.sub_apply, ← map_sub]
  congr 2
  rw [cometricLmodel_sub_eq_gInvDiffRaisedEndo (I := I) g₀ g₁ x
    ((Module.finBasis ℝ E).cDualBasis k)]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma kscr_deTurckCoeff_component_eq (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K : Fin 4 → Fin n) (J : Fin 2 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
        (show TensorRSSpace 4 2 I x from
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁).toSection x) n e K J =
      g₀.inner x (e (K 0)) (gInvDiffRaisedEndo (I := I) g₀ g₁ x (e (K 1))) *
        ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0)) := by
  classical
  have hcomp : fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
        (show TensorRSSpace 4 2 I x from
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁).toSection x) n e K J =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁).toSection x)
          (coframeS (I := I) (M := M) g₀ x 4 e K))
        (fun k => ((e (J k) : TangentSpace I x) : E)) := rfl
  rw [hcomp, kscr_deTurckCoeff_toModel_eq (I := I) (M := M) g₀ g₁ x
    (coframeS (I := I) (M := M) g₀ x 4 e K) (fun k => ((e (J k) : TangentSpace I x) : E))]
  set Rk : Fin (Module.finrank ℝ E) → TangentSpace I x := fun k =>
    cometricLmodel (I := I) g₀ x
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis k)) with hRk
  set Λ : TangentSpace I x →L[ℝ] TangentSpace I x :=
    gInvDiffRaisedEndo (I := I) g₀ g₁ x with hΛ
  have hk : ∀ k : Fin (Module.finrank ℝ E),
      (Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 4 e K))
          (Fin.cons ((Λ (Rk k) : TangentSpace I x) : E)
            (Fin.cons (((Module.finBasis ℝ E) k : E))
              (fun j => ((e (J j) : TangentSpace I x) : E))))
        = g₀.inner x (e (K 0)) (Λ (Rk k))
          * g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k)
          * ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0)) := by
    intro k
    have hcf : (Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 4 e K))
          (Fin.cons ((Λ (Rk k) : TangentSpace I x) : E)
            (Fin.cons (((Module.finBasis ℝ E) k : E))
              (fun j => ((e (J j) : TangentSpace I x) : E))))
        = coframeS (I := I) (M := M) g₀ x 4 e K
            (Fin.cons ((Λ (Rk k)) : TangentSpace I x)
              (Fin.cons (((Module.finBasis ℝ E) k : TangentSpace I x))
                (fun j => (e (J j) : TangentSpace I x)))) := rfl
    rw [hcf, coframeS_apply, Fin.prod_univ_four]
    change g₀.inner x (e (K 0)) (Λ (Rk k))
          * g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k)
          * g₀.inner x (e (K 2)) (e (J 0))
          * g₀.inner x (e (K 3)) (e (J 1))
        = _
    rw [horth (K 2) (J 0), horth (K 3) (J 1)]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hk k)]
  rw [← Finset.sum_mul]
  congr 1
  have hpull : g₀.inner x (e (K 0)) (Λ
          (∑ k : Fin (Module.finrank ℝ E),
            (g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k) : ℝ) • Rk k))
      = ∑ k : Fin (Module.finrank ℝ E),
          g₀.inner x (e (K 0)) (Λ (Rk k)) * g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k) := by
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_smul, ContinuousLinearMap.map_smul, smul_eq_mul]
    ring
  rw [← hpull, kscr_flatRecon_eq_basisVec (I := I) g₀ x e (K 1)]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma kscr_sum_pi_fin_succ {n : ℕ} {β : Type*} [AddCommMonoid β]
    {N : ℕ} (g : (Fin (N + 1) → Fin n) → β) :
    (∑ p : Fin (N + 1) → Fin n, g p)
      = ∑ a : Fin n, ∑ q : Fin N → Fin n, g (Fin.cons a q) := by
  classical
  rw [← (Fin.consEquiv (fun _ : Fin (N + 1) => Fin n)).sum_comp g]
  rw [Fintype.sum_prod_type]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma kscr_deTurckCoeff_componentSqSum_eq (n : ℕ) (f : Fin n → Fin n → ℝ) :
    (∑ K : Fin 4 → Fin n, ∑ J : Fin 2 → Fin n,
      (f (K 0) (K 1) *
        ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0))) ^ 2)
      = (n : ℝ) ^ 2 * ∑ a : Fin n, ∑ b : Fin n, (f a b) ^ 2 := by
  classical
  have hJcollapse : ∀ K : Fin 4 → Fin n,
      (∑ J : Fin 2 → Fin n,
        (f (K 0) (K 1) *
          ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0))) ^ 2)
        = (f (K 0) (K 1)) ^ 2 := by
    intro K
    have hsplit : ∀ J : Fin 2 → Fin n,
        (f (K 0) (K 1) *
          ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0))) ^ 2
          = (f (K 0) (K 1)) ^ 2 *
              ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0)) := by
      intro J
      by_cases h2 : K 2 = J 0 <;> by_cases h3 : K 3 = J 1 <;>
        simp [h2, h3]
    rw [Finset.sum_congr rfl (fun J _ => hsplit J), ← Finset.mul_sum]
    rw [kscr_sum_pi_fin_succ (fun J : Fin 2 → Fin n =>
      (if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0))]
    have hinner : ∀ a : Fin n, (∑ q : Fin 1 → Fin n,
        (if K 2 = (Fin.cons a q : Fin 2 → Fin n) 0 then (1 : ℝ) else 0) *
          (if K 3 = (Fin.cons a q : Fin 2 → Fin n) 1 then (1 : ℝ) else 0))
        = (if K 2 = a then (1 : ℝ) else 0) := by
      intro a
      rw [kscr_sum_pi_fin_succ (fun q : Fin 1 → Fin n =>
        (if K 2 = (Fin.cons a q : Fin 2 → Fin n) 0 then (1 : ℝ) else 0) *
          (if K 3 = (Fin.cons a q : Fin 2 → Fin n) 1 then (1 : ℝ) else 0))]
      have hb : ∀ b : Fin n, (∑ _r : Fin 0 → Fin n,
          (if K 2 = (Fin.cons a (Fin.cons b (_r : Fin 0 → Fin n)) : Fin 2 → Fin n) 0
            then (1 : ℝ) else 0) *
            (if K 3 = (Fin.cons a (Fin.cons b (_r : Fin 0 → Fin n)) : Fin 2 → Fin n) 1
              then (1 : ℝ) else 0))
          = (if K 2 = a then (1 : ℝ) else 0) * (if K 3 = b then (1 : ℝ) else 0) := by
        intro b
        have hbody : ∀ r : Fin 0 → Fin n,
            (if K 2 = (Fin.cons a (Fin.cons b r) : Fin 2 → Fin n) 0 then (1 : ℝ) else 0) *
              (if K 3 = (Fin.cons a (Fin.cons b r) : Fin 2 → Fin n) 1 then (1 : ℝ) else 0)
            = (if K 2 = a then (1 : ℝ) else 0) * (if K 3 = b then (1 : ℝ) else 0) := by
          intro r
          rw [show (Fin.cons a (Fin.cons b r) : Fin 2 → Fin n) 0 = a from rfl,
            show (Fin.cons a (Fin.cons b r) : Fin 2 → Fin n) 1 = b from rfl]
        rw [Finset.sum_congr rfl (fun r _ => hbody r), Finset.sum_const, Finset.card_univ]
        simp only [Fintype.card_fun, Fintype.card_fin, pow_zero, one_smul]
      rw [Finset.sum_congr rfl (fun b _ => hb b), ← Finset.mul_sum]
      rw [Finset.sum_ite_eq Finset.univ (K 3) (fun _ => (1 : ℝ))]
      simp
    rw [Finset.sum_congr rfl (fun a _ => hinner a)]
    rw [Finset.sum_ite_eq Finset.univ (K 2) (fun _ => (1 : ℝ))]
    simp
  rw [Finset.sum_congr rfl (fun K _ => hJcollapse K)]
  rw [kscr_sum_pi_fin_succ (fun K : Fin 4 → Fin n => (f (K 0) (K 1)) ^ 2)]
  have hstep : ∀ a : Fin n, (∑ q : Fin 3 → Fin n,
      (f ((Fin.cons a q : Fin 4 → Fin n) 0) ((Fin.cons a q : Fin 4 → Fin n) 1)) ^ 2)
      = (n : ℝ) ^ 2 * ∑ b : Fin n, (f a b) ^ 2 := by
    intro a
    rw [kscr_sum_pi_fin_succ (fun q : Fin 3 → Fin n =>
      (f ((Fin.cons a q : Fin 4 → Fin n) 0) ((Fin.cons a q : Fin 4 → Fin n) 1)) ^ 2)]
    have hb : ∀ b : Fin n, (∑ r : Fin 2 → Fin n,
        (f ((Fin.cons a (Fin.cons b r) : Fin 4 → Fin n) 0)
          ((Fin.cons a (Fin.cons b r) : Fin 4 → Fin n) 1)) ^ 2)
        = (n : ℝ) ^ 2 * (f a b) ^ 2 := by
      intro b
      have hval : ∀ r : Fin 2 → Fin n,
          (f ((Fin.cons a (Fin.cons b r) : Fin 4 → Fin n) 0)
            ((Fin.cons a (Fin.cons b r) : Fin 4 → Fin n) 1)) ^ 2 = (f a b) ^ 2 := by
        intro r
        rw [show (Fin.cons a (Fin.cons b r) : Fin 4 → Fin n) 0 = a from rfl,
          show (Fin.cons a (Fin.cons b r) : Fin 4 → Fin n) 1 = b from rfl]
      rw [Finset.sum_congr rfl (fun r _ => hval r), Finset.sum_const, Finset.card_univ]
      simp only [Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    rw [Finset.sum_congr rfl (fun b _ => hb b), ← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun a _ => hstep a), ← Finset.mul_sum]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in

private lemma kscr_rfns_pcc_deviation_le (g₀ ga gb : SmoothRiemannianMetric I M)
    (ha hb : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie_a : ∀ (y : M) (v w : TangentSpace I y),
      ga.inner y v w = g₀.inner y v w + ha y v w)
    (htie_b : ∀ (y : M) (v w : TangentSpace I y),
      gb.inner y v w = g₀.inner y v w + hb y v w)
    {δa δb δab : ℝ} (hδa_lt : δa < 1)
    (hδa : gFibreOpBound (I := I) (M := M) g₀ ha δa)
    (hδb_lt : δb < 1) (hδb_nn : 0 ≤ δb)
    (hδb : gFibreOpBound (I := I) (M := M) g₀ hb δb)
    (hδab_nn : 0 ≤ δab)
    (hδab : gFibreOpBound (I := I) (M := M) g₀ (fun y => ha y - hb y) δab)
    (hδa_nn : 0 ≤ δa)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ ga
          - deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ gb).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 3 * (δab / ((1 - δa) * (1 - δb))) ^ 2 := by
  classical
  set Λ : TangentSpace I x →L[ℝ] TangentSpace I x :=
    gInvDiffRaisedEndo (I := I) g₀ ga x - gInvDiffRaisedEndo (I := I) g₀ gb x with hΛ
  obtain ⟨n, e, hn, horth, hpar, hrepr⟩ :=
    exists_orthonormal_frame_riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
  have hnE : (n : ℝ) = (Module.finrank ℝ E : ℝ) := by rw [hn]; rfl
  have hsec : (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ ga
        - deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ gb).toSection x =
      (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ ga).toSection x
        - (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ gb).toSection x := by
    rw [SmoothCcTensor.toSection_sub]; rfl
  rw [hsec]
  rw [riemannianFiberNormSq_eq_sum_componentRS_sq (I := I) (M := M) g₀ x 4 2 e hrepr
    (show TensorRSSpace 4 2 I x from
      (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ ga).toSection x
        - (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ gb).toSection x)]
  have hcompsub : ∀ (K : Fin 4 → Fin n) (J : Fin 2 → Fin n),
      fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
          (show TensorRSSpace 4 2 I x from
            (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ ga).toSection x
              - (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ gb).toSection x) n e K J =
        fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
          (show TensorRSSpace 4 2 I x from
            (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ ga).toSection x) n e K J
        - fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
          (show TensorRSSpace 4 2 I x from
            (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ gb).toSection x) n e K J := by
    intro K J
    rw [show ((deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ ga).toSection x
          - (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ gb).toSection x :
            TensorRSSpace 4 2 I x)
        = (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ ga).toSection x
          + (-1 : ℝ) • (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ gb).toSection x from
      by rw [neg_one_smul]; exact sub_eq_add_neg _ _]
    rw [fiberNormSqComponent_add, fiberNormSqComponent_smul]
    ring
  have hcompsq : ∀ (K : Fin 4 → Fin n) (J : Fin 2 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
          (show TensorRSSpace 4 2 I x from
            (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ ga).toSection x
              - (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ gb).toSection x)
          n e K J) ^ 2
        = (g₀.inner x (e (K 0)) (Λ (e (K 1))) *
            ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0))) ^ 2 := by
    intro K J
    rw [hcompsub K J, kscr_deTurckCoeff_component_eq (I := I) (M := M) g₀ ga x e horth K J,
      kscr_deTurckCoeff_component_eq (I := I) (M := M) g₀ gb x e horth K J, hΛ,
      ContinuousLinearMap.sub_apply, map_sub]
    ring
  rw [Finset.sum_congr rfl (fun K _ => Finset.sum_congr rfl (fun J _ => hcompsq K J))]
  rw [kscr_deTurckCoeff_componentSqSum_eq n (fun a b => g₀.inner x (e a) (Λ (e b)))]
  have h1δa : (0 : ℝ) < 1 - δa := by linarith
  have h1δb : (0 : ℝ) < 1 - δb := by linarith
  have hr_nn : (0 : ℝ) ≤ δab / ((1 - δa) * (1 - δb)) :=
    div_nonneg hδab_nn (le_of_lt (mul_pos h1δa h1δb))
  set r : ℝ := δab / ((1 - δa) * (1 - δb)) with hr
  have hper : ∀ b : Fin n, g₀.inner x (Λ (e b)) (Λ (e b)) ≤ r ^ 2 := by
    intro b
    have hsqrt := DifferentialGeometry.Analysis.Sobolev.TensorHilbert.sqrt_inner_gInvDiffRaisedEndo_sub_le
      (I := I) (M := M) g₀ ga gb ha hb htie_a htie_b hδa_lt hδa hδb_lt hδb_nn hδb
      hδab_nn hδab x (e b)
    have hΛb : Λ (e b) = gInvDiffRaisedEndo (I := I) g₀ ga x (e b)
        - gInvDiffRaisedEndo (I := I) g₀ gb x (e b) := by
      rw [hΛ, ContinuousLinearMap.sub_apply]
    rw [← hΛb, ← hr] at hsqrt
    have he1 : g₀.inner x (e b) (e b) = 1 := by rw [horth b b]; simp
    rw [he1, Real.sqrt_one, mul_one] at hsqrt
    have hLnn : 0 ≤ g₀.inner x (Λ (e b)) (Λ (e b)) :=
      DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M)
        g₀ x (Λ (e b))
    have hsq := Real.sq_sqrt hLnn
    nlinarith [Real.sqrt_nonneg (g₀.inner x (Λ (e b)) (Λ (e b))), hsqrt, hsq, hr_nn]
  have hParseval : ∀ b : Fin n,
      (∑ a : Fin n, (g₀.inner x (e a) (Λ (e b))) ^ 2) = g₀.inner x (Λ (e b)) (Λ (e b)) := by
    intro b
    have hpb := hpar (Λ (e b))
    refine hpb ▸ ?_
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [g₀.symm x (e a) (Λ (e b))]
  have hAB : (∑ a : Fin n, ∑ b : Fin n, (g₀.inner x (e a) (Λ (e b))) ^ 2)
      ≤ (n : ℝ) * r ^ 2 := by
    rw [Finset.sum_comm]
    calc (∑ b : Fin n, ∑ a : Fin n, (g₀.inner x (e a) (Λ (e b))) ^ 2)
        = ∑ b : Fin n, g₀.inner x (Λ (e b)) (Λ (e b)) :=
          Finset.sum_congr rfl (fun b _ => hParseval b)
      _ ≤ ∑ _b : Fin n, r ^ 2 := Finset.sum_le_sum (fun b _ => hper b)
      _ = (n : ℝ) * r ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  calc (n : ℝ) ^ 2 * ∑ a : Fin n, ∑ b : Fin n, (g₀.inner x (e a) (Λ (e b))) ^ 2
      ≤ (n : ℝ) ^ 2 * ((n : ℝ) * r ^ 2) := mul_le_mul_of_nonneg_left hAB hn_nn
    _ = (Module.finrank ℝ E : ℝ) ^ 3 * r ^ 2 := by rw [← hnE]; ring

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma kscr_combinedTrace42Model_apply_symbolic
    (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E)
    (D : Tensor0SBundle.Tensor0SModel 4 ℝ E) (m : Fin 2 → E) :
    combinedTrace42Model (E := E) L D m =
      (1 / 2 : ℝ) *
        (modelDoubleTrace (E := E) 2 L
            (ContinuousMultilinearMap.domDomCongr koszulSlotPerm D) m
          + modelDoubleTrace (E := E) 2 L (ContinuousMultilinearMap.domDomCongr koszulSlotPerm D)
              (fun j : Fin 2 => m ((Equiv.swap (0 : Fin 2) 1) j))
          - modelDoubleTrace (E := E) 2 L D m) := by
  rw [combinedTrace42Model, ContinuousLinearMap.smul_apply,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  congr 1

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma kscr_ricciArmPrincipalCoeff_sub_add_self_eq_reindexSum
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
          - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)
        + (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
          - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀) =
      reindexCoeffGen (I := I) (M := M) g₀ 4 2
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁) koszulSlotPerm
        + reindexCoeffGen (I := I) (M := M) g₀ 4 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 4 2 (Equiv.swap (0 : Fin 2) 1)
              (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)) koszulSlotPerm
        - deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁ := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  refine tensorRSSpace_ext 4 2 x (fun w => ?_)
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  beta_reduce
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply,
    ricciArmPrincipalCoeff_toSection, ricciArmPrincipalCoeff_toSection,
    ricciArmPrincipalCoeffFib_toModel, ricciArmPrincipalCoeffFib_toModel,
    kscr_combinedTrace42Model_apply_symbolic, kscr_combinedTrace42Model_apply_symbolic]
  rw [SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_add, ContMDiffSection.coe_sub,
    ContMDiffSection.coe_add, Pi.sub_apply, Pi.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_sub, Tensor0SSpace.toModel_add,
    ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.add_apply]
  simp only [reindexCoeffGen_toSection, reindexCoeffFibGen_apply, rsDomDomCongrSection_toSection,
    toModel_rsDomDomCongr_apply, deTurckPrincipalCometricCoeff_toSection_clm_eq,
    cometricDoubleTraceFib_toModel,
    Tensor0SSpace.toModel_ofModel, Tensor0SSpace.toModel_sub, ContinuousLinearMap.sub_apply,
    ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.sub_apply]
  ring

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma kscr_traceHessianCoeff_sub_eq_reindex_pcc
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    traceHessianCoeff (I := I) (M := M) g₀ g₁ - traceHessianCoeff (I := I) (M := M) g₀ g₀ =
      reindexCoeffGen (I := I) (M := M) g₀ 4 2
        (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁) traceHessianSlotPerm := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    traceHessianCoeff_toSection, traceHessianCoeff_toSection, reindexCoeffGen_toSection]
  apply ContinuousLinearMap.ext
  intro D
  rw [ContinuousLinearMap.sub_apply, reindexCoeffFibGen_apply,
    deTurckPrincipalCometricCoeff_toSection_clm_eq, ContinuousLinearMap.sub_apply,
    traceHessianFib, traceHessianFib, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, domDomCongrFib_apply]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private theorem kscr_reindexCoeffGen_sub (g₀ : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g₀ 4 2) (ρ : Equiv.Perm (Fin 4)) :
    reindexCoeffGen (I := I) (M := M) g₀ 4 2 (A - B) ρ =
      reindexCoeffGen (I := I) (M := M) g₀ 4 2 A ρ -
        reindexCoeffGen (I := I) (M := M) g₀ 4 2 B ρ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    reindexCoeffGen_toSection, reindexCoeffGen_toSection, reindexCoeffGen_toSection,
    SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  apply ContinuousLinearMap.ext
  intro D
  rw [ContinuousLinearMap.sub_apply, reindexCoeffFibGen_apply, reindexCoeffFibGen_apply,
    reindexCoeffFibGen_apply, ContinuousLinearMap.sub_apply]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private theorem kscr_jointTotalSpaceRS_sub {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p - B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hB p₀ hp₀)
  refine (hA'.2.sub hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_sub (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_sub
      (A p₀) (B p₀)

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private theorem kscr_jointTotalSpaceRS_add {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p + B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hB p₀ hp₀)
  refine (hA'.2.add hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_add (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_add
      (A p₀) (B p₀)

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma kscr_phiMet_realizedFam_eq_lieSubLich
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) :
    deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg (realizedFam (I := I) g₀ T T' hδ hδ' s) =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieArm2PrincipalCoeff
          (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
        - (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s
            + linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s) := by
  rw [deTurckPhiMetTotal, linearizedRicciArm2FieldLichnerowicz]
  set X : SmoothCcTensor g₀ 4 2 :=
    ricciArmPrincipalCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) with hX
  set Y : SmoothCcTensor g₀ 4 2 :=
    traceHessianCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) with hY
  have hhalf : (1 / 2 : ℝ) • Y + (1 / 2 : ℝ) • Y = Y := by
    rw [← add_smul]
    norm_num
  have hgrp : (X - (1 / 2 : ℝ) • Y) + (X - (1 / 2 : ℝ) • Y) =
      (X + X) - ((1 / 2 : ℝ) • Y + (1 / 2 : ℝ) • Y) := by abel
  rw [hgrp, hhalf]
  abel

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private theorem kscr_phiMet_realizedFam_jointSmooth
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4
      (fun s => deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
        (realizedFam (I := I) g₀ T T' hδ hδ' s)) (δ := δ) (δ' := δ') := by
  have hLie :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieArm2PrincipalCoeff_realizedFam_jointSmooth
      (I := I) g₀ T T' hδ hδ' g_bg
  have hLich := linearizedRicci_arm2FieldLichnerowicz_jointSmooth (I := I) g₀ T T' hδ hδ'
  have hadd := kscr_jointTotalSpaceRS_add (I := I) (r := 4) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ =>
      (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' p.2).toSection p.1)
    (fun p : M × ℝ =>
      (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' p.2).toSection p.1)
    hLich hLich
  have hsub := kscr_jointTotalSpaceRS_sub (I := I) (r := 4) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ =>
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieArm2PrincipalCoeff
        (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg).toSection p.1)
    (fun p : M × ℝ =>
      (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' p.2).toSection p.1
        + (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' p.2).toSection p.1)
    hLie hadd
  refine hsub.congr (fun p _ => ?_)
  beta_reduce
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1 t) ?_
  rw [kscr_phiMet_realizedFam_eq_lieSubLich (I := I) (M := M) g₀ g_bg T T' hδ hδ' p.2,
    SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]

set_option maxHeartbeats 25600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem exists_deTurckPhiTotPathIntegral_sub_background_sub_principalCometricCoeff_fibreSup_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ εCD : ℝ, 0 ≤ εCD ∧
      (0 ≤ δ → εCD ≤ 3 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2),
        (∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T₀ x v w = ccTensorBilin (I := I) g₀ T₀ x w v) →
        ∀ (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ∀ x : M,
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
                    (hδ_fibre T₀ hball))).toSection x) ≤ εCD ^ 2 := by
  classical
  have hfC_nn : (0 : ℝ) ≤ deTurckArmFibreConst (Module.finrank ℝ E) :=
    deTurckArmFibreConst_nonneg _
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  have h1δ : (0 : ℝ) < 1 - δ := by linarith
  rcases isEmpty_or_nonempty M with hM | hM
  · refine ⟨0, le_refl 0, fun hδ0' => ?_, fun T₀ hTsymm hball x => (hM.false x).elim⟩
    have hκ_nn : (0 : ℝ) ≤ δ / (1 - δ) := div_nonneg hδ0' (le_of_lt h1δ)
    positivity
  · have hδ0 : 0 ≤ δ :=
      delta_nonneg_of_ball_gFibreOpBound (I := I) (M := M) g₀ a hR₀ hδ_fibre
    have hκ_nn : (0 : ℝ) ≤ δ / (1 - δ) := div_nonneg hδ0 (le_of_lt h1δ)
    refine ⟨(11 / 4 : ℝ) * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)),
      mul_nonneg (mul_nonneg (by norm_num) hfC_nn) hκ_nn,
      fun _ => by nlinarith [mul_nonneg hfC_nn hκ_nn], ?_⟩
    intro T₀ hTsymm hball x
    set fC : ℝ := deTurckArmFibreConst (Module.finrank ℝ E) with hfC_def
    have hfC_sqrt : fC = Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3) := rfl
    set κ : ℝ := δ / (1 - δ) with hκ_def
    have hδT := hδ_fibre T₀ hball
    have hδZ := hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
      (by
        rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
            from (zero_smul _ _).symm, smoothCcToTensorHs_smul, tensorHs_norm_smul]
        simpa using hR₀)
    set g₁ : SmoothRiemannianMetric I M := tensorSectionRealizeMetric (I := I) g₀ T₀
      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) with hg₁_def
    set P : SmoothCcTensor g₀ 4 2 := deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
      (0 : SmoothCcTensor g₀ 0 2)
      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
      (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
        (by
          rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
              from (zero_smul _ _).symm, smoothCcToTensorHs_smul, tensorHs_norm_smul]
          simpa using hR₀)) with hP_def
    set C1 : SmoothCcTensor g₀ 4 2 := deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀
      with hC1_def
    set Δ1 : SmoothCcTensor g₀ 4 2 := deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁
      with hΔ1_def
    set Φ : ℝ → SmoothCcTensor g₀ 4 2 := fun s =>
      deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
        (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s) with hΦ_def
    have hjoint : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 Φ
        (δ := δ) (δ' := δ) :=
      kscr_phiMet_realizedFam_jointSmooth (I := I) (M := M) g₀ g_bg T₀
        (0 : SmoothCcTensor g₀ 0 2) hδT hδZ
    have hSIu : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ) := by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_realizedSmallSet hδ_lt hδ_lt
    have hIccS : Set.Icc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ) :=
      Icc_subset_realizedSmallSet hδ_lt hδ_lt
    have hjointC : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
          ((Φ p.2).toSection p.1))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
      have h := hjoint
      rw [linearizedRicciThreeArmHjoint] at h
      exact h
    have hslice : ContinuousOn (fun t : ℝ =>
        Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x))
        (realizedSmallSet (δ := δ) (δ' := δ)) :=
      DifferentialGeometry.PDE.DeTurck.RicciLinearization.jointContMDiff_toModel_continuous_slice
        (I := I) g₀ 4 2 Φ (realizedSmallSet (δ := δ) (δ' := δ)) hjointC x
    have hcontIcc : ContinuousOn (fun t : ℝ =>
        Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x)) (Set.Icc (0 : ℝ) 1) :=
      hslice.mono hIccS
    set Cx : Tensor0SBundle.TensorRSModel 4 2 ℝ E :=
      Tensor0SBundle.TensorRSSpace.toModel (C1.toSection x)
        + Tensor0SBundle.TensorRSSpace.toModel (Δ1.toSection x) with hCx_def
    have hsecPD : ((P - C1 - Δ1).toSection x : Tensor0SBundle.TensorRSSpace 4 2 I x) =
        P.toSection x - C1.toSection x - Δ1.toSection x := by
      rw [show ((P - C1 - Δ1).toSection x : Tensor0SBundle.TensorRSSpace 4 2 I x) =
          (P - C1).toSection x - Δ1.toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      rw [show ((P - C1).toSection x : Tensor0SBundle.TensorRSSpace 4 2 I x) =
          P.toSection x - C1.toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
    have hint_fPhi : IntervalIntegrable (fun t : ℝ =>
        Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x))
        MeasureTheory.volume 0 1 :=
      (hslice.mono hSIu).intervalIntegrable
    have hDmodel : Tensor0SBundle.TensorRSSpace.toModel ((P - C1 - Δ1).toSection x) =
        ∫ t in (0 : ℝ)..1,
          (Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) - Cx) := by
      rw [hsecPD, Tensor0SBundle.TensorRSSpace.toModel_sub,
        Tensor0SBundle.TensorRSSpace.toModel_sub]
      rw [show Tensor0SBundle.TensorRSSpace.toModel (P.toSection x) =
          ∫ t in (0 : ℝ)..1, Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) from by
        rw [hP_def]
        unfold deTurckPhiTotPathIntegral
        rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pathIntegralCoeffField_toModel]]
      rw [intervalIntegral.integral_sub hint_fPhi intervalIntegrable_const,
        intervalIntegral.integral_const, hCx_def]
      norm_num
      abel
    clear_value P C1 Δ1 g₁ Φ Cx
    have htpn_val : ∀ (W : SmoothCcTensor g₀ 4 2),
        tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
            (Tensor0SBundle.TensorRSSpace.toModel (W.toSection x)) =
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (W.toSection x)) := by
      intro W
      rw [riemannianFiberNormSq_eq_tensorInnerPointwise]
      rfl
    have htpn_neg : ∀ m : Tensor0SBundle.TensorRSModel 4 2 ℝ E,
        tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x (-m) =
          tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x m := by
      intro m
      unfold tensorPointwiseNorm
      rw [show (-m : Tensor0SBundle.TensorRSModel 4 2 ℝ E) = (-1 : ℝ) • m from
        (neg_one_smul ℝ m).symm, tensorInnerPointwise_smul_left,
        tensorInnerPointwise_smul_right]
      norm_num
    have hsqrt_n3 : ∀ r : ℝ, 0 ≤ r →
        Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3 * r ^ 2) = fC * r := by
      intro r hr
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hr, hfC_sqrt]
    have hsup : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
            (Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) - Cx) ≤
          fC * κ * (4 * t + (3 / 2) * (1 - t)) := by
      intro t ht
      have ht0 : (0 : ℝ) ≤ t := ht.1
      have ht1 : t ≤ 1 := ht.2
      set g_t : SmoothRiemannianMetric I M :=
        realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ t with hg_t_def
      set Δt : SmoothCcTensor g₀ 4 2 :=
        deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g_t with hΔt_def
      clear_value Δt
      have htδ_nn : (0 : ℝ) ≤ t * δ := mul_nonneg ht0 hδ0
      have htδ_le : t * δ ≤ δ := by nlinarith
      have htδ_lt : t * δ < 1 := lt_of_le_of_lt htδ_le hδ_lt
      have h1tδ : (0 : ℝ) < 1 - t * δ := by linarith
      have htie_t : ∀ (y : M) (v w : TangentSpace I y),
          g_t.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀
              (convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) t) y v w :=
        fun y v w => realizedFam_inner_of_mem (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
          hδT hδZ (hIccS ht) y v w
      clear_value g_t
      have hcp : convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) t
          = t • T₀ := by
        rw [show convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) t =
            (1 - t) • (0 : SmoothCcTensor g₀ 0 2) + t • T₀ from rfl, smul_zero, zero_add]
      have hbilin_cp : ∀ (y : M) (v w : TangentSpace I y),
          ccTensorBilinSymm (I := I) g₀
            (convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) t) y v w =
            t * ccTensorBilinSymm (I := I) g₀ T₀ y v w := by
        intro y v w
        rw [hcp, ccTensorBilinSymm_smul]
      have hδa : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀
            (convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) t)) (t * δ) := by
        intro y v w
        rw [hbilin_cp y v w, abs_mul, abs_of_nonneg ht0]
        have hbase := hδT y v w
        have hs1 : (0 : ℝ) ≤ Real.sqrt (g₀.inner y v v) := Real.sqrt_nonneg _
        have hs2 : (0 : ℝ) ≤ Real.sqrt (g₀.inner y w w) := Real.sqrt_nonneg _
        calc t * |ccTensorBilinSymm (I := I) g₀ T₀ y v w|
            ≤ t * (δ * Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w w)) :=
              mul_le_mul_of_nonneg_left hbase ht0
          _ = t * δ * Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w w) := by ring
      have hδab : gFibreOpBound (I := I) (M := M) g₀
          (fun y => ccTensorBilinSymm (I := I) g₀
              (convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) t) y
            - ccTensorBilinSymm (I := I) g₀ T₀ y) ((1 - t) * δ) := by
        intro y v w
        beta_reduce
        have hval : (ccTensorBilinSymm (I := I) g₀
            (convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) t) y
            - ccTensorBilinSymm (I := I) g₀ T₀ y) v w =
            ccTensorBilinSymm (I := I) g₀
              (convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) t) y v w
              - ccTensorBilinSymm (I := I) g₀ T₀ y v w := rfl
        rw [hval, hbilin_cp y v w]
        have hfact : t * (ccTensorBilinSymm (I := I) g₀ T₀ y v w)
            - ccTensorBilinSymm (I := I) g₀ T₀ y v w =
            (t - 1) * (ccTensorBilinSymm (I := I) g₀ T₀ y v w) := by ring
        rw [hfact, abs_mul, abs_of_nonpos (by linarith : t - 1 ≤ 0)]
        have hbase := hδT y v w
        have habs_nn : (0 : ℝ) ≤ |ccTensorBilinSymm (I := I) g₀ T₀ y v w| := abs_nonneg _
        calc -(t - 1) * |ccTensorBilinSymm (I := I) g₀ T₀ y v w|
            = (1 - t) * |ccTensorBilinSymm (I := I) g₀ T₀ y v w| := by ring
          _ ≤ (1 - t) * (δ * Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w w)) :=
              mul_le_mul_of_nonneg_left hbase (by linarith)
          _ = (1 - t) * δ * Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w w) := by ring
      have htie_1 : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₀ y v w := by
        intro y v w
        rw [hg₁_def]
        exact tensorSectionRealizeMetric_inner (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) y v w
      have hΔt_rfns : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (Δt.toSection x) ≤
          (Module.finrank ℝ E : ℝ) ^ 3 * (t * δ / (1 - t * δ)) ^ 2 := by
        rw [hΔt_def]
        exact riemannianFiberNormSq_deTurckPrincipalCometricCoeff_le (I := I) (M := M)
          g₀ g_t _ htie_t htδ_lt htδ_nn hδa x
      have hΔt_sqrt : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          (Δt.toSection x)) ≤ fC * (t * δ / (1 - t * δ)) := by
        refine le_trans (Real.sqrt_le_sqrt hΔt_rfns) ?_
        rw [hsqrt_n3 _ (div_nonneg htδ_nn (le_of_lt h1tδ))]
      have hdev_rfns : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((Δt - Δ1).toSection x) ≤
          (Module.finrank ℝ E : ℝ) ^ 3 *
            ((1 - t) * δ / ((1 - t * δ) * (1 - δ))) ^ 2 := by
        rw [hΔt_def, hΔ1_def]
        exact kscr_rfns_pcc_deviation_le (I := I) (M := M) g₀ g_t g₁ _ _
          htie_t htie_1 htδ_lt hδa hδ_lt hδ0 hδT
          (mul_nonneg (by linarith) hδ0) hδab htδ_nn x
      have hdev_sqrt : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((Δt - Δ1).toSection x)) ≤
          fC * ((1 - t) * δ / ((1 - t * δ) * (1 - δ))) := by
        refine le_trans (Real.sqrt_le_sqrt hdev_rfns) ?_
        rw [hsqrt_n3 _ (div_nonneg (mul_nonneg (by linarith) hδ0)
          (le_of_lt (mul_pos h1tδ h1δ)))]
      have hdec_t := deTurckPhiMetTotal_eq_reindex_decomp_fw (I := I) (M := M) g₀ g_bg g_t
      have hdec_0 := deTurckPhiMetTotal_eq_reindex_decomp_fw (I := I) (M := M) g₀ g_bg g₀
      set ρA : Equiv.Perm (Fin 4) := traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA
        with hρA_def
      set ρAT : Equiv.Perm (Fin 4) := traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT
        with hρAT_def
      set A1 : SmoothCcTensor g₀ 4 2 := reindexCoeffGen (I := I) (M := M) g₀ 4 2
        (reindexCoeffGen (I := I) (M := M) g₀ 4 2 Δt traceHessianSlotPerm) ρA with hA1_def
      set A2 : SmoothCcTensor g₀ 4 2 := reindexCoeffGen (I := I) (M := M) g₀ 4 2
        (reindexCoeffGen (I := I) (M := M) g₀ 4 2 Δt traceHessianSlotPerm) ρAT with hA2_def
      set R1 : SmoothCcTensor g₀ 4 2 := reindexCoeffGen (I := I) (M := M) g₀ 4 2 Δt
        koszulSlotPerm with hR1_def
      set R2 : SmoothCcTensor g₀ 4 2 := reindexCoeffGen (I := I) (M := M) g₀ 4 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 4 2 (Equiv.swap (0 : Fin 2) 1) Δt)
        koszulSlotPerm with hR2_def
      clear_value A1 A2 R1 R2
      have hXX : (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g_t
            + ricciArmPrincipalCoeff (I := I) (M := M) g₀ g_t)
          - (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀
            + ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀) = R1 + R2 - Δt := by
        have h691 := kscr_ricciArmPrincipalCoeff_sub_add_self_eq_reindexSum
          (I := I) (M := M) g₀ g_t
        calc (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g_t
              + ricciArmPrincipalCoeff (I := I) (M := M) g₀ g_t)
            - (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀
              + ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)
            = (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g_t
                - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)
              + (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g_t
                - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀) := by abel
          _ = R1 + R2 - Δt := by rw [h691, hR1_def, hR2_def, hΔt_def]
      have hΨ : Φ t - C1 - Δ1 = A1 + A2 - R1 - R2 + (Δt - Δ1) := by
        have h327 := kscr_traceHessianCoeff_sub_eq_reindex_pcc (I := I) (M := M) g₀ g_t
        calc Φ t - C1 - Δ1
            = (reindexCoeffGen (I := I) (M := M) g₀ 4 2
                  (traceHessianCoeff (I := I) (M := M) g₀ g_t) ρA
                - reindexCoeffGen (I := I) (M := M) g₀ 4 2
                  (traceHessianCoeff (I := I) (M := M) g₀ g₀) ρA)
              + (reindexCoeffGen (I := I) (M := M) g₀ 4 2
                  (traceHessianCoeff (I := I) (M := M) g₀ g_t) ρAT
                - reindexCoeffGen (I := I) (M := M) g₀ 4 2
                  (traceHessianCoeff (I := I) (M := M) g₀ g₀) ρAT)
              - ((ricciArmPrincipalCoeff (I := I) (M := M) g₀ g_t
                  + ricciArmPrincipalCoeff (I := I) (M := M) g₀ g_t)
                - (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀
                  + ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀))
              - Δ1 := by
              rw [hΦ_def]
              beta_reduce
              rw [show deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
                  (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ t) =
                  deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g_t from by rw [hg_t_def]]
              rw [hdec_t, hC1_def, hdec_0, hρA_def, hρAT_def]
              abel
          _ = (reindexCoeffGen (I := I) (M := M) g₀ 4 2
                (traceHessianCoeff (I := I) (M := M) g₀ g_t
                  - traceHessianCoeff (I := I) (M := M) g₀ g₀) ρA)
              + (reindexCoeffGen (I := I) (M := M) g₀ 4 2
                (traceHessianCoeff (I := I) (M := M) g₀ g_t
                  - traceHessianCoeff (I := I) (M := M) g₀ g₀) ρAT)
              - (R1 + R2 - Δt) - Δ1 := by
              rw [kscr_reindexCoeffGen_sub (I := I) (M := M) g₀ _ _ ρA,
                kscr_reindexCoeffGen_sub (I := I) (M := M) g₀ _ _ ρAT, hXX]
          _ = A1 + A2 - R1 - R2 + (Δt - Δ1) := by
              rw [h327, ← hΔt_def, hA1_def, hA2_def]
              abel
      have hΨsec : ((Φ t - C1 - Δ1).toSection x : Tensor0SBundle.TensorRSSpace 4 2 I x) =
          A1.toSection x + A2.toSection x - R1.toSection x - R2.toSection x
            + (Δt - Δ1).toSection x := by
        rw [hΨ]
        rw [show ((A1 + A2 - R1 - R2 + (Δt - Δ1)).toSection x :
            Tensor0SBundle.TensorRSSpace 4 2 I x) =
            (A1 + A2 - R1 - R2).toSection x + (Δt - Δ1).toSection x from by
          rw [SmoothCcTensor.toSection_add]; rfl]
        rw [show ((A1 + A2 - R1 - R2).toSection x :
            Tensor0SBundle.TensorRSSpace 4 2 I x) =
            (A1 + A2 - R1).toSection x - R2.toSection x from by
          rw [SmoothCcTensor.toSection_sub]; rfl]
        rw [show ((A1 + A2 - R1).toSection x : Tensor0SBundle.TensorRSSpace 4 2 I x) =
            (A1 + A2).toSection x - R1.toSection x from by
          rw [SmoothCcTensor.toSection_sub]; rfl]
        rw [show ((A1 + A2).toSection x : Tensor0SBundle.TensorRSSpace 4 2 I x) =
            A1.toSection x + A2.toSection x from by
          rw [SmoothCcTensor.toSection_add]; rfl]
      have hΨmodel : Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) - Cx =
          Tensor0SBundle.TensorRSSpace.toModel ((Φ t - C1 - Δ1).toSection x) := by
        rw [show ((Φ t - C1 - Δ1).toSection x : Tensor0SBundle.TensorRSSpace 4 2 I x) =
            (Φ t - C1).toSection x - Δ1.toSection x from by
          rw [SmoothCcTensor.toSection_sub]; rfl]
        rw [show ((Φ t - C1).toSection x : Tensor0SBundle.TensorRSSpace 4 2 I x) =
            (Φ t).toSection x - C1.toSection x from by
          rw [SmoothCcTensor.toSection_sub]; rfl]
        rw [Tensor0SBundle.TensorRSSpace.toModel_sub,
          Tensor0SBundle.TensorRSSpace.toModel_sub, hCx_def]
        abel
      have hexA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (A1.toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (Δt.toSection x) := by
        rw [hA1_def]
        rw [reindexCoeffGen_toSection]
        rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannianFiberNormSq_reindexCoeffFibGen
          (I := I) (M := M) g₀ 4 2 x ρA _]
        rw [reindexCoeffGen_toSection]
        exact DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannianFiberNormSq_reindexCoeffFibGen
          (I := I) (M := M) g₀ 4 2 x traceHessianSlotPerm _
      have hexA2 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (A2.toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (Δt.toSection x) := by
        rw [hA2_def]
        rw [reindexCoeffGen_toSection]
        rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannianFiberNormSq_reindexCoeffFibGen
          (I := I) (M := M) g₀ 4 2 x ρAT _]
        rw [reindexCoeffGen_toSection]
        exact DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannianFiberNormSq_reindexCoeffFibGen
          (I := I) (M := M) g₀ 4 2 x traceHessianSlotPerm _
      have hexR1 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (R1.toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (Δt.toSection x) := by
        rw [hR1_def, reindexCoeffGen_toSection]
        exact DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannianFiberNormSq_reindexCoeffFibGen
          (I := I) (M := M) g₀ 4 2 x koszulSlotPerm _
      have hexR2 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (R2.toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (Δt.toSection x) := by
        have h20 := rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ 4 2
          koszulSlotPerm (Equiv.swap (0 : Fin 2) 1) Δt 0 x
        rw [hR2_def]
        simpa [iteratedCovGrad_zero] using h20
      have htpn_piece : ∀ (W : SmoothCcTensor g₀ 4 2),
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (W.toSection x) =
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (Δt.toSection x) →
          tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
              (Tensor0SBundle.TensorRSSpace.toModel (W.toSection x)) ≤
            fC * (t * δ / (1 - t * δ)) := by
        intro W hW
        rw [htpn_val W, hW]
        exact hΔt_sqrt
      have htpn_sub_le : ∀ u v : Tensor0SBundle.TensorRSModel 4 2 ℝ E,
          tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x (u - v) ≤
            tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x u
              + tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x v := by
        intro u v
        rw [sub_eq_add_neg]
        refine le_trans (tensorPointwiseNorm_add_le (I := I) (M := M) g₀ 4 2 x u (-v)) ?_
        rw [htpn_neg v]
      have htri : tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
          (Tensor0SBundle.TensorRSSpace.toModel ((Φ t - C1 - Δ1).toSection x)) ≤
          4 * (fC * (t * δ / (1 - t * δ)))
            + fC * ((1 - t) * δ / ((1 - t * δ) * (1 - δ))) := by
        rw [hΨsec]
        rw [Tensor0SBundle.TensorRSSpace.toModel_add, Tensor0SBundle.TensorRSSpace.toModel_sub,
          Tensor0SBundle.TensorRSSpace.toModel_sub, Tensor0SBundle.TensorRSSpace.toModel_add]
        have t4 := tensorPointwiseNorm_add_le (I := I) (M := M) g₀ 4 2 x
          (Tensor0SBundle.TensorRSSpace.toModel (A1.toSection x)
            + Tensor0SBundle.TensorRSSpace.toModel (A2.toSection x)
            - Tensor0SBundle.TensorRSSpace.toModel (R1.toSection x)
            - Tensor0SBundle.TensorRSSpace.toModel (R2.toSection x))
          (Tensor0SBundle.TensorRSSpace.toModel ((Δt - Δ1).toSection x))
        have t3 := htpn_sub_le
          (Tensor0SBundle.TensorRSSpace.toModel (A1.toSection x)
            + Tensor0SBundle.TensorRSSpace.toModel (A2.toSection x)
            - Tensor0SBundle.TensorRSSpace.toModel (R1.toSection x))
          (Tensor0SBundle.TensorRSSpace.toModel (R2.toSection x))
        have t2 := htpn_sub_le
          (Tensor0SBundle.TensorRSSpace.toModel (A1.toSection x)
            + Tensor0SBundle.TensorRSSpace.toModel (A2.toSection x))
          (Tensor0SBundle.TensorRSSpace.toModel (R1.toSection x))
        have t1 := tensorPointwiseNorm_add_le (I := I) (M := M) g₀ 4 2 x
          (Tensor0SBundle.TensorRSSpace.toModel (A1.toSection x))
          (Tensor0SBundle.TensorRSSpace.toModel (A2.toSection x))
        have b1 := htpn_piece A1 hexA1
        have b2 := htpn_piece A2 hexA2
        have b3 := htpn_piece R1 hexR1
        have b4 := htpn_piece R2 hexR2
        have b5 : tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
            (Tensor0SBundle.TensorRSSpace.toModel ((Δt - Δ1).toSection x)) ≤
            fC * ((1 - t) * δ / ((1 - t * δ) * (1 - δ))) := by
          rw [htpn_val (Δt - Δ1)]
          exact hdev_sqrt
        linarith [t1, t2, t3, t4, b1, b2, b3, b4, b5]
      have hrate1 : t * δ / (1 - t * δ) ≤ t * κ := by
        rw [hκ_def, div_le_iff₀ h1tδ]
        have h1 : t * (δ / (1 - δ)) * (1 - t * δ) = (t * δ * (1 - t * δ)) / (1 - δ) := by
          field_simp
        rw [h1, le_div_iff₀ h1δ]
        nlinarith [mul_nonneg (mul_nonneg (mul_nonneg ht0 hδ0) hδ0)
          (by linarith : (0:ℝ) ≤ 1 - t)]
      have hrate2 : (1 - t) * δ / ((1 - t * δ) * (1 - δ)) ≤ (3 / 2) * ((1 - t) * κ) := by
        rw [hκ_def, div_le_iff₀ (mul_pos h1tδ h1δ)]
        have h1 : (3 / 2 : ℝ) * ((1 - t) * (δ / (1 - δ))) * ((1 - t * δ) * (1 - δ)) =
            (3 / 2) * ((1 - t) * δ) * (1 - t * δ) := by
          field_simp
        rw [h1]
        have hkey : (0 : ℝ) ≤ 1 / 2 - (3 / 2) * (t * δ) := by nlinarith
        nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - t) hδ0) hkey]
      calc tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
            (Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) - Cx)
          = tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
            (Tensor0SBundle.TensorRSSpace.toModel ((Φ t - C1 - Δ1).toSection x)) := by
            rw [hΨmodel]
        _ ≤ 4 * (fC * (t * δ / (1 - t * δ)))
            + fC * ((1 - t) * δ / ((1 - t * δ) * (1 - δ))) := htri
        _ ≤ 4 * (fC * (t * κ)) + fC * ((3 / 2) * ((1 - t) * κ)) := by
            have e1 : fC * (t * δ / (1 - t * δ)) ≤ fC * (t * κ) :=
              mul_le_mul_of_nonneg_left hrate1 hfC_nn
            have e2 : fC * ((1 - t) * δ / ((1 - t * δ) * (1 - δ))) ≤
                fC * ((3 / 2) * ((1 - t) * κ)) :=
              mul_le_mul_of_nonneg_left hrate2 hfC_nn
            linarith
        _ = fC * κ * (4 * t + (3 / 2) * (1 - t)) := by ring
    have hrfns_tpn : riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x
        ((P - C1 - Δ1).toSection x) =
        tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
          (Tensor0SBundle.TensorRSSpace.toModel ((P - C1 - Δ1).toSection x)) ^ 2 := by
      rw [riemannianFiberNormSq_eq_tensorInnerPointwise]
      unfold tensorPointwiseNorm
      rw [Real.sq_sqrt (tensorInnerPointwise_nonneg (I := I) (M := M) g₀ 4 2 x _)]
    rw [hrfns_tpn, hDmodel]
    have hcont_shift : ContinuousOn (fun t : ℝ =>
        Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) - Cx)
        (Set.Icc (0 : ℝ) 1) := hcontIcc.sub continuousOn_const
    have hint_le := tensorPointwiseNorm_intervalIntegral_le (I := I) (M := M) g₀ 4 2 x
      (fun t => Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) - Cx) hcont_shift
    have hint1 : IntervalIntegrable (fun t : ℝ =>
        tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
          (Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) - Cx))
        MeasureTheory.volume 0 1 :=
      ((tensorPointwiseNorm_continuous (I := I) (M := M) g₀ 4 2 x).comp_continuousOn
        hcont_shift).intervalIntegrable_of_Icc (by norm_num)
    have hint2 : IntervalIntegrable (fun t : ℝ => fC * κ * (4 * t + (3 / 2) * (1 - t)))
        MeasureTheory.volume 0 1 := by
      apply Continuous.intervalIntegrable
      continuity
    have hmono : (∫ t in (0 : ℝ)..1, tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
        (Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) - Cx)) ≤
        ∫ t in (0 : ℝ)..1, fC * κ * (4 * t + (3 / 2) * (1 - t)) :=
      intervalIntegral.integral_mono_on (by norm_num) hint1 hint2 hsup
    have hwval : (∫ t in (0 : ℝ)..1, fC * κ * (4 * t + (3 / 2) * (1 - t))) =
        (11 / 4) * fC * κ := by
      rw [intervalIntegral.integral_const_mul]
      rw [show (fun t : ℝ => 4 * t + (3 / 2) * (1 - t)) =
          fun t : ℝ => (5 / 2) * t + 3 / 2 from funext fun t => by ring]
      rw [intervalIntegral.integral_add ((intervalIntegral.intervalIntegrable_id).const_mul _)
        intervalIntegrable_const]
      rw [intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
      norm_num
      ring
    have htpn_nn : (0 : ℝ) ≤ tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
        (∫ t in (0 : ℝ)..1,
          (Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) - Cx)) :=
      tensorPointwiseNorm_nonneg (I := I) (M := M) g₀ 4 2 x _
    have hfinal : tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
        (∫ t in (0 : ℝ)..1,
          (Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) - Cx)) ≤
        (11 / 4) * fC * κ := by
      refine le_trans hint_le ?_
      rw [← hwval]
      exact hmono
    calc tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
          (∫ t in (0 : ℝ)..1,
            (Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) - Cx)) ^ 2
        ≤ ((11 / 4) * fC * κ) ^ 2 := by
          exact pow_le_pow_left₀ htpn_nn hfinal 2
      _ = ((11 / 4 : ℝ) * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) ^ 2 := by
          rw [hfC_def, hκ_def]

end

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
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
      (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
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
      have hGNspec := (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 2 i hi1).choose_spec.2
      have hCgn_i : (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
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
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
open DifferentialGeometry.Integral.Measure in
theorem exists_deTurckPrincipalCometricCoeff_realize_coeffJetEnvelope_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2),
        (∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T₀ x v w = ccTensorBilin (I := I) g₀ T₀ x w v) →
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
    rfns_iteratedCovGrad_gInvDiffSlotCoeff_diagonalProductGrid_le (I := I) (M := M) g₀
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

section

open Tensor0SBundle
open DifferentialGeometry.Integral.Measure

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem dscr_iteratedCovGrad_jointSmooth
    (g₀ : SmoothRiemannianMetric I M) (r sIdx i : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r sIdx) (S : Set ℝ)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r sIdx ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r sIdx ℝ E)
        (E := fun z : M => TensorRSSpace r sIdx I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r (sIdx + i) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (sIdx + i) ℝ E)
        (E := fun z : M => TensorRSSpace r (sIdx + i) I z) q.1
        ((iteratedCovGrad (I := I) g₀ r sIdx i (Φ q.2)).toSection q.1))
      ((Set.univ : Set M) ×ˢ S) := by
  induction i with
  | zero => exact hjoint
  | succ j ih =>
    exact covGrad_step_jointContMDiffOn (I := I) (M := M) g₀ r (sIdx + j)
      (fun t => iteratedCovGrad (I := I) g₀ r sIdx j (Φ t)) S ih

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem dscr_rfns_jointContinuous
    (g₀ : SmoothRiemannianMetric I M) (r sIdx : ℕ)
    (Ψ : ℝ → SmoothCcTensor g₀ r sIdx) (S : Set ℝ)
    (hSI : Set.Icc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r sIdx ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r sIdx ℝ E)
        (E := fun z : M => TensorRSSpace r sIdx I z) q.1 ((Ψ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContinuousOn (fun p : ℝ × M =>
      riemannianFiberNormSq (I := I) (M := M) g₀ r sIdx p.2 ((Ψ p.1).toSection p.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) := by
  have hIccprod : (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) ⊆
      (fun p : ℝ × M => (p.2, p.1)) ⁻¹' ((Set.univ : Set M) ×ˢ S) := by
    rintro ⟨t, x⟩ ⟨ht, -⟩
    exact ⟨Set.mem_univ _, hSI ht⟩
  have hswapCont : Continuous (fun p : ℝ × M => (p.2, p.1)) := by fun_prop
  have hv : ContinuousOn
      (fun p : ℝ × M => TotalSpace.mk' (TensorRSModel r sIdx ℝ E)
        (E := fun z : M => TensorRSSpace r sIdx I z) p.2 ((Ψ p.1).toSection p.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) := by
    refine (hjoint.continuousOn.comp hswapCont.continuousOn hIccprod).congr ?_
    rintro ⟨t, x⟩ -
    rfl
  have hψ : ContinuousOn
      (fun p : ℝ × M => TotalSpace.mk'
        (TensorRSModel r sIdx ℝ E →L[ℝ] TensorRSModel r sIdx ℝ E →L[ℝ] ℝ)
        (E := fun x : M => TensorRSSpace r sIdx I x →L[ℝ] TensorRSSpace r sIdx I x →L[ℝ] ℝ)
        p.2
        (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g₀ r sIdx p.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) :=
    ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorRSRiemannianInnerCLM_continuous
      (I := I) (M := M) g₀ r sIdx).comp continuous_snd).continuousOn
  have happ : ContinuousOn
      (fun p : ℝ × M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) p.2
        (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g₀ r sIdx p.2 ((Ψ p.1).toSection p.2) ((Ψ p.1).toSection p.2)))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) :=
    ContinuousOn.clm_bundle_apply₂ (F₁ := TensorRSModel r sIdx ℝ E)
      (F₂ := TensorRSModel r sIdx ℝ E) (F₃ := ℝ) (b := fun p : ℝ × M => p.2) hψ hv hv
  have hscalar : ContinuousOn
      (fun p : ℝ × M =>
        DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g₀ r sIdx p.2 ((Ψ p.1).toSection p.2) ((Ψ p.1).toSection p.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) := by
    intro p hp
    have hp2 := ((FiberBundle.continuousWithinAt_totalSpace ℝ
      (fun p : ℝ × M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) p.2
        (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g₀ r sIdx p.2
          ((Ψ p.1).toSection p.2) ((Ψ p.1).toSection p.2)))).mp (happ p hp)).2
    exact hp2
  refine hscalar.congr ?_
  rintro ⟨t, x⟩ -
  simp only
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ r sIdx x
      ((Ψ t).toSection x),
    DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_apply]

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 3200000 in
set_option backward.isDefEq.respectTransparency false in
private theorem dscr_pathIntegralCoeffField_congr
    (g₀ : SmoothRiemannianMetric I M) (r sIdx : ℕ)
    (Ψ₁ Ψ₂ : ℝ → SmoothCcTensor g₀ r sIdx) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hj₁ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r sIdx ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r sIdx ℝ E)
        (E := fun z : M => TensorRSSpace r sIdx I z) q.1 ((Ψ₁ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (hj₂ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r sIdx ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r sIdx ℝ E)
        (E := fun z : M => TensorRSSpace r sIdx I z) q.1 ((Ψ₂ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (hΨ : Ψ₁ = Ψ₂) :
    pathIntegralCoeffField (I := I) (M := M) g₀ r sIdx Ψ₁ S hS hSI hj₁ =
      pathIntegralCoeffField (I := I) (M := M) g₀ r sIdx Ψ₂ S hS hSI hj₂ := by
  subst hΨ
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rfl

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 3200000 in
set_option backward.isDefEq.respectTransparency false in
private theorem dscr_iteratedCovGrad_pathIntegral_comm
    (g₀ : SmoothRiemannianMetric I M) (r sIdx i : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r sIdx) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r sIdx ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r sIdx ℝ E)
        (E := fun z : M => TensorRSSpace r sIdx I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (hji : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r (sIdx + i) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (sIdx + i) ℝ E)
        (E := fun z : M => TensorRSSpace r (sIdx + i) I z) q.1
        ((iteratedCovGrad (I := I) g₀ r sIdx i (Φ q.2)).toSection q.1))
      ((Set.univ : Set M) ×ˢ S)) :
    iteratedCovGrad (I := I) g₀ r sIdx i
        (pathIntegralCoeffField (I := I) (M := M) g₀ r sIdx Φ S hS hSI hjoint) =
      pathIntegralCoeffField (I := I) (M := M) g₀ r (sIdx + i)
        (fun t => iteratedCovGrad (I := I) g₀ r sIdx i (Φ t)) S hS hSI hji := by
  induction i with
  | zero =>
    rw [iteratedCovGrad_zero]
    exact dscr_pathIntegralCoeffField_congr (I := I) g₀ r sIdx Φ
      (fun t => iteratedCovGrad (I := I) g₀ r sIdx 0 (Φ t)) S hS hSI hjoint hji
      (by funext t; rw [iteratedCovGrad_zero])
  | succ j ih =>
    have hjg_j : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r (sIdx + j) ℝ E)) ∞
        (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (sIdx + j) ℝ E)
          (E := fun z : M => TensorRSSpace r (sIdx + j) I z) q.1
          ((iteratedCovGrad (I := I) g₀ r sIdx j (Φ q.2)).toSection q.1))
        ((Set.univ : Set M) ×ˢ S) :=
      dscr_iteratedCovGrad_jointSmooth (I := I) g₀ r sIdx j Φ S hjoint
    have hjgsucc : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, TensorRSModel r (sIdx + j + 1) ℝ E)) ∞
        (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (sIdx + j + 1) ℝ E)
          (E := fun z : M => TensorRSSpace r (sIdx + j + 1) I z) q.1
          ((covGrad (I := I) (M := M) g₀ r (sIdx + j)
              (iteratedCovGrad (I := I) g₀ r sIdx j (Φ q.2))).toSection q.1))
        ((Set.univ : Set M) ×ˢ S) :=
      covGrad_step_jointContMDiffOn (I := I) (M := M) g₀ r (sIdx + j)
        (fun t => iteratedCovGrad (I := I) g₀ r sIdx j (Φ t)) S hjg_j
    rw [iteratedCovGrad_succ, ih hjg_j]
    rw [covGrad_pathIntegral_comm (I := I) (M := M) g₀ r (sIdx + j)
      (fun t => iteratedCovGrad (I := I) g₀ r sIdx j (Φ t)) S hS hSI hjg_j hjgsucc]
    exact dscr_pathIntegralCoeffField_congr (I := I) g₀ r (sIdx + j + 1)
      (fun t => covGrad (I := I) (M := M) g₀ r (sIdx + j)
        (iteratedCovGrad (I := I) g₀ r sIdx j (Φ t)))
      (fun t => iteratedCovGrad (I := I) g₀ r sIdx (j + 1) (Φ t)) S hS hSI hjgsucc hji
      (by funext t; rw [iteratedCovGrad_succ])

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem armField_pathIntegral_jetL2_perOrder_le
    (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r 2) {δ δ' : ℝ}
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedSmallSet (δ := δ) (δ' := δ'))
    (hSopen : IsOpen (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedSmallSet (δ := δ) (δ' := δ')))
    (hjoint : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r Φ (δ := δ) (δ' := δ'))
    (i : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hΦjet : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖iteratedCovGrad (I := I) g₀ r 2 i (Φ s)‖ ^ 2 ≤ B ^ 2) :
    ‖iteratedCovGrad (I := I) g₀ r 2 i
        (pathIntegralCoeffField (I := I) (M := M) g₀ r 2 Φ
          (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hjoint)‖ ^ 2 ≤ B ^ 2 := by
  classical
  set S : Set ℝ :=
    DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedSmallSet
      (δ := δ) (δ' := δ') with hS_def
  have hjointC : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r 2 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r 2 ℝ E)
        (E := fun z : M => TensorRSSpace r 2 I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S) := hjoint
  have hji : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r (2 + i) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (2 + i) ℝ E)
        (E := fun z : M => TensorRSSpace r (2 + i) I z) q.1
        ((iteratedCovGrad (I := I) g₀ r 2 i (Φ q.2)).toSection q.1))
      ((Set.univ : Set M) ×ˢ S) :=
    dscr_iteratedCovGrad_jointSmooth (I := I) g₀ r 2 i Φ S hjointC
  have hcomm : iteratedCovGrad (I := I) g₀ r 2 i
      (pathIntegralCoeffField (I := I) (M := M) g₀ r 2 Φ S hSopen hSI hjoint) =
      pathIntegralCoeffField (I := I) (M := M) g₀ r (2 + i)
        (fun t => iteratedCovGrad (I := I) g₀ r 2 i (Φ t)) S hSopen hSI hji :=
    dscr_iteratedCovGrad_pathIntegral_comm (I := I) g₀ r 2 i Φ S hSopen hSI hjointC hji
  rw [hcomm]
  have hci : ∀ x : M, ContinuousOn (fun t : ℝ =>
      TensorRSSpace.toModel ((iteratedCovGrad (I := I) g₀ r 2 i (Φ t)).toSection x))
      (Set.Icc (0 : ℝ) 1) := by
    intro x
    exact (DifferentialGeometry.PDE.DeTurck.RicciLinearization.jointContMDiff_toModel_continuous_slice
      (I := I) g₀ r (2 + i)
      (fun t => iteratedCovGrad (I := I) g₀ r 2 i (Φ t)) S hji x).mono
      (by rw [← Set.uIcc_of_le (zero_le_one (α := ℝ))]; exact hSI)
  have hri : ContinuousOn (fun p : ℝ × M =>
      riemannianFiberNormSq (I := I) (M := M) g₀ r (2 + i) p.2
        ((iteratedCovGrad (I := I) g₀ r 2 i (Φ p.1)).toSection p.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) :=
    dscr_rfns_jointContinuous (I := I) g₀ r (2 + i)
      (fun t => iteratedCovGrad (I := I) g₀ r 2 i (Φ t)) S
      (by rw [← Set.uIcc_of_le (zero_le_one (α := ℝ))]; exact hSI) hji
  have hL2 := tensorL2NormSq_pathIntegralCoeffField_le_intervalIntegral_normSq
    (I := I) (M := M) g₀ r (2 + i)
    (fun t => iteratedCovGrad (I := I) g₀ r 2 i (Φ t)) S hSopen hSI hji hci hri
  refine le_trans hL2 ?_
  have hmono : (∫ t in (0 : ℝ)..1, ‖iteratedCovGrad (I := I) g₀ r 2 i (Φ t)‖ ^ 2) ≤
      ∫ _t in (0 : ℝ)..1, B ^ 2 := by
    refine intervalIntegral.integral_mono_on (by norm_num) ?_ intervalIntegrable_const ?_
    · have hFcont : ContinuousOn (fun p : ℝ × M =>
          riemannianFiberNormSq (I := I) (M := M) g₀ r (2 + i) p.2
            ((iteratedCovGrad (I := I) g₀ r 2 i (Φ p.1)).toSection p.2))
          (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) := hri
      letI : MeasurableSpace E := borel E
      haveI : BorelSpace E := ⟨rfl⟩
      letI : MeasurableSpace M := borel M
      haveI : BorelSpace M := ⟨rfl⟩
      set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
      haveI : IsFiniteMeasure μ :=
        riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
      have hnormsq : ∀ t : ℝ,
          ‖iteratedCovGrad (I := I) g₀ r 2 i (Φ t)‖ ^ 2 =
            ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r (2 + i) x
              ((iteratedCovGrad (I := I) g₀ r 2 i (Φ t)).toSection x) ∂μ := by
        intro t
        rw [SmoothCcTensor.norm_def]
        have hsec : (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
              (r := r) (s := 2 + i) (x := x)
              ((iteratedCovGrad (I := I) g₀ r 2 i (Φ t)).toSection x)) =
            (iteratedCovGrad (I := I) g₀ r 2 i (Φ t)).toFun := by
          funext x
          rw [SmoothCcTensor.toFun_apply]
        rw [← hsec,
          tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ r (2 + i)
            (fun x => (iteratedCovGrad (I := I) g₀ r 2 i (Φ t)).toSection x)]
      have hcontInt : ContinuousOn (fun t : ℝ =>
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r (2 + i) x
            ((iteratedCovGrad (I := I) g₀ r 2 i (Φ t)).toSection x) ∂μ)
          (Set.Icc (0 : ℝ) 1) :=
        continuousOn_integral_of_compact_support (μ := μ) isCompact_univ hFcont
          (fun _ x _ hx => absurd (Set.mem_univ x) hx)
      have heq : (fun t : ℝ => ‖iteratedCovGrad (I := I) g₀ r 2 i (Φ t)‖ ^ 2) =
          fun t : ℝ => ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r (2 + i) x
            ((iteratedCovGrad (I := I) g₀ r 2 i (Φ t)).toSection x) ∂μ := funext hnormsq
      rw [heq]
      exact hcontInt.intervalIntegrable_of_Icc (by norm_num)
    · exact fun t ht => hΦjet t ht
  refine le_trans hmono ?_
  rw [intervalIntegral.integral_const]
  simp

end

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem pje_icg_smul (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) =
      c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma pje_rfns_toSection_smul (g : SmoothRiemannianMetric I M) (r s : ℕ)
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

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
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
  exact rfns_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 4 2 R ρ i x

set_option maxHeartbeats 25600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
open DifferentialGeometry.PDE.DeTurck.RicciLinearization in
open DifferentialGeometry.Integral.Measure in
theorem exists_deTurckPhiTotPathIntegral_sub_background_coeffJetEnvelope_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2),
        (∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T₀ x v w = ccTensorBilin (I := I) g₀ T₀ x w v) →
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
    rfns_iteratedCovGrad_gInvDiffSlotCoeff_diagonalProductGrid_le (I := I) (M := M) g₀
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
  show ‖iteratedCovGrad (I := I) g₀ 4 2 i
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
    have hj2 := kscr_phiMet_realizedFam_jointSmooth (I := I) (M := M) g₀ g_bg T₀
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
    have hdev : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
              (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
                (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s) -
            deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ^ 2 ≤
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
      have hδP : gFibreOpBound (I := I) (M := M) g₀
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
                pje_rfns_toSection_smul (I := I) (M := M) g₀ 0 (2 + e m) s
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
          kscr_reindexCoeffGen_sub (I := I) (M := M) g₀ _ _
            (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA),
          kscr_reindexCoeffGen_sub (I := I) (M := M) g₀ _ _
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
        nlinarith [htri,
          norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
            (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₁ -
              deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)),
          norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA))),
          norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT))),
          norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
            (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
              - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)),
          sq_nonneg (‖iteratedCovGrad (I := I) g₀ 4 2 i
              (reindexCoeffGen (I := I) (M := M) g₀ 4 2
                (traceHessianCoeff (I := I) (M := M) g₀ g₁
                  - traceHessianCoeff (I := I) (M := M) g₀ g₀)
                (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA))‖ -
            ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (reindexCoeffGen (I := I) (M := M) g₀ 4 2
                (traceHessianCoeff (I := I) (M := M) g₀ g₁
                  - traceHessianCoeff (I := I) (M := M) g₀ g₀)
                (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT))‖),
          sq_nonneg (‖iteratedCovGrad (I := I) g₀ 4 2 i
              (reindexCoeffGen (I := I) (M := M) g₀ 4 2
                (traceHessianCoeff (I := I) (M := M) g₀ g₁
                  - traceHessianCoeff (I := I) (M := M) g₀ g₀)
                (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA))‖ -
            2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
                - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)‖),
          sq_nonneg (‖iteratedCovGrad (I := I) g₀ 4 2 i
              (reindexCoeffGen (I := I) (M := M) g₀ 4 2
                (traceHessianCoeff (I := I) (M := M) g₀ g₁
                  - traceHessianCoeff (I := I) (M := M) g₀ g₀)
                (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT))‖ -
            2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
                - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)‖)]
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
            nlinarith [hth, hr]
        _ ≤ (6 * Cth i + 12 * Cr i) * ((∑ j ∈ Finset.range (i + 1), (Klo j + Cg j * Kg j)) *
              (1 + ∑ l ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left hslotSum
              (by have := hCth_nn i; have := hCr_nn i; linarith)
        _ = KdevF i * (1 + ∑ l ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
            simp only [hKdevF_def]; ring
    have hbare : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
            (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
              (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s))‖ ^ 2 ≤
        (2 * KdevF i + 2 * cB i) * (1 + ∑ l ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
      intro s hs
      have hsplit1 : ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
            (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
              (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s))‖ ≤
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
                (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
                  (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s) -
              deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ +
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ := by
        have hid : deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
            (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
              (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s) =
            (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
                (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
                  (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s) -
              deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀) +
              deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ := (sub_add_cancel _ _).symm
        calc ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
                (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
                  (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s))‖
            = ‖iteratedCovGrad (I := I) g₀ 4 2 i
                ((deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
                    (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
                      (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s) -
                  deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀) +
                  deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ := by rw [← hid]
          _ = ‖iteratedCovGrad (I := I) g₀ 4 2 i
                (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
                    (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
                      (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s) -
                  deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀) +
                iteratedCovGrad (I := I) g₀ 4 2 i
                  (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ := by
              rw [iteratedCovGrad_add]
          _ ≤ _ := norm_add_le _ _
      have hd := hdev s hs
      have hcBi : cB i = ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ^ 2 := rfl
      have hcmul : cB i * 1 ≤ cB i * (1 + ∑ l ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h1S_ge (hcB_nn i)
      nlinarith [hsplit1, hd, hcBi, hcmul,
        norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
            (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
              (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s))),
        norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
              (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
                (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s) -
            deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)),
        norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)),
        sq_nonneg (‖iteratedCovGrad (I := I) g₀ 4 2 i
            (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
                (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
                  (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s) -
              deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ -
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖)]
    have hprod2_nn : (0 : ℝ) ≤ (2 * KdevF i + 2 * cB i) * (1 + ∑ l ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) :=
      mul_nonneg (by have := hKdevF_nn i; have := hcB_nn i; linarith) h1S_nn
    have htower := armField_pathIntegral_jetL2_perOrder_le (I := I) (M := M) g₀ 4
      (fun s => deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
        (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
          (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s))
      hSI hSopen hj2 i
      (B := Real.sqrt ((2 * KdevF i + 2 * cB i) * (1 + ∑ l ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2)))
      (Real.sqrt_nonneg _)
      (fun s hs => by rw [Real.sq_sqrt hprod2_nn]; exact hbare s hs)
    rw [Real.sq_sqrt hprod2_nn] at htower
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
        pathIntegralCoeffField (I := I) (M := M) g₀ 4 2
          (fun s => deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
            (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
              (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s))
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
      nlinarith [h,
        norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
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
            deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)),
        norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
            (0 : SmoothCcTensor g₀ 0 2)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
              (by
                rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                    from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                  tensorHs_norm_smul]
                simpa using hR₀)))),
        norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)),
        sq_nonneg (‖iteratedCovGrad (I := I) g₀ 4 2 i
            (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
              (0 : SmoothCcTensor g₀ 0 2)
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
              (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                (by
                  rw [show (0 : SmoothCcTensor g₀ 0 2) =
                      (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                      from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                    tensorHs_norm_smul]
                  simpa using hR₀)))‖ -
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖)]
    have hcmul : cB i * 1 ≤ cB i * (1 + ∑ l ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h1S_ge (hcB_nn i)
    nlinarith [hsplit, htower', hcmul, hKdevF_nn i, hcB_nn i, h1S_nn, hS_nn]

theorem exists_deTurckPhiTotPathIntegral_sub_background_sub_principalCometricCoeff_coeffJetEnvelope_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2),
        (∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T₀ x v w = ccTensorBilin (I := I) g₀ T₀ x w v) →
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

theorem exists_deTurckPhiTotPathIntegral_sub_background_sub_principalCometricCoeff_fibreSmall_coeffJetEnvelope
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ εCD : ℝ, 0 ≤ εCD ∧
      (0 ≤ δ → εCD ≤ 3 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) ∧
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2),
        (∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T₀ x v w = ccTensorBilin (I := I) g₀ T₀ x w v) →
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

set_option maxHeartbeats 1000000 in
theorem exists_deTurckSmoothRemainderDiff_sub_principalCometricArm_threeArmAppCc_endpointResidual_coeffJetEnvelope
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
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
          ccTensorBilin (I := I) g₀ T₀ x v w = ccTensorBilin (I := I) g₀ T₀ x w v) →
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
            appCc (I := I) (M := M) g₀ (2 + 0) 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 T₀) +
              appCc (I := I) (M := M) g₀ (2 + 1) 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 T₀) +
              appCc (I := I) (M := M) g₀ (2 + 2) 2
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
        appCc (I := I) (M := M) g₀ (2 + 0) 2 C₀k (iteratedCovGrad (I := I) g₀ 0 2 0 T₀) +
          appCc (I := I) (M := M) g₀ (2 + 1) 2 C₁k (iteratedCovGrad (I := I) g₀ 0 2 1 T₀) +
          appCc (I := I) (M := M) g₀ (2 + 2) 2
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
          appCc (I := I) (M := M) g₀ (2 + 2) 2 C₂r (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) :=
      hidArm
    have hfold := hK₀fold T₀ hTsymm
    have hfold' : appCc (I := I) (M := M) g₀ (2 + 2) 2
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)
          (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) -
        appCc (I := I) (M := M) g₀ (2 + 2) 2
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
            (I := I) (M := M) g₀ g₀)
          (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) =
        appCc (I := I) (M := M) g₀ (2 + 0) 2 K₀ (iteratedCovGrad (I := I) g₀ 0 2 0 T₀) := by
      rw [← appCc_sub_left]
      exact hfold
    have hlift : rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀ =
        appCc (I := I) (M := M) g₀ (2 + 2) 2
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
            (I := I) (M := M) g₀ g₀)
          (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) := by
      apply smoothCcTensor_ext_of_unitModel
      intro x
      apply ContinuousMultilinearMap.ext
      intro v
      exact
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.rawTensorConnLapSmooth_eq_appCc_cometricDoubleTrace
          (I := I) (M := M) g₀ T₀ x v
    have hArm : deTurckPrincipalCometricArm (I := I) (M := M) g₀
        (tensorSectionRealizeMetric (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre T₀ hball)) T₀ =
        appCc (I := I) (M := M) g₀ (2 + 2) 2
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
    have hn := norm_add_le (iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀k)
      (iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀)
    have hAB : 0 ≤ ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀k +
        iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀‖ := norm_nonneg _
    have htri : ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀k +
          iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀‖ ^ 2 ≤
        2 * ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀k‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀‖ ^ 2 := by
      nlinarith [sq_nonneg (‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀k‖ -
        ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀‖),
        mul_le_mul hn hn hAB (by positivity), norm_nonneg
          (iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀k), norm_nonneg
          (iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀)]
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
    nlinarith [hD, hSig_nn, sq_nonneg ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀‖,
      hKc1_nn i, hKW, hεX]
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

set_option maxHeartbeats 1000000 in
theorem exists_deTurckSmoothRemainderDiff_sub_principalCometricArm_threeArmAppCc_coeffJetEnvelope
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
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
          ccTensorBilin (I := I) g₀ T₀ x v w = ccTensorBilin (I := I) g₀ T₀ x w v) →
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
            appCc (I := I) (M := M) g₀ (2 + 0) 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 T₀) +
              appCc (I := I) (M := M) g₀ (2 + 1) 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 T₀) +
              appCc (I := I) (M := M) g₀ (2 + 2) 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) ∧
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
    exists_deTurckPhiTotPathIntegral_sub_background_sub_principalCometricCoeff_fibreSmall_coeffJetEnvelope
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  obtain ⟨εCr, hεCr_nn, hεCr_cap, Kc1, hKc1_nn, εa, hεa_nn, hεa_cap, Λ1, hΛ1_nn, hK1⟩ :=
    exists_deTurckSmoothRemainderDiff_sub_principalCometricArm_threeArmAppCc_endpointResidual_coeffJetEnvelope
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
    have htri : ∀ A B : SmoothCcTensor g₀ (2 + 2) (2 + i),
        ‖A + B‖ ^ 2 ≤ 2 * ‖A‖ ^ 2 + 2 * ‖B‖ ^ 2 := by
      intro A B
      have hn := norm_add_le A B
      have hA := norm_nonneg A
      have hB := norm_nonneg B
      have hAB : 0 ≤ ‖A + B‖ := norm_nonneg _
      nlinarith [sq_nonneg (‖A‖ - ‖B‖), mul_le_mul hn hn hAB (by linarith)]
    refine le_trans (htri _ _) ?_
    have hD := hDenv i
    have hr := hC₂r_env i
    have hSig_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by
      have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (i + 2)) =>
        sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖)
      linarith
    have hKc1i := hKc1_nn i
    nlinarith [hD, hr, hSig_nn]

open DifferentialGeometry.Integral.Measure in
private theorem iteratedCovGrad_comp_l2_sq_eq_rs
    (g₀ : SmoothRiemannianMetric I M) (r s m l : ℕ) (W : SmoothCcTensor g₀ r s) :
    ‖iteratedCovGrad (I := I) g₀ r (s + m) l (iteratedCovGrad (I := I) g₀ r s m W)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ r s (m + l) W‖ ^ 2 := by
  have hbridgeL : ‖iteratedCovGrad (I := I) g₀ r (s + m) l
        (iteratedCovGrad (I := I) g₀ r s m W)‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r ((s + m) + l) x
        ((iteratedCovGrad (I := I) g₀ r (s + m) l
          (iteratedCovGrad (I := I) g₀ r s m W)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [SmoothCcTensor.norm_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ r
      ((s + m) + l)
      (iteratedCovGrad (I := I) g₀ r (s + m) l (iteratedCovGrad (I := I) g₀ r s m W))
  have hbridgeR : ‖iteratedCovGrad (I := I) g₀ r s (m + l) W‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r (s + (m + l)) x
        ((iteratedCovGrad (I := I) g₀ r s (m + l) W).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [SmoothCcTensor.norm_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ r
      (s + (m + l)) (iteratedCovGrad (I := I) g₀ r s (m + l) W)
  rw [hbridgeL, hbridgeR]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  have hrw := rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ r s m l W x
  simpa only [Nat.add_assoc] using hrw

theorem exists_appCc_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le_of_lowOrder
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) :
    ∃ Cm : ℕ → ℝ, (∀ q, 0 ≤ Cm q) ∧
      ∀ (m : ℕ), m ≤ 1 →
      ∀ (C : SmoothCcTensor g₀ (2 + m) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i C‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) →
        ∀ q : ℕ, q + (Module.finrank ℝ E / 2 + 3) ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (appCc (I := I) (M := M) g₀ (2 + m) 2 C
                (iteratedCovGrad (I := I) g₀ 0 2 m T₀))‖ ≤
            Cm q * Real.sqrt (∑ i ∈ Finset.range (q + 1 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
  classical
  have hrsub : ∀ k l : ℕ, k ≤ l → Finset.range k ⊆ Finset.range l :=
    fun k l hkl x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hkl)
  have hB2 : ∀ m i : ℕ, ∃ Csh : ℝ, 0 ≤ Csh ∧
      ∀ (T : SmoothCcTensor g₀ (2 + m) (2 + i)) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) (2 + i) x (T.toSection x) ≤
          Csh ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            ‖iteratedCovGrad (I := I) g₀ (2 + m) (2 + i) j T‖ ^ 2 :=
    fun m i =>
      exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
        (I := I) (M := M) g₀ (2 + m) (2 + i)
  choose Csh2 hCsh2_nn hCsh2 using hB2
  obtain ⟨C2, hC2_nn, hC2⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ (a + 2)
  set B : ℝ := C2 * R₀ with hB_def
  have hB_nn : 0 ≤ B := mul_nonneg hC2_nn hR₀
  set Lam : ℕ → ℕ → ℝ := fun m i => (Csh2 m i) ^ 2 *
    ((∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2), Kc (i + j)) * (1 + B ^ 2))
    with hLam_def
  have hLam_nn : ∀ m i, 0 ≤ Lam m i := by
    intro m i
    rw [hLam_def]
    have h1 : 0 ≤ ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2), Kc (i + j) :=
      Finset.sum_nonneg (fun j _ => hKc_nn _)
    have h2 : (0 : ℝ) ≤ 1 + B ^ 2 := by positivity
    exact mul_nonneg (sq_nonneg _) (mul_nonneg h1 h2)
  set D : ℕ → ℕ → ℝ := fun m q => Real.sqrt (appCcGdiag (E := E) q *
    ∑ i ∈ Finset.range (q + 1), Lam m i) * ((q : ℝ) + 1) with hD_def
  have hD_nn : ∀ m q, 0 ≤ D m q := by
    intro m q
    rw [hD_def]
    exact mul_nonneg (Real.sqrt_nonneg _) (by positivity)
  refine ⟨fun q => D 0 q + D 1 q, fun q => add_nonneg (hD_nn 0 q) (hD_nn 1 q), ?_⟩
  intro m hm C T₀ hball henv q hband
  set S : ℝ := ∑ i ∈ Finset.range (q + 1 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 with hS_def
  have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  set W : SmoothCcTensor g₀ 0 (2 + m) := iteratedCovGrad (I := I) g₀ 0 2 m T₀ with hW_def
  have hball_sq : (∑ i ∈ Finset.range (a + 2 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) ≤ B ^ 2 := by
    have hsq_le : ∑ i ∈ Finset.range (a + 2 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 ≤
        (∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖) ^ 2 := by
      have hnn : ∀ i ∈ Finset.range (a + 2 + 1),
          (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ := fun i _ => norm_nonneg _
      have hstep : ∀ i ∈ Finset.range (a + 2 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 ≤
            ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ *
              (∑ j ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖) := by
        intro i hi
        rw [sq]
        exact mul_le_mul_of_nonneg_left (Finset.single_le_sum hnn hi) (norm_nonneg _)
      refine le_trans (Finset.sum_le_sum hstep) ?_
      rw [← Finset.sum_mul, sq]
    refine le_trans hsq_le ?_
    have hjets : ∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ≤
        C2 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 2 : ℕ) : ℝ) T₀‖ := hC2 T₀
    have hcast : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 2 : ℕ) : ℝ) T₀‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [hcast] at hjets
    have hjets2 : ∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ≤
        B := by
      rw [hB_def]
      exact le_trans hjets (mul_le_mul_of_nonneg_left hball hC2_nn)
    have hsum_nn : 0 ≤ ∑ i ∈ Finset.range (a + 2 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ :=
      Finset.sum_nonneg (fun i _ => norm_nonneg _)
    exact pow_le_pow_left₀ hsum_nn hjets2 2
  have hCoeff : ∀ i : ℕ, i ≤ q → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) (2 + i) x
        ((iteratedCovGrad (I := I) g₀ (2 + m) 2 i C).toSection x) ≤ Lam m i := by
    intro i hi x
    refine le_trans (hCsh2 m i (iteratedCovGrad (I := I) g₀ (2 + m) 2 i C) x) ?_
    rw [hLam_def]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    have hterm : ∀ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
        ‖iteratedCovGrad (I := I) g₀ (2 + m) (2 + i) j
          (iteratedCovGrad (I := I) g₀ (2 + m) 2 i C)‖ ^ 2 ≤ Kc (i + j) * (1 + B ^ 2) := by
      intro j hj
      rw [iteratedCovGrad_comp_l2_sq_eq_rs (I := I) g₀ (2 + m) 2 i j C]
      refine le_trans (henv (i + j)) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hKc_nn _)
      have hjw : j < Module.finrank ℝ E / 2 + 2 := Finset.mem_range.mp hj
      have hwin : ∑ l ∈ Finset.range (i + j + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 ≤
          ∑ l ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (hrsub _ _ (show i + j + 2 ≤ a + 2 + 1 by omega))
          (fun l _ _ => sq_nonneg _)
      linarith [hball_sq]
    calc ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
          ‖iteratedCovGrad (I := I) g₀ (2 + m) (2 + i) j
            (iteratedCovGrad (I := I) g₀ (2 + m) 2 i C)‖ ^ 2
        ≤ ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2), Kc (i + j) * (1 + B ^ 2) :=
          Finset.sum_le_sum hterm
      _ = (∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2), Kc (i + j)) * (1 + B ^ 2) := by
          rw [← Finset.sum_mul]
  set Cpt : ℝ := Real.sqrt (appCcGdiag (E := E) q *
    ∑ i ∈ Finset.range (q + 1), Lam m i) with hCpt_def
  have hGq_nn : 0 ≤ appCcGdiag (E := E) q := appCcGdiag_nonneg (E := E) q
  have hSumLam_nn : 0 ≤ ∑ i ∈ Finset.range (q + 1), Lam m i :=
    Finset.sum_nonneg (fun i _ => hLam_nn m i)
  have hCpt_nn : 0 ≤ Cpt := Real.sqrt_nonneg _
  have hCpt_sq : Cpt ^ 2 = appCcGdiag (E := E) q * ∑ i ∈ Finset.range (q + 1), Lam m i := by
    rw [hCpt_def]
    exact Real.sq_sqrt (mul_nonneg hGq_nn hSumLam_nn)
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 0 2 q
          (appCc (I := I) (M := M) g₀ (2 + m) 2 C W)).toSection x) ≤
      Cpt ^ 2 * ∑ l ∈ Finset.range (q + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
          ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l W).toSection x) := by
    intro x
    refine le_trans
      (appCc_iteratedCovGrad_diagonalProductGrid_le (I := I) (M := M) g₀ (2 + m) 2 C W q x) ?_
    rw [hCpt_sq]
    have hb_nn : 0 ≤ ∑ l ∈ Finset.range (q + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
          ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l W).toSection x) :=
      Finset.sum_nonneg (fun l _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ _ _ _ _)
    have hstep : ∀ i ∈ Finset.range (q + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) (2 + i) x
            ((iteratedCovGrad (I := I) g₀ (2 + m) 2 i C).toSection x) *
          (∑ l ∈ Finset.range (q + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l W).toSection x)) ≤
        Lam m i * ∑ l ∈ Finset.range (q + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l W).toSection x) := by
      intro i hi
      have hi' : i ≤ q := by
        have := Finset.mem_range.mp hi
        omega
      have hinner : (∑ l ∈ Finset.range (q + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l W).toSection x)) ≤
          ∑ l ∈ Finset.range (q + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l W).toSection x) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (hrsub _ _ (show q + 1 - i ≤ q + 1 by omega))
          (fun l _ _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ _ _ _ _)
      have hinner_nn : 0 ≤ ∑ l ∈ Finset.range (q + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l W).toSection x) :=
        Finset.sum_nonneg (fun l _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ _ _ _ _)
      exact mul_le_mul (hCoeff i hi' x) hinner hinner_nn (hLam_nn m i)
    refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hstep) hGq_nn) ?_
    rw [← Finset.sum_mul, ← mul_assoc]
  have hPTLP := tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum (I := I) (M := M) g₀
    (q + 1) (fun l => (2 + m) + l)
    (fun l => iteratedCovGrad (I := I) g₀ 0 (2 + m) l W)
    (iteratedCovGrad (I := I) g₀ 0 2 q (appCc (I := I) (M := M) g₀ (2 + m) 2 C W))
    Cpt hCpt_nn hpt
  have hWl : ∀ l ∈ Finset.range (q + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ≤ Real.sqrt S := by
    intro l hl
    have hl' : l ≤ q := by
      have := Finset.mem_range.mp hl
      omega
    have hsq : ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ^ 2 =
        ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) T₀‖ ^ 2 := by
      rw [hW_def]
      exact iteratedCovGrad_comp_l2_sq_eq_rs (I := I) g₀ 0 2 m l T₀
    have hin : ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) T₀‖ ^ 2 ≤ S := by
      rw [hS_def]
      exact Finset.single_le_sum
        (f := fun i => ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2)
        (fun i _ => sq_nonneg _)
        (Finset.mem_range.mpr (show m + l < q + 1 + 1 by omega))
    calc ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖
        = Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) T₀‖ ^ 2) := by rw [hsq]
      _ ≤ Real.sqrt S := Real.sqrt_le_sqrt hin
  have hsumW : ∑ l ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ≤
      ((q : ℝ) + 1) * Real.sqrt S := by
    have := Finset.sum_le_card_nsmul (Finset.range (q + 1))
      (fun l => ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖) (Real.sqrt S) hWl
    rw [Finset.card_range, nsmul_eq_mul] at this
    calc ∑ l ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖
        ≤ ((q + 1 : ℕ) : ℝ) * Real.sqrt S := this
      _ = ((q : ℝ) + 1) * Real.sqrt S := by push_cast; ring
  refine le_trans hPTLP ?_
  have hfin : Cpt * (∑ l ∈ Finset.range (q + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖) ≤ Cpt * (((q : ℝ) + 1) * Real.sqrt S) :=
    mul_le_mul_of_nonneg_left hsumW hCpt_nn
  refine le_trans hfin ?_
  have hDm : Cpt * (((q : ℝ) + 1) * Real.sqrt S) = D m q * Real.sqrt S := by
    rw [hD_def, hCpt_def]
    ring
  rw [hDm]
  have hDle : D m q ≤ D 0 q + D 1 q := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm with h | h
    · rw [h]; have := hD_nn 1 q; linarith
    · rw [h]; have := hD_nn 0 q; linarith
  exact mul_le_mul_of_nonneg_right hDle (Real.sqrt_nonneg _)

open DifferentialGeometry.Integral.Measure in
private theorem iteratedCovGrad_comp_l2_sq_eq
    (g₀ : SmoothRiemannianMetric I M) (m l : ℕ) (W : SmoothCcTensor g₀ 0 2) :
    ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l (iteratedCovGrad (I := I) g₀ 0 2 m W)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) W‖ ^ 2 := by
  have hbridgeL : ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
        (iteratedCovGrad (I := I) g₀ 0 2 m W)‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
        ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
          (iteratedCovGrad (I := I) g₀ 0 2 m W)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [SmoothCcTensor.norm_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ ((2 + m) + l)
      (iteratedCovGrad (I := I) g₀ 0 (2 + m) l (iteratedCovGrad (I := I) g₀ 0 2 m W))
  have hbridgeR : ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) W‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (m + l)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (m + l) W).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [SmoothCcTensor.norm_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ (2 + (m + l))
      (iteratedCovGrad (I := I) g₀ 0 2 (m + l) W)
  rw [hbridgeL, hbridgeR]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  have hrw := rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 m l W x
  simpa only [Nat.add_assoc] using hrw

open DifferentialGeometry.Integral.Measure in
private theorem iteratedCovGrad_comp_jetSum_le
    (g₀ : SmoothRiemannianMetric I M) (p m : ℕ) (W : SmoothCcTensor g₀ 0 2) :
    (∑ l ∈ Finset.range (p + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l (iteratedCovGrad (I := I) g₀ 0 2 m W)‖ ^ 2) ≤
      ∑ i ∈ Finset.range (p + m + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2 := by
  rw [show (∑ l ∈ Finset.range (p + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l (iteratedCovGrad (I := I) g₀ 0 2 m W)‖ ^ 2) =
      ∑ l ∈ Finset.range (p + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) W‖ ^ 2 from
    Finset.sum_congr rfl (fun l _ => iteratedCovGrad_comp_l2_sq_eq (I := I) g₀ m l W)]
  set f : ℕ → ℝ := fun i => ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2 with hf_def
  have hf_nn : ∀ i, 0 ≤ f i := fun i => sq_nonneg _
  have himg : (Finset.range (p + 1)).image (fun l => m + l) ⊆ Finset.range (p + m + 1) := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨l, hl, rfl⟩ := hi
    rw [Finset.mem_range] at hl ⊢
    omega
  have hinj : ∀ l₁ ∈ Finset.range (p + 1), ∀ l₂ ∈ Finset.range (p + 1),
      m + l₁ = m + l₂ → l₁ = l₂ := fun l₁ _ l₂ _ h => by omega
  calc (∑ l ∈ Finset.range (p + 1), f (m + l))
      = ∑ i ∈ (Finset.range (p + 1)).image (fun l => m + l), f i :=
        (Finset.sum_image hinj).symm
    _ ≤ ∑ i ∈ Finset.range (p + m + 1), f i :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun i _ _ => hf_nn i)

theorem exists_appCc_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le_of_highOrder
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) (Λ : ℝ) (hΛ_nn : 0 ≤ Λ) :
    ∃ Cm : ℕ → ℝ, (∀ q, 0 ≤ Cm q) ∧
      ∀ (m : ℕ), m ≤ 1 →
      ∀ (C : SmoothCcTensor g₀ (2 + m) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) 2 x (C.toSection x) ≤ Λ ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i C‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) →
        ∀ q : ℕ, a ≤ q + (Module.finrank ℝ E / 2 + 3) →
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (appCc (I := I) (M := M) g₀ (2 + m) 2 C
                (iteratedCovGrad (I := I) g₀ 0 2 m T₀))‖ ≤
            Cm q * Real.sqrt (∑ i ∈ Finset.range (q + 1 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
  classical
  have hrsub : ∀ k l : ℕ, k ≤ l → Finset.range k ⊆ Finset.range l :=
    fun k l hkl x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hkl)
  have hE : ∀ m q : ℕ, ∃ CE : ℝ, 0 ≤ CE ∧
      ∀ (Φ : SmoothCcTensor g₀ (2 + m) 2) (W : SmoothCcTensor g₀ 0 (2 + m)) (ΛΦ ΛW : ℝ),
        0 ≤ ΛΦ → 0 ≤ ΛW →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) 2 x (Φ.toSection x) ≤
          ΛΦ ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x (W.toSection x) ≤
          ΛW ^ 2) →
        ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (appCc (I := I) (M := M) g₀ (2 + m) 2 Φ W)‖ ^ 2 ≤
          CE * (ΛW ^ 2 * ∑ i ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Φ‖ ^ 2
              + ΛΦ ^ 2 * ∑ l ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ^ 2) :=
    fun m q => appCc_topOrder_l2_twoArm_mixed_le (I := I) (M := M) g₀ (2 + m) 2 q
  choose CE hCE_nn hCE using hE
  have hB : ∀ m : ℕ, ∃ Csh : ℝ, 0 ≤ Csh ∧
      ∀ (T : SmoothCcTensor g₀ 0 (2 + m)) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x (T.toSection x) ≤
          Csh ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) j T‖ ^ 2 :=
    fun m =>
      exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
        (I := I) (M := M) g₀ 0 (2 + m)
  choose Csh hCsh_nn hCsh using hB
  obtain ⟨C2, hC2_nn, hC2⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ (a + 2)
  set B : ℝ := C2 * R₀ with hB_def
  have hB_nn : 0 ≤ B := mul_nonneg hC2_nn hR₀
  set D : ℕ → ℕ → ℝ := fun m q => Real.sqrt (CE m q *
    ((Csh m) ^ 2 * (∑ i ∈ Finset.range (q + 1), Kc i) * (1 + B ^ 2) + Λ ^ 2)) with hD_def
  have hD_nn : ∀ m q, 0 ≤ D m q := fun m q => Real.sqrt_nonneg _
  refine ⟨fun q => D 0 q + D 1 q, fun q => add_nonneg (hD_nn 0 q) (hD_nn 1 q), ?_⟩
  intro m hm C T₀ hball hsup henv q hband
  set S : ℝ := ∑ i ∈ Finset.range (q + 1 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 with hS_def
  have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  set W : SmoothCcTensor g₀ 0 (2 + m) := iteratedCovGrad (I := I) g₀ 0 2 m T₀ with hW_def
  set SW : ℝ := ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) j W‖ ^ 2 with hSW_def
  have hSW_nn : 0 ≤ SW := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  set ΛW : ℝ := Csh m * Real.sqrt SW with hΛW_def
  have hΛW_nn : 0 ≤ ΛW := mul_nonneg (hCsh_nn m) (Real.sqrt_nonneg _)
  have hWsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
      (W.toSection x) ≤ ΛW ^ 2 := by
    intro x
    have h := hCsh m W x
    rw [hΛW_def, mul_pow, Real.sq_sqrt hSW_nn, hSW_def]
    exact h
  have hMain := hCE m q C W Λ ΛW hΛ_nn hΛW_nn hsup hWsup
  have hSW_case : SW ≤ ∑ i ∈ Finset.range (Module.finrank ℝ E / 2 + 1 + m + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 := by
    have h := iteratedCovGrad_comp_jetSum_le (I := I) g₀ (Module.finrank ℝ E / 2 + 1) m T₀
    rw [hSW_def, hW_def]
    exact h
  have hSW_le_S : SW ≤ S := by
    refine le_trans hSW_case ?_
    rw [hS_def]
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (hrsub _ _ (show Module.finrank ℝ E / 2 + 1 + m + 1 ≤ q + 1 + 1 by omega))
      (fun i _ _ => sq_nonneg _)
  have hSW_le_B : SW ≤ B ^ 2 := by
    refine le_trans hSW_case ?_
    have hsub : ∑ i ∈ Finset.range (Module.finrank ℝ E / 2 + 1 + m + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 ≤
        ∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (hrsub _ _ (show Module.finrank ℝ E / 2 + 1 + m + 1 ≤ a + 2 + 1 by omega))
        (fun i _ _ => sq_nonneg _)
    refine le_trans hsub ?_
    have hsq_le : ∑ i ∈ Finset.range (a + 2 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 ≤
        (∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖) ^ 2 := by
      have hnn : ∀ i ∈ Finset.range (a + 2 + 1),
          (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ := fun i _ => norm_nonneg _
      have hstep : ∀ i ∈ Finset.range (a + 2 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 ≤
            ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ *
              (∑ j ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖) := by
        intro i hi
        rw [sq]
        exact mul_le_mul_of_nonneg_left
          (Finset.single_le_sum hnn hi) (norm_nonneg _)
      refine le_trans (Finset.sum_le_sum hstep) ?_
      rw [← Finset.sum_mul, sq]
    refine le_trans hsq_le ?_
    have hjets : ∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ≤
        C2 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 2 : ℕ) : ℝ) T₀‖ := hC2 T₀
    have hcast : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 2 : ℕ) : ℝ) T₀‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [hcast] at hjets
    have hjets2 : ∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ≤
        B := by
      rw [hB_def]
      exact le_trans hjets (mul_le_mul_of_nonneg_left hball hC2_nn)
    have hsum_nn : 0 ≤ ∑ i ∈ Finset.range (a + 2 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ :=
      Finset.sum_nonneg (fun i _ => norm_nonneg _)
    exact pow_le_pow_left₀ hsum_nn hjets2 2
  have hSigC : ∑ i ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i C‖ ^ 2 ≤
      (∑ i ∈ Finset.range (q + 1), Kc i) * (1 + S) := by
    have hstep : ∀ i ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i C‖ ^ 2 ≤ Kc i * (1 + S) := by
      intro i hi
      rw [Finset.mem_range] at hi
      refine le_trans (henv i) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hKc_nn i)
      have hwin : ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 ≤
          S := by
        rw [hS_def]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (hrsub _ _ (show i + 2 ≤ q + 1 + 1 by omega))
          (fun j _ _ => sq_nonneg _)
      linarith
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [← Finset.sum_mul]
  have hSigW : ∑ l ∈ Finset.range (q + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ^ 2 ≤ S := by
    have := iteratedCovGrad_comp_jetSum_le (I := I) g₀ q m T₀
    rw [← hW_def] at this
    refine le_trans this ?_
    rw [hS_def]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (hrsub _ _ (show q + m + 1 ≤ q + 1 + 1 by omega))
      (fun i _ _ => sq_nonneg _)
  have hcore : ‖iteratedCovGrad (I := I) g₀ 0 2 q
      (appCc (I := I) (M := M) g₀ (2 + m) 2 C W)‖ ^ 2 ≤ (D m q) ^ 2 * S := by
    have hΛW_sq : ΛW ^ 2 = (Csh m) ^ 2 * SW := by
      rw [hΛW_def, mul_pow, Real.sq_sqrt hSW_nn]
    have h1 : ΛW ^ 2 * (∑ i ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i C‖ ^ 2) ≤
        (Csh m) ^ 2 * ((∑ i ∈ Finset.range (q + 1), Kc i) * (SW + SW * S)) := by
      rw [hΛW_sq]
      have hKcS_nn : 0 ≤ (∑ i ∈ Finset.range (q + 1), Kc i) :=
        Finset.sum_nonneg (fun i _ => hKc_nn i)
      calc (Csh m) ^ 2 * SW * (∑ i ∈ Finset.range (q + 1),
            ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i C‖ ^ 2)
          ≤ (Csh m) ^ 2 * SW * ((∑ i ∈ Finset.range (q + 1), Kc i) * (1 + S)) := by
            refine mul_le_mul_of_nonneg_left hSigC ?_
            positivity
        _ = (Csh m) ^ 2 * ((∑ i ∈ Finset.range (q + 1), Kc i) * (SW + SW * S)) := by ring
    have h2 : SW + SW * S ≤ (1 + B ^ 2) * S := by
      have ha' : SW * S ≤ B ^ 2 * S := mul_le_mul_of_nonneg_right hSW_le_B hS_nn
      have hb' : SW ≤ S := hSW_le_S
      have : (1 + B ^ 2) * S = S + B ^ 2 * S := by ring
      linarith
    have h3 : (Csh m) ^ 2 * ((∑ i ∈ Finset.range (q + 1), Kc i) * (SW + SW * S)) ≤
        (Csh m) ^ 2 * ((∑ i ∈ Finset.range (q + 1), Kc i) * ((1 + B ^ 2) * S)) := by
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      refine mul_le_mul_of_nonneg_left h2 ?_
      exact Finset.sum_nonneg (fun i _ => hKc_nn i)
    have h4 : Λ ^ 2 * (∑ l ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ^ 2) ≤ Λ ^ 2 * S :=
      mul_le_mul_of_nonneg_left hSigW (sq_nonneg _)
    have hD_sq : (D m q) ^ 2 = CE m q *
        ((Csh m) ^ 2 * (∑ i ∈ Finset.range (q + 1), Kc i) * (1 + B ^ 2) + Λ ^ 2) := by
      rw [hD_def]
      refine Real.sq_sqrt ?_
      have hKcS_nn : 0 ≤ ∑ i ∈ Finset.range (q + 1), Kc i :=
        Finset.sum_nonneg (fun i _ => hKc_nn i)
      have h6 : 0 ≤ (Csh m) ^ 2 * (∑ i ∈ Finset.range (q + 1), Kc i) * (1 + B ^ 2) := by
        refine mul_nonneg (mul_nonneg (sq_nonneg _) hKcS_nn) ?_
        have := sq_nonneg B
        linarith
      exact mul_nonneg (hCE_nn m q) (by linarith [sq_nonneg Λ])
    calc ‖iteratedCovGrad (I := I) g₀ 0 2 q
          (appCc (I := I) (M := M) g₀ (2 + m) 2 C W)‖ ^ 2
        ≤ CE m q * (ΛW ^ 2 * ∑ i ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i C‖ ^ 2
            + Λ ^ 2 * ∑ l ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ^ 2) := hMain
      _ ≤ CE m q * ((Csh m) ^ 2 * ((∑ i ∈ Finset.range (q + 1), Kc i) * ((1 + B ^ 2) * S))
            + Λ ^ 2 * S) := by
          refine mul_le_mul_of_nonneg_left ?_ (hCE_nn m q)
          have := le_trans h1 h3
          linarith
      _ = (CE m q * ((Csh m) ^ 2 * (∑ i ∈ Finset.range (q + 1), Kc i) * (1 + B ^ 2)
            + Λ ^ 2)) * S := by ring
      _ = (D m q) ^ 2 * S := by rw [hD_sq]
  have hfinal : ‖iteratedCovGrad (I := I) g₀ 0 2 q
      (appCc (I := I) (M := M) g₀ (2 + m) 2 C W)‖ ≤ D m q * Real.sqrt S := by
    have h1 : ‖iteratedCovGrad (I := I) g₀ 0 2 q
        (appCc (I := I) (M := M) g₀ (2 + m) 2 C W)‖ =
        Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 2 q
          (appCc (I := I) (M := M) g₀ (2 + m) 2 C W)‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    rw [h1]
    refine le_trans (Real.sqrt_le_sqrt hcore) ?_
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hD_nn m q)]
  refine le_trans hfinal ?_
  have hDle : D m q ≤ D 0 q + D 1 q := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm with h | h
    · rw [h]; have := hD_nn 1 q; linarith
    · rw [h]; have := hD_nn 0 q; linarith
  exact mul_le_mul_of_nonneg_right hDle (Real.sqrt_nonneg _)

theorem exists_appCc_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) (Λ : ℝ) (hΛ_nn : 0 ≤ Λ) :
    ∃ Cm : ℕ → ℝ, (∀ q, 0 ≤ Cm q) ∧
      ∀ (m : ℕ), m ≤ 1 →
      ∀ (C : SmoothCcTensor g₀ (2 + m) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) 2 x (C.toSection x) ≤ Λ ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i C‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) →
        ∀ q : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (appCc (I := I) (M := M) g₀ (2 + m) 2 C
                (iteratedCovGrad (I := I) g₀ 0 2 m T₀))‖ ≤
            Cm q * Real.sqrt (∑ i ∈ Finset.range (q + 1 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
  classical
  obtain ⟨CmA, hCmA_nn, hA⟩ :=
    exists_appCc_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le_of_lowOrder
      (I := I) (M := M) g₀ a ha_super hR₀ Kc hKc_nn
  obtain ⟨CmB, hCmB_nn, hB⟩ :=
    exists_appCc_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le_of_highOrder
      (I := I) (M := M) g₀ a ha_super hR₀ Kc hKc_nn Λ hΛ_nn
  refine ⟨fun q => CmA q + CmB q,
    fun q => add_nonneg (hCmA_nn q) (hCmB_nn q), ?_⟩
  intro m hm C T₀ hball hsup henv q
  have hsqrt_nn : 0 ≤ Real.sqrt (∑ i ∈ Finset.range (q + 1 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := Real.sqrt_nonneg _
  rcases le_total (q + (Module.finrank ℝ E / 2 + 3)) a with hband | hband
  · refine le_trans (hA m hm C T₀ hball henv q hband) ?_
    have := mul_le_mul_of_nonneg_right
      (show CmA q ≤ CmA q + CmB q by have := hCmB_nn q; linarith) hsqrt_nn
    linarith
  · refine le_trans (hB m hm C T₀ hball hsup henv q hband) ?_
    have := mul_le_mul_of_nonneg_right
      (show CmB q ≤ CmA q + CmB q by have := hCmA_nn q; linarith) hsqrt_nn
    linarith

set_option maxHeartbeats 1000000 in

theorem exists_deTurckSmoothRemainderDiff_sub_principalCometricArm_smallThirdArm_iteratedCovGrad_jet_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ εC : ℝ, 0 ≤ εC ∧
      (0 ≤ δ → εC ≤ 32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 * (δ / (1 - δ))) ∧
      (0 ≤ δ → εC ≤ 28 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) ∧
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
    ∃ εa : ℝ, 0 ≤ εa ∧
      2 * Real.sqrt (Module.finrank ℝ E) * εa ≤
        32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
          28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 ∧
    ∃ Λa : ℝ, 0 ≤ Λa ∧
    ∃ Clow : ℕ → ℝ, (∀ q, 0 ≤ Clow q) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2)
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T₀ x v w = ccTensorBilin (I := I) g₀ T₀ x w v)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ∃ (C₂ : SmoothCcTensor g₀ (2 + 2) 2) (C₀ : SmoothCcTensor g₀ (2 + 0) 2),
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x (C₂.toSection x) ≤ εC ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 0) 2 x (C₀.toSection x) ≤
              Λa ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
                εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) ∧
          ∀ q : ℕ,
            ‖iteratedCovGrad (I := I) g₀ 0 2 q
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
                      (hδ_fibre T₀ hball)) T₀ -
                  appCc (I := I) (M := M) g₀ (2 + 2) 2 C₂
                    (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) -
                  appCc (I := I) (M := M) g₀ (2 + 0) 2 C₀
                    (iteratedCovGrad (I := I) g₀ 0 2 0 T₀))‖ ≤
              Clow q * Real.sqrt (∑ i ∈ Finset.range (q + 1 + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
  classical
  obtain ⟨εC, hεC_nn, hεC_cap, hεC_cap', Kc, hKc_nn, εa, hεa_nn, hεa_cap, Λ, hΛ_nn, hL1⟩ :=
    exists_deTurckSmoothRemainderDiff_sub_principalCometricArm_threeArmAppCc_coeffJetEnvelope
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  obtain ⟨Cm, hCm_nn, hM2⟩ :=
    exists_appCc_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le
      (I := I) (M := M) g₀ a ha_super hR₀ Kc hKc_nn Λ hΛ_nn
  refine ⟨εC, hεC_nn, hεC_cap, hεC_cap', Kc, hKc_nn, εa, hεa_nn, hεa_cap, Λ, hΛ_nn,
    Cm, hCm_nn, fun T₀ hTsymm hball => ?_⟩
  obtain ⟨C₀, C₁, C₂, hid, hC₂sup, hC₀sup, hC₁sup, hC₀jet, hC₁jet, hC₂jet⟩ :=
    hL1 T₀ hTsymm hball
  refine ⟨C₂, C₀, hC₂sup, hC₂jet, hC₀sup, hC₀jet, fun q => ?_⟩
  have hsplit :
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
              (hδ_fibre T₀ hball)) T₀ -
          appCc (I := I) (M := M) g₀ (2 + 2) 2 C₂
            (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) -
          appCc (I := I) (M := M) g₀ (2 + 0) 2 C₀
            (iteratedCovGrad (I := I) g₀ 0 2 0 T₀)) =
        appCc (I := I) (M := M) g₀ (2 + 1) 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 T₀) := by
    rw [sub_eq_iff_eq_add, sub_eq_iff_eq_add, hid]
    abel
  rw [hsplit]
  exact hM2 1 (by omega) C₁ T₀ hball hC₁sup hC₁jet q

set_option maxHeartbeats 1000000 in

theorem exists_smoothCcToTensorHs_deTurckSmoothRemainderDiff_sub_principalCometricArm_smallThirdArm_tame_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ εC : ℝ, 0 ≤ εC ∧
      (0 ≤ δ → εC ≤ 32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 * (δ / (1 - δ))) ∧
      (0 ≤ δ → εC ≤ 28 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) ∧
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
    ∃ εa : ℝ, 0 ≤ εa ∧
      2 * Real.sqrt (Module.finrank ℝ E) * εa ≤
        32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
          28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 ∧
    ∃ Λa : ℝ, 0 ≤ Λa ∧
    ∃ Ctame : ℕ → ℝ, (∀ k, 0 ≤ Ctame k) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2)
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T₀ x v w = ccTensorBilin (I := I) g₀ T₀ x w v)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ∃ (C₂ : SmoothCcTensor g₀ (2 + 2) 2) (C₀ : SmoothCcTensor g₀ (2 + 0) 2),
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x (C₂.toSection x) ≤ εC ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 0) 2 x (C₀.toSection x) ≤
              Λa ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
                εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) ∧
          ∀ k : ℕ,
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
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
                      (hδ_fibre T₀ hball)) T₀ -
                  appCc (I := I) (M := M) g₀ (2 + 2) 2 C₂
                    (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) -
                  appCc (I := I) (M := M) g₀ (2 + 0) 2 C₀
                    (iteratedCovGrad (I := I) g₀ 0 2 0 T₀))‖ ≤
              Ctame k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖ := by
  classical
  obtain ⟨εC, hεC_nn, hεC_cap, hεC_cap', Kc, hKc_nn, εa, hεa_nn, hεa_cap, Λa, hΛa_nn,
    Clow, hClow_nn, hjet⟩ :=
    exists_deTurckSmoothRemainderDiff_sub_principalCometricArm_smallThirdArm_iteratedCovGrad_jet_le
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  obtain ⟨Ctame, hCtame_nn, hCtame⟩ :=
    exists_smoothCcToTensorHs_real_le_of_iteratedCovGrad_jet_window
      (I := I) (M := M) g₀ a (by omega) Clow hClow_nn
  refine ⟨εC, hεC_nn, hεC_cap, hεC_cap', Kc, hKc_nn, εa, hεa_nn, hεa_cap, Λa, hΛa_nn,
    Ctame, hCtame_nn, fun T₀ hTsymm hball => ?_⟩
  obtain ⟨C₂, C₀, hC₂sup, hC₂jet, hC₀sup, hC₀jet, hwin⟩ := hjet T₀ hTsymm hball
  exact ⟨C₂, C₀, hC₂sup, hC₂jet, hC₀sup, hC₀jet, fun k => hCtame k _ T₀ hwin⟩

set_option maxHeartbeats 1000000 in
theorem exists_smoothCcToTensorHs_appCc_fibreSmallCoeff_opNorm_le_zero
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (εC : ℝ) (hεC_nn : 0 ≤ εC) (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) :
    ∃ Cop : ℝ, 0 ≤ Cop ∧
      ∀ (C₂ : SmoothCcTensor g₀ (2 + 2) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x (C₂.toSection x) ≤ εC ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) →
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
            (appCc (I := I) (M := M) g₀ (2 + 2) 2 C₂
              (iteratedCovGrad (I := I) g₀ 0 2 2 T₀))‖ ≤
          deTurckArmFibreConst (Module.finrank ℝ E) * εC *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ +
            Cop * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖ := by
  classical
  obtain ⟨Ccross, hCcross_nn, hcross⟩ := exists_Ccross_for_secondCovGrad (I := I) (M := M) g₀
  obtain ⟨C21, hC21_nn, hC21⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ 1
  refine ⟨εC * Real.sqrt Ccross * (2 * C21),
    mul_nonneg (mul_nonneg hεC_nn (Real.sqrt_nonneg _)) (by linarith), ?_⟩
  intro C₂ T₀ hball hsup hjets
  set W₂ : SmoothCcTensor g₀ 0 (2 + 2) := iteratedCovGrad (I := I) g₀ 0 2 2 T₀ with hW₂_def
  set P : SmoothCcTensor g₀ 0 2 :=
    appCc (I := I) (M := M) g₀ (2 + 2) 2 C₂ W₂ with hP_def
  have hLHS_eq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ) P‖ = ‖P‖ := by
    rw [smoothCcToTensorHs_zero_norm_eq (I := I) (M := M) g₀ P, SmoothCcTensor.norm_toL2]
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤
        εC ^ 2 * ∑ i ∈ Finset.range 1,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 2) x (W₂.toSection x) := by
    intro x
    have hgrid := appCc_iteratedCovGrad_diagonalProductGrid_le
      (I := I) (M := M) g₀ (2 + 2) 2 C₂ W₂ 0 x
    rw [show Finset.range (0 + 1) = Finset.range 1 from rfl, Finset.sum_range_one] at hgrid
    rw [show Finset.range (0 + 1 - 0) = Finset.range 1 from rfl,
      Finset.sum_range_one] at hgrid
    rw [show appCcGdiag (E := E) 0 = 1 by simp [appCcGdiag], one_mul] at hgrid
    rw [Finset.sum_range_one]
    have hW_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 2) x
        (W₂.toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ _ _ _ _
    refine le_trans hgrid ?_
    exact mul_le_mul_of_nonneg_right (hsup x) hW_nn
  have hprod : ‖P‖ ≤ εC * ‖W₂‖ := by
    have hPTLP := tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum (I := I) (M := M) g₀
      1 (fun _ => 2 + 2) (fun _ => W₂) P εC hεC_nn hpt
    rw [Finset.sum_range_one] at hPTLP
    exact hPTLP
  clear_value W₂ P
  have hweitz := weitzenbock_integrated_covGrad_l2_normSq (I := I) (M := M) g₀ 2 T₀
  have hcrossT := hcross T₀
  set nHess : ℝ := tensorL2Norm (I := I) (M := M) g₀ 0 (2 + 1 + 1)
    (covGrad (I := I) (M := M) g₀ 0 (2 + 1)
      (covGrad (I := I) (M := M) g₀ 0 2 T₀)).toFun with hnHess_def
  set nGrad : ℝ := tensorL2Norm (I := I) (M := M) g₀ 0 (2 + 1)
    (covGrad (I := I) (M := M) g₀ 0 2 T₀).toFun with hnGrad_def
  set nLap : ℝ := tensorL2Norm (I := I) (M := M) g₀ 0 2
    (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀).toFun with hnLap_def
  set nT : ℝ := tensorL2Norm (I := I) (M := M) g₀ 0 2 T₀.toFun with hnT_def
  have hnHess_nn : 0 ≤ nHess := tensorL2Norm_nonneg (I := I) (M := M) g₀ 0 (2 + 1 + 1) _
  have hnGrad_nn : 0 ≤ nGrad := tensorL2Norm_nonneg (I := I) (M := M) g₀ 0 (2 + 1) _
  have hnLap_nn : 0 ≤ nLap := tensorL2Norm_nonneg (I := I) (M := M) g₀ 0 2 _
  have hnT_nn : 0 ≤ nT := tensorL2Norm_nonneg (I := I) (M := M) g₀ 0 2 _
  clear_value nHess nGrad nLap nT
  have hW₂_norm : ‖W₂‖ = nHess := by
    have hW2eq : W₂ = covGrad (I := I) (M := M) g₀ 0 (2 + 1)
        (covGrad (I := I) (M := M) g₀ 0 2 T₀) := by
      rw [hW₂_def]
      rw [iteratedCovGrad_succ (I := I) (M := M) g₀ 0 2 1 T₀,
        iteratedCovGrad_succ (I := I) (M := M) g₀ 0 2 0 T₀,
        iteratedCovGrad_zero (I := I) (M := M) g₀ 0 2 T₀]
    rw [hW2eq, SmoothCcTensor.norm_def]
    exact hnHess_def.symm
  have hstep1 : nHess ^ 2 ≤ nLap ^ 2 + Ccross * (nGrad ^ 2 + nT * nGrad) := by
    linarith [hweitz, hcrossT]
  have hstep2 : nHess ^ 2 ≤ (nLap + Real.sqrt Ccross * (nGrad + nT)) ^ 2 := by
    have hsq : Real.sqrt Ccross ^ 2 = Ccross := Real.sq_sqrt hCcross_nn
    have hexp : (nLap + Real.sqrt Ccross * (nGrad + nT)) ^ 2 =
        nLap ^ 2 + 2 * nLap * (Real.sqrt Ccross * (nGrad + nT)) +
          Ccross * (nGrad + nT) ^ 2 := by
      rw [show (nLap + Real.sqrt Ccross * (nGrad + nT)) ^ 2 =
        nLap ^ 2 + 2 * nLap * (Real.sqrt Ccross * (nGrad + nT)) +
          Real.sqrt Ccross ^ 2 * (nGrad + nT) ^ 2 by ring, hsq]
    rw [hexp]
    have hc1 : 0 ≤ 2 * nLap * (Real.sqrt Ccross * (nGrad + nT)) := by positivity
    have hc2 : nGrad ^ 2 + nT * nGrad ≤ (nGrad + nT) ^ 2 := by nlinarith
    have hc3 : Ccross * (nGrad ^ 2 + nT * nGrad) ≤ Ccross * (nGrad + nT) ^ 2 :=
      mul_le_mul_of_nonneg_left hc2 hCcross_nn
    linarith [hstep1]
  have hHess_le : nHess ≤ nLap + Real.sqrt Ccross * (nGrad + nT) := by
    have hrhs_nn : 0 ≤ nLap + Real.sqrt Ccross * (nGrad + nT) := by positivity
    calc nHess = Real.sqrt (nHess ^ 2) := (Real.sqrt_sq hnHess_nn).symm
      _ ≤ Real.sqrt ((nLap + Real.sqrt Ccross * (nGrad + nT)) ^ 2) :=
          Real.sqrt_le_sqrt hstep2
      _ = nLap + Real.sqrt Ccross * (nGrad + nT) := Real.sqrt_sq hrhs_nn
  have hLap_le : nLap ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ := by
    have h1 : nLap = ‖rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀‖ := by
      rw [hnLap_def, SmoothCcTensor.norm_def]
    have h2 : ‖rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ := by
      rw [smoothCcToTensorHs_zero_norm_eq, SmoothCcTensor.norm_toL2]
    have h3 := smoothCcToTensorHs_rawTensorConnLapSmooth_le (I := I) (M := M) g₀ (0 : ℝ) T₀
    have h4 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℝ) + 2) T₀‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by norm_num) T₀
    rw [h1, h2]
    rw [h4] at h3
    exact h3
  have hjets1 : ∀ j : ℕ, j < 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
        C21 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖ := by
    intro j hj
    have hsum := hC21 T₀
    have hcast : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by norm_num) T₀
    rw [hcast] at hsum
    refine le_trans ?_ hsum
    exact Finset.single_le_sum
      (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖)
      (fun i _ => norm_nonneg _) (Finset.mem_range.mpr hj)
  have hnT_le : nT ≤ C21 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖ := by
    have h0 : nT = ‖iteratedCovGrad (I := I) g₀ 0 2 0 T₀‖ := by
      rw [hnT_def, iteratedCovGrad_zero (I := I) (M := M) g₀ 0 2 T₀,
        SmoothCcTensor.norm_def]
    rw [h0]
    exact hjets1 0 (by norm_num)
  have hnGrad_le : nGrad ≤ C21 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖ := by
    have h1 : iteratedCovGrad (I := I) g₀ 0 2 1 T₀ =
        covGrad (I := I) (M := M) g₀ 0 2 T₀ := by
      rw [iteratedCovGrad_succ (I := I) (M := M) g₀ 0 2 0 T₀,
        iteratedCovGrad_zero (I := I) (M := M) g₀ 0 2 T₀]
    have h0 : nGrad = ‖iteratedCovGrad (I := I) g₀ 0 2 1 T₀‖ := by
      rw [hnGrad_def, h1, SmoothCcTensor.norm_def]
    rw [h0]
    exact hjets1 1 (by norm_num)
  have hfibre1 : (1 : ℝ) ≤ deTurckArmFibreConst (Module.finrank ℝ E) :=
    one_le_deTurckArmFibreConst (Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Module.finrank ℝ E)))
  have hHs2_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ := norm_nonneg _
  have hHs1_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖ := norm_nonneg _
  have hchain : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ) P‖ ≤
      εC * (‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ +
        Real.sqrt Ccross * (2 * C21 *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖)) := by
    rw [hLHS_eq]
    refine le_trans hprod ?_
    rw [hW₂_norm]
    refine le_trans (mul_le_mul_of_nonneg_left hHess_le hεC_nn) ?_
    refine mul_le_mul_of_nonneg_left ?_ hεC_nn
    have hGT : nGrad + nT ≤ 2 * C21 *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖ := by
      linarith [hnGrad_le, hnT_le]
    have := mul_le_mul_of_nonneg_left hGT (Real.sqrt_nonneg Ccross)
    linarith [hLap_le]
  refine le_trans hchain ?_
  have hexpand : εC * (‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ +
      Real.sqrt Ccross * (2 * C21 *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖)) =
      εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ +
        εC * Real.sqrt Ccross * (2 * C21) *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖ := by ring
  rw [hexpand]
  have h1 : εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ ≤
      deTurckArmFibreConst (Module.finrank ℝ E) * εC *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ := by
    have h2 : (1 : ℝ) * εC ≤ deTurckArmFibreConst (Module.finrank ℝ E) * εC :=
      mul_le_mul_of_nonneg_right hfibre1 hεC_nn
    have h3 := mul_le_mul_of_nonneg_right h2 hHs2_nn
    calc εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖
        = 1 * εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ := by ring
      _ ≤ deTurckArmFibreConst (Module.finrank ℝ E) * εC *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ := h3
  linarith [h1]

theorem exists_smoothCcToTensorHs_appCc_fibreSmallCoeff_opNorm_le_succ
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (εC : ℝ) (hεC_nn : 0 ≤ εC) (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) :
    ∃ Cop : ℕ → ℝ, (∀ m, 0 ≤ Cop m) ∧
      ∀ (C₂ : SmoothCcTensor g₀ (2 + 2) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x (C₂.toSection x) ≤ εC ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) →
        ∀ m : ℕ,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1)
              (appCc (I := I) (M := M) g₀ (2 + 2) 2 C₂
                (iteratedCovGrad (I := I) g₀ 0 2 2 T₀))‖ ≤
            deTurckArmFibreConst (Module.finrank ℝ E) * εC *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ +
              Cop m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ := by
  classical
  obtain ⟨Clower, hClower_nn, hfam⟩ :=
    exists_appCc_secondCovGrad_fibreSmallCoeff_Hs_family_le (I := I) (M := M) g₀ a
      (by omega) hR₀ εC hεC_nn Kc hKc_nn
  refine ⟨fun m => Clower (m + 1), fun m => hClower_nn (m + 1), ?_⟩
  intro C₂ T₀ hball hsup hjets m
  have hbase := hfam C₂ T₀ hball hsup hjets (m + 1) T₀
    ⟨0, (oneMinusConnLapSmoothIter_zero (I := I) (M := M) (T := T₀)).symm⟩
  have hΔ : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m + 1 : ℕ) : ℝ)
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ := by
    have h1 := smoothCcToTensorHs_rawTensorConnLapSmooth_le (I := I) (M := M) g₀
      (((m + 1 : ℕ) : ℝ)) T₀
    have h2 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((m + 1 : ℕ) : ℝ) + 2) T₀‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [h2] at h1
    exact h1
  have hcastL : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m + 1 : ℕ) : ℝ)
      (appCc (I := I) (M := M) g₀ (2 + 2) 2 C₂
        (iteratedCovGrad (I := I) g₀ 0 2 2 T₀))‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1)
        (appCc (I := I) (M := M) g₀ (2 + 2) 2 C₂
          (iteratedCovGrad (I := I) g₀ 0 2 2 T₀))‖ :=
    smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) _
  have hcastQ : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m + 1 + 1 : ℕ) : ℝ) T₀‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ :=
    smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
  rw [hcastL, hcastQ] at hbase
  have hfibre1 : (1 : ℝ) ≤ deTurckArmFibreConst (Module.finrank ℝ E) :=
    one_le_deTurckArmFibreConst (Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Module.finrank ℝ E)))
  have hH3_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ :=
    norm_nonneg _
  have htop : εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m + 1 : ℕ) : ℝ)
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ ≤
      deTurckArmFibreConst (Module.finrank ℝ E) * εC *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ := by
    have hstep1 : εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m + 1 : ℕ) : ℝ)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ ≤
        εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ :=
      mul_le_mul_of_nonneg_left hΔ hεC_nn
    have hstep2 : εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ ≤
        deTurckArmFibreConst (Module.finrank ℝ E) * εC *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ := by
      have h2 : (1 : ℝ) * εC ≤ deTurckArmFibreConst (Module.finrank ℝ E) * εC :=
        mul_le_mul_of_nonneg_right hfibre1 hεC_nn
      have h3 := mul_le_mul_of_nonneg_right h2 hH3_nn
      calc εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖
          = 1 * εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ := by ring
        _ ≤ deTurckArmFibreConst (Module.finrank ℝ E) * εC *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ := h3
    exact le_trans hstep1 hstep2
  linarith [hbase, htop]

theorem exists_smoothCcToTensorHs_appCc_fibreSmallCoeff_opNorm_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (εC : ℝ) (hεC_nn : 0 ≤ εC) (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) :
    ∃ Cop : ℕ → ℝ, (∀ m, 0 ≤ Cop m) ∧
      ∀ (C₂ : SmoothCcTensor g₀ (2 + 2) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x (C₂.toSection x) ≤ εC ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) →
        ∀ m : ℕ,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
              (appCc (I := I) (M := M) g₀ (2 + 2) 2 C₂
                (iteratedCovGrad (I := I) g₀ 0 2 2 T₀))‖ ≤
            deTurckArmFibreConst (Module.finrank ℝ E) * εC *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ +
              Cop m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T₀‖ := by
  classical
  obtain ⟨Cop0, hCop0_nn, h0⟩ :=
    exists_smoothCcToTensorHs_appCc_fibreSmallCoeff_opNorm_le_zero
      (I := I) (M := M) g₀ a ha_super hR₀ εC hεC_nn Kc hKc_nn
  obtain ⟨Cops, hCops_nn, hs⟩ :=
    exists_smoothCcToTensorHs_appCc_fibreSmallCoeff_opNorm_le_succ
      (I := I) (M := M) g₀ a ha_super hR₀ εC hεC_nn Kc hKc_nn
  refine ⟨fun m => match m with
    | 0 => Cop0
    | (k + 1) => Cops k, fun m => ?_, fun C₂ T₀ hball hsup hjets m => ?_⟩
  · match m with
    | 0 => exact hCop0_nn
    | (k + 1) => exact hCops_nn k
  · match m with
    | 0 =>
      have hb := h0 C₂ T₀ hball hsup hjets
      have hnormL := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (show ((0 : ℕ) : ℝ) = (0 : ℝ) by norm_num)
        (appCc (I := I) (M := M) g₀ (2 + 2) 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 T₀))
      have hnorm2 := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (show ((0 : ℕ) : ℝ) + 2 = (2 : ℝ) by norm_num) T₀
      have hnorm1 := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (show ((0 : ℕ) : ℝ) + 1 = (1 : ℝ) by norm_num) T₀
      rw [hnormL, hnorm2, hnorm1]
      exact hb
    | (k + 1) =>
      have hb := hs C₂ T₀ hball hsup hjets k
      have hnormL := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring)
        (appCc (I := I) (M := M) g₀ (2 + 2) 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 T₀))
      have hnorm2 := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (show ((k + 1 : ℕ) : ℝ) + 2 = (k : ℝ) + 3 by push_cast; ring) T₀
      have hnorm1 := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (show ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 by push_cast; ring) T₀
      rw [hnormL, hnorm2, hnorm1]
      exact hb

set_option linter.unusedSectionVars false in
private lemma armZeroTwoArm_delta_nonneg [Nonempty M] (g₀ : SmoothRiemannianMetric I M)
    {δ : ℝ}
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hfb : gFibreOpBound (I := I) (M := M) g₀ h δ) : 0 ≤ δ := by
  classical
  obtain ⟨x⟩ := (inferInstance : Nonempty M)
  obtain ⟨n, e, hn, horth, hpars, hexpand, hrfns⟩ :=
    tangent_frame_expansion (I := I) (M := M) g₀ x
  have hn_pos : 0 < n := by
    rw [hn]
    have : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
    rw [this]
    exact Nat.pos_of_ne_zero (NeZero.ne _)
  set i0 : Fin n := ⟨0, hn_pos⟩ with hi0_def
  have hb := hfb x (e i0) (e i0)
  have hgi : g₀.inner x (e i0) (e i0) = 1 := by
    rw [horth i0 i0, if_pos rfl]
  rw [hgi, Real.sqrt_one, mul_one, mul_one] at hb
  exact le_trans (abs_nonneg _) hb

set_option linter.unusedSectionVars false in

private lemma armZeroTwoArm_data_fibreNormSq_le [Nonempty M]
    (g₀ : SmoothRiemannianMetric I M) {δ : ℝ}
    (T₀ : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T₀ x v w = ccTensorBilin (I := I) g₀ T₀ x w v)
    (hfibre : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T₀.toSection x) ≤
      (Module.finrank ℝ E : ℝ) * δ ^ 2 := by
  classical
  intro x
  have hop : ∀ v w : TangentSpace I x,
      |ccTensorBilin (I := I) g₀ T₀ x v w| ≤
        δ * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by
    intro v w
    have h := hfibre x v w
    have heq : ccTensorBilinSymm (I := I) g₀ T₀ x v w =
        ccTensorBilin (I := I) g₀ T₀ x v w := by
      rw [ccTensorBilinSymm_apply, hTsymm x v w]; ring
    rwa [heq] at h
  obtain ⟨n, e, hn, horth, hpars, hexpand, hrfns⟩ :=
    tangent_frame_expansion (I := I) (M := M) g₀ x
  have hcomp_fiber : ∀ (i j : Fin n),
      ccTensorBilin (I := I) g₀ T₀ x (e i) (e j) =
        fiberNormSqComponent (I := I) (M := M) g₀ x 0 2 (T₀.toSection x) n e
          (default : Fin 0 → Fin n) (![i, j] : Fin 2 → Fin n) := by
    intro i j
    have hconst : ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k : Fin 0 => g₀.inner x (e ((default : Fin 0 → Fin n) k))) :
          Tensor0SBundle.Tensor0SSpace 0 I x) =
        ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ) := by
      apply Tensor0SBundle.tensor0SSpace_ext
      intro u
      change ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k : Fin 0 => g₀.inner x (e ((default : Fin 0 → Fin n) k)))) u =
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) u
      rw [show ((ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) u : ℝ) = 1 from rfl]
      change (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ)
          (fun k => g₀.inner x (e ((default : Fin 0 → Fin n) k)) (u k)) = 1
      rw [ContinuousMultilinearMap.mkPiAlgebra_apply]
      exact Finset.prod_of_isEmpty _
    rw [ccTensorBilin_apply]
    unfold fiberNormSqComponent
    rw [hconst]
    have htuple : (fun k => e ((![i, j] : Fin 2 → Fin n) k)) =
        (![e i, e j] : Fin 2 → TangentSpace I x) := by
      funext k; fin_cases k <;> rfl
    rw [htuple]
    change ccTensorModel (I := I) g₀ T₀ x ![e i, e j] =
      ((T₀.toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
        ![e i, e j] : ℝ)
    unfold ccTensorModel
    rw [ccTensorMultilinear_apply]
    rfl
  have hbridge : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T₀.toSection x) =
      ∑ a : Fin n, ∑ b : Fin n, (ccTensorBilin (I := I) g₀ T₀ x (e a) (e b)) ^ 2 := by
    rw [riemannianFiberNormSq_eq_sum_component_sq (I := I) (M := M) g₀ x e hrfns
      (T₀.toSection x) (default : Fin 0 → Fin n)]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [hcomp_fiber a b]
  rw [hbridge]
  have hrow : ∀ a : Fin n,
      ∑ b : Fin n, (ccTensorBilin (I := I) g₀ T₀ x (e a) (e b)) ^ 2 ≤ δ ^ 2 := by
    intro a
    set c : Fin n → ℝ := fun b => ccTensorBilin (I := I) g₀ T₀ x (e a) (e b) with hc_def
    set S : ℝ := ∑ b : Fin n, (c b) ^ 2 with hS_def
    have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun b _ => sq_nonneg _)
    set u : TangentSpace I x := ∑ b : Fin n, c b • e b with hu_def
    have hval : ccTensorBilin (I := I) g₀ T₀ x (e a) u = S := by
      have hexp : ccTensorBilin (I := I) g₀ T₀ x (e a) u =
          ∑ b : Fin n, c b * ccTensorBilin (I := I) g₀ T₀ x (e a) (e b) := by
        rw [hu_def, map_sum]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [map_smul, smul_eq_mul]
      rw [hexp, hS_def]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      show c b * c b = (c b) ^ 2
      ring
    have hgiu : ∀ i : Fin n, g₀.inner x (e i) u = c i := by
      intro i
      have hexp : g₀.inner x (e i) u =
          ∑ b : Fin n, c b * g₀.inner x (e i) (e b) := by
        rw [hu_def, map_sum]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [map_smul, smul_eq_mul]
      rw [hexp]
      rw [Finset.sum_congr rfl (fun b _ => by rw [horth i b])]
      simp
    have hguu : g₀.inner x u u = S := by
      rw [← hpars u, hS_def]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hgiu i]
    have hgee : g₀.inner x (e a) (e a) = 1 := by rw [horth a a, if_pos rfl]
    have hopau := hop (e a) u
    rw [hgee, Real.sqrt_one, mul_one, hguu, hval] at hopau
    have hSle : S ≤ δ * Real.sqrt S := le_trans (le_abs_self S) hopau
    have hsqrtS : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS_nn
    nlinarith [hSle, hsqrtS, sq_nonneg (Real.sqrt S - δ), Real.sqrt_nonneg S]
  calc ∑ a : Fin n, ∑ b : Fin n, (ccTensorBilin (I := I) g₀ T₀ x (e a) (e b)) ^ 2
      ≤ ∑ _a : Fin n, δ ^ 2 := Finset.sum_le_sum (fun a _ => hrow a)
    _ = (n : ℝ) * δ ^ 2 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (Module.finrank ℝ E : ℝ) * δ ^ 2 := by
        rw [show n = Module.finrank ℝ E from hn]

section BalLadder

variable (g₀ : SmoothRiemannianMetric I M)

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
open Tensor0SBundle in
private lemma bal_rawLap_frame_sum_eval (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (x : M) (D : Tensor0SSpace r I x)
    (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          (rawTensorConnLapSmooth (I := I) g r s Φ).toSection x) D) m =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 2) I x from
            (iteratedCovGrad (I := I) g r s 2 Φ).toSection x) D)
          (Fin.cons ((smoothOrthoFrame (I := I) g x i x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g x i x : TangentSpace I x) : E) m)) := by
  classical
  have hsec : (rawTensorConnLapSmooth (I := I) g r s Φ).toSection x =
      ∑ i : Fin (Module.finrank ℝ E),
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          tensorSecondCovDeriv (I := I) g r s
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (fun z : M => Φ.toSection z) x) := by
    rw [rawTensorConnLapSmooth_toSection_apply (I := I) g r s Φ x,
      rawTensorConnLap_eq_frame_trace_secondCovDeriv (I := I) g r s
        (fun z : M => Φ.toSection z) x]
  have happ : (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
      (rawTensorConnLapSmooth (I := I) g r s Φ).toSection x) D =
      ∑ i : Fin (Module.finrank ℝ E),
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          tensorSecondCovDeriv (I := I) g r s
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (fun z : M => Φ.toSection z) x) D := by
    rw [hsec, ContinuousLinearMap.sum_apply]
  rw [happ, toModel_sum_eval]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show (iteratedCovGrad (I := I) g r s 2 Φ).toSection x =
      (covGrad (I := I) (M := M) g r (s + 1)
        (covGrad (I := I) (M := M) g r s Φ)).toSection x from rfl]
  exact (secondCovGrad_eval_eq_tensorSecondCovDeriv (I := I) g r s Φ
    (smoothOrthoFrame_smooth (I := I) g x i) (smoothOrthoFrame_smooth (I := I) g x i)
    x D m).symm

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
open Tensor0SBundle in
private lemma bal_appCcRS_cometric_eval (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (K : SmoothCcTensor g r (s + 2)) (x : M) (D : Tensor0SSpace r I x)
    (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          (appCcRS (I := I) (M := M) g r (s + 2) s
            (DeTurck.cometricDoubleTraceField (I := I) g s) K).toSection x) D) m =
      ∑ k : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 2) I x from
            K.toSection x) D)
          (Fin.cons (DeTurck.cometricLmodel (I := I) g x
              (model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) m)) := by
  rw [show (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        (appCcRS (I := I) (M := M) g r (s + 2) s
          (DeTurck.cometricDoubleTraceField (I := I) g s) K).toSection x) D =
      DeTurck.cometricDoubleTraceFib (I := I) g s x
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 2) I x from
          K.toSection x) D) from rfl]
  rw [DeTurck.cometricDoubleTraceFib_toModel]
  exact DeTurck.modelDoubleTrace_apply (E := E) s (DeTurck.cometricLmodel (I := I) g x)
    (Tensor0SSpace.toModel
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 2) I x from
        K.toSection x) D)) m

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
open Tensor0SBundle in
private lemma bal_rawLap_toSection_eq_cometric (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (x : M) :
    (rawTensorConnLapSmooth (I := I) g r s Φ).toSection x =
      (appCcRS (I := I) (M := M) g r (s + 2) s
        (DeTurck.cometricDoubleTraceField (I := I) g s)
        (iteratedCovGrad (I := I) g r s 2 Φ)).toSection x := by
  classical
  apply tensorRS_eq_of_toModel_eval_eq
  intro D m
  refine (bal_rawLap_frame_sum_eval (I := I) g r s Φ x D m).trans ?_
  refine Eq.trans ?_ (bal_appCcRS_cometric_eval (I := I) g r s
    (iteratedCovGrad (I := I) g r s 2 Φ) x D m).symm
  exact (DeTurck.cometric_dualTrace_eq_orthoFrame_diag (I := I) g (s := s) x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 2) I x from
        (iteratedCovGrad (I := I) g r s 2 Φ).toSection x) D)) m).symm

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in

theorem rawTensorConnLapSmooth_eq_appCcRS_cometricDoubleTrace_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (Φ : SmoothCcTensor g r s) :
    rawTensorConnLapSmooth (I := I) g r s Φ =
      appCcRS (I := I) (M := M) g r (s + 2) s (DeTurck.cometricDoubleTraceField (I := I) g s)
        (iteratedCovGrad (I := I) g r s 2 Φ) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  exact bal_rawLap_toSection_eq_cometric (I := I) g r s Φ x

private lemma bal_appCc_sub_right (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (A B : SmoothCcTensor g 0 r) :
    appCc (I := I) (M := M) g r s Φ (A - B) =
      appCc (I := I) (M := M) g r s Φ A - appCc (I := I) (M := M) g r s Φ B := by
  have hAB : A - B = A + (-1 : ℝ) • B := by
    rw [neg_one_smul]
    exact sub_eq_add_neg A B
  rw [hAB, appCc_add_right (I := I) (M := M) g r s Φ A ((-1 : ℝ) • B),
    appCc_smul_right (I := I) (M := M) g r s (-1 : ℝ) Φ B,
    neg_one_smul, ← sub_eq_add_neg]

private lemma bal_iter_sub (g : SmoothRiemannianMetric I M) (r s : ℕ) (q : ℕ)
    (A B : SmoothCcTensor g r s) :
    oneMinusConnLapSmoothIter (I := I) g r s q (A - B) =
      oneMinusConnLapSmoothIter (I := I) g r s q A -
        oneMinusConnLapSmoothIter (I := I) g r s q B := by
  induction q with
  | zero => simp only [oneMinusConnLapSmoothIter_zero]
  | succ k ih =>
    rw [oneMinusConnLapSmoothIter_succ, oneMinusConnLapSmoothIter_succ,
      oneMinusConnLapSmoothIter_succ, ih]
    unfold oneMinusConnLapSmooth
    rw [rawTensorConnLapSmooth_sub]
    abel

private lemma bal_lap_add (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (A B : SmoothCcTensor g r s) :
    rawTensorConnLapSmooth (I := I) g r s (A + B) =
      rawTensorConnLapSmooth (I := I) g r s A + rawTensorConnLapSmooth (I := I) g r s B := by
  have h0 : rawTensorConnLapSmooth (I := I) g r s (0 : SmoothCcTensor g r s) = 0 := by
    have := rawTensorConnLapSmooth_sub (I := I) (M := M) g r s A A
    rw [sub_self, sub_self] at this
    exact this
  have hneg : rawTensorConnLapSmooth (I := I) g r s (-B) =
      -rawTensorConnLapSmooth (I := I) g r s B := by
    have := rawTensorConnLapSmooth_sub (I := I) (M := M) g r s 0 B
    rw [zero_sub, h0, zero_sub] at this
    exact this
  have := rawTensorConnLapSmooth_sub (I := I) (M := M) g r s A (-B)
  rw [sub_neg_eq_add, hneg, sub_neg_eq_add] at this
  exact this

private lemma bal_P_add (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (A B : SmoothCcTensor g r s) :
    oneMinusConnLapSmooth (I := I) g r s (A + B) =
      oneMinusConnLapSmooth (I := I) g r s A + oneMinusConnLapSmooth (I := I) g r s B := by
  unfold oneMinusConnLapSmooth
  rw [bal_lap_add]
  abel

private lemma bal_peel (Φ : SmoothCcTensor g₀ 2 2) (W : SmoothCcTensor g₀ 0 2) :
    oneMinusConnLapSmooth (I := I) g₀ 0 2 (appCc (I := I) (M := M) g₀ 2 2 Φ W) =
      appCc (I := I) (M := M) g₀ 2 2 (oneMinusConnLapSmooth (I := I) g₀ 2 2 Φ) W +
        (-(appCc (I := I) (M := M) g₀ 2 2 Φ (rawTensorConnLapSmooth (I := I) g₀ 0 2 W))
          - appCc (I := I) (M := M) g₀ (2 + 2) 2 (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
              (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                (slotExtend (I := I) (M := M) g₀ 2 (2 + 1) (covGrad (I := I) (M := M) g₀ 2 2 Φ))
                (covGrad (I := I) (M := M) g₀ 0 2 W))
          - appCc (I := I) (M := M) g₀ (2 + 2) 2 (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
              (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                  (slotExtend (I := I) (M := M) g₀ 2 2 Φ))
                (covGrad (I := I) (M := M) g₀ 0 2 W))) := by
  have hlap : appCc (I := I) (M := M) g₀ 2 2 (rawTensorConnLapSmooth (I := I) g₀ 2 2 Φ) W =
      appCc (I := I) (M := M) g₀ (2 + 2) 2 (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
        (appCc (I := I) (M := M) g₀ 2 (2 + 2)
          (covGrad (I := I) (M := M) g₀ 2 (2 + 1) (covGrad (I := I) (M := M) g₀ 2 2 Φ)) W) := by
    rw [rawTensorConnLapSmooth_eq_appCcRS_cometricDoubleTrace_rs (I := I) (M := M) g₀ 2 2 Φ]
    rw [show iteratedCovGrad (I := I) g₀ 2 2 2 Φ =
        covGrad (I := I) (M := M) g₀ 2 (2 + 1) (covGrad (I := I) (M := M) g₀ 2 2 Φ) from rfl]
    exact (SmoothCcTensor.ext_iff.mpr rfl).symm
  have hpeel := rawTensorConnLap_appCc_comm_of_rank (I := I) g₀ 2 2 Φ W
  unfold oneMinusConnLapSmooth
  rw [hpeel, appCc_sub_left (I := I) (M := M) g₀ 2 2 Φ
    (rawTensorConnLapSmooth (I := I) g₀ 2 2 Φ) W, hlap]
  abel

private lemma bal_transport (Φ : SmoothCcTensor g₀ 2 2) (W : SmoothCcTensor g₀ 0 2) (p : ℕ) :
    oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p (appCc (I := I) (M := M) g₀ 2 2 Φ W) =
      appCc (I := I) (M := M) g₀ 2 2 (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p Φ) W +
        ∑ q ∈ Finset.range p, oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (p - 1 - q)
          (-(appCc (I := I) (M := M) g₀ 2 2 (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q Φ)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 W))
            - appCc (I := I) (M := M) g₀ (2 + 2) 2 (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                  (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
                    (covGrad (I := I) (M := M) g₀ 2 2
                      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q Φ)))
                  (covGrad (I := I) (M := M) g₀ 0 2 W))
            - appCc (I := I) (M := M) g₀ (2 + 2) 2 (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                  (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                    (slotExtend (I := I) (M := M) g₀ 2 2
                      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q Φ)))
                  (covGrad (I := I) (M := M) g₀ 0 2 W))) := by
  classical
  set Efun : ℕ → SmoothCcTensor g₀ 0 2 := fun q =>
    -(appCc (I := I) (M := M) g₀ 2 2 (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q Φ)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 W))
      - appCc (I := I) (M := M) g₀ (2 + 2) 2 (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
          (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2)
            (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
              (covGrad (I := I) (M := M) g₀ 2 2
                (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q Φ)))
            (covGrad (I := I) (M := M) g₀ 0 2 W))
      - appCc (I := I) (M := M) g₀ (2 + 2) 2 (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
          (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2)
            (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
              (slotExtend (I := I) (M := M) g₀ 2 2
                (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q Φ)))
            (covGrad (I := I) (M := M) g₀ 0 2 W)) with hEfun
  induction p with
  | zero =>
    simp only [oneMinusConnLapSmoothIter_zero, Finset.range_zero, Finset.sum_empty, add_zero]
  | succ p ih =>
    have hPhom : ∀ (A B : SmoothCcTensor g₀ 0 2),
        oneMinusConnLapSmooth (I := I) g₀ 0 2 (A + B) =
          oneMinusConnLapSmooth (I := I) g₀ 0 2 A +
            oneMinusConnLapSmooth (I := I) g₀ 0 2 B :=
      fun A B => bal_P_add (I := I) (M := M) g₀ 0 2 A B
    have hpeelp := bal_peel (I := I) (M := M) g₀
      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p Φ) W
    calc oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (p + 1)
          (appCc (I := I) (M := M) g₀ 2 2 Φ W) = oneMinusConnLapSmooth (I := I) g₀ 0 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p
              (appCc (I := I) (M := M) g₀ 2 2 Φ W)) := by
          rw [oneMinusConnLapSmoothIter_succ]
      _ = oneMinusConnLapSmooth (I := I) g₀ 0 2
            (appCc (I := I) (M := M) g₀ 2 2 (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p Φ) W +
              ∑ q ∈ Finset.range p,
                oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (p - 1 - q) (Efun q)) := by
          rw [ih]
      _ = oneMinusConnLapSmooth (I := I) g₀ 0 2
            (appCc (I := I) (M := M) g₀ 2 2 (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p Φ) W) +
            ∑ q ∈ Finset.range p,
              oneMinusConnLapSmooth (I := I) g₀ 0 2
                (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (p - 1 - q) (Efun q)) := by
          rw [hPhom]
          congr 1
          exact map_sum (AddMonoidHom.mk' (oneMinusConnLapSmooth (I := I) g₀ 0 2)
            (fun A B => hPhom A B)) (fun q => oneMinusConnLapSmoothIter (I := I) g₀ 0 2
              (p - 1 - q) (Efun q)) (Finset.range p)
      _ = (appCc (I := I) (M := M) g₀ 2 2
              (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 (p + 1) Φ) W + Efun p) +
            ∑ q ∈ Finset.range p,
              oneMinusConnLapSmooth (I := I) g₀ 0 2
                (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (p - 1 - q) (Efun q)) := by
          rw [hpeelp, ← oneMinusConnLapSmoothIter_succ (I := I) g₀ 2 2 p Φ]
      _ = (appCc (I := I) (M := M) g₀ 2 2
              (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 (p + 1) Φ) W + Efun p) +
            ∑ q ∈ Finset.range p,
              oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (p + 1 - 1 - q) (Efun q) := by
          congr 1
          refine Finset.sum_congr rfl (fun q hq => ?_)
          have hqlt : q < p := Finset.mem_range.mp hq
          rw [← oneMinusConnLapSmoothIter_succ (I := I) g₀ 0 2 (p - 1 - q) (Efun q),
            show p - 1 - q + 1 = p + 1 - 1 - q from by omega]
      _ = appCc (I := I) (M := M) g₀ 2 2
              (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 (p + 1) Φ) W +
            ∑ q ∈ Finset.range (p + 1),
              oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (p + 1 - 1 - q) (Efun q) := by
          rw [Finset.sum_range_succ,
            show p + 1 - 1 - p = 0 from by omega, oneMinusConnLapSmoothIter_zero]
          abel

private lemma bal_norm_icg_comp (g : SmoothRiemannianMetric I M) (r s j i : ℕ)
    (Ψ : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g r (s + j) i (iteratedCovGrad (I := I) g r s j Ψ)‖ =
      ‖iteratedCovGrad (I := I) g r s (j + i) Ψ‖ := by
  have hnn1 : 0 ≤ ‖iteratedCovGrad (I := I) g r (s + j) i
      (iteratedCovGrad (I := I) g r s j Ψ)‖ := norm_nonneg _
  have hnn2 : 0 ≤ ‖iteratedCovGrad (I := I) g r s (j + i) Ψ‖ := norm_nonneg _
  have hsq : ‖iteratedCovGrad (I := I) g r (s + j) i
        (iteratedCovGrad (I := I) g r s j Ψ)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g r s (j + i) Ψ‖ ^ 2 := by
    simp only [SmoothCcTensor.norm_def]
    rw [tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g r
        ((s + j) + i),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g r
        (s + (j + i))]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact rfns_iteratedCovGrad_comp (I := I) (M := M) g r s j i Ψ x
  nlinarith [hsq, hnn1, hnn2,
    sq_nonneg (‖iteratedCovGrad (I := I) g r (s + j) i
        (iteratedCovGrad (I := I) g r s j Ψ)‖ -
      ‖iteratedCovGrad (I := I) g r s (j + i) Ψ‖)]

private lemma bal_icg_zero_tensor (g : SmoothRiemannianMetric I M) (r s j : ℕ) :
    iteratedCovGrad (I := I) g r s j (0 : SmoothCcTensor g r s) = 0 := by
  have h := iteratedCovGrad_sub (I := I) (M := M) g r s j
    (0 : SmoothCcTensor g r s) (0 : SmoothCcTensor g r s)
  rw [sub_self, sub_self] at h
  exact h

private lemma bal_jet_l2_of_pointwise_window (g : SmoothRiemannianMetric I M)
    {rz sz rw : ℕ} (Z : SmoothCcTensor g rz sz) (c : ℝ) (_hc : 0 ≤ c)
    (sw : ℕ → ℕ) (F : (i : ℕ) → SmoothCcTensor g rw (sw i)) (n : ℕ)
    (hpt : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g rz sz x (Z.toSection x) ≤
      c * ∑ i ∈ Finset.range n,
        riemannianFiberNormSq (I := I) (M := M) g rw (sw i) x ((F i).toSection x)) :
    ‖Z‖ ^ 2 ≤ c * ∑ i ∈ Finset.range n, ‖F i‖ ^ 2 := by
  have hint : MeasureTheory.Integrable
      (fun x => c * ∑ i ∈ Finset.range n,
        riemannianFiberNormSq (I := I) (M := M) g rw (sw i) x ((F i).toSection x))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine MeasureTheory.Integrable.const_mul ?_ c
    exact MeasureTheory.integrable_finset_sum _ (fun i _ =>
      integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g rw (sw i) (F i))
  have h1 := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g rz sz
    Z _ hint hpt
  rw [MeasureTheory.integral_const_mul] at h1
  rw [MeasureTheory.integral_finset_sum _ (fun i _ =>
    integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g rw (sw i) (F i))] at h1
  refine le_trans h1 (le_of_eq ?_)
  refine congrArg (fun t => c * t) (Finset.sum_congr rfl (fun i _ => ?_))
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g rw (sw i)]

private lemma bal_sq_sum_le_sum_sq {n : ℕ} (u : ℕ → ℝ) (hu : ∀ i, 0 ≤ u i) :
    ∑ i ∈ Finset.range n, (u i) ^ 2 ≤ (∑ i ∈ Finset.range n, u i) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have h1 : 0 ≤ ∑ i ∈ Finset.range n, u i :=
      Finset.sum_nonneg (fun i _ => hu i)
    nlinarith [ih, hu n, sq_nonneg (u n)]

private lemma bal_shift_sq_sum_le (u : ℕ → ℝ) (hu : ∀ b, 0 ≤ u b) (j m : ℕ) (hm : m ≤ 2) :
    ∑ i ∈ Finset.range (1 + j), (u (i + m)) ^ 2 ≤ (∑ b ∈ Finset.range (j + 3), u b) ^ 2 := by
  have h1 : ∑ i ∈ Finset.range (1 + j), (u (i + m)) ^ 2 =
      ∑ b ∈ Finset.image (· + m) (Finset.range (1 + j)), (u b) ^ 2 := by
    rw [Finset.sum_image (fun a _ b _ hab => by omega)]
  rw [h1]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun b _ _ => sq_nonneg _))
    (bal_sq_sum_le_sum_sq u hu)
  intro b hb
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
  have := Finset.mem_range.mp hi
  exact Finset.mem_range.mpr (by omega)

set_option maxHeartbeats 1000000 in
private lemma bal_ptcRS_jet_le (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧
      ∀ (j : ℕ) (S : SmoothCcTensor g r s),
        ‖iteratedCovGrad (I := I) g r (s + 1) j
            (pointwiseTensorCurvRS (I := I) (M := M) g r s S)‖ ≤
          K j * ∑ b ∈ Finset.range (j + 3), ‖iteratedCovGrad (I := I) g r s b S‖ := by
  classical
  obtain ⟨Q₀, Q₁, Q₂, hQ⟩ :=
    exists_pointwiseTensorCurvRS_homField_jetDecomposition (I := I) (M := M) g r s
  obtain ⟨cc₀, hcc₀_nn, hcc₀⟩ :=
    exists_appFullSec_iteratedCovGrad_window_bound (I := I) (M := M) g r s (s + 1) Q₀
  obtain ⟨cc₁, hcc₁_nn, hcc₁⟩ :=
    exists_appFullSec_on_jet_iteratedCovGrad_window_bound (I := I) (M := M) g r s 1 (s + 1) Q₁
  obtain ⟨cc₂, hcc₂_nn, hcc₂⟩ :=
    exists_appFullSec_on_jet_iteratedCovGrad_window_bound (I := I) (M := M) g r s 2 (s + 1) Q₂
  refine ⟨fun j => Real.sqrt (cc₀ j) + Real.sqrt (cc₁ j) + Real.sqrt (cc₂ j),
    fun j => by positivity, fun j S => ?_⟩
  set Sj : ℝ := ∑ b ∈ Finset.range (j + 3), ‖iteratedCovGrad (I := I) g r s b S‖ with hSj_def
  have hSj_nn : 0 ≤ Sj := Finset.sum_nonneg (fun b _ => norm_nonneg _)
  have h₀ : ‖iteratedCovGrad (I := I) g r (s + 1) j
      (appFullSec (I := I) (M := M) g r s (s + 1) Q₀ S)‖ ≤ Real.sqrt (cc₀ j) * Sj := by
    have hsq := bal_jet_l2_of_pointwise_window (I := I) (M := M) g
      (iteratedCovGrad (I := I) g r (s + 1) j
        (appFullSec (I := I) (M := M) g r s (s + 1) Q₀ S))
      (cc₀ j) (hcc₀_nn j) (fun i => s + i)
      (fun i => iteratedCovGrad (I := I) g r s i S) (j + 1) (fun x => hcc₀ S j x)
    have hsum_le : ∑ i ∈ Finset.range (j + 1),
        ‖iteratedCovGrad (I := I) g r s i S‖ ^ 2 ≤ Sj ^ 2 := by
      have := bal_shift_sq_sum_le (fun b => ‖iteratedCovGrad (I := I) g r s b S‖)
        (fun b => norm_nonneg _) j 0 (by omega)
      simpa [Nat.add_comm 1 j] using this
    refine le_of_sq_le_sq ?_ (mul_nonneg (Real.sqrt_nonneg _) hSj_nn)
    rw [mul_pow, Real.sq_sqrt (hcc₀_nn j)]
    exact le_trans hsq (mul_le_mul_of_nonneg_left hsum_le (hcc₀_nn j))
  have h₁ : ‖iteratedCovGrad (I := I) g r (s + 1) j
      (appFullSec (I := I) (M := M) g r (s + 1) (s + 1) Q₁
        (iteratedCovGrad (I := I) g r s 1 S))‖ ≤ Real.sqrt (cc₁ j) * Sj := by
    have hsq := bal_jet_l2_of_pointwise_window (I := I) (M := M) g
      (iteratedCovGrad (I := I) g r (s + 1) j
        (appFullSec (I := I) (M := M) g r (s + 1) (s + 1) Q₁
          (iteratedCovGrad (I := I) g r s 1 S)))
      (cc₁ j) (hcc₁_nn j) (fun i => s + (i + 1))
      (fun i => iteratedCovGrad (I := I) g r s (i + 1) S) (1 + j) (fun x => hcc₁ S j x)
    have hsum_le : ∑ i ∈ Finset.range (1 + j),
        ‖iteratedCovGrad (I := I) g r s (i + 1) S‖ ^ 2 ≤ Sj ^ 2 :=
      bal_shift_sq_sum_le (fun b => ‖iteratedCovGrad (I := I) g r s b S‖)
        (fun b => norm_nonneg _) j 1 (by omega)
    refine le_of_sq_le_sq ?_ (mul_nonneg (Real.sqrt_nonneg _) hSj_nn)
    rw [mul_pow, Real.sq_sqrt (hcc₁_nn j)]
    exact le_trans hsq (mul_le_mul_of_nonneg_left hsum_le (hcc₁_nn j))
  have h₂ : ‖iteratedCovGrad (I := I) g r (s + 1) j
      (appFullSec (I := I) (M := M) g r (s + 2) (s + 1) Q₂
        (iteratedCovGrad (I := I) g r s 2 S))‖ ≤ Real.sqrt (cc₂ j) * Sj := by
    have hsq := bal_jet_l2_of_pointwise_window (I := I) (M := M) g
      (iteratedCovGrad (I := I) g r (s + 1) j
        (appFullSec (I := I) (M := M) g r (s + 2) (s + 1) Q₂
          (iteratedCovGrad (I := I) g r s 2 S)))
      (cc₂ j) (hcc₂_nn j) (fun i => s + (i + 2))
      (fun i => iteratedCovGrad (I := I) g r s (i + 2) S) (1 + j) (fun x => hcc₂ S j x)
    have hsum_le : ∑ i ∈ Finset.range (1 + j),
        ‖iteratedCovGrad (I := I) g r s (i + 2) S‖ ^ 2 ≤ Sj ^ 2 :=
      bal_shift_sq_sum_le (fun b => ‖iteratedCovGrad (I := I) g r s b S‖)
        (fun b => norm_nonneg _) j 2 (by omega)
    refine le_of_sq_le_sq ?_ (mul_nonneg (Real.sqrt_nonneg _) hSj_nn)
    rw [mul_pow, Real.sq_sqrt (hcc₂_nn j)]
    exact le_trans hsq (mul_le_mul_of_nonneg_left hsum_le (hcc₂_nn j))
  have htri : ‖iteratedCovGrad (I := I) g r (s + 1) j
      (pointwiseTensorCurvRS (I := I) (M := M) g r s S)‖ ≤
      ‖iteratedCovGrad (I := I) g r (s + 1) j
        (appFullSec (I := I) (M := M) g r s (s + 1) Q₀ S)‖ +
      ‖iteratedCovGrad (I := I) g r (s + 1) j
        (appFullSec (I := I) (M := M) g r (s + 1) (s + 1) Q₁
          (covGrad (I := I) (M := M) g r s S))‖ +
      ‖iteratedCovGrad (I := I) g r (s + 1) j
        (appFullSec (I := I) (M := M) g r (s + 2) (s + 1) Q₂
          (iteratedCovGrad (I := I) g r s 2 S))‖ := by
    rw [hQ S, iteratedCovGrad_add, iteratedCovGrad_add]
    refine le_trans (norm_add_le _ _) ?_
    have h := norm_add_le
      (iteratedCovGrad (I := I) g r (s + 1) j
        (appFullSec (I := I) (M := M) g r s (s + 1) Q₀ S))
      (iteratedCovGrad (I := I) g r (s + 1) j
        (appFullSec (I := I) (M := M) g r (s + 1) (s + 1) Q₁
          (covGrad (I := I) (M := M) g r s S)))
    linarith
  have hcov1 : covGrad (I := I) (M := M) g r s S = iteratedCovGrad (I := I) g r s 1 S := rfl
  rw [hcov1] at htri
  refine le_trans htri ?_
  calc ‖iteratedCovGrad (I := I) g r (s + 1) j
        (appFullSec (I := I) (M := M) g r s (s + 1) Q₀ S)‖ +
      ‖iteratedCovGrad (I := I) g r (s + 1) j
        (appFullSec (I := I) (M := M) g r (s + 1) (s + 1) Q₁
          (iteratedCovGrad (I := I) g r s 1 S))‖ +
      ‖iteratedCovGrad (I := I) g r (s + 1) j
        (appFullSec (I := I) (M := M) g r (s + 2) (s + 1) Q₂
          (iteratedCovGrad (I := I) g r s 2 S))‖
      ≤ Real.sqrt (cc₀ j) * Sj + Real.sqrt (cc₁ j) * Sj + Real.sqrt (cc₂ j) * Sj :=
        add_le_add (add_le_add h₀ h₁) h₂
    _ = (Real.sqrt (cc₀ j) + Real.sqrt (cc₁ j) + Real.sqrt (cc₂ j)) * Sj := by ring

set_option linter.unusedSectionVars false in
private lemma bal_icg_one (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X : SmoothCcTensor g r s) :
    covGrad (I := I) (M := M) g r s X = iteratedCovGrad (I := I) g r s 1 X := rfl

private lemma bal_shift_sum_le (u : ℕ → ℝ) (hu : ∀ b, 0 ≤ u b) (k m n : ℕ)
    (hkm : ∀ i < k, i + m < n) :
    ∑ b ∈ Finset.range k, u (b + m) ≤ ∑ b ∈ Finset.range n, u b := by
  have h1 : ∑ b ∈ Finset.range k, u (b + m) =
      ∑ b ∈ Finset.image (· + m) (Finset.range k), u b := by
    rw [Finset.sum_image (fun a _ b _ hab => by omega)]
  rw [h1]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun b _ _ => hu b)
  intro b hb
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
  exact Finset.mem_range.mpr (hkm i (Finset.mem_range.mp hi))

private lemma bal_comm_tower (g : SmoothRiemannianMetric I M) (r s : ℕ) (m : ℕ) :
    ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧
      ∀ (j : ℕ) (S : SmoothCcTensor g r s),
        ‖iteratedCovGrad (I := I) g r (s + m) j
            (rawTensorConnLapSmooth (I := I) g r (s + m)
                (iteratedCovGrad (I := I) g r s m S) -
              iteratedCovGrad (I := I) g r s m
                (rawTensorConnLapSmooth (I := I) g r s S))‖ ≤
          K j * ∑ b ∈ Finset.range (m + j + 2), ‖iteratedCovGrad (I := I) g r s b S‖ := by
  classical
  induction m with
  | zero =>
    refine ⟨fun _ => 0, fun _ => le_refl 0, fun j S => ?_⟩
    have hz : rawTensorConnLapSmooth (I := I) g r (s + 0)
          (iteratedCovGrad (I := I) g r s 0 S) -
        iteratedCovGrad (I := I) g r s 0 (rawTensorConnLapSmooth (I := I) g r s S) = 0 := by
      simp only [iteratedCovGrad_zero]
      exact sub_self _
    rw [hz, bal_icg_zero_tensor, norm_zero, zero_mul]
  | succ m ih =>
    obtain ⟨Km, hKm_nn, hKm⟩ := ih
    obtain ⟨Kp, hKp_nn, hKp⟩ := bal_ptcRS_jet_le (I := I) (M := M) g r (s + m)
    refine ⟨fun j => Kp j + Km (j + 1), fun j => add_nonneg (hKp_nn j) (hKm_nn (j + 1)),
      fun j S => ?_⟩
    set Y : SmoothCcTensor g r (s + m) := iteratedCovGrad (I := I) g r s m S with hY_def
    set Cm : SmoothCcTensor g r (s + m) :=
      rawTensorConnLapSmooth (I := I) g r (s + m) Y -
        iteratedCovGrad (I := I) g r s m (rawTensorConnLapSmooth (I := I) g r s S)
      with hCm_def
    have hid : rawTensorConnLapSmooth (I := I) g r (s + (m + 1))
          (iteratedCovGrad (I := I) g r s (m + 1) S) -
        iteratedCovGrad (I := I) g r s (m + 1) (rawTensorConnLapSmooth (I := I) g r s S) =
        pointwiseTensorCurvRS (I := I) (M := M) g r (s + m) Y +
          covGrad (I := I) (M := M) g r (s + m) Cm := by
      rw [iteratedCovGrad_succ, iteratedCovGrad_succ, hCm_def]
      rw [covGrad_sub (I := I) (M := M) g r (s + m)]
      show rawTensorConnLapSmooth (I := I) g r ((s + m) + 1)
          (covGrad (I := I) (M := M) g r (s + m) Y) -
          covGrad (I := I) (M := M) g r (s + m)
            (iteratedCovGrad (I := I) g r s m (rawTensorConnLapSmooth (I := I) g r s S)) =
        (rawTensorConnLapSmooth (I := I) g r ((s + m) + 1)
            (covGrad (I := I) (M := M) g r (s + m) Y) -
          covGrad (I := I) (M := M) g r (s + m)
            (rawTensorConnLapSmooth (I := I) g r (s + m) Y)) +
        (covGrad (I := I) (M := M) g r (s + m) (rawTensorConnLapSmooth (I := I) g r (s + m) Y) -
          covGrad (I := I) (M := M) g r (s + m)
            (iteratedCovGrad (I := I) g r s m (rawTensorConnLapSmooth (I := I) g r s S)))
      abel
    rw [hid, iteratedCovGrad_add]
    refine le_trans (norm_add_le _ _) ?_
    have hpiece1 : ‖iteratedCovGrad (I := I) g r ((s + m) + 1) j
        (pointwiseTensorCurvRS (I := I) (M := M) g r (s + m) Y)‖ ≤
        Kp j * ∑ b ∈ Finset.range ((m + 1) + j + 2),
          ‖iteratedCovGrad (I := I) g r s b S‖ := by
      refine le_trans (hKp j Y) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hKp_nn j)
      have hcomp : ∀ b, ‖iteratedCovGrad (I := I) g r (s + m) b Y‖ =
          ‖iteratedCovGrad (I := I) g r s (m + b) S‖ := fun b =>
        bal_norm_icg_comp (I := I) (M := M) g r s m b S
      calc ∑ b ∈ Finset.range (j + 3), ‖iteratedCovGrad (I := I) g r (s + m) b Y‖
          = ∑ b ∈ Finset.range (j + 3),
              ‖iteratedCovGrad (I := I) g r s (b + m) S‖ := by
            refine Finset.sum_congr rfl (fun b _ => ?_)
            rw [hcomp b, show m + b = b + m from by omega]
        _ ≤ ∑ b ∈ Finset.range ((m + 1) + j + 2),
              ‖iteratedCovGrad (I := I) g r s b S‖ :=
            bal_shift_sum_le (fun b => ‖iteratedCovGrad (I := I) g r s b S‖)
              (fun b => norm_nonneg _) (j + 3) m ((m + 1) + j + 2) (fun i hi => by omega)
    have hpiece2 : ‖iteratedCovGrad (I := I) g r ((s + m) + 1) j
        (covGrad (I := I) (M := M) g r (s + m) Cm)‖ ≤
        Km (j + 1) * ∑ b ∈ Finset.range ((m + 1) + j + 2),
          ‖iteratedCovGrad (I := I) g r s b S‖ := by
      have hnc : ‖iteratedCovGrad (I := I) g r ((s + m) + 1) j
          (covGrad (I := I) (M := M) g r (s + m) Cm)‖ =
          ‖iteratedCovGrad (I := I) g r (s + m) (1 + j) Cm‖ := by
        rw [bal_icg_one (I := I) (M := M) g r (s + m) Cm]
        exact bal_norm_icg_comp (I := I) (M := M) g r (s + m) 1 j Cm
      rw [hnc, show 1 + j = j + 1 from by omega]
      refine le_trans (hKm (j + 1) S) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hKm_nn (j + 1))
      have hsub : Finset.range (m + (j + 1) + 2) ⊆ Finset.range ((m + 1) + j + 2) :=
        fun x hx => Finset.mem_range.mpr
          (by have := Finset.mem_range.mp hx; omega)
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun b _ _ => norm_nonneg _)
    calc ‖iteratedCovGrad (I := I) g r ((s + m) + 1) j
          (pointwiseTensorCurvRS (I := I) (M := M) g r (s + m) Y)‖ +
        ‖iteratedCovGrad (I := I) g r ((s + m) + 1) j
          (covGrad (I := I) (M := M) g r (s + m) Cm)‖
        ≤ Kp j * ∑ b ∈ Finset.range ((m + 1) + j + 2),
              ‖iteratedCovGrad (I := I) g r s b S‖ +
            Km (j + 1) * ∑ b ∈ Finset.range ((m + 1) + j + 2),
              ‖iteratedCovGrad (I := I) g r s b S‖ := add_le_add hpiece1 hpiece2
      _ = (Kp j + Km (j + 1)) * ∑ b ∈ Finset.range ((m + 1) + j + 2),
            ‖iteratedCovGrad (I := I) g r s b S‖ := by ring

set_option maxHeartbeats 1600000 in
private lemma bal_G2 (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ S : SmoothCcTensor g r s,
      ‖rawTensorConnLapSmooth (I := I) g r s S‖ ≤
        ‖iteratedCovGrad (I := I) g r s 2 S‖ +
          c * (‖iteratedCovGrad (I := I) g r s 1 S‖ + ‖S‖) := by
  classical
  obtain ⟨Kp, hKp_nn, hKp⟩ := bal_ptcRS_jet_le (I := I) (M := M) g r s
  refine ⟨Kp 0 + 1, by linarith [hKp_nn 0], fun S => ?_⟩
  have hW := weitzenbock_integrated_covGrad_l2_normSq_rs (I := I) (M := M) g r s S
  have hicg2 : covGrad (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s S) =
      iteratedCovGrad (I := I) g r s 2 S := rfl
  have hicg1 : covGrad (I := I) (M := M) g r s S = iteratedCovGrad (I := I) g r s 1 S := rfl
  have hptc : rawTensorConnLapSmooth (I := I) g r (s + 1) (covGrad (I := I) (M := M) g r s S) -
      covGrad (I := I) (M := M) g r s (rawTensorConnLapSmooth (I := I) g r s S) =
      pointwiseTensorCurvRS (I := I) (M := M) g r s S := rfl
  rw [hicg2, hptc] at hW
  rw [show tensorL2Norm (I := I) (M := M) g r (s + 1 + 1)
      (iteratedCovGrad (I := I) g r s 2 S).toFun =
      ‖iteratedCovGrad (I := I) g r s 2 S‖ from (SmoothCcTensor.norm_def _).symm] at hW
  rw [show tensorL2Norm (I := I) (M := M) g r s
      (rawTensorConnLapSmooth (I := I) g r s S).toFun =
      ‖rawTensorConnLapSmooth (I := I) g r s S‖ from (SmoothCcTensor.norm_def _).symm] at hW
  have hCS : |tensorL2Inner (I := I) (M := M) g r (s + 1)
      (pointwiseTensorCurvRS (I := I) (M := M) g r s S).toFun
      (covGrad (I := I) (M := M) g r s S).toFun| ≤
      ‖pointwiseTensorCurvRS (I := I) (M := M) g r s S‖ *
        ‖covGrad (I := I) (M := M) g r s S‖ := by
    have h := DifferentialGeometry.Integral.L2.abs_tensorL2Inner_le (I := I) (M := M) g r (s + 1)
      (pointwiseTensorCurvRS (I := I) (M := M) g r s S).toFun
      (covGrad (I := I) (M := M) g r s S).toFun
      (SmoothCcTensor.memL2_toFun (I := I) (M := M)
        (pointwiseTensorCurvRS (I := I) (M := M) g r s S))
      (SmoothCcTensor.memL2_toFun (I := I) (M := M) (covGrad (I := I) (M := M) g r s S))
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
        (pointwiseTensorCurvRS (I := I) (M := M) g r s S)
        (covGrad (I := I) (M := M) g r s S))
    rw [show tensorL2Norm (I := I) (M := M) g r (s + 1)
        (pointwiseTensorCurvRS (I := I) (M := M) g r s S).toFun =
        ‖pointwiseTensorCurvRS (I := I) (M := M) g r s S‖ from
      (SmoothCcTensor.norm_def _).symm] at h
    rw [show tensorL2Norm (I := I) (M := M) g r (s + 1)
        (covGrad (I := I) (M := M) g r s S).toFun =
        ‖covGrad (I := I) (M := M) g r s S‖ from (SmoothCcTensor.norm_def _).symm] at h
    exact h
  have hptc_le : ‖pointwiseTensorCurvRS (I := I) (M := M) g r s S‖ ≤
      Kp 0 * (‖S‖ + ‖iteratedCovGrad (I := I) g r s 1 S‖ +
        ‖iteratedCovGrad (I := I) g r s 2 S‖) := by
    have h := hKp 0 S
    have h0 : ‖iteratedCovGrad (I := I) g r (s + 1) 0
        (pointwiseTensorCurvRS (I := I) (M := M) g r s S)‖ =
        ‖pointwiseTensorCurvRS (I := I) (M := M) g r s S‖ := by
      rw [iteratedCovGrad_zero]
    have hsum : ∑ b ∈ Finset.range (0 + 3), ‖iteratedCovGrad (I := I) g r s b S‖ =
        ‖S‖ + ‖iteratedCovGrad (I := I) g r s 1 S‖ +
          ‖iteratedCovGrad (I := I) g r s 2 S‖ := by
      rw [show (0 + 3 : ℕ) = 3 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_one, iteratedCovGrad_zero]
    rw [h0, hsum] at h
    exact h
  set a0 : ℝ := ‖S‖ with ha0
  set a1 : ℝ := ‖iteratedCovGrad (I := I) g r s 1 S‖ with ha1
  set a2 : ℝ := ‖iteratedCovGrad (I := I) g r s 2 S‖ with ha2
  have ha0_nn : 0 ≤ a0 := norm_nonneg _
  have ha1_nn : 0 ≤ a1 := norm_nonneg _
  have ha2_nn : 0 ≤ a2 := norm_nonneg _
  have hgrad_eq : ‖covGrad (I := I) (M := M) g r s S‖ = a1 := by rw [hicg1]
  have hsq : ‖rawTensorConnLapSmooth (I := I) g r s S‖ ^ 2 ≤
      a2 ^ 2 + Kp 0 * (a0 + a1 + a2) * a1 := by
    have h1 : ‖rawTensorConnLapSmooth (I := I) g r s S‖ ^ 2 =
        a2 ^ 2 + tensorL2Inner (I := I) (M := M) g r (s + 1)
          (pointwiseTensorCurvRS (I := I) (M := M) g r s S).toFun
          (covGrad (I := I) (M := M) g r s S).toFun := by linarith [hW]
    rw [h1]
    have h2 : tensorL2Inner (I := I) (M := M) g r (s + 1)
        (pointwiseTensorCurvRS (I := I) (M := M) g r s S).toFun
        (covGrad (I := I) (M := M) g r s S).toFun ≤
        Kp 0 * (a0 + a1 + a2) * a1 := by
      refine le_trans (le_abs_self _) (le_trans hCS ?_)
      rw [hgrad_eq]
      exact mul_le_mul_of_nonneg_right hptc_le (by rw [← hgrad_eq]; exact norm_nonneg _)
    linarith
  have hrhs_nn : 0 ≤ a2 + (Kp 0 + 1) * (a1 + a0) := by
    have := hKp_nn 0
    nlinarith
  refine le_of_sq_le_sq ?_ hrhs_nn
  have e1 : Kp 0 * a2 * a1 ≤ 2 * (Kp 0 + 1) * a2 * (a1 + a0) := by
    nlinarith [mul_nonneg ha2_nn ha1_nn, mul_nonneg ha2_nn ha0_nn, hKp_nn 0,
      mul_nonneg (mul_nonneg (hKp_nn 0) ha2_nn) ha0_nn,
      mul_nonneg (mul_nonneg (hKp_nn 0) ha2_nn) ha1_nn]
  have e2 : Kp 0 * (a0 + a1) * a1 ≤ (Kp 0 + 1) ^ 2 * (a1 + a0) ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg (hKp_nn 0) (add_nonneg ha0_nn ha1_nn)) ha0_nn,
      mul_nonneg (mul_nonneg (hKp_nn 0) (hKp_nn 0)) (sq_nonneg (a1 + a0)),
      mul_nonneg (hKp_nn 0) (sq_nonneg (a1 + a0)), sq_nonneg (a1 + a0)]
  have esplit : Kp 0 * (a0 + a1 + a2) * a1 =
      Kp 0 * (a0 + a1) * a1 + Kp 0 * a2 * a1 := by ring
  have expand : (a2 + (Kp 0 + 1) * (a1 + a0)) ^ 2 =
      a2 ^ 2 + 2 * (Kp 0 + 1) * a2 * (a1 + a0) + (Kp 0 + 1) ^ 2 * (a1 + a0) ^ 2 := by ring
  rw [expand]
  linarith [hsq, e1, e2, esplit]

private lemma bal_lap_jets (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ c : ℕ → ℝ, (∀ b, 0 ≤ c b) ∧
      ∀ (b : ℕ) (S : SmoothCcTensor g r s),
        ‖iteratedCovGrad (I := I) g r s b (rawTensorConnLapSmooth (I := I) g r s S)‖ ≤
          c b * ∑ b' ∈ Finset.range (b + 3), ‖iteratedCovGrad (I := I) g r s b' S‖ := by
  classical
  have hG2fam : ∀ b : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ Y : SmoothCcTensor g r (s + b),
      ‖rawTensorConnLapSmooth (I := I) g r (s + b) Y‖ ≤
        ‖iteratedCovGrad (I := I) g r (s + b) 2 Y‖ +
          c * (‖iteratedCovGrad (I := I) g r (s + b) 1 Y‖ + ‖Y‖) :=
    fun b => bal_G2 (I := I) (M := M) g r (s + b)
  choose cG hcG_nn hcG using hG2fam
  have hTfam : ∀ m : ℕ, ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧
      ∀ (j : ℕ) (S : SmoothCcTensor g r s),
        ‖iteratedCovGrad (I := I) g r (s + m) j
            (rawTensorConnLapSmooth (I := I) g r (s + m)
                (iteratedCovGrad (I := I) g r s m S) -
              iteratedCovGrad (I := I) g r s m
                (rawTensorConnLapSmooth (I := I) g r s S))‖ ≤
          K j * ∑ b ∈ Finset.range (m + j + 2), ‖iteratedCovGrad (I := I) g r s b S‖ :=
    fun m => bal_comm_tower (I := I) (M := M) g r s m
  choose KT hKT_nn hKT using hTfam
  refine ⟨fun b => 1 + 2 * cG b + KT b 0,
    fun b => by have := hcG_nn b; have := hKT_nn b 0; linarith, fun b S => ?_⟩
  set Sb : ℝ := ∑ b' ∈ Finset.range (b + 3), ‖iteratedCovGrad (I := I) g r s b' S‖
    with hSb_def
  have hSb_nn : 0 ≤ Sb := Finset.sum_nonneg (fun b' _ => norm_nonneg _)
  have hsingle : ∀ b' : ℕ, b' < b + 3 →
      ‖iteratedCovGrad (I := I) g r s b' S‖ ≤ Sb := by
    intro b' hb'
    exact Finset.single_le_sum (f := fun b'' => ‖iteratedCovGrad (I := I) g r s b'' S‖)
      (fun b'' _ => norm_nonneg _) (Finset.mem_range.mpr hb')
  have hdecomp : iteratedCovGrad (I := I) g r s b (rawTensorConnLapSmooth (I := I) g r s S) =
      rawTensorConnLapSmooth (I := I) g r (s + b) (iteratedCovGrad (I := I) g r s b S) -
        (rawTensorConnLapSmooth (I := I) g r (s + b) (iteratedCovGrad (I := I) g r s b S) -
          iteratedCovGrad (I := I) g r s b (rawTensorConnLapSmooth (I := I) g r s S)) := by
    abel
  rw [hdecomp]
  refine le_trans (norm_sub_le _ _) ?_
  have hpiece1 : ‖rawTensorConnLapSmooth (I := I) g r (s + b)
      (iteratedCovGrad (I := I) g r s b S)‖ ≤ (1 + 2 * cG b) * Sb := by
    refine le_trans (hcG b (iteratedCovGrad (I := I) g r s b S)) ?_
    have h2 : ‖iteratedCovGrad (I := I) g r (s + b) 2 (iteratedCovGrad (I := I) g r s b S)‖ =
        ‖iteratedCovGrad (I := I) g r s (b + 2) S‖ :=
      bal_norm_icg_comp (I := I) (M := M) g r s b 2 S
    have h1 : ‖iteratedCovGrad (I := I) g r (s + b) 1 (iteratedCovGrad (I := I) g r s b S)‖ =
        ‖iteratedCovGrad (I := I) g r s (b + 1) S‖ :=
      bal_norm_icg_comp (I := I) (M := M) g r s b 1 S
    rw [h2, h1]
    have e2 : ‖iteratedCovGrad (I := I) g r s (b + 2) S‖ ≤ Sb := hsingle (b + 2) (by omega)
    have e1 : ‖iteratedCovGrad (I := I) g r s (b + 1) S‖ ≤ Sb := hsingle (b + 1) (by omega)
    have e0 : ‖iteratedCovGrad (I := I) g r s b S‖ ≤ Sb := hsingle b (by omega)
    nlinarith [hcG_nn b, hSb_nn]
  have hpiece2 : ‖rawTensorConnLapSmooth (I := I) g r (s + b)
      (iteratedCovGrad (I := I) g r s b S) -
        iteratedCovGrad (I := I) g r s b (rawTensorConnLapSmooth (I := I) g r s S)‖ ≤
      KT b 0 * Sb := by
    have h := hKT b 0 S
    have h0 : ‖iteratedCovGrad (I := I) g r (s + b) 0
        (rawTensorConnLapSmooth (I := I) g r (s + b)
            (iteratedCovGrad (I := I) g r s b S) -
          iteratedCovGrad (I := I) g r s b
            (rawTensorConnLapSmooth (I := I) g r s S))‖ =
        ‖rawTensorConnLapSmooth (I := I) g r (s + b)
            (iteratedCovGrad (I := I) g r s b S) -
          iteratedCovGrad (I := I) g r s b
            (rawTensorConnLapSmooth (I := I) g r s S)‖ := by
      rw [iteratedCovGrad_zero]
    rw [h0] at h
    refine le_trans h ?_
    refine mul_le_mul_of_nonneg_left ?_ (hKT_nn b 0)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun b' _ _ => norm_nonneg _)
    exact fun x hx => Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega)
  calc ‖rawTensorConnLapSmooth (I := I) g r (s + b)
        (iteratedCovGrad (I := I) g r s b S)‖ +
      ‖rawTensorConnLapSmooth (I := I) g r (s + b)
          (iteratedCovGrad (I := I) g r s b S) -
        iteratedCovGrad (I := I) g r s b (rawTensorConnLapSmooth (I := I) g r s S)‖
      ≤ (1 + 2 * cG b) * Sb + KT b 0 * Sb := add_le_add hpiece1 hpiece2
    _ = (1 + 2 * cG b + KT b 0) * Sb := by ring

private lemma bal_iter_one (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    oneMinusConnLapSmoothIter (I := I) g r s 1 S =
      S - rawTensorConnLapSmooth (I := I) g r s S := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, oneMinusConnLapSmoothIter_succ,
    oneMinusConnLapSmoothIter_zero]
  rfl

private lemma bal_iter_succ_inner (g : SmoothRiemannianMetric I M) (r s : ℕ) (q : ℕ)
    (S : SmoothCcTensor g r s) :
    oneMinusConnLapSmoothIter (I := I) g r s (q + 1) S =
      oneMinusConnLapSmoothIter (I := I) g r s q S -
        oneMinusConnLapSmoothIter (I := I) g r s q
          (rawTensorConnLapSmooth (I := I) g r s S) := by
  rw [oneMinusConnLapSmoothIter_add (I := I) (M := M) g r s q 1 S,
    bal_iter_one (I := I) (M := M) g r s S,
    bal_iter_sub (I := I) (M := M) g r s q]

private lemma bal_sum_lap_jets (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (cL : ℕ → ℝ) (hcL_nn : ∀ b, 0 ≤ cL b)
    (hcL : ∀ (b : ℕ) (S : SmoothCcTensor g r s),
      ‖iteratedCovGrad (I := I) g r s b (rawTensorConnLapSmooth (I := I) g r s S)‖ ≤
        cL b * ∑ b' ∈ Finset.range (b + 3), ‖iteratedCovGrad (I := I) g r s b' S‖)
    (K : ℕ) (S : SmoothCcTensor g r s) :
    ∑ b ∈ Finset.range K,
        ‖iteratedCovGrad (I := I) g r s b (rawTensorConnLapSmooth (I := I) g r s S)‖ ≤
      (∑ b ∈ Finset.range K, cL b) *
        ∑ b' ∈ Finset.range (K + 2), ‖iteratedCovGrad (I := I) g r s b' S‖ := by
  have hbig_nn : 0 ≤ ∑ b' ∈ Finset.range (K + 2), ‖iteratedCovGrad (I := I) g r s b' S‖ :=
    Finset.sum_nonneg (fun b' _ => norm_nonneg _)
  calc ∑ b ∈ Finset.range K,
      ‖iteratedCovGrad (I := I) g r s b (rawTensorConnLapSmooth (I := I) g r s S)‖
      ≤ ∑ b ∈ Finset.range K, cL b *
          ∑ b' ∈ Finset.range (K + 2), ‖iteratedCovGrad (I := I) g r s b' S‖ := by
        refine Finset.sum_le_sum (fun b hb => ?_)
        refine le_trans (hcL b S) ?_
        refine mul_le_mul_of_nonneg_left ?_ (hcL_nn b)
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun b' _ _ => norm_nonneg _)
        have hbK := Finset.mem_range.mp hb
        exact fun x hx => Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega)
    _ = (∑ b ∈ Finset.range K, cL b) *
          ∑ b' ∈ Finset.range (K + 2), ‖iteratedCovGrad (I := I) g r s b' S‖ := by
        rw [Finset.sum_mul]

private lemma bal_iter_jets (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ c : ℕ → ℕ → ℝ, (∀ γ q, 0 ≤ c γ q) ∧
      ∀ (γ q : ℕ) (S : SmoothCcTensor g r s),
        ‖iteratedCovGrad (I := I) g r s γ (oneMinusConnLapSmoothIter (I := I) g r s q S)‖ ≤
          c γ q * ∑ b ∈ Finset.range (γ + 2 * q + 1), ‖iteratedCovGrad (I := I) g r s b S‖ := by
  classical
  obtain ⟨cL, hcL_nn, hcL⟩ := bal_lap_jets (I := I) (M := M) g r s
  have hmain : ∀ q : ℕ, ∃ c : ℕ → ℝ, (∀ γ, 0 ≤ c γ) ∧
      ∀ (γ : ℕ) (S : SmoothCcTensor g r s),
        ‖iteratedCovGrad (I := I) g r s γ (oneMinusConnLapSmoothIter (I := I) g r s q S)‖ ≤
          c γ * ∑ b ∈ Finset.range (γ + 2 * q + 1), ‖iteratedCovGrad (I := I) g r s b S‖ := by
    intro q
    induction q with
    | zero =>
      refine ⟨fun _ => 1, fun _ => zero_le_one, fun γ S => ?_⟩
      rw [oneMinusConnLapSmoothIter_zero, one_mul]
      exact Finset.single_le_sum
        (f := fun b => ‖iteratedCovGrad (I := I) g r s b S‖)
        (fun b _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
    | succ q ih =>
      obtain ⟨cq, hcq_nn, hcq⟩ := ih
      refine ⟨fun γ => cq γ * (1 + ∑ b ∈ Finset.range (γ + 2 * q + 1), cL b),
        fun γ => mul_nonneg (hcq_nn γ)
          (by have : 0 ≤ ∑ b ∈ Finset.range (γ + 2 * q + 1), cL b :=
                Finset.sum_nonneg (fun b _ => hcL_nn b)
              linarith),
        fun γ S => ?_⟩
      have hsplit := bal_iter_succ_inner (I := I) (M := M) g r s q S
      rw [hsplit, iteratedCovGrad_sub]
      refine le_trans (norm_sub_le _ _) ?_
      have hbig_nn : 0 ≤ ∑ b ∈ Finset.range (γ + 2 * (q + 1) + 1),
          ‖iteratedCovGrad (I := I) g r s b S‖ :=
        Finset.sum_nonneg (fun b _ => norm_nonneg _)
      have hmono : ∑ b ∈ Finset.range (γ + 2 * q + 1),
          ‖iteratedCovGrad (I := I) g r s b S‖ ≤
          ∑ b ∈ Finset.range (γ + 2 * (q + 1) + 1),
            ‖iteratedCovGrad (I := I) g r s b S‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun x hx => Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega))
          (fun b _ _ => norm_nonneg _)
      have h1 : ‖iteratedCovGrad (I := I) g r s γ
          (oneMinusConnLapSmoothIter (I := I) g r s q S)‖ ≤
          cq γ * ∑ b ∈ Finset.range (γ + 2 * (q + 1) + 1),
            ‖iteratedCovGrad (I := I) g r s b S‖ :=
        le_trans (hcq γ S) (mul_le_mul_of_nonneg_left hmono (hcq_nn γ))
      have h2 : ‖iteratedCovGrad (I := I) g r s γ
          (oneMinusConnLapSmoothIter (I := I) g r s q
            (rawTensorConnLapSmooth (I := I) g r s S))‖ ≤
          (cq γ * ∑ b ∈ Finset.range (γ + 2 * q + 1), cL b) *
            ∑ b ∈ Finset.range (γ + 2 * (q + 1) + 1),
              ‖iteratedCovGrad (I := I) g r s b S‖ := by
        refine le_trans (hcq γ (rawTensorConnLapSmooth (I := I) g r s S)) ?_
        have hsum := bal_sum_lap_jets (I := I) (M := M) g r s cL hcL_nn hcL
          (γ + 2 * q + 1) S
        have hK2 : γ + 2 * q + 1 + 2 = γ + 2 * (q + 1) + 1 := by omega
        rw [hK2] at hsum
        calc cq γ * ∑ b ∈ Finset.range (γ + 2 * q + 1),
            ‖iteratedCovGrad (I := I) g r s b
              (rawTensorConnLapSmooth (I := I) g r s S)‖
            ≤ cq γ * ((∑ b ∈ Finset.range (γ + 2 * q + 1), cL b) *
                ∑ b ∈ Finset.range (γ + 2 * (q + 1) + 1),
                  ‖iteratedCovGrad (I := I) g r s b S‖) :=
              mul_le_mul_of_nonneg_left hsum (hcq_nn γ)
          _ = (cq γ * ∑ b ∈ Finset.range (γ + 2 * q + 1), cL b) *
                ∑ b ∈ Finset.range (γ + 2 * (q + 1) + 1),
                  ‖iteratedCovGrad (I := I) g r s b S‖ := by ring
      calc ‖iteratedCovGrad (I := I) g r s γ
            (oneMinusConnLapSmoothIter (I := I) g r s q S)‖ +
          ‖iteratedCovGrad (I := I) g r s γ
            (oneMinusConnLapSmoothIter (I := I) g r s q
              (rawTensorConnLapSmooth (I := I) g r s S))‖
          ≤ cq γ * ∑ b ∈ Finset.range (γ + 2 * (q + 1) + 1),
                ‖iteratedCovGrad (I := I) g r s b S‖ +
              (cq γ * ∑ b ∈ Finset.range (γ + 2 * q + 1), cL b) *
                ∑ b ∈ Finset.range (γ + 2 * (q + 1) + 1),
                  ‖iteratedCovGrad (I := I) g r s b S‖ := add_le_add h1 h2
        _ = cq γ * (1 + ∑ b ∈ Finset.range (γ + 2 * q + 1), cL b) *
              ∑ b ∈ Finset.range (γ + 2 * (q + 1) + 1),
                ‖iteratedCovGrad (I := I) g r s b S‖ := by ring
  choose cfun hcfun_nn hcfun using hmain
  exact ⟨fun γ q => cfun q γ, fun γ q => hcfun_nn q γ, fun γ q S => hcfun q γ S⟩

private lemma bal_lap_jets_exact (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ c : ℕ → ℝ, (∀ b, 0 ≤ c b) ∧
      ∀ (b : ℕ) (S : SmoothCcTensor g r s),
        ‖iteratedCovGrad (I := I) g r s b (rawTensorConnLapSmooth (I := I) g r s S)‖ ≤
          ‖iteratedCovGrad (I := I) g r s (b + 2) S‖ +
            c b * ∑ b' ∈ Finset.range (b + 2), ‖iteratedCovGrad (I := I) g r s b' S‖ := by
  classical
  have hG2fam : ∀ b : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ Y : SmoothCcTensor g r (s + b),
      ‖rawTensorConnLapSmooth (I := I) g r (s + b) Y‖ ≤
        ‖iteratedCovGrad (I := I) g r (s + b) 2 Y‖ +
          c * (‖iteratedCovGrad (I := I) g r (s + b) 1 Y‖ + ‖Y‖) :=
    fun b => bal_G2 (I := I) (M := M) g r (s + b)
  choose cG hcG_nn hcG using hG2fam
  have hTfam : ∀ m : ℕ, ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧
      ∀ (j : ℕ) (S : SmoothCcTensor g r s),
        ‖iteratedCovGrad (I := I) g r (s + m) j
            (rawTensorConnLapSmooth (I := I) g r (s + m)
                (iteratedCovGrad (I := I) g r s m S) -
              iteratedCovGrad (I := I) g r s m
                (rawTensorConnLapSmooth (I := I) g r s S))‖ ≤
          K j * ∑ b ∈ Finset.range (m + j + 2), ‖iteratedCovGrad (I := I) g r s b S‖ :=
    fun m => bal_comm_tower (I := I) (M := M) g r s m
  choose KT hKT_nn hKT using hTfam
  refine ⟨fun b => cG b + cG b + KT b 0,
    fun b => by have := hcG_nn b; have := hKT_nn b 0; linarith, fun b S => ?_⟩
  set Sb : ℝ := ∑ b' ∈ Finset.range (b + 2), ‖iteratedCovGrad (I := I) g r s b' S‖
    with hSb_def
  have hSb_nn : 0 ≤ Sb := Finset.sum_nonneg (fun b' _ => norm_nonneg _)
  have hsingle : ∀ b' : ℕ, b' < b + 2 →
      ‖iteratedCovGrad (I := I) g r s b' S‖ ≤ Sb := by
    intro b' hb'
    exact Finset.single_le_sum (f := fun b'' => ‖iteratedCovGrad (I := I) g r s b'' S‖)
      (fun b'' _ => norm_nonneg _) (Finset.mem_range.mpr hb')
  have hdecomp : iteratedCovGrad (I := I) g r s b (rawTensorConnLapSmooth (I := I) g r s S) =
      rawTensorConnLapSmooth (I := I) g r (s + b) (iteratedCovGrad (I := I) g r s b S) -
        (rawTensorConnLapSmooth (I := I) g r (s + b) (iteratedCovGrad (I := I) g r s b S) -
          iteratedCovGrad (I := I) g r s b (rawTensorConnLapSmooth (I := I) g r s S)) := by
    abel
  rw [hdecomp]
  refine le_trans (norm_sub_le _ _) ?_
  have hpiece1 : ‖rawTensorConnLapSmooth (I := I) g r (s + b)
      (iteratedCovGrad (I := I) g r s b S)‖ ≤
      ‖iteratedCovGrad (I := I) g r s (b + 2) S‖ + (cG b + cG b) * Sb := by
    refine le_trans (hcG b (iteratedCovGrad (I := I) g r s b S)) ?_
    have h2 : ‖iteratedCovGrad (I := I) g r (s + b) 2 (iteratedCovGrad (I := I) g r s b S)‖ =
        ‖iteratedCovGrad (I := I) g r s (b + 2) S‖ :=
      bal_norm_icg_comp (I := I) (M := M) g r s b 2 S
    have h1 : ‖iteratedCovGrad (I := I) g r (s + b) 1 (iteratedCovGrad (I := I) g r s b S)‖ =
        ‖iteratedCovGrad (I := I) g r s (b + 1) S‖ :=
      bal_norm_icg_comp (I := I) (M := M) g r s b 1 S
    rw [h2, h1]
    have e1 : ‖iteratedCovGrad (I := I) g r s (b + 1) S‖ ≤ Sb := hsingle (b + 1) (by omega)
    have e0 : ‖iteratedCovGrad (I := I) g r s b S‖ ≤ Sb := hsingle b (by omega)
    nlinarith [hcG_nn b]
  have hpiece2 : ‖rawTensorConnLapSmooth (I := I) g r (s + b)
      (iteratedCovGrad (I := I) g r s b S) -
        iteratedCovGrad (I := I) g r s b (rawTensorConnLapSmooth (I := I) g r s S)‖ ≤
      KT b 0 * Sb := by
    have h := hKT b 0 S
    have h0 : ‖iteratedCovGrad (I := I) g r (s + b) 0
        (rawTensorConnLapSmooth (I := I) g r (s + b)
            (iteratedCovGrad (I := I) g r s b S) -
          iteratedCovGrad (I := I) g r s b
            (rawTensorConnLapSmooth (I := I) g r s S))‖ =
        ‖rawTensorConnLapSmooth (I := I) g r (s + b)
            (iteratedCovGrad (I := I) g r s b S) -
          iteratedCovGrad (I := I) g r s b
            (rawTensorConnLapSmooth (I := I) g r s S)‖ := by
      rw [iteratedCovGrad_zero]
    rw [h0] at h
    exact h
  linarith [hpiece1, hpiece2]

private lemma bal_Ccore (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ c : ℕ → ℝ, (∀ p, 0 ≤ c p) ∧
      ∀ (p : ℕ) (S : SmoothCcTensor g r s),
        ‖oneMinusConnLapSmoothIter (I := I) g r s p S‖ ≤
          ‖iteratedCovGrad (I := I) g r s (2 * p) S‖ +
            c p * ∑ b ∈ Finset.range (2 * p), ‖iteratedCovGrad (I := I) g r s b S‖ ∧
        ‖covGrad (I := I) (M := M) g r s (oneMinusConnLapSmoothIter (I := I) g r s p S)‖ ≤
          ‖iteratedCovGrad (I := I) g r s (2 * p + 1) S‖ +
            c p * ∑ b ∈ Finset.range (2 * p + 1), ‖iteratedCovGrad (I := I) g r s b S‖ := by
  classical
  obtain ⟨cL, hcL_nn, hcL⟩ := bal_lap_jets (I := I) (M := M) g r s
  obtain ⟨cE, hcE_nn, hcE⟩ := bal_lap_jets_exact (I := I) (M := M) g r s
  have hmain : ∀ p : ℕ, ∃ c : ℝ, 0 ≤ c ∧
      ∀ S : SmoothCcTensor g r s,
        ‖oneMinusConnLapSmoothIter (I := I) g r s p S‖ ≤
          ‖iteratedCovGrad (I := I) g r s (2 * p) S‖ +
            c * ∑ b ∈ Finset.range (2 * p), ‖iteratedCovGrad (I := I) g r s b S‖ ∧
        ‖covGrad (I := I) (M := M) g r s (oneMinusConnLapSmoothIter (I := I) g r s p S)‖ ≤
          ‖iteratedCovGrad (I := I) g r s (2 * p + 1) S‖ +
            c * ∑ b ∈ Finset.range (2 * p + 1), ‖iteratedCovGrad (I := I) g r s b S‖ := by
    intro p
    induction p with
    | zero =>
      refine ⟨0, le_refl 0, fun S => ⟨?_, ?_⟩⟩
      · rw [oneMinusConnLapSmoothIter_zero]
        simp only [Nat.mul_zero, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
        rw [iteratedCovGrad_zero]
      · rw [oneMinusConnLapSmoothIter_zero]
        show ‖covGrad (I := I) (M := M) g r s S‖ ≤
          ‖iteratedCovGrad (I := I) g r s 1 S‖ +
            0 * ∑ b ∈ Finset.range 1, ‖iteratedCovGrad (I := I) g r s b S‖
        rw [bal_icg_one (I := I) (M := M) g r s S]
        simp
    | succ p ih =>
      obtain ⟨cp, hcp_nn, hcp⟩ := ih
      set CL : ℝ := ∑ b ∈ Finset.range (2 * p + 1), cL b with hCL_def
      have hCL_nn : 0 ≤ CL := Finset.sum_nonneg (fun b _ => hcL_nn b)
      refine ⟨1 + cE (2 * p) + cE (2 * p + 1) + cp * (2 + CL),
        by nlinarith [hcE_nn (2 * p), hcE_nn (2 * p + 1)], fun S => ?_⟩
      set ΔS : SmoothCcTensor g r s := rawTensorConnLapSmooth (I := I) g r s S with hΔS_def
      have hsplit := bal_iter_succ_inner (I := I) (M := M) g r s p S
      constructor
      · set Big : ℝ := ∑ b ∈ Finset.range (2 * (p + 1)),
          ‖iteratedCovGrad (I := I) g r s b S‖ with hBig_def
        have hBig_nn : 0 ≤ Big := Finset.sum_nonneg (fun b _ => norm_nonneg _)
        have hsingleB : ∀ b' : ℕ, b' < 2 * (p + 1) →
            ‖iteratedCovGrad (I := I) g r s b' S‖ ≤ Big := fun b' hb' =>
          Finset.single_le_sum (f := fun b'' => ‖iteratedCovGrad (I := I) g r s b'' S‖)
            (fun b'' _ => norm_nonneg _) (Finset.mem_range.mpr hb')
        have hmonoB : ∑ b ∈ Finset.range (2 * p),
            ‖iteratedCovGrad (I := I) g r s b S‖ ≤ Big :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun x hx => Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega))
            (fun b _ _ => norm_nonneg _)
        rw [hsplit]
        refine le_trans (norm_sub_le _ _) ?_
        have h1 := (hcp S).1
        have h2 := (hcp ΔS).1
        have htop : ‖iteratedCovGrad (I := I) g r s (2 * p) ΔS‖ ≤
            ‖iteratedCovGrad (I := I) g r s (2 * (p + 1)) S‖ + cE (2 * p) * Big := by
          have h := hcE (2 * p) S
          rw [show 2 * p + 2 = 2 * (p + 1) from by omega, ← hBig_def] at h
          exact h
        have hlow : ∑ b ∈ Finset.range (2 * p),
            ‖iteratedCovGrad (I := I) g r s b ΔS‖ ≤ CL * Big := by
          have h := bal_sum_lap_jets (I := I) (M := M) g r s cL hcL_nn hcL (2 * p) S
          have hle1 : ∑ b ∈ Finset.range (2 * p), cL b ≤ CL := by
            rw [hCL_def]
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (fun x hx => Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega))
              (fun b _ _ => hcL_nn b)
          rw [show 2 * p + 2 = 2 * (p + 1) from by omega, ← hBig_def] at h
          refine le_trans h (mul_le_mul_of_nonneg_right hle1 hBig_nn)
        have htop_prev : ‖iteratedCovGrad (I := I) g r s (2 * p) S‖ ≤ Big :=
          hsingleB (2 * p) (by omega)
        calc ‖oneMinusConnLapSmoothIter (I := I) g r s p S‖ +
            ‖oneMinusConnLapSmoothIter (I := I) g r s p ΔS‖
            ≤ (‖iteratedCovGrad (I := I) g r s (2 * p) S‖ +
                cp * ∑ b ∈ Finset.range (2 * p), ‖iteratedCovGrad (I := I) g r s b S‖) +
              (‖iteratedCovGrad (I := I) g r s (2 * p) ΔS‖ +
                cp * ∑ b ∈ Finset.range (2 * p),
                  ‖iteratedCovGrad (I := I) g r s b ΔS‖) := add_le_add h1 h2
          _ ≤ ‖iteratedCovGrad (I := I) g r s (2 * (p + 1)) S‖ +
              (1 + cE (2 * p) + cE (2 * p + 1) + cp * (2 + CL)) * Big := by
            have e1 : cp * ∑ b ∈ Finset.range (2 * p),
                ‖iteratedCovGrad (I := I) g r s b S‖ ≤ cp * Big :=
              mul_le_mul_of_nonneg_left hmonoB hcp_nn
            have e2 : cp * ∑ b ∈ Finset.range (2 * p),
                ‖iteratedCovGrad (I := I) g r s b ΔS‖ ≤ cp * (CL * Big) :=
              mul_le_mul_of_nonneg_left hlow hcp_nn
            nlinarith [hcE_nn (2 * p + 1), hcp_nn, hCL_nn, hBig_nn, htop, htop_prev]
      · set Big : ℝ := ∑ b ∈ Finset.range (2 * (p + 1) + 1),
          ‖iteratedCovGrad (I := I) g r s b S‖ with hBig_def
        have hBig_nn : 0 ≤ Big := Finset.sum_nonneg (fun b _ => norm_nonneg _)
        have hsingleB : ∀ b' : ℕ, b' < 2 * (p + 1) + 1 →
            ‖iteratedCovGrad (I := I) g r s b' S‖ ≤ Big := fun b' hb' =>
          Finset.single_le_sum (f := fun b'' => ‖iteratedCovGrad (I := I) g r s b'' S‖)
            (fun b'' _ => norm_nonneg _) (Finset.mem_range.mpr hb')
        have hmonoB : ∑ b ∈ Finset.range (2 * p + 1),
            ‖iteratedCovGrad (I := I) g r s b S‖ ≤ Big :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun x hx => Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega))
            (fun b _ _ => norm_nonneg _)
        rw [hsplit, covGrad_sub]
        refine le_trans (norm_sub_le _ _) ?_
        have h1 := (hcp S).2
        have h2 := (hcp ΔS).2
        have htop : ‖iteratedCovGrad (I := I) g r s (2 * p + 1) ΔS‖ ≤
            ‖iteratedCovGrad (I := I) g r s (2 * (p + 1) + 1) S‖ +
              cE (2 * p + 1) * Big := by
          have h := hcE (2 * p + 1) S
          rw [show 2 * p + 1 + 2 = 2 * (p + 1) + 1 from by omega, ← hBig_def] at h
          exact h
        have hlow : ∑ b ∈ Finset.range (2 * p + 1),
            ‖iteratedCovGrad (I := I) g r s b ΔS‖ ≤ CL * Big := by
          have h := bal_sum_lap_jets (I := I) (M := M) g r s cL hcL_nn hcL (2 * p + 1) S
          rw [show 2 * p + 1 + 2 = 2 * (p + 1) + 1 from by omega, ← hBig_def,
            ← hCL_def] at h
          exact h
        have htop_prev : ‖iteratedCovGrad (I := I) g r s (2 * p + 1) S‖ ≤ Big :=
          hsingleB (2 * p + 1) (by omega)
        calc ‖covGrad (I := I) (M := M) g r s (oneMinusConnLapSmoothIter (I := I) g r s p S)‖ +
            ‖covGrad (I := I) (M := M) g r s (oneMinusConnLapSmoothIter (I := I) g r s p ΔS)‖
            ≤ (‖iteratedCovGrad (I := I) g r s (2 * p + 1) S‖ +
                cp * ∑ b ∈ Finset.range (2 * p + 1), ‖iteratedCovGrad (I := I) g r s b S‖) +
              (‖iteratedCovGrad (I := I) g r s (2 * p + 1) ΔS‖ +
                cp * ∑ b ∈ Finset.range (2 * p + 1),
                  ‖iteratedCovGrad (I := I) g r s b ΔS‖) := add_le_add h1 h2
          _ ≤ ‖iteratedCovGrad (I := I) g r s (2 * (p + 1) + 1) S‖ +
              (1 + cE (2 * p) + cE (2 * p + 1) + cp * (2 + CL)) * Big := by
            have e1 : cp * ∑ b ∈ Finset.range (2 * p + 1),
                ‖iteratedCovGrad (I := I) g r s b S‖ ≤ cp * Big :=
              mul_le_mul_of_nonneg_left hmonoB hcp_nn
            have e2 : cp * ∑ b ∈ Finset.range (2 * p + 1),
                ‖iteratedCovGrad (I := I) g r s b ΔS‖ ≤ cp * (CL * Big) :=
              mul_le_mul_of_nonneg_left hlow hcp_nn
            nlinarith [hcE_nn (2 * p), hcp_nn, hCL_nn, hBig_nn, htop, htop_prev]
  choose cfun hcfun_nn hcfun using hmain
  exact ⟨cfun, hcfun_nn, fun p S => hcfun p S⟩

private lemma bal_hs_mono (g₀ : SmoothRiemannianMetric I M)
    {σ τ : ℝ} (hστ : σ ≤ τ) (w : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ w‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ τ w‖ := by
  have hbσ : smoothCcToTensorHs (I := I) (M := M) g₀ σ w =
      ccSpectralEmbed (I := I) (M := M) g₀ σ w := tensorHs.ext (funext fun i => rfl)
  have hbτ : smoothCcToTensorHs (I := I) (M := M) g₀ τ w =
      ccSpectralEmbed (I := I) (M := M) g₀ τ w := tensorHs.ext (funext fun i => rfl)
  rw [hbσ, hbτ]
  exact ccSpectralEmbed_norm_mono (I := I) (M := M) g₀ hστ w

private lemma bal_jet_hs_gap (g₀ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ u : SmoothCcTensor g₀ 0 2,
      ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u‖ ≤
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℝ) + 1) u‖ +
          Cg * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ) u‖ := by
  obtain ⟨Cgap, hCgap_nn, hgap⟩ :=
    exists_iteratedCovGrad_l2NormSq_le_smoothCcToTensorHs_succ_add_lower
      (I := I) (M := M) g₀ n
  refine ⟨Real.sqrt Cgap, Real.sqrt_nonneg _, fun u => ?_⟩
  have h := hgap u
  rw [SmoothCcTensor.norm_toL2] at h
  set A : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℝ) + 1) u‖ with hA_def
  set B : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ) u‖ with hB_def
  have hA_nn : 0 ≤ A := norm_nonneg _
  have hB_nn : 0 ≤ B := norm_nonneg _
  refine le_of_sq_le_sq ?_ (by positivity)
  have hs : Real.sqrt Cgap ^ 2 = Cgap := Real.sq_sqrt hCgap_nn
  nlinarith [h, mul_nonneg (mul_nonneg hA_nn (Real.sqrt_nonneg Cgap)) hB_nn]

private lemma bal_hs_logConvex (g₀ : SmoothRiemannianMetric I M)
    (T₀ : SmoothCcTensor g₀ 0 2) (k : ℕ) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) T₀‖ ^ 2 ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) T₀‖ *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ) T₀‖ := by
  have hv := DifferentialGeometry.Analysis.Parabolic.QuasiLinear.tensorHs_incl_norm_sq_le
    (I := I) (M := M) (g := g₀) (r := 0) (s := 2) (a := (k : ℝ))
    (smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℝ) + 2) T₀)
  rw [tensorHsInclusion_smoothCcToTensorHs (I := I) (M := M) g₀
        (show (k : ℝ) + 1 ≤ (k : ℝ) + 2 by linarith) T₀,
      tensorHsInclusion_smoothCcToTensorHs (I := I) (M := M) g₀
        (show (k : ℝ) ≤ (k : ℝ) + 2 by linarith) T₀] at hv
  rw [smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring) T₀,
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (show ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 by push_cast; ring) T₀]
  exact hv

private lemma bal_hs_extreme_interp {f : ℕ → ℝ} (hf_nn : ∀ k, 0 ≤ f k)
    (hlc : ∀ k, f (k + 1) ^ 2 ≤ f (k + 2) * f k)
    (hmono : ∀ {k k' : ℕ}, k ≤ k' → f k ≤ f k')
    {B : ℝ} {m₀ : ℕ} (hB : ∀ k, k ≤ m₀ → f k ≤ B)
    {α β γ : ℕ} (hαγ : α ≤ γ) (hβγ : β ≤ γ) (hsum : α + β ≤ m₀ + γ) :
    f α * f β ≤ B * f γ := by
  have hkey : ∀ σ₁ σ₂ : ℕ, σ₁ ≤ σ₂ → σ₁ ≤ γ → σ₂ ≤ γ → σ₁ + σ₂ ≤ m₀ + γ →
      f σ₁ * f σ₂ ≤ B * f γ := by
    intro σ₁ σ₂ hle h1γ h2γ hs
    by_cases hge : γ ≤ σ₁ + σ₂
    · have hex := DifferentialGeometry.Analysis.Parabolic.QuasiLinear.logConvex_extreme_pair
        hf_nn hlc (σ₁ := σ₁) (σ₂ := σ₂) (τ₁ := σ₁ + σ₂ - γ) (τ₂ := γ)
        (by omega) hle (by omega) (by omega)
      have hlowB : f (σ₁ + σ₂ - γ) ≤ B := hB _ (by omega)
      exact le_trans hex (mul_le_mul_of_nonneg_right hlowB (hf_nn γ))
    · have hex := DifferentialGeometry.Analysis.Parabolic.QuasiLinear.logConvex_extreme_pair
        hf_nn hlc (σ₁ := σ₁) (σ₂ := σ₂) (τ₁ := 0) (τ₂ := σ₁ + σ₂)
        (Nat.zero_le _) hle (by omega) (by omega)
      have hf0B : f 0 ≤ B := hB 0 (Nat.zero_le _)
      have hαβγ : f (σ₁ + σ₂) ≤ f γ := hmono (by omega)
      exact le_trans hex (mul_le_mul hf0B hαβγ (hf_nn _) (le_trans (hf_nn 0) hf0B))
  rcases le_total α β with hab | hab
  · exact hkey α β hab hαγ hβγ hsum
  · rw [mul_comm]; exact hkey β α hab hβγ hαγ (by omega)

private lemma bal_sqrt_pair_two (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) :
    Real.sqrt ((a + b) ^ 2 + (c + d) ^ 2) ≤
      Real.sqrt (a ^ 2 + c ^ 2) + Real.sqrt (b ^ 2 + d ^ 2) := by
  have hcs : a * b + c * d ≤ Real.sqrt (a ^ 2 + c ^ 2) * Real.sqrt (b ^ 2 + d ^ 2) := by
    have h1 : (a * b + c * d) ^ 2 ≤ (a ^ 2 + c ^ 2) * (b ^ 2 + d ^ 2) := by
      nlinarith [sq_nonneg (a * d - b * c)]
    have h2 : 0 ≤ a * b + c * d := by positivity
    have h3 : Real.sqrt ((a * b + c * d) ^ 2) ≤
        Real.sqrt ((a ^ 2 + c ^ 2) * (b ^ 2 + d ^ 2)) := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_sq h2, Real.sqrt_mul (by positivity)] at h3
    exact h3
  have hrhs_nn : 0 ≤ Real.sqrt (a ^ 2 + c ^ 2) + Real.sqrt (b ^ 2 + d ^ 2) := by positivity
  have hexp : (a + b) ^ 2 + (c + d) ^ 2 ≤
      (Real.sqrt (a ^ 2 + c ^ 2) + Real.sqrt (b ^ 2 + d ^ 2)) ^ 2 := by
    have e1 : Real.sqrt (a ^ 2 + c ^ 2) ^ 2 = a ^ 2 + c ^ 2 := Real.sq_sqrt (by positivity)
    have e2 : Real.sqrt (b ^ 2 + d ^ 2) ^ 2 = b ^ 2 + d ^ 2 := Real.sq_sqrt (by positivity)
    nlinarith [hcs]
  calc Real.sqrt ((a + b) ^ 2 + (c + d) ^ 2)
      ≤ Real.sqrt ((Real.sqrt (a ^ 2 + c ^ 2) + Real.sqrt (b ^ 2 + d ^ 2)) ^ 2) :=
        Real.sqrt_le_sqrt hexp
    _ = Real.sqrt (a ^ 2 + c ^ 2) + Real.sqrt (b ^ 2 + d ^ 2) := Real.sqrt_sq hrhs_nn

private lemma bal_sqrt_mono_pair {x' x y' y : ℝ} (hx' : 0 ≤ x') (hy' : 0 ≤ y')
    (hx : x' ≤ x) (hy : y' ≤ y) :
    Real.sqrt (x' ^ 2 + y' ^ 2) ≤ Real.sqrt (x ^ 2 + y ^ 2) := by
  refine Real.sqrt_le_sqrt ?_
  have h1 : x' ^ 2 ≤ x ^ 2 := by nlinarith
  have h2 : y' ^ 2 ≤ y ^ 2 := by nlinarith
  linarith

set_option maxHeartbeats 1600000 in
private lemma bal_h1_sum (g₀ : SmoothRiemannianMetric I M) (n : ℕ)
    (F : ℕ → SmoothCcTensor g₀ 0 2) :
    Real.sqrt (‖∑ i ∈ Finset.range n, F i‖ ^ 2 +
        ‖covGrad (I := I) (M := M) g₀ 0 2 (∑ i ∈ Finset.range n, F i)‖ ^ 2) ≤
      ∑ i ∈ Finset.range n,
        Real.sqrt (‖F i‖ ^ 2 + ‖covGrad (I := I) (M := M) g₀ 0 2 (F i)‖ ^ 2) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    have hcg0 : covGrad (I := I) (M := M) g₀ 0 2 (0 : SmoothCcTensor g₀ 0 2) = 0 := by
      have h := covGrad_sub (I := I) (M := M) g₀ 0 2
        (0 : SmoothCcTensor g₀ 0 2) (0 : SmoothCcTensor g₀ 0 2)
      rw [sub_self, sub_self] at h
      exact h
    rw [hcg0, norm_zero]
    simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hcg : covGrad (I := I) (M := M) g₀ 0 2 ((∑ i ∈ Finset.range n, F i) + F n) =
        covGrad (I := I) (M := M) g₀ 0 2 (∑ i ∈ Finset.range n, F i) +
          covGrad (I := I) (M := M) g₀ 0 2 (F n) :=
      covGrad_add (I := I) (M := M) g₀ 0 2 _ _
    have hm : Real.sqrt (‖(∑ i ∈ Finset.range n, F i) + F n‖ ^ 2 +
        ‖covGrad (I := I) (M := M) g₀ 0 2 ((∑ i ∈ Finset.range n, F i) + F n)‖ ^ 2) ≤
        Real.sqrt ((‖∑ i ∈ Finset.range n, F i‖ + ‖F n‖) ^ 2 +
          (‖covGrad (I := I) (M := M) g₀ 0 2 (∑ i ∈ Finset.range n, F i)‖ +
            ‖covGrad (I := I) (M := M) g₀ 0 2 (F n)‖) ^ 2) := by
      rw [hcg]
      exact bal_sqrt_mono_pair (norm_nonneg _) (norm_nonneg _)
        (norm_add_le _ _) (norm_add_le _ _)
    have hp2 := bal_sqrt_pair_two ‖∑ i ∈ Finset.range n, F i‖ ‖F n‖
      ‖covGrad (I := I) (M := M) g₀ 0 2 (∑ i ∈ Finset.range n, F i)‖
      ‖covGrad (I := I) (M := M) g₀ 0 2 (F n)‖
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    refine le_trans hm (le_trans hp2 ?_)
    exact add_le_add ih (le_refl _)

private lemma bal_score (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (T₀ : SmoothCcTensor g₀ 0 2)
    (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀)
    {u v γ : ℕ} (hv : v ≤ γ) (hsum : u + v ≤ (a + 2) + γ) (hu : u ≤ γ ∨ u ≤ a + 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((u : ℕ) : ℝ) T₀‖ *
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((v : ℕ) : ℝ) T₀‖ ≤
    R₀ * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((γ : ℕ) : ℝ) T₀‖ := by
  set f : ℕ → ℝ := fun k => ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ) T₀‖
    with hf_def
  have hf_nn : ∀ k, 0 ≤ f k := fun k => norm_nonneg _
  have hf_mono : ∀ {k k' : ℕ}, k ≤ k' → f k ≤ f k' := by
    intro k k' hk
    exact bal_hs_mono (I := I) (M := M) g₀ (by exact_mod_cast hk) T₀
  have hf_lc : ∀ k, f (k + 1) ^ 2 ≤ f (k + 2) * f k := fun k =>
    bal_hs_logConvex (I := I) (M := M) g₀ T₀ k
  have hf_ball : ∀ k, k ≤ a + 2 → f k ≤ R₀ := by
    intro k hk
    have h1 : f k ≤ f (a + 2) := hf_mono hk
    have h2 : f (a + 2) = ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [h2] at h1
    exact le_trans h1 hball
  rcases hu with huγ | hua
  · exact bal_hs_extreme_interp hf_nn hf_lc (fun {k k'} h => hf_mono h) hf_ball
      huγ hv hsum
  · have h1 : f u ≤ R₀ := hf_ball u hua
    have h2 : f v ≤ f γ := hf_mono hv
    calc f u * f v ≤ R₀ * f v := mul_le_mul_of_nonneg_right h1 (hf_nn v)
      _ ≤ R₀ * f γ := mul_le_mul_of_nonneg_left h2 hR₀

set_option linter.unusedSectionVars false in
private lemma bal_env_lin (g₀ : SmoothRiemannianMetric I M)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) (εa : ℝ) (hεa_nn : 0 ≤ εa)
    (C₀ : SmoothCcTensor g₀ 2 2) (T₀ : SmoothCcTensor g₀ 0 2)
    (henv : ∀ i : ℕ,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2 ≤
        Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
          εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2)
    (i : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ≤
      Real.sqrt (Kc i) * (1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖) +
        εa * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ := by
  have hS_nn : 0 ≤ ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ :=
    Finset.sum_nonneg (fun j _ => norm_nonneg _)
  have hrhs_nn : 0 ≤ Real.sqrt (Kc i) * (1 + ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖) +
      εa * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ := by
    have := Real.sqrt_nonneg (Kc i)
    have := norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀)
    nlinarith
  refine le_of_sq_le_sq ?_ hrhs_nn
  have hsq_sum : ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 ≤
      (∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖) ^ 2 :=
    bal_sq_sum_le_sum_sq _ (fun j => norm_nonneg _)
  have hKsq : Real.sqrt (Kc i) ^ 2 = Kc i := Real.sq_sqrt (hKc_nn i)
  have h := henv i
  nlinarith [h, hsq_sum, hKc_nn i, hS_nn, Real.sqrt_nonneg (Kc i), hεa_nn,
    norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀),
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg (Kc i)) hS_nn)
      (mul_nonneg hεa_nn (norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀))),
    mul_nonneg (Real.sqrt_nonneg (Kc i))
      (mul_nonneg hεa_nn (norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀)))]

private lemma bal_jets_to_f (g₀ : SmoothRiemannianMetric I M) :
    ∃ CJ : ℕ → ℝ, (∀ j, 0 ≤ CJ j) ∧
      ∀ (j : ℕ) (T : SmoothCcTensor g₀ 0 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤
          CJ j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ) T‖ := by
  classical
  have hfam := fun n => exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general
    (I := I) (M := M) g₀ n
  choose CJ hCJ using hfam
  refine ⟨CJ, fun j => (hCJ j).1, fun j T => ?_⟩
  refine le_trans ?_ ((hCJ j).2 T)
  exact Finset.single_le_sum
    (f := fun b => ‖iteratedCovGrad (I := I) g₀ 0 2 b T‖)
    (fun b _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))

private lemma bal_l2_two_family (g : SmoothRiemannianMetric I M)
    {rz sz : ℕ} (Z : SmoothCcTensor g rz sz)
    (n1 n2 : ℕ) (c1 c2 : ℕ → ℝ) (_hc1 : ∀ i, 0 ≤ c1 i) (_hc2 : ∀ i, 0 ≤ c2 i)
    (rw1 sw1 : ℕ → ℕ) (F1 : (i : ℕ) → SmoothCcTensor g (rw1 i) (sw1 i))
    (rw2 sw2 : ℕ → ℕ) (F2 : (i : ℕ) → SmoothCcTensor g (rw2 i) (sw2 i))
    (hpt : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g rz sz x (Z.toSection x) ≤
      (∑ i ∈ Finset.range n1,
        c1 i * riemannianFiberNormSq (I := I) (M := M) g (rw1 i) (sw1 i) x
          ((F1 i).toSection x)) +
      ∑ i ∈ Finset.range n2,
        c2 i * riemannianFiberNormSq (I := I) (M := M) g (rw2 i) (sw2 i) x
          ((F2 i).toSection x)) :
    ‖Z‖ ^ 2 ≤ (∑ i ∈ Finset.range n1, c1 i * ‖F1 i‖ ^ 2) +
      ∑ i ∈ Finset.range n2, c2 i * ‖F2 i‖ ^ 2 := by
  have hint1 : ∀ i ∈ Finset.range n1, MeasureTheory.Integrable
      (fun x => c1 i * riemannianFiberNormSq (I := I) (M := M) g (rw1 i) (sw1 i) x
        ((F1 i).toSection x))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g) :=
    fun i _ => (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g
      (rw1 i) (sw1 i) (F1 i)).const_mul _
  have hint2 : ∀ i ∈ Finset.range n2, MeasureTheory.Integrable
      (fun x => c2 i * riemannianFiberNormSq (I := I) (M := M) g (rw2 i) (sw2 i) x
        ((F2 i).toSection x))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g) :=
    fun i _ => (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g
      (rw2 i) (sw2 i) (F2 i)).const_mul _
  have hint : MeasureTheory.Integrable
      (fun x =>
        (∑ i ∈ Finset.range n1,
          c1 i * riemannianFiberNormSq (I := I) (M := M) g (rw1 i) (sw1 i) x
            ((F1 i).toSection x)) +
        ∑ i ∈ Finset.range n2,
          c2 i * riemannianFiberNormSq (I := I) (M := M) g (rw2 i) (sw2 i) x
            ((F2 i).toSection x))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g) :=
    ((MeasureTheory.integrable_finset_sum _ hint1).add
      (MeasureTheory.integrable_finset_sum _ hint2))
  have h1 := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g rz sz
    Z _ hint hpt
  rw [MeasureTheory.integral_add (MeasureTheory.integrable_finset_sum _ hint1)
    (MeasureTheory.integrable_finset_sum _ hint2),
    MeasureTheory.integral_finset_sum _ hint1,
    MeasureTheory.integral_finset_sum _ hint2] at h1
  refine le_trans h1 (le_of_eq ?_)
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [MeasureTheory.integral_const_mul, SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g
        (rw1 i) (sw1 i)]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [MeasureTheory.integral_const_mul, SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g
        (rw2 i) (sw2 i)]

private lemma bal_fmono (g₀ : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g₀ 0 2)
    {j k : ℕ} (hjk : j ≤ k) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ) T₀‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ) T₀‖ :=
  bal_hs_mono (I := I) (M := M) g₀ (by exact_mod_cast hjk) T₀

private lemma bal_CJET (g₀ : SmoothRiemannianMetric I M)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) (εa : ℝ) (hεa_nn : 0 ≤ εa) :
    ∃ CC : ℕ → ℕ → ℝ, (∀ γ q, 0 ≤ CC γ q) ∧
      ∀ (C₀ : SmoothCcTensor g₀ 2 2) (T₀ : SmoothCcTensor g₀ 0 2),
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
              εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) →
        ∀ (γ q : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 2 2 γ
              (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)‖ ≤
            CC γ q * (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀
              ((γ + 2 * q + 2 : ℕ) : ℝ) T₀‖) := by
  classical
  obtain ⟨cit, hcit_nn, hcit⟩ := bal_iter_jets (I := I) (M := M) g₀ 2 2
  obtain ⟨CJ, hCJ_nn, hCJ⟩ := bal_jets_to_f (I := I) (M := M) g₀
  refine ⟨fun γ q => cit γ q * ∑ b ∈ Finset.range (γ + 2 * q + 1),
      (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) + εa * CJ (b + 2)),
    fun γ q => mul_nonneg (hcit_nn γ q) (Finset.sum_nonneg (fun b _ => by
      have h1 : 0 ≤ ∑ j ∈ Finset.range (b + 2), CJ j :=
        Finset.sum_nonneg (fun j _ => hCJ_nn j)
      have h2 := Real.sqrt_nonneg (Kc b)
      have h3 := hCJ_nn (b + 2)
      nlinarith)), ?_⟩
  intro C₀ T₀ henv γ q
  set fT : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((γ + 2 * q + 2 : ℕ) : ℝ) T₀‖
    with hfdef
  have hf_nn : 0 ≤ fT := norm_nonneg _
  refine le_trans (hcit γ q C₀) ?_
  have hterm : ∀ b ∈ Finset.range (γ + 2 * q + 1),
      ‖iteratedCovGrad (I := I) g₀ 2 2 b C₀‖ ≤
        (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) + εa * CJ (b + 2)) *
          (1 + fT) := by
    intro b hb
    have hbmem := Finset.mem_range.mp hb
    refine le_trans (bal_env_lin (I := I) (M := M) g₀ Kc hKc_nn εa hεa_nn C₀ T₀ henv b) ?_
    have hjets : ∀ j ∈ Finset.range (b + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤ CJ j * fT := by
      intro j hj
      have hjb := Finset.mem_range.mp hj
      refine le_trans (hCJ j T₀) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCJ_nn j)
      exact bal_fmono (I := I) (M := M) g₀ T₀ (by omega)
    have hsum : ∑ j ∈ Finset.range (b + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
        (∑ j ∈ Finset.range (b + 2), CJ j) * fT := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum hjets
    have htop : ‖iteratedCovGrad (I := I) g₀ 0 2 (b + 2) T₀‖ ≤ CJ (b + 2) * fT := by
      refine le_trans (hCJ (b + 2) T₀) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCJ_nn (b + 2))
      exact bal_fmono (I := I) (M := M) g₀ T₀ (by omega)
    have hCJsum_nn : 0 ≤ ∑ j ∈ Finset.range (b + 2), CJ j :=
      Finset.sum_nonneg (fun j _ => hCJ_nn j)
    nlinarith [Real.sqrt_nonneg (Kc b), hεa_nn, hCJ_nn (b + 2), hf_nn, hsum, htop,
      mul_nonneg (Real.sqrt_nonneg (Kc b)) hCJsum_nn,
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg (Kc b)) hCJsum_nn) hf_nn]
  calc cit γ q * ∑ b ∈ Finset.range (γ + 2 * q + 1),
      ‖iteratedCovGrad (I := I) g₀ 2 2 b C₀‖
      ≤ cit γ q * ∑ b ∈ Finset.range (γ + 2 * q + 1),
          (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) + εa * CJ (b + 2)) *
            (1 + fT) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (hcit_nn γ q)
    _ = cit γ q * (∑ b ∈ Finset.range (γ + 2 * q + 1),
          (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) + εa * CJ (b + 2))) *
            (1 + fT) := by
        rw [← Finset.sum_mul]
        ring

private lemma bal_CSUP (g₀ : SmoothRiemannianMetric I M)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) (εa : ℝ) (hεa_nn : 0 ≤ εa) :
    ∃ CCS : ℕ → ℕ → ℝ, (∀ γ q, 0 ≤ CCS γ q) ∧
      ∀ (C₀ : SmoothCcTensor g₀ 2 2) (T₀ : SmoothCcTensor g₀ 0 2),
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
              εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) →
        ∀ (γ q : ℕ) (x : M),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + γ) x
              ((iteratedCovGrad (I := I) g₀ 2 2 γ
                (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)).toSection x) ≤
            (CCS γ q * (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀
              ((γ + (Module.finrank ℝ E / 2 + 2) + 2 * q + 1 : ℕ) : ℝ) T₀‖)) ^ 2 := by
  classical
  obtain ⟨CC, hCC_nn, hCC⟩ := bal_CJET (I := I) (M := M) g₀ Kc hKc_nn εa hεa_nn
  have hfam := fun γ : ℕ =>
    exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g₀ 2 (2 + γ)
  choose Csh hCsh_nn hCsh using hfam
  set w : ℕ := Module.finrank ℝ E / 2 + 2 with hw_def
  refine ⟨fun γ q => Csh γ * ∑ t ∈ Finset.range w, CC (γ + t) q,
    fun γ q => mul_nonneg (hCsh_nn γ) (Finset.sum_nonneg (fun t _ => hCC_nn (γ + t) q)),
    ?_⟩
  intro C₀ T₀ henv γ q x
  dsimp only
  set fT : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀
    ((γ + w + 2 * q + 1 : ℕ) : ℝ) T₀‖ with hfT_def
  have hfT_nn : 0 ≤ fT := norm_nonneg _
  have h := hCsh γ (iteratedCovGrad (I := I) g₀ 2 2 γ
    (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)) x
  refine le_trans h ?_
  have hterm : ∀ t ∈ Finset.range w,
      ‖iteratedCovGrad (I := I) g₀ 2 (2 + γ) t
          (iteratedCovGrad (I := I) g₀ 2 2 γ
            (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀))‖ ^ 2 ≤
        (CC (γ + t) q * (1 + fT)) ^ 2 := by
    intro t ht
    have htw := Finset.mem_range.mp ht
    have hcomp : ‖iteratedCovGrad (I := I) g₀ 2 (2 + γ) t
        (iteratedCovGrad (I := I) g₀ 2 2 γ
          (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀))‖ =
        ‖iteratedCovGrad (I := I) g₀ 2 2 (γ + t)
          (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)‖ :=
      bal_norm_icg_comp (I := I) (M := M) g₀ 2 2 γ t
        (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
    rw [hcomp]
    have hb := hCC C₀ T₀ henv (γ + t) q
    have hmono : ‖smoothCcToTensorHs (I := I) (M := M) g₀
        ((γ + t + 2 * q + 2 : ℕ) : ℝ) T₀‖ ≤ fT := by
      rw [hfT_def]
      exact bal_fmono (I := I) (M := M) g₀ T₀ (by omega)
    have hle : ‖iteratedCovGrad (I := I) g₀ 2 2 (γ + t)
        (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)‖ ≤
        CC (γ + t) q * (1 + fT) := by
      refine le_trans hb ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCC_nn (γ + t) q)
      linarith
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm)
    (sq_nonneg (Csh γ))) ?_
  have hsq : ∑ t ∈ Finset.range w, (CC (γ + t) q * (1 + fT)) ^ 2 ≤
      ((∑ t ∈ Finset.range w, CC (γ + t) q) * (1 + fT)) ^ 2 := by
    have h1 : ∑ t ∈ Finset.range w, (CC (γ + t) q * (1 + fT)) ^ 2 ≤
        (∑ t ∈ Finset.range w, CC (γ + t) q * (1 + fT)) ^ 2 :=
      bal_sq_sum_le_sum_sq _ (fun t => mul_nonneg (hCC_nn (γ + t) q) (by linarith))
    rw [← Finset.sum_mul] at h1
    exact h1
  calc Csh γ ^ 2 * ∑ t ∈ Finset.range w, (CC (γ + t) q * (1 + fT)) ^ 2
      ≤ Csh γ ^ 2 * ((∑ t ∈ Finset.range w, CC (γ + t) q) * (1 + fT)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    _ = ((Csh γ * ∑ t ∈ Finset.range w, CC (γ + t) q) * (1 + fT)) ^ 2 := by ring

private lemma bal_DL2 (g₀ : SmoothRiemannianMetric I M) :
    ∃ CDL : ℕ → ℝ, (∀ l, 0 ≤ CDL l) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2) (l : ℕ),
        ‖iteratedCovGrad (I := I) g₀ 0 2 l
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ ≤
          CDL l * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + 2 : ℕ) : ℝ) T₀‖ := by
  classical
  obtain ⟨cL, hcL_nn, hcL⟩ := bal_lap_jets (I := I) (M := M) g₀ 0 2
  obtain ⟨CJ, hCJ_nn, hCJ⟩ := bal_jets_to_f (I := I) (M := M) g₀
  refine ⟨fun l => cL l * ∑ b ∈ Finset.range (l + 3), CJ b,
    fun l => mul_nonneg (hcL_nn l) (Finset.sum_nonneg (fun b _ => hCJ_nn b)), ?_⟩
  intro T₀ l
  refine le_trans (hcL l T₀) ?_
  have hterm : ∀ b ∈ Finset.range (l + 3),
      ‖iteratedCovGrad (I := I) g₀ 0 2 b T₀‖ ≤
        CJ b * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + 2 : ℕ) : ℝ) T₀‖ := by
    intro b hb
    have hbl := Finset.mem_range.mp hb
    refine le_trans (hCJ b T₀) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCJ_nn b)
    exact bal_fmono (I := I) (M := M) g₀ T₀ (by omega)
  calc cL l * ∑ b ∈ Finset.range (l + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 b T₀‖
      ≤ cL l * ∑ b ∈ Finset.range (l + 3),
          CJ b * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + 2 : ℕ) : ℝ) T₀‖ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (hcL_nn l)
    _ = cL l * (∑ b ∈ Finset.range (l + 3), CJ b) *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + 2 : ℕ) : ℝ) T₀‖ := by
        rw [← Finset.sum_mul]
        ring

private lemma bal_DSUPD (g₀ : SmoothRiemannianMetric I M) :
    ∃ CDS : ℕ → ℝ, (∀ l, 0 ≤ CDS l) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2) (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)).toSection x) ≤
          (CDS l * ‖smoothCcToTensorHs (I := I) (M := M) g₀
            ((l + (Module.finrank ℝ E / 2 + 2) + 1 : ℕ) : ℝ) T₀‖) ^ 2 := by
  classical
  obtain ⟨CDL, hCDL_nn, hCDL⟩ := bal_DL2 (I := I) (M := M) g₀
  have hfam := fun l : ℕ =>
    exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g₀ 0 (2 + l)
  choose Csh hCsh_nn hCsh using hfam
  set w : ℕ := Module.finrank ℝ E / 2 + 2 with hw_def
  refine ⟨fun l => Csh l * ∑ t ∈ Finset.range w, CDL (l + t),
    fun l => mul_nonneg (hCsh_nn l) (Finset.sum_nonneg (fun t _ => hCDL_nn (l + t))), ?_⟩
  intro T₀ l x
  dsimp only
  set fT : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + w + 1 : ℕ) : ℝ) T₀‖
    with hfT_def
  have hfT_nn : 0 ≤ fT := norm_nonneg _
  have h := hCsh l (iteratedCovGrad (I := I) g₀ 0 2 l
    (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)) x
  refine le_trans h ?_
  have hterm : ∀ t ∈ Finset.range w,
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + l) t
          (iteratedCovGrad (I := I) g₀ 0 2 l
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))‖ ^ 2 ≤
        (CDL (l + t) * fT) ^ 2 := by
    intro t ht
    have htw := Finset.mem_range.mp ht
    have hcomp : ‖iteratedCovGrad (I := I) g₀ 0 (2 + l) t
        (iteratedCovGrad (I := I) g₀ 0 2 l
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))‖ =
        ‖iteratedCovGrad (I := I) g₀ 0 2 (l + t)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ :=
      bal_norm_icg_comp (I := I) (M := M) g₀ 0 2 l t
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)
    rw [hcomp]
    have hb := hCDL T₀ (l + t)
    have hmono : ‖smoothCcToTensorHs (I := I) (M := M) g₀
        ((l + t + 2 : ℕ) : ℝ) T₀‖ ≤ fT := by
      rw [hfT_def]
      exact bal_fmono (I := I) (M := M) g₀ T₀ (by omega)
    have hle : ‖iteratedCovGrad (I := I) g₀ 0 2 (l + t)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ ≤ CDL (l + t) * fT := by
      refine le_trans hb ?_
      exact mul_le_mul_of_nonneg_left hmono (hCDL_nn (l + t))
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm)
    (sq_nonneg (Csh l))) ?_
  have hsq : ∑ t ∈ Finset.range w, (CDL (l + t) * fT) ^ 2 ≤
      ((∑ t ∈ Finset.range w, CDL (l + t)) * fT) ^ 2 := by
    have h1 : ∑ t ∈ Finset.range w, (CDL (l + t) * fT) ^ 2 ≤
        (∑ t ∈ Finset.range w, CDL (l + t) * fT) ^ 2 :=
      bal_sq_sum_le_sum_sq _ (fun t => mul_nonneg (hCDL_nn (l + t)) hfT_nn)
    rw [← Finset.sum_mul] at h1
    exact h1
  calc Csh l ^ 2 * ∑ t ∈ Finset.range w, (CDL (l + t) * fT) ^ 2
      ≤ Csh l ^ 2 * ((∑ t ∈ Finset.range w, CDL (l + t)) * fT) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    _ = ((Csh l * ∑ t ∈ Finset.range w, CDL (l + t)) * fT) ^ 2 := by ring

private lemma bal_DSUPT (g₀ : SmoothRiemannianMetric I M) :
    ∃ CDS0 : ℕ → ℝ, (∀ β, 0 ≤ CDS0 β) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2) (β : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + β) x
            ((iteratedCovGrad (I := I) g₀ 0 2 β T₀).toSection x) ≤
          (CDS0 β * ‖smoothCcToTensorHs (I := I) (M := M) g₀
            ((β + (Module.finrank ℝ E / 2 + 1) : ℕ) : ℝ) T₀‖) ^ 2 := by
  classical
  obtain ⟨CJ, hCJ_nn, hCJ⟩ := bal_jets_to_f (I := I) (M := M) g₀
  have hfam := fun β : ℕ =>
    exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g₀ 0 (2 + β)
  choose Csh hCsh_nn hCsh using hfam
  set w : ℕ := Module.finrank ℝ E / 2 + 2 with hw_def
  refine ⟨fun β => Csh β * ∑ t ∈ Finset.range w, CJ (β + t),
    fun β => mul_nonneg (hCsh_nn β) (Finset.sum_nonneg (fun t _ => hCJ_nn (β + t))), ?_⟩
  intro T₀ β x
  dsimp only
  set fT : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀
    ((β + (Module.finrank ℝ E / 2 + 1) : ℕ) : ℝ) T₀‖ with hfT_def
  have hfT_nn : 0 ≤ fT := norm_nonneg _
  have h := hCsh β (iteratedCovGrad (I := I) g₀ 0 2 β T₀) x
  refine le_trans h ?_
  have hterm : ∀ t ∈ Finset.range w,
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + β) t
          (iteratedCovGrad (I := I) g₀ 0 2 β T₀)‖ ^ 2 ≤ (CJ (β + t) * fT) ^ 2 := by
    intro t ht
    have htw := Finset.mem_range.mp ht
    have hcomp : ‖iteratedCovGrad (I := I) g₀ 0 (2 + β) t
        (iteratedCovGrad (I := I) g₀ 0 2 β T₀)‖ =
        ‖iteratedCovGrad (I := I) g₀ 0 2 (β + t) T₀‖ :=
      bal_norm_icg_comp (I := I) (M := M) g₀ 0 2 β t T₀
    rw [hcomp]
    have hb := hCJ (β + t) T₀
    have hmono : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((β + t : ℕ) : ℝ) T₀‖ ≤ fT := by
      rw [hfT_def]
      exact bal_fmono (I := I) (M := M) g₀ T₀ (by omega)
    have hle : ‖iteratedCovGrad (I := I) g₀ 0 2 (β + t) T₀‖ ≤ CJ (β + t) * fT :=
      le_trans hb (mul_le_mul_of_nonneg_left hmono (hCJ_nn (β + t)))
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm)
    (sq_nonneg (Csh β))) ?_
  have hsq : ∑ t ∈ Finset.range w, (CJ (β + t) * fT) ^ 2 ≤
      ((∑ t ∈ Finset.range w, CJ (β + t)) * fT) ^ 2 := by
    have h1 : ∑ t ∈ Finset.range w, (CJ (β + t) * fT) ^ 2 ≤
        (∑ t ∈ Finset.range w, CJ (β + t) * fT) ^ 2 :=
      bal_sq_sum_le_sum_sq _ (fun t => mul_nonneg (hCJ_nn (β + t)) hfT_nn)
    rw [← Finset.sum_mul] at h1
    exact h1
  calc Csh β ^ 2 * ∑ t ∈ Finset.range w, (CJ (β + t) * fT) ^ 2
      ≤ Csh β ^ 2 * ((∑ t ∈ Finset.range w, CJ (β + t)) * fT) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    _ = ((Csh β * ∑ t ∈ Finset.range w, CJ (β + t)) * fT) ^ 2 := by ring

set_option maxHeartbeats 1600000 in
private lemma bal_gridcore (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (T₀ : SmoothCcTensor g₀ 0 2)
    (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀)
    (q j dc d₂ dw : ℕ) (hdc : dc ≤ 1) (hd₂ : d₂ ≤ 2)
    (hdw : dw ≤ Module.finrank ℝ E / 2 + 3)
    (hdw' : Module.finrank ℝ E / 2 + 1 ≤ dw)
    {sz : ℕ} (Z : SmoothCcTensor g₀ 0 sz)
    (sc : ℕ → ℕ) (Cf : (i : ℕ) → SmoothCcTensor g₀ 2 (sc i))
    (cC cCS : ℕ → ℝ) (hcC_nn : ∀ i, 0 ≤ cC i) (hcCS_nn : ∀ i, 0 ≤ cCS i)
    (hCL2 : ∀ i, ‖Cf i‖ ≤ cC i *
      (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((dc + i + 2 * q + 2 : ℕ) : ℝ) T₀‖))
    (hCsup : ∀ (i : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x ((Cf i).toSection x) ≤
        (cCS i * (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀
          ((dc + i + (Module.finrank ℝ E / 2 + 2) + 2 * q + 1 : ℕ) : ℝ) T₀‖)) ^ 2)
    (sd : ℕ → ℕ) (Df : (l : ℕ) → SmoothCcTensor g₀ 0 (sd l))
    (cD cDS : ℕ → ℝ) (hcD_nn : ∀ l, 0 ≤ cD l) (_hcDS_nn : ∀ l, 0 ≤ cDS l)
    (hDL2 : ∀ l, ‖Df l‖ ≤ cD l *
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + d₂ : ℕ) : ℝ) T₀‖)
    (hDsup : ∀ (l : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x) ≤
        (cDS l * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + dw : ℕ) : ℝ) T₀‖) ^ 2)
    (G : ℝ) (hG : 0 ≤ G)
    (hpt : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 sz x (Z.toSection x) ≤
      G * ∑ i ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x ((Cf i).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x)) :
    ‖Z‖ ≤ Real.sqrt (G * ((∑ i ∈ Finset.range (j + 1), (cCS i * (1 + R₀)) ^ 2) *
        (∑ l ∈ Finset.range (j + 1), (cD l) ^ 2) +
        (∑ i ∈ Finset.range (j + 1), (cC i) ^ 2) *
          ((∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2) * (1 + R₀) ^ 2))) *
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 2 * q + 3 : ℕ) : ℝ) T₀‖ := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  set w : ℕ := n / 2 + 2 with hw_def
  set γ' : ℕ := j + 2 * q + 3 with hγ_def
  set fT : ℕ → ℝ := fun k => ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ) T₀‖
    with hfT_def
  have hfT_nn : ∀ k, 0 ≤ fT k := fun k => norm_nonneg _
  have hfT_mono : ∀ {k k' : ℕ}, k ≤ k' → fT k ≤ fT k' := fun {k k'} h =>
    bal_fmono (I := I) (M := M) g₀ T₀ h
  have hfT_ball : ∀ k, k ≤ a + 2 → fT k ≤ R₀ := by
    intro k hk
    have h1 : fT k ≤ fT (a + 2) := hfT_mono hk
    have h2 : fT (a + 2) = ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [h2] at h1
    exact le_trans h1 hball
  set SApred : ℕ → Prop := fun i => dc + i + w + 2 * q + 1 ≤ a + 2 with hSA_def
  have hSAdec : DecidablePred SApred := fun i => by
    rw [hSA_def]
    infer_instance
  set c1 : ℝ := G * ∑ i ∈ (Finset.range (j + 1)).filter SApred,
    (cCS i * (1 + R₀)) ^ 2 with hc1_def
  have hc1_nn : 0 ≤ c1 :=
    mul_nonneg hG (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  set c2 : ℕ → ℝ := fun i => G * (if SApred i then 0 else
    ∑ l ∈ Finset.range (j + 1 - i), (cDS l * fT (l + dw)) ^ 2) with hc2_def
  have hc2_nn : ∀ i, 0 ≤ c2 i := by
    intro i
    rw [hc2_def]
    dsimp only
    split_ifs with h
    · simp
    · exact mul_nonneg hG (Finset.sum_nonneg (fun l _ => sq_nonneg _))
  have hpt2 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 sz x (Z.toSection x) ≤
      (∑ l ∈ Finset.range (j + 1),
        c1 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x)) +
      ∑ i ∈ Finset.range (j + 1),
        c2 i * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x
          ((Cf i).toSection x) := by
    intro x
    refine le_trans (hpt x) ?_
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (j + 1)) SApred]
    have hSApart : ∑ i ∈ (Finset.range (j + 1)).filter SApred,
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x ((Cf i).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x) ≤
        (∑ i ∈ (Finset.range (j + 1)).filter SApred, (cCS i * (1 + R₀)) ^ 2) *
          ∑ l ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun i hi => ?_)
      have hiSA : SApred i := (Finset.mem_filter.mp hi).2
      have hCf_le : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x
          ((Cf i).toSection x) ≤ (cCS i * (1 + R₀)) ^ 2 := by
        refine le_trans (hCsup i x) ?_
        have hf_le : fT (dc + i + w + 2 * q + 1) ≤ R₀ := hfT_ball _ hiSA
        have h1 : cCS i * (1 + fT (dc + i + w + 2 * q + 1)) ≤ cCS i * (1 + R₀) := by
          refine mul_le_mul_of_nonneg_left ?_ (hcCS_nn i)
          linarith
        refine pow_le_pow_left₀ ?_ h1 2
        have := hfT_nn (dc + i + w + 2 * q + 1)
        have := hcCS_nn i
        positivity
      have hDsum_le : ∑ l ∈ Finset.range (j + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x) ≤
          ∑ l ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun y hy => Finset.mem_range.mpr (by have := Finset.mem_range.mp hy; omega))
          (fun l _ _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (sd l) x _)
      have hD_nn : 0 ≤ ∑ l ∈ Finset.range (j + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x) :=
        Finset.sum_nonneg (fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (sd l) x _)
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x ((Cf i).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x)
          ≤ (cCS i * (1 + R₀)) ^ 2 *
            ∑ l ∈ Finset.range (j + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x) :=
            mul_le_mul_of_nonneg_right hCf_le hD_nn
        _ ≤ (cCS i * (1 + R₀)) ^ 2 *
            ∑ l ∈ Finset.range (j + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x) :=
            mul_le_mul_of_nonneg_left hDsum_le (sq_nonneg _)
    have hSBpart : ∑ i ∈ (Finset.range (j + 1)).filter (fun i => ¬ SApred i),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x ((Cf i).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x) ≤
        ∑ i ∈ Finset.range (j + 1),
          (if SApred i then 0 else
            ∑ l ∈ Finset.range (j + 1 - i), (cDS l * fT (l + dw)) ^ 2) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x ((Cf i).toSection x) := by
      rw [Finset.sum_filter]
      refine Finset.sum_le_sum (fun i hi => ?_)
      split_ifs with h
      · simp
      · have hDsum_le : ∑ l ∈ Finset.range (j + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x) ≤
            ∑ l ∈ Finset.range (j + 1 - i), (cDS l * fT (l + dw)) ^ 2 :=
          Finset.sum_le_sum (fun l _ => hDsup l x)
        have hC_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x
            ((Cf i).toSection x) :=
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (sc i) x _
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x ((Cf i).toSection x) *
            ∑ l ∈ Finset.range (j + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x)
            ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x ((Cf i).toSection x) *
              ∑ l ∈ Finset.range (j + 1 - i), (cDS l * fT (l + dw)) ^ 2 :=
              mul_le_mul_of_nonneg_left hDsum_le hC_nn
          _ = (∑ l ∈ Finset.range (j + 1 - i), (cDS l * fT (l + dw)) ^ 2) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x ((Cf i).toSection x) := by
              ring
    have hGmul := mul_le_mul_of_nonneg_left (add_le_add hSApart hSBpart) hG
    refine le_trans hGmul (le_of_eq ?_)
    rw [mul_add]
    congr 1
    · rw [← Finset.mul_sum, hc1_def]
      ring
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hc2_def]
      dsimp only
      ring
  have hL2 := bal_l2_two_family (I := I) (M := M) g₀ Z (j + 1) (j + 1)
    (fun _ => c1) c2 (fun _ => hc1_nn) hc2_nn
    (fun _ => 0) sd Df (fun _ => 2) sc Cf hpt2
  have hSAfinal : ∑ l ∈ Finset.range (j + 1), c1 * ‖Df l‖ ^ 2 ≤
      (G * (∑ i ∈ Finset.range (j + 1), (cCS i * (1 + R₀)) ^ 2) *
        (∑ l ∈ Finset.range (j + 1), (cD l) ^ 2)) * fT γ' ^ 2 := by
    have hc1_le : c1 ≤ G * ∑ i ∈ Finset.range (j + 1), (cCS i * (1 + R₀)) ^ 2 := by
      rw [hc1_def]
      refine mul_le_mul_of_nonneg_left ?_ hG
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => sq_nonneg _)
    have hterm : ∀ l ∈ Finset.range (j + 1), ‖Df l‖ ^ 2 ≤ (cD l) ^ 2 * fT γ' ^ 2 := by
      intro l hl
      have hlj := Finset.mem_range.mp hl
      have h1 : ‖Df l‖ ≤ cD l * fT γ' := by
        refine le_trans (hDL2 l) ?_
        refine mul_le_mul_of_nonneg_left ?_ (hcD_nn l)
        exact hfT_mono (by omega)
      calc ‖Df l‖ ^ 2 ≤ (cD l * fT γ') ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ = (cD l) ^ 2 * fT γ' ^ 2 := by ring
    calc ∑ l ∈ Finset.range (j + 1), c1 * ‖Df l‖ ^ 2
        ≤ ∑ l ∈ Finset.range (j + 1),
            (G * ∑ i ∈ Finset.range (j + 1), (cCS i * (1 + R₀)) ^ 2) *
              ((cD l) ^ 2 * fT γ' ^ 2) := by
          refine Finset.sum_le_sum (fun l hl => ?_)
          refine mul_le_mul hc1_le (hterm l hl) (sq_nonneg _) ?_
          exact mul_nonneg hG (Finset.sum_nonneg (fun i _ => sq_nonneg _))
      _ = (G * (∑ i ∈ Finset.range (j + 1), (cCS i * (1 + R₀)) ^ 2) *
            (∑ l ∈ Finset.range (j + 1), (cD l) ^ 2)) * fT γ' ^ 2 := by
          rw [← Finset.mul_sum, ← Finset.sum_mul]
          ring
  have hSBfinal : ∑ i ∈ Finset.range (j + 1), c2 i * ‖Cf i‖ ^ 2 ≤
      (G * (∑ i ∈ Finset.range (j + 1), (cC i) ^ 2) *
        ((∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2) * (1 + R₀) ^ 2)) * fT γ' ^ 2 := by
    have hterm : ∀ i ∈ Finset.range (j + 1), c2 i * ‖Cf i‖ ^ 2 ≤
        G * ((cC i) ^ 2 * ((∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2) * (1 + R₀) ^ 2) *
          fT γ' ^ 2) := by
      intro i hi
      have hij := Finset.mem_range.mp hi
      rw [hc2_def]
      dsimp only
      split_ifs with hSA
      · have h0 : G * 0 * ‖Cf i‖ ^ 2 = 0 := by ring
        rw [h0]
        have : (0:ℝ) ≤ G * ((cC i) ^ 2 * ((∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2) *
            (1 + R₀) ^ 2) * fT γ' ^ 2) := by positivity
        linarith
      · have hSB : ¬ (dc + i + w + 2 * q + 1 ≤ a + 2) := hSA
        have hcell : ∀ l ∈ Finset.range (j + 1 - i),
            (cDS l * fT (l + dw)) ^ 2 * ‖Cf i‖ ^ 2 ≤
              (cDS l) ^ 2 * ((cC i) ^ 2 * ((1 + R₀) ^ 2 * fT γ' ^ 2)) := by
          intro l hl
          have hlj := Finset.mem_range.mp hl
          have hCf : ‖Cf i‖ ≤ cC i * (1 + fT (dc + i + 2 * q + 2)) := hCL2 i
          have hscore : fT (l + dw) * (1 + fT (dc + i + 2 * q + 2)) ≤ (1 + R₀) * fT γ' := by
            have hu_le : l + dw ≤ γ' := by omega
            have h1 : fT (l + dw) * 1 = fT (l + dw) := by ring
            have h2 : fT (l + dw) ≤ fT γ' := hfT_mono hu_le
            have h3 : fT (l + dw) * fT (dc + i + 2 * q + 2) ≤ R₀ * fT γ' := by
              have := bal_score (I := I) (M := M) g₀ a hR₀ T₀ hball
                (u := l + dw) (v := dc + i + 2 * q + 2) (γ := γ')
                (by omega) (by omega) (Or.inl hu_le)
              exact this
            calc fT (l + dw) * (1 + fT (dc + i + 2 * q + 2))
                = fT (l + dw) + fT (l + dw) * fT (dc + i + 2 * q + 2) := by ring
              _ ≤ fT γ' + R₀ * fT γ' := add_le_add h2 h3
              _ = (1 + R₀) * fT γ' := by ring
          have hprod : fT (l + dw) * ‖Cf i‖ ≤ cDS l * 0 + cC i * ((1 + R₀) * fT γ') := by
            have h1 : fT (l + dw) * ‖Cf i‖ ≤
                fT (l + dw) * (cC i * (1 + fT (dc + i + 2 * q + 2))) :=
              mul_le_mul_of_nonneg_left hCf (hfT_nn _)
            have h2 : fT (l + dw) * (cC i * (1 + fT (dc + i + 2 * q + 2))) =
                cC i * (fT (l + dw) * (1 + fT (dc + i + 2 * q + 2))) := by ring
            rw [h2] at h1
            refine le_trans h1 ?_
            have h3 := mul_le_mul_of_nonneg_left hscore (hcC_nn i)
            linarith
          have hprod' : fT (l + dw) * ‖Cf i‖ ≤ cC i * ((1 + R₀) * fT γ') := by
            linarith [hprod]
          have hboth_nn : 0 ≤ fT (l + dw) * ‖Cf i‖ :=
            mul_nonneg (hfT_nn _) (norm_nonneg _)
          have hsq := pow_le_pow_left₀ hboth_nn hprod' 2
          calc (cDS l * fT (l + dw)) ^ 2 * ‖Cf i‖ ^ 2
              = (cDS l) ^ 2 * (fT (l + dw) * ‖Cf i‖) ^ 2 := by ring
            _ ≤ (cDS l) ^ 2 * (cC i * ((1 + R₀) * fT γ')) ^ 2 :=
                mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
            _ = (cDS l) ^ 2 * ((cC i) ^ 2 * ((1 + R₀) ^ 2 * fT γ' ^ 2)) := by ring
        have hsum : (∑ l ∈ Finset.range (j + 1 - i), (cDS l * fT (l + dw)) ^ 2) *
            ‖Cf i‖ ^ 2 ≤
            (∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2) *
              ((cC i) ^ 2 * ((1 + R₀) ^ 2 * fT γ' ^ 2)) := by
          rw [Finset.sum_mul]
          refine le_trans (Finset.sum_le_sum hcell) ?_
          rw [← Finset.sum_mul]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (fun y hy => Finset.mem_range.mpr (by have := Finset.mem_range.mp hy; omega))
            (fun l _ _ => sq_nonneg _)
        calc G * (∑ l ∈ Finset.range (j + 1 - i), (cDS l * fT (l + dw)) ^ 2) *
            ‖Cf i‖ ^ 2
            = G * ((∑ l ∈ Finset.range (j + 1 - i), (cDS l * fT (l + dw)) ^ 2) *
              ‖Cf i‖ ^ 2) := by ring
          _ ≤ G * ((∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2) *
              ((cC i) ^ 2 * ((1 + R₀) ^ 2 * fT γ' ^ 2))) :=
              mul_le_mul_of_nonneg_left hsum hG
          _ = G * ((cC i) ^ 2 * ((∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2) *
              (1 + R₀) ^ 2) * fT γ' ^ 2) := by ring
    calc ∑ i ∈ Finset.range (j + 1), c2 i * ‖Cf i‖ ^ 2
        ≤ ∑ i ∈ Finset.range (j + 1),
            G * ((cC i) ^ 2 * ((∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2) *
              (1 + R₀) ^ 2) * fT γ' ^ 2) := Finset.sum_le_sum hterm
      _ = (G * (∑ i ∈ Finset.range (j + 1), (cC i) ^ 2) *
            ((∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2) * (1 + R₀) ^ 2)) * fT γ' ^ 2 := by
          rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_mul]
          ring
  have htot : ‖Z‖ ^ 2 ≤ (G * ((∑ i ∈ Finset.range (j + 1), (cCS i * (1 + R₀)) ^ 2) *
      (∑ l ∈ Finset.range (j + 1), (cD l) ^ 2) +
      (∑ i ∈ Finset.range (j + 1), (cC i) ^ 2) *
        ((∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2) * (1 + R₀) ^ 2))) * fT γ' ^ 2 := by
    refine le_trans hL2 ?_
    have := add_le_add hSAfinal hSBfinal
    refine le_trans this (le_of_eq ?_)
    ring
  have hCB_nn : 0 ≤ G * ((∑ i ∈ Finset.range (j + 1), (cCS i * (1 + R₀)) ^ 2) *
      (∑ l ∈ Finset.range (j + 1), (cD l) ^ 2) +
      (∑ i ∈ Finset.range (j + 1), (cC i) ^ 2) *
        ((∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2) * (1 + R₀) ^ 2)) := by
    have h1 : 0 ≤ ∑ i ∈ Finset.range (j + 1), (cCS i * (1 + R₀)) ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have h2 : 0 ≤ ∑ l ∈ Finset.range (j + 1), (cD l) ^ 2 :=
      Finset.sum_nonneg (fun l _ => sq_nonneg _)
    have h3 : 0 ≤ ∑ i ∈ Finset.range (j + 1), (cC i) ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have h4 : 0 ≤ ∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2 :=
      Finset.sum_nonneg (fun l _ => sq_nonneg _)
    have h5 : (0:ℝ) ≤ (1 + R₀) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg h1 h2, mul_nonneg h3 (mul_nonneg h4 h5)]
  refine le_of_sq_le_sq ?_ (mul_nonneg (Real.sqrt_nonneg _) (hfT_nn γ'))
  rw [mul_pow, Real.sq_sqrt hCB_nn]
  exact htot

private lemma bal_fT_index_congr (g₀ : SmoothRiemannianMetric I M)
    (T₀ : SmoothCcTensor g₀ 0 2) {k k' : ℕ} (h : k = k') :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ) T₀‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k' : ℕ) : ℝ) T₀‖ := by
  subst h; rfl

set_option maxHeartbeats 1600000 in
private lemma bal_block1 (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) (εa : ℝ) (hεa_nn : 0 ≤ εa) :
    ∃ CB : ℕ → ℕ → ℝ, (∀ q j, 0 ≤ CB q j) ∧
      ∀ (C₀ : SmoothCcTensor g₀ 2 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
              εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) →
        ∀ (q j : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j
              (appCc (I := I) (M := M) g₀ 2 2
                (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))‖ ≤
            CB q j * ‖smoothCcToTensorHs (I := I) (M := M) g₀
              ((j + 2 * q + 3 : ℕ) : ℝ) T₀‖ := by
  classical
  obtain ⟨CC, hCC_nn, hCC⟩ := bal_CJET (I := I) (M := M) g₀ Kc hKc_nn εa hεa_nn
  obtain ⟨CCS, hCCS_nn, hCCS⟩ := bal_CSUP (I := I) (M := M) g₀ Kc hKc_nn εa hεa_nn
  obtain ⟨CDL, hCDL_nn, hCDL⟩ := bal_DL2 (I := I) (M := M) g₀
  obtain ⟨CDS, hCDS_nn, hCDS⟩ := bal_DSUPD (I := I) (M := M) g₀
  refine ⟨fun q j => Real.sqrt (appCcGdiag (E := E) j *
      ((∑ i ∈ Finset.range (j + 1), (CCS i q * (1 + R₀)) ^ 2) *
        (∑ l ∈ Finset.range (j + 1), (CDL l) ^ 2) +
        (∑ i ∈ Finset.range (j + 1), (CC i q) ^ 2) *
          ((∑ l ∈ Finset.range (j + 1), (CDS l) ^ 2) * (1 + R₀) ^ 2))),
    fun q j => Real.sqrt_nonneg _, ?_⟩
  intro C₀ T₀ hball henv q j
  refine bal_gridcore (I := I) (M := M) g₀ a ha_super hR₀ T₀ hball q j 0 2
    (Module.finrank ℝ E / 2 + 3) (by omega) (by omega) (by omega) (by omega)
    (iteratedCovGrad (I := I) g₀ 0 2 j
      (appCc (I := I) (M := M) g₀ 2 2
        (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)))
    (fun i => 2 + i)
    (fun i => iteratedCovGrad (I := I) g₀ 2 2 i
      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀))
    (fun i => CC i q) (fun i => CCS i q) (fun i => hCC_nn i q) (fun i => hCCS_nn i q)
    (fun i => ?_) (fun i x => ?_)
    (fun l => 2 + l)
    (fun l => iteratedCovGrad (I := I) g₀ 0 2 l
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))
    CDL CDS hCDL_nn hCDS_nn
    (fun l => ?_) (fun l x => ?_)
    (appCcGdiag (E := E) j) (appCcGdiag_nonneg (E := E) j)
    (fun x => ?_)
  · rw [bal_fT_index_congr (I := I) (M := M) g₀ T₀ (show 0 + i + 2 * q + 2 = i + 2 * q + 2
      from by omega)]
    exact hCC C₀ T₀ henv i q
  · have h := hCCS C₀ T₀ henv i q x
    rw [bal_fT_index_congr (I := I) (M := M) g₀ T₀
      (show 0 + i + (Module.finrank ℝ E / 2 + 2) + 2 * q + 1 =
        i + (Module.finrank ℝ E / 2 + 2) + 2 * q + 1 from by omega)]
    exact h
  · exact hCDL T₀ l
  · have h := hCDS T₀ l x
    rw [bal_fT_index_congr (I := I) (M := M) g₀ T₀
      (show l + (Module.finrank ℝ E / 2 + 3) = l + (Module.finrank ℝ E / 2 + 2) + 1
        from by omega)]
    exact h
  · exact appCc_iteratedCovGrad_diagonalProductGrid_le (I := I) (M := M) g₀ 2 2
      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀) j x

private lemma bal_DTwrap (g₀ : SmoothRiemannianMetric I M) :
    ∃ CDT : ℝ, 0 ≤ CDT ∧ ∀ (Y : SmoothCcTensor g₀ 0 (2 + 2)) (j : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j
            (appCc (I := I) (M := M) g₀ (2 + 2) 2
              (DeTurck.cometricDoubleTraceField (I := I) g₀ 2) Y)).toSection x) ≤
        appCcGdiag (E := E) j * CDT * ∑ l' ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + l') x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) l' Y).toSection x) := by
  classical
  have hfam := fun i' : ℕ =>
    exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g₀ (2 + 2) (2 + i')
  choose Csh hCsh_nn hCsh using hfam
  set DT₂ : SmoothCcTensor g₀ (2 + 2) 2 := DeTurck.cometricDoubleTraceField (I := I) g₀ 2
    with hDT_def
  set w : ℕ := Module.finrank ℝ E / 2 + 2 with hw_def
  have hvanish : ∀ k : ℕ, 1 ≤ k → ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 k DT₂‖ = 0 := by
    intro k hk
    obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [show 1 + k' = k' + 1 from by omega]
    rw [iteratedCovGrad_eq_zero_of_covGrad_eq_zero (I := I) (M := M) g₀ (2 + 2) 2 DT₂
      (DeTurck.cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ 2) k']
    exact norm_zero
  set CDT : ℝ := Csh 0 ^ 2 * ∑ t ∈ Finset.range w,
    ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 t DT₂‖ ^ 2 with hCDT_def
  have hCDT_nn : 0 ≤ CDT :=
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun t _ => sq_nonneg _))
  refine ⟨CDT, hCDT_nn, fun Y j x => ?_⟩
  have hgrid := appCc_iteratedCovGrad_diagonalProductGrid_le (I := I) (M := M) g₀ (2 + 2) 2
    DT₂ Y j x
  refine le_trans hgrid ?_
  have hDTsup : ∀ i' : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) (2 + i') x
          ((iteratedCovGrad (I := I) g₀ (2 + 2) 2 i' DT₂).toSection x) ≤
        (if i' = 0 then CDT else 0) := by
    intro i'
    match i' with
    | 0 =>
      rw [if_pos rfl]
      have h := hCsh 0 (iteratedCovGrad (I := I) g₀ (2 + 2) 2 0 DT₂) x
      refine le_trans h ?_
      rw [hCDT_def]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      refine le_of_eq (Finset.sum_congr rfl (fun t _ => ?_))
      have hcomp : ‖iteratedCovGrad (I := I) g₀ (2 + 2) (2 + 0) t
          (iteratedCovGrad (I := I) g₀ (2 + 2) 2 0 DT₂)‖ =
          ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 (0 + t) DT₂‖ :=
        bal_norm_icg_comp (I := I) (M := M) g₀ (2 + 2) 2 0 t DT₂
      rw [hcomp, show (0 + t : ℕ) = t from by omega]
    | (k + 1) =>
      rw [if_neg (Nat.succ_ne_zero k)]
      have h := hCsh (k + 1) (iteratedCovGrad (I := I) g₀ (2 + 2) 2 (k + 1) DT₂) x
      refine le_trans h ?_
      have hz : ∑ t ∈ Finset.range w,
          ‖iteratedCovGrad (I := I) g₀ (2 + 2) (2 + (k + 1)) t
            (iteratedCovGrad (I := I) g₀ (2 + 2) 2 (k + 1) DT₂)‖ ^ 2 = 0 := by
        refine Finset.sum_eq_zero (fun t _ => ?_)
        have hcomp : ‖iteratedCovGrad (I := I) g₀ (2 + 2) (2 + (k + 1)) t
            (iteratedCovGrad (I := I) g₀ (2 + 2) 2 (k + 1) DT₂)‖ =
            ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 ((k + 1) + t) DT₂‖ :=
          bal_norm_icg_comp (I := I) (M := M) g₀ (2 + 2) 2 (k + 1) t DT₂
        rw [hcomp, hvanish ((k + 1) + t) (by omega)]
        norm_num
      rw [hz, mul_zero]
  have hterm : ∀ i' ∈ Finset.range (j + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) (2 + i') x
          ((iteratedCovGrad (I := I) g₀ (2 + 2) 2 i' DT₂).toSection x) *
        ∑ l' ∈ Finset.range (j + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + l') x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) l' Y).toSection x) ≤
      (if i' = 0 then CDT * ∑ l' ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + l') x
          ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) l' Y).toSection x) else 0) := by
    intro i' hi'
    have hY_nn : 0 ≤ ∑ l' ∈ Finset.range (j + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + l') x
          ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) l' Y).toSection x) :=
      Finset.sum_nonneg (fun l' _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 _ x _)
    split_ifs with h0
    · subst h0
      refine mul_le_mul (le_trans (hDTsup 0) (by rw [if_pos rfl])) ?_ hY_nn hCDT_nn
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun l' _ _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 _ x _)
      exact fun y hy => Finset.mem_range.mpr (by have := Finset.mem_range.mp hy; omega)
    · have hle := hDTsup i'
      rw [if_neg h0] at hle
      have hrf_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) (2 + i') x
          ((iteratedCovGrad (I := I) g₀ (2 + 2) 2 i' DT₂).toSection x) :=
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ (2 + 2) _ x _
      have hzero : riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) (2 + i') x
          ((iteratedCovGrad (I := I) g₀ (2 + 2) 2 i' DT₂).toSection x) = 0 :=
        le_antisymm hle hrf_nn
      rw [hzero, zero_mul]
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm)
    (appCcGdiag_nonneg (E := E) j)) ?_
  rw [Finset.sum_ite_eq' (Finset.range (j + 1)) 0]
  rw [if_pos (Finset.mem_range.mpr (by omega))]
  rw [← mul_assoc]

private lemma bal_grid_mono {A B : ℕ → ℝ} (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i)
    {l' j : ℕ} (hl' : l' ≤ j) :
    ∑ α ∈ Finset.range (l' + 1), A α * ∑ β ∈ Finset.range (l' + 1 - α), B β ≤
      ∑ α ∈ Finset.range (j + 1), A α * ∑ β ∈ Finset.range (j + 1 - α), B β := by
  refine le_trans (Finset.sum_le_sum (fun α _ => ?_))
    (Finset.sum_le_sum_of_subset_of_nonneg
      (fun y hy => Finset.mem_range.mpr (by have := Finset.mem_range.mp hy; omega))
      (fun α _ _ => mul_nonneg (hA α) (Finset.sum_nonneg (fun β _ => hB β))))
  refine mul_le_mul_of_nonneg_left ?_ (hA α)
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun y hy => Finset.mem_range.mpr (by have := Finset.mem_range.mp hy; omega))
    (fun β _ _ => hB β)

set_option maxHeartbeats 3200000 in
private lemma bal_block23 (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) (εa : ℝ) (hεa_nn : 0 ≤ εa) :
    ∃ CB : ℕ → ℕ → ℝ, (∀ q j, 0 ≤ CB q j) ∧
      ∀ (C₀ : SmoothCcTensor g₀ 2 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
              εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) →
        ∀ (q j : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j
              (appCc (I := I) (M := M) g₀ (2 + 2) 2
                (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                  (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
                    (covGrad (I := I) (M := M) g₀ 2 2
                      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                  (covGrad (I := I) (M := M) g₀ 0 2 T₀)))‖ ≤
            CB q j * ‖smoothCcToTensorHs (I := I) (M := M) g₀
              ((j + 2 * q + 3 : ℕ) : ℝ) T₀‖ ∧
          ‖iteratedCovGrad (I := I) g₀ 0 2 j
              (appCc (I := I) (M := M) g₀ (2 + 2) 2
                (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                  (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                    (slotExtend (I := I) (M := M) g₀ 2 2
                      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                  (covGrad (I := I) (M := M) g₀ 0 2 T₀)))‖ ≤
            CB q j * ‖smoothCcToTensorHs (I := I) (M := M) g₀
              ((j + 2 * q + 3 : ℕ) : ℝ) T₀‖ := by
  classical
  obtain ⟨CC, hCC_nn, hCC⟩ := bal_CJET (I := I) (M := M) g₀ Kc hKc_nn εa hεa_nn
  obtain ⟨CCS, hCCS_nn, hCCS⟩ := bal_CSUP (I := I) (M := M) g₀ Kc hKc_nn εa hεa_nn
  obtain ⟨CJ, hCJ_nn, hCJ⟩ := bal_jets_to_f (I := I) (M := M) g₀
  obtain ⟨CDS0, hCDS0_nn, hCDS0⟩ := bal_DSUPT (I := I) (M := M) g₀
  obtain ⟨CDT, hCDT_nn, hCDT⟩ := bal_DTwrap (I := I) (M := M) g₀
  set n : ℕ := Module.finrank ℝ E with hn_def
  set G : ℕ → ℝ := fun j => appCcGdiag (E := E) j * CDT *
    ((j + 1 : ℕ) * (appCcGdiag (E := E) j * n)) with hG_def
  have hG_nn : ∀ j, 0 ≤ G j := fun j => by
    have h1 := appCcGdiag_nonneg (E := E) j
    have h2 : (0:ℝ) ≤ (j + 1 : ℕ) := Nat.cast_nonneg _
    have h3 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    positivity
  refine ⟨fun q j => Real.sqrt (G j *
      ((∑ i ∈ Finset.range (j + 1), (CCS (1 + i) q * (1 + R₀)) ^ 2) *
        (∑ l ∈ Finset.range (j + 1), (CJ (1 + l)) ^ 2) +
        (∑ i ∈ Finset.range (j + 1), (CC (1 + i) q) ^ 2) *
          ((∑ l ∈ Finset.range (j + 1), (CDS0 (1 + l)) ^ 2) * (1 + R₀) ^ 2))),
    fun q j => Real.sqrt_nonneg _, ?_⟩
  intro C₀ T₀ hball henv q j
  set Ĉq : SmoothCcTensor g₀ 2 2 := oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀
    with hĈq_def
  have hcore : ∀ {sz : ℕ} (Z : SmoothCcTensor g₀ 0 sz),
      (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 sz x (Z.toSection x) ≤
        G j * ∑ i ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + (1 + i)) x
            ((iteratedCovGrad (I := I) g₀ 2 2 (1 + i) Ĉq).toSection x) *
            ∑ l ∈ Finset.range (j + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + l)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (1 + l) T₀).toSection x)) →
      ‖Z‖ ≤ Real.sqrt (G j *
        ((∑ i ∈ Finset.range (j + 1), (CCS (1 + i) q * (1 + R₀)) ^ 2) *
          (∑ l ∈ Finset.range (j + 1), (CJ (1 + l)) ^ 2) +
          (∑ i ∈ Finset.range (j + 1), (CC (1 + i) q) ^ 2) *
            ((∑ l ∈ Finset.range (j + 1), (CDS0 (1 + l)) ^ 2) * (1 + R₀) ^ 2))) *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 2 * q + 3 : ℕ) : ℝ) T₀‖ := by
    intro sz Z hpt
    refine bal_gridcore (I := I) (M := M) g₀ a ha_super hR₀ T₀ hball q j 1 1
      (Module.finrank ℝ E / 2 + 2) (by omega) (by omega) (by omega) (by omega)
      Z (fun i => 2 + (1 + i))
      (fun i => iteratedCovGrad (I := I) g₀ 2 2 (1 + i) Ĉq)
      (fun i => CC (1 + i) q) (fun i => CCS (1 + i) q)
      (fun i => hCC_nn (1 + i) q) (fun i => hCCS_nn (1 + i) q)
      (fun i => ?_) (fun i x => ?_)
      (fun l => 2 + (1 + l))
      (fun l => iteratedCovGrad (I := I) g₀ 0 2 (1 + l) T₀)
      (fun l => CJ (1 + l)) (fun l => CDS0 (1 + l))
      (fun l => hCJ_nn (1 + l)) (fun l => hCDS0_nn (1 + l))
      (fun l => ?_) (fun l x => ?_)
      (G j) (hG_nn j) hpt
    · rw [bal_fT_index_congr (I := I) (M := M) g₀ T₀
        (show 1 + i + 2 * q + 2 = (1 + i) + 2 * q + 2 from by omega)]
      exact hCC C₀ T₀ henv (1 + i) q
    · rw [bal_fT_index_congr (I := I) (M := M) g₀ T₀
        (show 1 + i + (Module.finrank ℝ E / 2 + 2) + 2 * q + 1 =
          (1 + i) + (Module.finrank ℝ E / 2 + 2) + 2 * q + 1 from by omega)]
      exact hCCS C₀ T₀ henv (1 + i) q x
    · rw [bal_fT_index_congr (I := I) (M := M) g₀ T₀
        (show (l + 1 : ℕ) = 1 + l from by omega)]
      exact hCJ (1 + l) T₀
    · rw [bal_fT_index_congr (I := I) (M := M) g₀ T₀
        (show l + (Module.finrank ℝ E / 2 + 2) =
          (1 + l) + (Module.finrank ℝ E / 2 + 1) from by omega)]
      exact hCDS0 T₀ (1 + l) x
  have hGd_mono : ∀ {l' : ℕ}, l' ≤ j → appCcGdiag (E := E) l' ≤ appCcGdiag (E := E) j := by
    intro l' hl'
    have hbase : (1 : ℝ) ≤ 2 * ((Module.finrank ℝ E : ℝ) + 1) := by
      have : (0:ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
      linarith
    exact pow_le_pow_right₀ hbase hl'
  have hYgrid : ∀ (Cf' : SmoothCcTensor g₀ (2 + 1) (2 + 2)),
      (∀ (α : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 1) ((2 + 2) + α) x
            ((iteratedCovGrad (I := I) g₀ (2 + 1) (2 + 2) α Cf').toSection x) ≤
          (n : ℝ) * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + (1 + α)) x
            ((iteratedCovGrad (I := I) g₀ 2 2 (1 + α) Ĉq).toSection x)) →
      ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 0 2 j
              (appCc (I := I) (M := M) g₀ (2 + 2) 2
                (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2) Cf'
                  (covGrad (I := I) (M := M) g₀ 0 2 T₀)))).toSection x) ≤
          G j * ∑ i ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + (1 + i)) x
              ((iteratedCovGrad (I := I) g₀ 2 2 (1 + i) Ĉq).toSection x) *
              ∑ l ∈ Finset.range (j + 1 - i),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + l)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (1 + l) T₀).toSection x) := by
    intro Cf' hCf' x
    have hβconv : ∀ (β : ℕ),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 1) + β) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + 1) β
              (covGrad (I := I) (M := M) g₀ 0 2 T₀)).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + β)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (1 + β) T₀).toSection x) := by
      intro β
      rw [bal_icg_one (I := I) (M := M) g₀ 0 2 T₀]
      exact rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 1 β T₀ x
    set gridj : ℝ := ∑ i ∈ Finset.range (j + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + (1 + i)) x
        ((iteratedCovGrad (I := I) g₀ 2 2 (1 + i) Ĉq).toSection x) *
        ∑ l ∈ Finset.range (j + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + l)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (1 + l) T₀).toSection x) with hgridj_def
    have hgridj_nn : 0 ≤ gridj :=
      Finset.sum_nonneg (fun i _ => mul_nonneg
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 _ x _)
        (Finset.sum_nonneg (fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 _ x _)))
    have hY : ∀ l' : ℕ, l' ≤ j →
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + l') x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) l'
              (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2) Cf'
                (covGrad (I := I) (M := M) g₀ 0 2 T₀))).toSection x) ≤
          appCcGdiag (E := E) j * (n : ℝ) * gridj := by
      intro l' hl'
      have hgrid := appCc_iteratedCovGrad_diagonalProductGrid_le (I := I) (M := M) g₀
        (2 + 1) (2 + 2) Cf' (covGrad (I := I) (M := M) g₀ 0 2 T₀) l' x
      refine le_trans hgrid ?_
      have hterm : ∀ α ∈ Finset.range (l' + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 1) ((2 + 2) + α) x
              ((iteratedCovGrad (I := I) g₀ (2 + 1) (2 + 2) α Cf').toSection x) *
            ∑ β ∈ Finset.range (l' + 1 - α),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 1) + β) x
                ((iteratedCovGrad (I := I) g₀ 0 (2 + 1) β
                  (covGrad (I := I) (M := M) g₀ 0 2 T₀)).toSection x) ≤
          (n : ℝ) * (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + (1 + α)) x
              ((iteratedCovGrad (I := I) g₀ 2 2 (1 + α) Ĉq).toSection x) *
            ∑ β ∈ Finset.range (l' + 1 - α),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + β)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (1 + β) T₀).toSection x)) := by
        intro α _
        have hsum_eq : ∑ β ∈ Finset.range (l' + 1 - α),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 1) + β) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + 1) β
                (covGrad (I := I) (M := M) g₀ 0 2 T₀)).toSection x) =
            ∑ β ∈ Finset.range (l' + 1 - α),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + β)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (1 + β) T₀).toSection x) :=
          Finset.sum_congr rfl (fun β _ => hβconv β)
        rw [hsum_eq]
        have hs_nn : 0 ≤ ∑ β ∈ Finset.range (l' + 1 - α),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + β)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (1 + β) T₀).toSection x) :=
          Finset.sum_nonneg (fun β _ =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 _ x _)
        have h := mul_le_mul_of_nonneg_right (hCf' α x) hs_nn
        refine le_trans h (le_of_eq ?_)
        ring
      refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm)
        (appCcGdiag_nonneg (E := E) l')) ?_
      have hpull : ∑ α ∈ Finset.range (l' + 1),
          (n : ℝ) * (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + (1 + α)) x
              ((iteratedCovGrad (I := I) g₀ 2 2 (1 + α) Ĉq).toSection x) *
            ∑ β ∈ Finset.range (l' + 1 - α),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + β)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (1 + β) T₀).toSection x)) =
          (n : ℝ) * ∑ α ∈ Finset.range (l' + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + (1 + α)) x
              ((iteratedCovGrad (I := I) g₀ 2 2 (1 + α) Ĉq).toSection x) *
              ∑ β ∈ Finset.range (l' + 1 - α),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + β)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (1 + β) T₀).toSection x) := by
        rw [Finset.mul_sum]
      rw [hpull]
      have hmono := bal_grid_mono
        (A := fun α => riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + (1 + α)) x
          ((iteratedCovGrad (I := I) g₀ 2 2 (1 + α) Ĉq).toSection x))
        (B := fun β => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + β)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (1 + β) T₀).toSection x))
        (fun α => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 _ x _)
        (fun β => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 _ x _) hl'
      calc appCcGdiag (E := E) l' * ((n : ℝ) * ∑ α ∈ Finset.range (l' + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + (1 + α)) x
              ((iteratedCovGrad (I := I) g₀ 2 2 (1 + α) Ĉq).toSection x) *
              ∑ β ∈ Finset.range (l' + 1 - α),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + β)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (1 + β) T₀).toSection x))
          ≤ appCcGdiag (E := E) l' * ((n : ℝ) * gridj) := by
            refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) l')
            exact mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg _)
        _ ≤ appCcGdiag (E := E) j * ((n : ℝ) * gridj) := by
            refine mul_le_mul_of_nonneg_right (hGd_mono hl') ?_
            exact mul_nonneg (Nat.cast_nonneg _) hgridj_nn
        _ = appCcGdiag (E := E) j * (n : ℝ) * gridj := by ring
    have hDT := hCDT (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2) Cf'
      (covGrad (I := I) (M := M) g₀ 0 2 T₀)) j x
    refine le_trans hDT ?_
    have hsum_le : ∑ l' ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + l') x
          ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) l'
            (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2) Cf'
              (covGrad (I := I) (M := M) g₀ 0 2 T₀))).toSection x) ≤
        ((j + 1 : ℕ) : ℝ) * (appCcGdiag (E := E) j * (n : ℝ) * gridj) := by
      have h1 : ∀ l' ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + l') x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) l'
              (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2) Cf'
                (covGrad (I := I) (M := M) g₀ 0 2 T₀))).toSection x) ≤
          appCcGdiag (E := E) j * (n : ℝ) * gridj :=
        fun l' hl' => hY l' (by have := Finset.mem_range.mp hl'; omega)
      refine le_trans (Finset.sum_le_sum h1) (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc appCcGdiag (E := E) j * CDT * ∑ l' ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + l') x
          ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) l'
            (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2) Cf'
              (covGrad (I := I) (M := M) g₀ 0 2 T₀))).toSection x)
        ≤ appCcGdiag (E := E) j * CDT *
            (((j + 1 : ℕ) : ℝ) * (appCcGdiag (E := E) j * (n : ℝ) * gridj)) := by
          refine mul_le_mul_of_nonneg_left hsum_le ?_
          exact mul_nonneg (appCcGdiag_nonneg (E := E) j) hCDT_nn
      _ = G j * gridj := by
          rw [hG_def]
          push_cast
          ring
  constructor
  · refine hcore (iteratedCovGrad (I := I) g₀ 0 2 j
      (appCc (I := I) (M := M) g₀ (2 + 2) 2
        (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
        (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2)
          (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
            (covGrad (I := I) (M := M) g₀ 2 2 Ĉq))
          (covGrad (I := I) (M := M) g₀ 0 2 T₀)))) ?_
    refine hYgrid (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
      (covGrad (I := I) (M := M) g₀ 2 2 Ĉq)) ?_
    intro α x
    have h1 := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 2 (2 + 1)
      (covGrad (I := I) (M := M) g₀ 2 2 Ĉq) α x
    refine le_trans h1 ?_
    refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (Nat.cast_nonneg _)
    rw [bal_icg_one (I := I) (M := M) g₀ 2 2 Ĉq]
    exact rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 2 2 1 α Ĉq x
  · refine hcore (iteratedCovGrad (I := I) g₀ 0 2 j
      (appCc (I := I) (M := M) g₀ (2 + 2) 2
        (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
        (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2)
          (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
            (slotExtend (I := I) (M := M) g₀ 2 2 Ĉq))
          (covGrad (I := I) (M := M) g₀ 0 2 T₀)))) ?_
    refine hYgrid (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
      (slotExtend (I := I) (M := M) g₀ 2 2 Ĉq)) ?_
    intro α x
    have hconv : riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 1) ((2 + 2) + α) x
        ((iteratedCovGrad (I := I) g₀ (2 + 1) (2 + 2) α
          (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
            (slotExtend (I := I) (M := M) g₀ 2 2 Ĉq))).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 1) ((2 + 1) + (1 + α)) x
          ((iteratedCovGrad (I := I) g₀ (2 + 1) (2 + 1) (1 + α)
            (slotExtend (I := I) (M := M) g₀ 2 2 Ĉq)).toSection x) := by
      rw [bal_icg_one (I := I) (M := M) g₀ (2 + 1) (2 + 1)
        (slotExtend (I := I) (M := M) g₀ 2 2 Ĉq)]
      exact rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ (2 + 1) (2 + 1) 1 α
        (slotExtend (I := I) (M := M) g₀ 2 2 Ĉq) x
    rw [hconv]
    exact rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 2 2 Ĉq (1 + α) x

private lemma bal_slotExt_norm (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g₀ r s) :
    ‖slotExtend (I := I) (M := M) g₀ r s Φ‖ ≤
      Real.sqrt (Module.finrank ℝ E) * ‖Φ‖ := by
  have hsq := bal_jet_l2_of_pointwise_window (I := I) (M := M) g₀
    (slotExtend (I := I) (M := M) g₀ r s Φ) (Module.finrank ℝ E : ℝ) (Nat.cast_nonneg _)
    (fun _ => s) (fun _ => Φ) 1 (fun x => ?_)
  · rw [Finset.sum_range_one] at hsq
    refine le_of_sq_le_sq ?_ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    exact hsq
  · rw [Finset.sum_range_one]
    have h := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ r s Φ 0 x
    rw [show iteratedCovGrad (I := I) g₀ (r + 1) (s + 1) 0
        (slotExtend (I := I) (M := M) g₀ r s Φ) =
      slotExtend (I := I) (M := M) g₀ r s Φ from iteratedCovGrad_zero _ _ _ _] at h
    rw [show iteratedCovGrad (I := I) g₀ r s 0 Φ = Φ from iteratedCovGrad_zero _ _ _ _] at h
    exact h

set_option maxHeartbeats 3200000 in
private lemma bal_top (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) (εa : ℝ) (hεa_nn : 0 ≤ εa) :
    ∃ KT : ℕ → ℝ, (∀ p, 0 ≤ KT p) ∧
      ∀ (C₀ : SmoothCcTensor g₀ 2 2) (T₀ : SmoothCcTensor g₀ 0 2) (B : ℝ), 0 ≤ B →
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T₀.toSection x) ≤ B ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
              εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) →
        ∀ p : ℕ,
          ‖appCc (I := I) (M := M) g₀ 2 2
              (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p C₀) T₀‖ ≤
            B * εa * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 2 : ℕ) : ℝ) T₀‖ +
              KT p * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 1 : ℕ) : ℝ) T₀‖ := by
  classical
  obtain ⟨CCS, hCCS_nn, hCCS⟩ := bal_CSUP (I := I) (M := M) g₀ Kc hKc_nn εa hεa_nn
  obtain ⟨CJ, hCJ_nn, hCJ⟩ := bal_jets_to_f (I := I) (M := M) g₀
  obtain ⟨CDS0, hCDS0_nn, hCDS0⟩ := bal_DSUPT (I := I) (M := M) g₀
  obtain ⟨c22, hc22_nn, hc22⟩ := bal_Ccore (I := I) (M := M) g₀ 2 2
  have hgapfam := fun k : ℕ => bal_jet_hs_gap (I := I) (M := M) g₀ k
  choose Cg hCg_nn hCg using hgapfam
  set n : ℕ := Module.finrank ℝ E with hn_def
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  set w : ℕ := n / 2 + 2 with hw_def
  set KE1 : ℕ → ℝ := fun p => (Real.sqrt (Kc (2 * p)) *
      (1 + ∑ j ∈ Finset.range (2 * p + 2), CJ j) + εa * CJ (2 * p + 2)) +
    c22 p * ∑ b ∈ Finset.range (2 * p),
      (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) + εa * CJ (b + 2))
    with hKE1_def
  have hKE1_nn : ∀ p, 0 ≤ KE1 p := by
    intro p
    have h1 : ∀ b : ℕ, 0 ≤ Real.sqrt (Kc b) *
        (1 + ∑ j ∈ Finset.range (b + 2), CJ j) + εa * CJ (b + 2) := by
      intro b
      have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (b + 2)) => hCJ_nn j)
      have := Real.sqrt_nonneg (Kc b)
      have := hCJ_nn (b + 2)
      nlinarith
    rw [hKE1_def]
    have h2 := Finset.sum_nonneg (fun b (_ : b ∈ Finset.range (2 * p)) => h1 b)
    have := h1 (2 * p)
    have := hc22_nn p
    nlinarith
  refine ⟨fun p => CCS 0 p * (1 + R₀) * CJ 0 +
      (CDS0 0 * R₀ * εa * Cg (2 * p + 1) +
        CDS0 0 * (1 + R₀) * KE1 p),
    fun p => ?_, ?_⟩
  · have h1 : (0:ℝ) ≤ CCS 0 p * (1 + R₀) * CJ 0 :=
      mul_nonneg (mul_nonneg (hCCS_nn 0 p) (by linarith)) (hCJ_nn 0)
    have h2 : (0:ℝ) ≤ CDS0 0 * R₀ * εa * Cg (2 * p + 1) :=
      mul_nonneg (mul_nonneg (mul_nonneg (hCDS0_nn 0) hR₀) hεa_nn) (hCg_nn _)
    have h3 : (0:ℝ) ≤ CDS0 0 * (1 + R₀) * KE1 p :=
      mul_nonneg (mul_nonneg (hCDS0_nn 0) (by linarith)) (hKE1_nn p)
    linarith
  intro C₀ T₀ B hB hball hdata henv p
  set fT : ℕ → ℝ := fun k => ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ) T₀‖
    with hfT_def
  have hfT_nn : ∀ k, 0 ≤ fT k := fun k => norm_nonneg _
  have hfT_mono : ∀ {k k' : ℕ}, k ≤ k' → fT k ≤ fT k' := fun {k k'} h =>
    bal_fmono (I := I) (M := M) g₀ T₀ h
  have hfT_ball : ∀ k, k ≤ a + 2 → fT k ≤ R₀ := by
    intro k hk
    refine le_trans (hfT_mono hk) ?_
    have h2 : fT (a + 2) = ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [h2]
    exact hball
  set Φp : SmoothCcTensor g₀ 2 2 := oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p C₀
    with hΦp_def
  by_cases hcase : w + 2 * p + 2 ≤ a + 2
  · have hsupΦ : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        (Φp.toSection x) ≤ (CCS 0 p * (1 + R₀)) ^ 2 := by
      intro x
      have h := hCCS C₀ T₀ henv 0 p x
      rw [show iteratedCovGrad (I := I) g₀ 2 2 0 Φp = Φp from
        iteratedCovGrad_zero _ _ _ _] at h
      refine le_trans h ?_
      have hf_le : fT (0 + w + 2 * p + 1) ≤ R₀ := hfT_ball _ (by omega)
      have h1 : CCS 0 p * (1 + fT (0 + w + 2 * p + 1)) ≤ CCS 0 p * (1 + R₀) := by
        refine mul_le_mul_of_nonneg_left ?_ (hCCS_nn 0 p)
        linarith
      refine pow_le_pow_left₀ ?_ h1 2
      have := hfT_nn (0 + w + 2 * p + 1)
      have := hCCS_nn 0 p
      nlinarith
    have hX : ‖appCc (I := I) (M := M) g₀ 2 2 Φp T₀‖ ≤
        CCS 0 p * (1 + R₀) * ‖T₀‖ := by
      refine appCc_l2_le_of_pointwise_fiberNormSq_bound_left (I := I) (M := M) g₀ 2 2
        Φp T₀ (CCS 0 p * (1 + R₀)) ?_ hsupΦ
      have := hCCS_nn 0 p
      nlinarith
    have hT0 : ‖T₀‖ ≤ CJ 0 * fT (2 * p + 1) := by
      have h := hCJ 0 T₀
      rw [show iteratedCovGrad (I := I) g₀ 0 2 0 T₀ = T₀ from
        iteratedCovGrad_zero _ _ _ _] at h
      refine le_trans h ?_
      exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hCJ_nn 0)
    have htot : ‖appCc (I := I) (M := M) g₀ 2 2 Φp T₀‖ ≤
        CCS 0 p * (1 + R₀) * CJ 0 * fT (2 * p + 1) := by
      refine le_trans hX ?_
      have h := mul_le_mul_of_nonneg_left hT0 (by
        have := hCCS_nn 0 p
        nlinarith : (0:ℝ) ≤ CCS 0 p * (1 + R₀))
      calc CCS 0 p * (1 + R₀) * ‖T₀‖
          ≤ CCS 0 p * (1 + R₀) * (CJ 0 * fT (2 * p + 1)) := h
        _ = CCS 0 p * (1 + R₀) * CJ 0 * fT (2 * p + 1) := by ring
    have hBεa_nn : 0 ≤ B * εa * fT (2 * p + 2) :=
      mul_nonneg (mul_nonneg hB hεa_nn) (hfT_nn _)
    have hrest_nn : 0 ≤ (CDS0 0 * R₀ * εa * Cg (2 * p + 1) +
        CDS0 0 * (1 + R₀) * KE1 p) * fT (2 * p + 1) := by
      have h2 : (0:ℝ) ≤ CDS0 0 * R₀ * εa * Cg (2 * p + 1) :=
        mul_nonneg (mul_nonneg (mul_nonneg (hCDS0_nn 0) hR₀) hεa_nn) (hCg_nn _)
      have h3 : (0:ℝ) ≤ CDS0 0 * (1 + R₀) * KE1 p :=
        mul_nonneg (mul_nonneg (hCDS0_nn 0) (by linarith)) (hKE1_nn p)
      exact mul_nonneg (by linarith) (hfT_nn _)
    calc ‖appCc (I := I) (M := M) g₀ 2 2 Φp T₀‖
        ≤ CCS 0 p * (1 + R₀) * CJ 0 * fT (2 * p + 1) := htot
      _ ≤ B * εa * fT (2 * p + 2) +
          (CCS 0 p * (1 + R₀) * CJ 0 +
            (CDS0 0 * R₀ * εa * Cg (2 * p + 1) +
              CDS0 0 * (1 + R₀) * KE1 p)) * fT (2 * p + 1) := by
          have h1 : 0 ≤ (CDS0 0 * R₀ * εa * Cg (2 * p + 1) +
              CDS0 0 * (1 + R₀) * KE1 p) * fT (2 * p + 1) := hrest_nn
          nlinarith [hBεa_nn]
  · set Bh : ℝ := CDS0 0 * fT (0 + (n / 2 + 1)) with hBh_def
    have hBh_nn : 0 ≤ Bh := mul_nonneg (hCDS0_nn 0) (hfT_nn _)
    set Bm : ℝ := min B Bh with hBm_def
    have hBm_nn : 0 ≤ Bm := le_min hB hBh_nn
    have hBm_pt : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        (T₀.toSection x) ≤ Bm ^ 2 := by
      intro x
      rcases le_total B Bh with h | h
      · rw [hBm_def, min_eq_left h]
        exact hdata x
      · rw [hBm_def, min_eq_right h]
        have hd := hCDS0 T₀ 0 x
        rw [show iteratedCovGrad (I := I) g₀ 0 2 0 T₀ = T₀ from
          iteratedCovGrad_zero _ _ _ _] at hd
        exact hd
    have hX : ‖appCc (I := I) (M := M) g₀ 2 2 Φp T₀‖ ≤ ‖Φp‖ * Bm :=
      appCc_l2_le_of_pointwise_fiberNormSq_bound_right (I := I) (M := M) g₀ 2 2
        Φp T₀ Bm hBm_nn hBm_pt
    have hΦcore := (hc22 p C₀).1
    have henvsum : ∀ (k : ℕ), k ≤ 2 * p + 2 →
        ∑ j ∈ Finset.range k, ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
          (∑ j ∈ Finset.range k, CJ j) * fT (2 * p + 1) := by
      intro k hk
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun j hj => ?_)
      have hjk := Finset.mem_range.mp hj
      refine le_trans (hCJ j T₀) ?_
      exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hCJ_nn j)
    set f₁ : ℝ := fT (2 * p + 1) with hf₁_def
    have hf₁_nn : 0 ≤ f₁ := hfT_nn _
    set u : ℝ := ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * p + 2) T₀‖ with hu_def
    have hu_nn : 0 ≤ u := norm_nonneg _
    have hone_aux : ∀ (X : ℝ), 0 ≤ X → 1 + X * f₁ ≤ (1 + X) * (1 + f₁) := by
      intro X hX
      nlinarith
    have htopC : ‖iteratedCovGrad (I := I) g₀ 2 2 (2 * p) C₀‖ ≤
        (Real.sqrt (Kc (2 * p)) * (1 + ∑ j ∈ Finset.range (2 * p + 2), CJ j)) *
          (1 + f₁) + εa * u := by
      refine le_trans (bal_env_lin (I := I) (M := M) g₀ Kc hKc_nn εa hεa_nn C₀ T₀ henv
        (2 * p)) ?_
      have hs := henvsum (2 * p + 2) (by omega)
      have hCJsum_nn : (0:ℝ) ≤ ∑ j ∈ Finset.range (2 * p + 2), CJ j :=
        Finset.sum_nonneg (fun j _ => hCJ_nn j)
      have h1 : 1 + ∑ j ∈ Finset.range (2 * p + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
          (1 + ∑ j ∈ Finset.range (2 * p + 2), CJ j) * (1 + f₁) := by
        refine le_trans ?_ (hone_aux _ hCJsum_nn)
        linarith
      have h2 := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg (Kc (2 * p)))
      have hueq : ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * p + 2) T₀‖ = u := rfl
      nlinarith [hεa_nn, hu_nn]
    have hlowC : ∑ b ∈ Finset.range (2 * p), ‖iteratedCovGrad (I := I) g₀ 2 2 b C₀‖ ≤
        (∑ b ∈ Finset.range (2 * p),
          (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) + εa * CJ (b + 2))) *
          (1 + f₁) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun b hb => ?_)
      have hb2p := Finset.mem_range.mp hb
      refine le_trans (bal_env_lin (I := I) (M := M) g₀ Kc hKc_nn εa hεa_nn C₀ T₀ henv b) ?_
      have hs := henvsum (b + 2) (by omega)
      have hCJsum_nn : (0:ℝ) ≤ ∑ j ∈ Finset.range (b + 2), CJ j :=
        Finset.sum_nonneg (fun j _ => hCJ_nn j)
      have h1 : 1 + ∑ j ∈ Finset.range (b + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
          (1 + ∑ j ∈ Finset.range (b + 2), CJ j) * (1 + f₁) := by
        refine le_trans ?_ (hone_aux _ hCJsum_nn)
        linarith
      have h2 := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg (Kc b))
      have h3 : ‖iteratedCovGrad (I := I) g₀ 0 2 (b + 2) T₀‖ ≤ CJ (b + 2) * f₁ := by
        refine le_trans (hCJ (b + 2) T₀) ?_
        exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hCJ_nn (b + 2))
      have h4 := mul_le_mul_of_nonneg_left h3 hεa_nn
      nlinarith [hεa_nn, hCJ_nn (b + 2), hf₁_nn]
    have hkey : ‖Φp‖ ≤ εa * u + KE1 p * (1 + f₁) := by
      refine le_trans hΦcore ?_
      have h5 := mul_le_mul_of_nonneg_left hlowC (hc22_nn p)
      rw [hKE1_def]
      have hε2p2 : (0:ℝ) ≤ εa * CJ (2 * p + 2) * (1 + f₁) :=
        mul_nonneg (mul_nonneg hεa_nn (hCJ_nn _)) (by linarith)
      nlinarith [htopC]
    have hgap := hCg (2 * p + 1) T₀
    have hc1 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p + 1 : ℕ) : ℝ) + 1) T₀‖ =
        fT (2 * p + 2) :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [hc1] at hgap
    have hu_le : u ≤ fT (2 * p + 2) + Cg (2 * p + 1) * f₁ := hgap
    have hBm_le_B : Bm ≤ B := min_le_left _ _
    have hBm_le_Bh : Bm ≤ Bh := min_le_right _ _
    have hBh_le : Bh ≤ CDS0 0 * R₀ := by
      rw [hBh_def]
      refine mul_le_mul_of_nonneg_left ?_ (hCDS0_nn 0)
      exact hfT_ball _ (by omega)
    have hBh_le_f₁ : Bh ≤ CDS0 0 * f₁ := by
      rw [hBh_def, hf₁_def]
      refine mul_le_mul_of_nonneg_left ?_ (hCDS0_nn 0)
      exact hfT_mono (by omega)
    have hfinal : ‖Φp‖ * Bm ≤
        B * εa * fT (2 * p + 2) +
          (CDS0 0 * R₀ * εa * Cg (2 * p + 1) + CDS0 0 * (1 + R₀) * KE1 p) * f₁ := by
      have hexp : ‖Φp‖ * Bm ≤ (εa * u + KE1 p * (1 + f₁)) * Bm :=
        mul_le_mul_of_nonneg_right hkey hBm_nn
      have h1 : εa * u * Bm ≤ εa * (fT (2 * p + 2) + Cg (2 * p + 1) * f₁) * Bm := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu_le hεa_nn) hBm_nn
      have h2 : εa * fT (2 * p + 2) * Bm ≤ εa * fT (2 * p + 2) * B :=
        mul_le_mul_of_nonneg_left hBm_le_B (mul_nonneg hεa_nn (hfT_nn _))
      have h3 : εa * (Cg (2 * p + 1) * f₁) * Bm ≤
          εa * (Cg (2 * p + 1) * f₁) * (CDS0 0 * R₀) :=
        mul_le_mul_of_nonneg_left (le_trans hBm_le_Bh hBh_le)
          (mul_nonneg hεa_nn (mul_nonneg (hCg_nn _) hf₁_nn))
      have h4 : KE1 p * 1 * Bm ≤ KE1 p * (CDS0 0 * f₁) := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left (le_trans hBm_le_Bh hBh_le_f₁) (hKE1_nn p)
      have h5 : KE1 p * f₁ * Bm ≤ KE1 p * f₁ * (CDS0 0 * R₀) :=
        mul_le_mul_of_nonneg_left (le_trans hBm_le_Bh hBh_le)
          (mul_nonneg (hKE1_nn p) hf₁_nn)
      nlinarith [hexp, h1, h2, h3, h4, h5]
    refine le_trans hX ?_
    simp only [hfT_def, hf₁_def] at hfinal
    refine le_trans hfinal ?_
    have hextra : 0 ≤ CCS 0 p * (1 + R₀) * CJ 0 *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 1 : ℕ) : ℝ) T₀‖ :=
      mul_nonneg (mul_nonneg (mul_nonneg (hCCS_nn 0 p) (by linarith)) (hCJ_nn 0))
        (norm_nonneg _)
    nlinarith [hextra]

set_option maxHeartbeats 3200000 in
private lemma bal_top_odd (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) (εa : ℝ) (hεa_nn : 0 ≤ εa) :
    ∃ KT : ℕ → ℝ, (∀ p, 0 ≤ KT p) ∧
      ∀ (C₀ : SmoothCcTensor g₀ 2 2) (T₀ : SmoothCcTensor g₀ 0 2) (B : ℝ), 0 ≤ B →
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T₀.toSection x) ≤ B ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
              εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) →
        ∀ p : ℕ,
          Real.sqrt (‖appCc (I := I) (M := M) g₀ 2 2
              (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p C₀) T₀‖ ^ 2 +
            ‖covGrad (I := I) (M := M) g₀ 0 2 (appCc (I := I) (M := M) g₀ 2 2
              (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p C₀) T₀)‖ ^ 2) ≤
            B * εa * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 3 : ℕ) : ℝ) T₀‖ +
              KT p * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 2 : ℕ) : ℝ) T₀‖ := by
  classical
  obtain ⟨CC, hCC_nn, hCC⟩ := bal_CJET (I := I) (M := M) g₀ Kc hKc_nn εa hεa_nn
  obtain ⟨CCS, hCCS_nn, hCCS⟩ := bal_CSUP (I := I) (M := M) g₀ Kc hKc_nn εa hεa_nn
  obtain ⟨CJ, hCJ_nn, hCJ⟩ := bal_jets_to_f (I := I) (M := M) g₀
  obtain ⟨CDS0, hCDS0_nn, hCDS0⟩ := bal_DSUPT (I := I) (M := M) g₀
  obtain ⟨c22, hc22_nn, hc22⟩ := bal_Ccore (I := I) (M := M) g₀ 2 2
  have hgapfam := fun k : ℕ =>
    exists_iteratedCovGrad_l2NormSq_le_smoothCcToTensorHs_succ_add_lower
      (I := I) (M := M) g₀ k
  choose Cq hCq_nn hCq using hgapfam
  set n : ℕ := Module.finrank ℝ E with hn_def
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  set w : ℕ := n / 2 + 2 with hw_def
  set KE1 : ℕ → ℝ := fun p => (Real.sqrt (Kc (2 * p)) *
      (1 + ∑ j ∈ Finset.range (2 * p + 2), CJ j) + εa * CJ (2 * p + 2)) +
    c22 p * ∑ b ∈ Finset.range (2 * p),
      (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) + εa * CJ (b + 2))
    with hKE1_def
  set KE2 : ℕ → ℝ := fun p => (Real.sqrt (Kc (2 * p + 1)) *
      (1 + ∑ j ∈ Finset.range (2 * p + 3), CJ j) + εa * CJ (2 * p + 3)) +
    c22 p * ∑ b ∈ Finset.range (2 * p + 1),
      (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) + εa * CJ (b + 2))
    with hKE2_def
  have hterm_nn : ∀ b : ℕ, 0 ≤ Real.sqrt (Kc b) *
      (1 + ∑ j ∈ Finset.range (b + 2), CJ j) + εa * CJ (b + 2) := by
    intro b
    have h1 := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (b + 2)) => hCJ_nn j)
    have h2 := Real.sqrt_nonneg (Kc b)
    have h3 := hCJ_nn (b + 2)
    nlinarith
  have hKE1_nn : ∀ p, 0 ≤ KE1 p := by
    intro p
    rw [hKE1_def]
    have h2 := Finset.sum_nonneg (fun b (_ : b ∈ Finset.range (2 * p)) => hterm_nn b)
    have := hterm_nn (2 * p)
    have := hc22_nn p
    nlinarith
  have hKE2_nn : ∀ p, 0 ≤ KE2 p := by
    intro p
    rw [hKE2_def]
    have h2 := Finset.sum_nonneg (fun b (_ : b ∈ Finset.range (2 * p + 1)) => hterm_nn b)
    have := hterm_nn (2 * p + 1)
    have := hc22_nn p
    nlinarith
  refine ⟨fun p =>
      (CCS 0 p * CJ 0 + CCS 1 p * CJ 0 + Real.sqrt n * CCS 0 p * CJ 1) * (1 + R₀) +
      (CDS0 0 * R₀ * εa * Real.sqrt (1 + Cq (2 * p + 1) + Cq (2 * p + 2)) +
        CDS0 0 * (1 + R₀) * (KE1 p + KE2 p) +
        Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀)),
    fun p => ?_, ?_⟩
  · have h1 : (0:ℝ) ≤ (CCS 0 p * CJ 0 + CCS 1 p * CJ 0 +
        Real.sqrt n * CCS 0 p * CJ 1) * (1 + R₀) := by
      have := hCCS_nn 0 p
      have := hCCS_nn 1 p
      have := hCJ_nn 0
      have := hCJ_nn 1
      have := Real.sqrt_nonneg (n : ℝ)
      have ha1 : (0:ℝ) ≤ CCS 0 p * CJ 0 := mul_nonneg (hCCS_nn 0 p) (hCJ_nn 0)
      have ha2 : (0:ℝ) ≤ CCS 1 p * CJ 0 := mul_nonneg (hCCS_nn 1 p) (hCJ_nn 0)
      have ha3 : (0:ℝ) ≤ Real.sqrt n * CCS 0 p * CJ 1 :=
        mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hCCS_nn 0 p)) (hCJ_nn 1)
      nlinarith
    have h2 : (0:ℝ) ≤ CDS0 0 * R₀ * εa *
        Real.sqrt (1 + Cq (2 * p + 1) + Cq (2 * p + 2)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (hCDS0_nn 0) hR₀) hεa_nn) (Real.sqrt_nonneg _)
    have h3 : (0:ℝ) ≤ CDS0 0 * (1 + R₀) * (KE1 p + KE2 p) :=
      mul_nonneg (mul_nonneg (hCDS0_nn 0) (by linarith))
        (add_nonneg (hKE1_nn p) (hKE2_nn p))
    have h4 : (0:ℝ) ≤ Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀) :=
      mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hCDS0_nn 1)) (hCC_nn 0 p))
        (by linarith)
    linarith
  intro C₀ T₀ B hB hball hdata henv p
  set fT : ℕ → ℝ := fun k => ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ) T₀‖
    with hfT_def
  have hfT_nn : ∀ k, 0 ≤ fT k := fun k => norm_nonneg _
  have hfT_mono : ∀ {k k' : ℕ}, k ≤ k' → fT k ≤ fT k' := fun {k k'} h =>
    bal_fmono (I := I) (M := M) g₀ T₀ h
  have hfT_ball : ∀ k, k ≤ a + 2 → fT k ≤ R₀ := by
    intro k hk
    refine le_trans (hfT_mono hk) ?_
    have h2 : fT (a + 2) = ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [h2]
    exact hball
  set Φp : SmoothCcTensor g₀ 2 2 := oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p C₀
    with hΦp_def
  set Xp : SmoothCcTensor g₀ 0 2 := appCc (I := I) (M := M) g₀ 2 2 Φp T₀ with hXp_def
  have hsplit : covGrad (I := I) (M := M) g₀ 0 2 Xp =
      appCc (I := I) (M := M) g₀ 2 (2 + 1) (covGrad (I := I) (M := M) g₀ 2 2 Φp) T₀ +
        appCc (I := I) (M := M) g₀ (2 + 1) (2 + 1)
          (slotExtend (I := I) (M := M) g₀ 2 2 Φp) (covGrad (I := I) (M := M) g₀ 0 2 T₀) :=
    covGrad_appCc_eq (I := I) (M := M) g₀ 2 2 Φp T₀
  set f₂ : ℝ := fT (2 * p + 2) with hf₂_def
  have hf₂_nn : 0 ≤ f₂ := hfT_nn _
  have hT0f : ‖T₀‖ ≤ CJ 0 * f₂ := by
    have h := hCJ 0 T₀
    rw [show iteratedCovGrad (I := I) g₀ 0 2 0 T₀ = T₀ from
      iteratedCovGrad_zero _ _ _ _] at h
    refine le_trans h ?_
    exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hCJ_nn 0)
  have hGT0f : ‖covGrad (I := I) (M := M) g₀ 0 2 T₀‖ ≤ CJ 1 * f₂ := by
    have h := hCJ 1 T₀
    rw [show iteratedCovGrad (I := I) g₀ 0 2 1 T₀ =
      covGrad (I := I) (M := M) g₀ 0 2 T₀ from
        (bal_icg_one (I := I) (M := M) g₀ 0 2 T₀).symm] at h
    refine le_trans h ?_
    exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hCJ_nn 1)
  by_cases hcase : w + 2 * p + 2 ≤ a + 2
  · have hsupΦ0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        (Φp.toSection x) ≤ (CCS 0 p * (1 + R₀)) ^ 2 := by
      intro x
      have h := hCCS C₀ T₀ henv 0 p x
      rw [show iteratedCovGrad (I := I) g₀ 2 2 0 Φp = Φp from
        iteratedCovGrad_zero _ _ _ _] at h
      refine le_trans h ?_
      have hf_le : fT (0 + w + 2 * p + 1) ≤ R₀ := hfT_ball _ (by omega)
      have h1 : CCS 0 p * (1 + fT (0 + w + 2 * p + 1)) ≤ CCS 0 p * (1 + R₀) := by
        refine mul_le_mul_of_nonneg_left ?_ (hCCS_nn 0 p)
        linarith
      refine pow_le_pow_left₀ ?_ h1 2
      have := hfT_nn (0 + w + 2 * p + 1)
      have := hCCS_nn 0 p
      nlinarith
    have hsupΦ1 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + 1) x
        ((covGrad (I := I) (M := M) g₀ 2 2 Φp).toSection x) ≤
        (CCS 1 p * (1 + R₀)) ^ 2 := by
      intro x
      have h := hCCS C₀ T₀ henv 1 p x
      rw [show iteratedCovGrad (I := I) g₀ 2 2 1 Φp =
        covGrad (I := I) (M := M) g₀ 2 2 Φp from
          (bal_icg_one (I := I) (M := M) g₀ 2 2 Φp).symm] at h
      refine le_trans h ?_
      have hf_le : fT (1 + w + 2 * p + 1) ≤ R₀ := hfT_ball _ (by omega)
      have h1 : CCS 1 p * (1 + fT (1 + w + 2 * p + 1)) ≤ CCS 1 p * (1 + R₀) := by
        refine mul_le_mul_of_nonneg_left ?_ (hCCS_nn 1 p)
        linarith
      refine pow_le_pow_left₀ ?_ h1 2
      have := hfT_nn (1 + w + 2 * p + 1)
      have := hCCS_nn 1 p
      nlinarith
    have hsupSE : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 1) (2 + 1) x
        ((slotExtend (I := I) (M := M) g₀ 2 2 Φp).toSection x) ≤
        (Real.sqrt n * (CCS 0 p * (1 + R₀))) ^ 2 := by
      intro x
      have h := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 2 2 Φp 0 x
      rw [show iteratedCovGrad (I := I) g₀ (2 + 1) (2 + 1) 0
          (slotExtend (I := I) (M := M) g₀ 2 2 Φp) =
        slotExtend (I := I) (M := M) g₀ 2 2 Φp from iteratedCovGrad_zero _ _ _ _] at h
      rw [show iteratedCovGrad (I := I) g₀ 2 2 0 Φp = Φp from
        iteratedCovGrad_zero _ _ _ _] at h
      refine le_trans h ?_
      have h2 := hsupΦ0 x
      have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
      have hns : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      nlinarith [riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 2 x (Φp.toSection x)]
    have hXb : ‖Xp‖ ≤ CCS 0 p * (1 + R₀) * (CJ 0 * f₂) := by
      have hn0' : (0:ℝ) ≤ CCS 0 p * (1 + R₀) :=
        mul_nonneg (hCCS_nn 0 p) (by linarith)
      have h := appCc_l2_le_of_pointwise_fiberNormSq_bound_left (I := I) (M := M) g₀ 2 2
        Φp T₀ (CCS 0 p * (1 + R₀)) hn0' hsupΦ0
      refine le_trans h ?_
      exact mul_le_mul_of_nonneg_left hT0f hn0'
    have hGXb : ‖covGrad (I := I) (M := M) g₀ 0 2 Xp‖ ≤
        CCS 1 p * (1 + R₀) * (CJ 0 * f₂) +
          Real.sqrt n * (CCS 0 p * (1 + R₀)) * (CJ 1 * f₂) := by
      rw [hsplit]
      refine le_trans (norm_add_le _ _) ?_
      have hn1' : (0:ℝ) ≤ CCS 1 p * (1 + R₀) :=
        mul_nonneg (hCCS_nn 1 p) (by linarith)
      have hn2' : (0:ℝ) ≤ Real.sqrt n * (CCS 0 p * (1 + R₀)) :=
        mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (hCCS_nn 0 p) (by linarith))
      have h1 := appCc_l2_le_of_pointwise_fiberNormSq_bound_left (I := I) (M := M) g₀ 2
        (2 + 1) (covGrad (I := I) (M := M) g₀ 2 2 Φp) T₀ (CCS 1 p * (1 + R₀))
        hn1' hsupΦ1
      have h2 := appCc_l2_le_of_pointwise_fiberNormSq_bound_left (I := I) (M := M) g₀
        (2 + 1) (2 + 1) (slotExtend (I := I) (M := M) g₀ 2 2 Φp)
        (covGrad (I := I) (M := M) g₀ 0 2 T₀) (Real.sqrt n * (CCS 0 p * (1 + R₀)))
        hn2' hsupSE
      have h1' : CCS 1 p * (1 + R₀) * ‖T₀‖ ≤ CCS 1 p * (1 + R₀) * (CJ 0 * f₂) :=
        mul_le_mul_of_nonneg_left hT0f hn1'
      have h2' : Real.sqrt n * (CCS 0 p * (1 + R₀)) *
          ‖covGrad (I := I) (M := M) g₀ 0 2 T₀‖ ≤
          Real.sqrt n * (CCS 0 p * (1 + R₀)) * (CJ 1 * f₂) :=
        mul_le_mul_of_nonneg_left hGT0f hn2'
      linarith [le_trans h1 h1', le_trans h2 h2']
    have hpair : Real.sqrt (‖Xp‖ ^ 2 + ‖covGrad (I := I) (M := M) g₀ 0 2 Xp‖ ^ 2) ≤
        ‖Xp‖ + ‖covGrad (I := I) (M := M) g₀ 0 2 Xp‖ := by
      have h := bal_sqrt_pair_two ‖Xp‖ 0 0 ‖covGrad (I := I) (M := M) g₀ 0 2 Xp‖
        (norm_nonneg _) (le_refl 0) (le_refl 0) (norm_nonneg _)
      simpa using h
    refine le_trans hpair ?_
    have hBεa_nn : 0 ≤ B * εa * fT (2 * p + 3) :=
      mul_nonneg (mul_nonneg hB hεa_nn) (hfT_nn _)
    have henv_nn : (0:ℝ) ≤ (CDS0 0 * R₀ * εa *
        Real.sqrt (1 + Cq (2 * p + 1) + Cq (2 * p + 2)) +
        CDS0 0 * (1 + R₀) * (KE1 p + KE2 p) +
        Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀)) * f₂ := by
      have h2 : (0:ℝ) ≤ CDS0 0 * R₀ * εa *
          Real.sqrt (1 + Cq (2 * p + 1) + Cq (2 * p + 2)) :=
        mul_nonneg (mul_nonneg (mul_nonneg (hCDS0_nn 0) hR₀) hεa_nn) (Real.sqrt_nonneg _)
      have h3 : (0:ℝ) ≤ CDS0 0 * (1 + R₀) * (KE1 p + KE2 p) :=
        mul_nonneg (mul_nonneg (hCDS0_nn 0) (by linarith))
          (add_nonneg (hKE1_nn p) (hKE2_nn p))
      have h4 : (0:ℝ) ≤ Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀) :=
        mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hCDS0_nn 1)) (hCC_nn 0 p))
          (by linarith)
      exact mul_nonneg (by linarith) hf₂_nn
    simp only [hf₂_def, hfT_def] at hXb hGXb
    nlinarith [hXb, hGXb, hBεa_nn, henv_nn]
  · set Bh : ℝ := CDS0 0 * fT (0 + (n / 2 + 1)) with hBh_def
    have hBh_nn : 0 ≤ Bh := mul_nonneg (hCDS0_nn 0) (hfT_nn _)
    set Bm : ℝ := min B Bh with hBm_def
    have hBm_nn : 0 ≤ Bm := le_min hB hBh_nn
    have hBm_pt : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        (T₀.toSection x) ≤ Bm ^ 2 := by
      intro x
      rcases le_total B Bh with h | h
      · rw [hBm_def, min_eq_left h]
        exact hdata x
      · rw [hBm_def, min_eq_right h]
        have hd := hCDS0 T₀ 0 x
        rw [show iteratedCovGrad (I := I) g₀ 0 2 0 T₀ = T₀ from
          iteratedCovGrad_zero _ _ _ _] at hd
        exact hd
    have hBm_le_B : Bm ≤ B := min_le_left _ _
    have hBm_le_Bh : Bm ≤ Bh := min_le_right _ _
    have hBh_le : Bh ≤ CDS0 0 * R₀ := by
      rw [hBh_def]
      exact mul_le_mul_of_nonneg_left (hfT_ball _ (by omega)) (hCDS0_nn 0)
    have hBh_le_f₂ : Bh ≤ CDS0 0 * f₂ := by
      rw [hBh_def, hf₂_def]
      exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hCDS0_nn 0)
    set u₂ : ℝ := ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * p + 2) T₀‖ with hu₂_def
    set u₃ : ℝ := ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * p + 3) T₀‖ with hu₃_def
    have hu₂_nn : 0 ≤ u₂ := norm_nonneg _
    have hu₃_nn : 0 ≤ u₃ := norm_nonneg _
    have hone_aux : ∀ (X : ℝ), 0 ≤ X → 1 + X * f₂ ≤ (1 + X) * (1 + f₂) := by
      intro X hX
      nlinarith
    have henvsum : ∀ (k : ℕ), k ≤ 2 * p + 3 →
        ∑ j ∈ Finset.range k, ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
          (∑ j ∈ Finset.range k, CJ j) * f₂ := by
      intro k hk
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun j hj => ?_)
      have hjk := Finset.mem_range.mp hj
      refine le_trans (hCJ j T₀) ?_
      rw [hf₂_def]
      exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hCJ_nn j)
    have henvC : ∀ (b : ℕ), b + 2 ≤ 2 * p + 3 → b + 2 ≤ 2 * p + 2 →
        ‖iteratedCovGrad (I := I) g₀ 2 2 b C₀‖ ≤
          (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) + εa * CJ (b + 2)) *
            (1 + f₂) := by
      intro b hb hb2
      refine le_trans (bal_env_lin (I := I) (M := M) g₀ Kc hKc_nn εa hεa_nn C₀ T₀ henv b) ?_
      have hs := henvsum (b + 2) hb
      have hCJsum_nn : (0:ℝ) ≤ ∑ j ∈ Finset.range (b + 2), CJ j :=
        Finset.sum_nonneg (fun j _ => hCJ_nn j)
      have h1 : 1 + ∑ j ∈ Finset.range (b + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
          (1 + ∑ j ∈ Finset.range (b + 2), CJ j) * (1 + f₂) := by
        refine le_trans ?_ (hone_aux _ hCJsum_nn)
        linarith
      have h2 := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg (Kc b))
      have h3 : ‖iteratedCovGrad (I := I) g₀ 0 2 (b + 2) T₀‖ ≤ CJ (b + 2) * f₂ := by
        refine le_trans (hCJ (b + 2) T₀) ?_
        rw [hf₂_def]
        exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hCJ_nn (b + 2))
      have h4 := mul_le_mul_of_nonneg_left h3 hεa_nn
      nlinarith [hεa_nn, hCJ_nn (b + 2), hf₂_nn]
    have hXb : ‖Xp‖ ≤ Bm * εa * u₂ + Bm * (KE1 p * (1 + f₂)) := by
      have hX : ‖Xp‖ ≤ ‖Φp‖ * Bm :=
        appCc_l2_le_of_pointwise_fiberNormSq_bound_right (I := I) (M := M) g₀ 2 2
          Φp T₀ Bm hBm_nn hBm_pt
      have hΦcore := (hc22 p C₀).1
      have htopC : ‖iteratedCovGrad (I := I) g₀ 2 2 (2 * p) C₀‖ ≤
          (Real.sqrt (Kc (2 * p)) * (1 + ∑ j ∈ Finset.range (2 * p + 2), CJ j)) *
            (1 + f₂) + εa * u₂ := by
        refine le_trans (bal_env_lin (I := I) (M := M) g₀ Kc hKc_nn εa hεa_nn C₀ T₀ henv
          (2 * p)) ?_
        have hs := henvsum (2 * p + 2) (by omega)
        have hCJsum_nn : (0:ℝ) ≤ ∑ j ∈ Finset.range (2 * p + 2), CJ j :=
          Finset.sum_nonneg (fun j _ => hCJ_nn j)
        have h1 : 1 + ∑ j ∈ Finset.range (2 * p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
            (1 + ∑ j ∈ Finset.range (2 * p + 2), CJ j) * (1 + f₂) := by
          refine le_trans ?_ (hone_aux _ hCJsum_nn)
          linarith
        have h2 := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg (Kc (2 * p)))
        nlinarith [hεa_nn, hu₂_nn]
      have hlowC : ∑ b ∈ Finset.range (2 * p), ‖iteratedCovGrad (I := I) g₀ 2 2 b C₀‖ ≤
          (∑ b ∈ Finset.range (2 * p),
            (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) +
              εa * CJ (b + 2))) * (1 + f₂) := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum (fun b hb => ?_)
        have hb2p := Finset.mem_range.mp hb
        exact henvC b (by omega) (by omega)
      have hkey : ‖Φp‖ ≤ εa * u₂ + KE1 p * (1 + f₂) := by
        refine le_trans hΦcore ?_
        have h5 := mul_le_mul_of_nonneg_left hlowC (hc22_nn p)
        rw [hKE1_def]
        have hε2p2 : (0:ℝ) ≤ εa * CJ (2 * p + 2) * (1 + f₂) :=
          mul_nonneg (mul_nonneg hεa_nn (hCJ_nn _)) (by linarith)
        nlinarith [htopC]
      calc ‖Xp‖ ≤ ‖Φp‖ * Bm := hX
        _ ≤ (εa * u₂ + KE1 p * (1 + f₂)) * Bm := mul_le_mul_of_nonneg_right hkey hBm_nn
        _ = Bm * εa * u₂ + Bm * (KE1 p * (1 + f₂)) := by ring
    have hGXb : ‖covGrad (I := I) (M := M) g₀ 0 2 Xp‖ ≤
        Bm * εa * u₃ + (Bm * (KE2 p * (1 + f₂)) +
          Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀) * f₂) := by
      rw [hsplit]
      refine le_trans (norm_add_le _ _) ?_
      have hp1 : ‖appCc (I := I) (M := M) g₀ 2 (2 + 1)
          (covGrad (I := I) (M := M) g₀ 2 2 Φp) T₀‖ ≤
          Bm * εa * u₃ + Bm * (KE2 p * (1 + f₂)) := by
        have hX := appCc_l2_le_of_pointwise_fiberNormSq_bound_right (I := I) (M := M) g₀
          2 (2 + 1) (covGrad (I := I) (M := M) g₀ 2 2 Φp) T₀ Bm hBm_nn hBm_pt
        have hΦcore := (hc22 p C₀).2
        have htopC : ‖iteratedCovGrad (I := I) g₀ 2 2 (2 * p + 1) C₀‖ ≤
            (Real.sqrt (Kc (2 * p + 1)) *
              (1 + ∑ j ∈ Finset.range (2 * p + 3), CJ j)) * (1 + f₂) + εa * u₃ := by
          refine le_trans (bal_env_lin (I := I) (M := M) g₀ Kc hKc_nn εa hεa_nn C₀ T₀ henv
            (2 * p + 1)) ?_
          have hs := henvsum (2 * p + 3) (by omega)
          have hCJsum_nn : (0:ℝ) ≤ ∑ j ∈ Finset.range (2 * p + 3), CJ j :=
            Finset.sum_nonneg (fun j _ => hCJ_nn j)
          have h1 : 1 + ∑ j ∈ Finset.range (2 * p + 3),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
              (1 + ∑ j ∈ Finset.range (2 * p + 3), CJ j) * (1 + f₂) := by
            refine le_trans ?_ (hone_aux _ hCJsum_nn)
            linarith
          have h2 := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg (Kc (2 * p + 1)))
          nlinarith [hεa_nn, hu₃_nn]
        have hlowC : ∑ b ∈ Finset.range (2 * p + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 b C₀‖ ≤
            (∑ b ∈ Finset.range (2 * p + 1),
              (Real.sqrt (Kc b) * (1 + ∑ j ∈ Finset.range (b + 2), CJ j) +
                εa * CJ (b + 2))) * (1 + f₂) := by
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum (fun b hb => ?_)
          have hb2p := Finset.mem_range.mp hb
          exact henvC b (by omega) (by omega)
        have hkey : ‖covGrad (I := I) (M := M) g₀ 2 2 Φp‖ ≤
            εa * u₃ + KE2 p * (1 + f₂) := by
          refine le_trans hΦcore ?_
          have h5 := mul_le_mul_of_nonneg_left hlowC (hc22_nn p)
          rw [hKE2_def]
          have hε2p3 : (0:ℝ) ≤ εa * CJ (2 * p + 3) * (1 + f₂) :=
            mul_nonneg (mul_nonneg hεa_nn (hCJ_nn _)) (by linarith)
          nlinarith [htopC]
        calc ‖appCc (I := I) (M := M) g₀ 2 (2 + 1)
              (covGrad (I := I) (M := M) g₀ 2 2 Φp) T₀‖
            ≤ ‖covGrad (I := I) (M := M) g₀ 2 2 Φp‖ * Bm := hX
          _ ≤ (εa * u₃ + KE2 p * (1 + f₂)) * Bm :=
              mul_le_mul_of_nonneg_right hkey hBm_nn
          _ = Bm * εa * u₃ + Bm * (KE2 p * (1 + f₂)) := by ring
      have hp2 : ‖appCc (I := I) (M := M) g₀ (2 + 1) (2 + 1)
          (slotExtend (I := I) (M := M) g₀ 2 2 Φp)
          (covGrad (I := I) (M := M) g₀ 0 2 T₀)‖ ≤
          Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀) * f₂ := by
        have hdsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
            ((covGrad (I := I) (M := M) g₀ 0 2 T₀).toSection x) ≤
            (CDS0 1 * fT (1 + (n / 2 + 1))) ^ 2 := by
          intro x
          have hd := hCDS0 T₀ 1 x
          rw [show iteratedCovGrad (I := I) g₀ 0 2 1 T₀ =
            covGrad (I := I) (M := M) g₀ 0 2 T₀ from
              (bal_icg_one (I := I) (M := M) g₀ 0 2 T₀).symm] at hd
          exact hd
        have hX := appCc_l2_le_of_pointwise_fiberNormSq_bound_right (I := I) (M := M) g₀
          (2 + 1) (2 + 1) (slotExtend (I := I) (M := M) g₀ 2 2 Φp)
          (covGrad (I := I) (M := M) g₀ 0 2 T₀) (CDS0 1 * fT (1 + (n / 2 + 1)))
          (mul_nonneg (hCDS0_nn 1) (hfT_nn _)) hdsup
        have hse := bal_slotExt_norm (I := I) (M := M) g₀ 2 2 Φp
        have hΦpl2 : ‖Φp‖ ≤ CC 0 p * (1 + fT (0 + 2 * p + 2)) := by
          have h := hCC C₀ T₀ henv 0 p
          rw [show iteratedCovGrad (I := I) g₀ 2 2 0 Φp = Φp from
            iteratedCovGrad_zero _ _ _ _] at h
          exact h
        have hprod : fT (1 + (n / 2 + 1)) * (1 + fT (0 + 2 * p + 2)) ≤ (1 + R₀) * f₂ := by
          have hm1 : fT (1 + (n / 2 + 1)) ≤ f₂ := by
            rw [hf₂_def]
            exact hfT_mono (by omega)
          have hm2 : fT (1 + (n / 2 + 1)) * fT (0 + 2 * p + 2) ≤ R₀ * f₂ := by
            have hb1 : fT (1 + (n / 2 + 1)) ≤ R₀ := hfT_ball _ (by omega)
            have hm3 : fT (0 + 2 * p + 2) ≤ f₂ := by
              rw [hf₂_def]
              exact hfT_mono (by omega)
            have := mul_le_mul hb1 hm3 (hfT_nn _) hR₀
            linarith
          nlinarith [hfT_nn (1 + (n / 2 + 1)), hfT_nn (0 + 2 * p + 2)]
        calc ‖appCc (I := I) (M := M) g₀ (2 + 1) (2 + 1)
              (slotExtend (I := I) (M := M) g₀ 2 2 Φp)
              (covGrad (I := I) (M := M) g₀ 0 2 T₀)‖
            ≤ ‖slotExtend (I := I) (M := M) g₀ 2 2 Φp‖ *
              (CDS0 1 * fT (1 + (n / 2 + 1))) := hX
          _ ≤ (Real.sqrt n * ‖Φp‖) * (CDS0 1 * fT (1 + (n / 2 + 1))) := by
              refine mul_le_mul_of_nonneg_right hse ?_
              exact mul_nonneg (hCDS0_nn 1) (hfT_nn _)
          _ ≤ (Real.sqrt n * (CC 0 p * (1 + fT (0 + 2 * p + 2)))) *
              (CDS0 1 * fT (1 + (n / 2 + 1))) := by
              refine mul_le_mul_of_nonneg_right ?_
                (mul_nonneg (hCDS0_nn 1) (hfT_nn _))
              exact mul_le_mul_of_nonneg_left hΦpl2 (Real.sqrt_nonneg _)
          _ = Real.sqrt n * CC 0 p * CDS0 1 *
              (fT (1 + (n / 2 + 1)) * (1 + fT (0 + 2 * p + 2))) := by ring
          _ ≤ Real.sqrt n * CC 0 p * CDS0 1 * ((1 + R₀) * f₂) := by
              refine mul_le_mul_of_nonneg_left hprod ?_
              exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hCC_nn 0 p)) (hCDS0_nn 1)
          _ = Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀) * f₂ := by ring
      linarith [hp1, hp2]
    have hgap₂ : u₂ ^ 2 ≤ fT (2 * p + 2) ^ 2 + Cq (2 * p + 1) * fT (2 * p + 1) ^ 2 := by
      have h := hCq (2 * p + 1) T₀
      rw [SmoothCcTensor.norm_toL2] at h
      have hc : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p + 1 : ℕ) : ℝ) + 1) T₀‖ =
          fT (2 * p + 2) :=
        smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
      rw [hc] at h
      exact h
    have hgap₃ : u₃ ^ 2 ≤ fT (2 * p + 3) ^ 2 + Cq (2 * p + 2) * fT (2 * p + 2) ^ 2 := by
      have h := hCq (2 * p + 2) T₀
      rw [SmoothCcTensor.norm_toL2] at h
      have hc : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p + 2 : ℕ) : ℝ) + 1) T₀‖ =
          fT (2 * p + 3) :=
        smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
      rw [hc] at h
      exact h
    set CqP : ℝ := Real.sqrt (1 + Cq (2 * p + 1) + Cq (2 * p + 2)) with hCqP_def
    have hCqP_nn : 0 ≤ CqP := Real.sqrt_nonneg _
    have hupair : Real.sqrt (u₂ ^ 2 + u₃ ^ 2) ≤ fT (2 * p + 3) + CqP * f₂ := by
      have hsq : CqP ^ 2 = 1 + Cq (2 * p + 1) + Cq (2 * p + 2) :=
        Real.sq_sqrt (by
          have := hCq_nn (2 * p + 1)
          have := hCq_nn (2 * p + 2)
          linarith)
      have hf₁f₂ : fT (2 * p + 1) ≤ f₂ := by
        rw [hf₂_def]
        exact hfT_mono (by omega)
      have hsum : u₂ ^ 2 + u₃ ^ 2 ≤ (fT (2 * p + 3) + CqP * f₂) ^ 2 := by
        have h23 : fT (2 * p + 2) ≤ fT (2 * p + 3) := hfT_mono (by omega)
        have hcross : 0 ≤ 2 * fT (2 * p + 3) * (CqP * f₂) := by
          have := hfT_nn (2 * p + 3)
          have := mul_nonneg hCqP_nn hf₂_nn
          nlinarith
        have hf₁sq : fT (2 * p + 1) ^ 2 ≤ f₂ ^ 2 := by
          nlinarith [hfT_nn (2 * p + 1)]
        have hf₂23 : fT (2 * p + 2) ^ 2 ≤ fT (2 * p + 3) ^ 2 := by
          nlinarith [hfT_nn (2 * p + 2)]
        nlinarith [hgap₂, hgap₃, hCq_nn (2 * p + 1), hCq_nn (2 * p + 2), hf₂_nn,
          hfT_nn (2 * p + 3), hf₁sq, hf₂23, hcross, hsq]
      calc Real.sqrt (u₂ ^ 2 + u₃ ^ 2)
          ≤ Real.sqrt ((fT (2 * p + 3) + CqP * f₂) ^ 2) := Real.sqrt_le_sqrt hsum
        _ = fT (2 * p + 3) + CqP * f₂ := Real.sqrt_sq (by
            have := hfT_nn (2 * p + 3)
            have := mul_nonneg hCqP_nn hf₂_nn
            linarith)
    set s₀ : ℝ := Bm * (KE1 p * (1 + f₂)) with hs₀_def
    set s₁ : ℝ := Bm * (KE2 p * (1 + f₂)) +
      Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀) * f₂ with hs₁_def
    have hs₀_nn : 0 ≤ s₀ := by
      rw [hs₀_def]
      exact mul_nonneg hBm_nn (mul_nonneg (hKE1_nn p) (by linarith))
    have hs₁_nn : 0 ≤ s₁ := by
      rw [hs₁_def]
      have h1 : (0:ℝ) ≤ Bm * (KE2 p * (1 + f₂)) :=
        mul_nonneg hBm_nn (mul_nonneg (hKE2_nn p) (by linarith))
      have h2 : (0:ℝ) ≤ Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀) * f₂ :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hCDS0_nn 1))
          (hCC_nn 0 p)) (by linarith)) hf₂_nn
      linarith
    have hBεu_nn : ∀ (v : ℝ), 0 ≤ v → 0 ≤ Bm * εa * v := fun v hv =>
      mul_nonneg (mul_nonneg hBm_nn hεa_nn) hv
    have hmono := bal_sqrt_mono_pair (norm_nonneg Xp)
      (norm_nonneg (covGrad (I := I) (M := M) g₀ 0 2 Xp)) hXb hGXb
    have htwo := bal_sqrt_pair_two (Bm * εa * u₂) s₀ (Bm * εa * u₃) s₁
      (hBεu_nn u₂ hu₂_nn) hs₀_nn (hBεu_nn u₃ hu₃_nn) hs₁_nn
    have hfactor : Real.sqrt ((Bm * εa * u₂) ^ 2 + (Bm * εa * u₃) ^ 2) =
        Bm * εa * Real.sqrt (u₂ ^ 2 + u₃ ^ 2) := by
      have h1 : (Bm * εa * u₂) ^ 2 + (Bm * εa * u₃) ^ 2 =
          (Bm * εa) ^ 2 * (u₂ ^ 2 + u₃ ^ 2) := by ring
      rw [h1, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hBm_nn hεa_nn)]
    have hs01 : Real.sqrt (s₀ ^ 2 + s₁ ^ 2) ≤ s₀ + s₁ := by
      have h := bal_sqrt_pair_two s₀ 0 0 s₁ hs₀_nn (le_refl 0) (le_refl 0) hs₁_nn
      simpa [Real.sqrt_sq hs₀_nn, Real.sqrt_sq hs₁_nn] using h
    have hchain : Real.sqrt (‖Xp‖ ^ 2 + ‖covGrad (I := I) (M := M) g₀ 0 2 Xp‖ ^ 2) ≤
        Bm * εa * fT (2 * p + 3) + Bm * εa * (CqP * f₂) + (s₀ + s₁) := by
      have h1 : Bm * εa * Real.sqrt (u₂ ^ 2 + u₃ ^ 2) ≤
          Bm * εa * (fT (2 * p + 3) + CqP * f₂) :=
        mul_le_mul_of_nonneg_left hupair (mul_nonneg hBm_nn hεa_nn)
      refine le_trans hmono (le_trans htwo ?_)
      rw [hfactor]
      refine le_trans (add_le_add h1 hs01) (le_of_eq ?_)
      ring
    have hsplit1 : Bm * εa * fT (2 * p + 3) ≤ B * εa * fT (2 * p + 3) := by
      have := mul_le_mul_of_nonneg_right hBm_le_B hεa_nn
      exact mul_le_mul_of_nonneg_right this (hfT_nn _)
    have hBm_leC : Bm ≤ CDS0 0 * R₀ := le_trans hBm_le_Bh hBh_le
    have hsplit2 : Bm * εa * (CqP * f₂) ≤ CDS0 0 * R₀ * εa * CqP * f₂ := by
      have h1 : Bm * εa ≤ CDS0 0 * R₀ * εa := mul_le_mul_of_nonneg_right hBm_leC hεa_nn
      have h2 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hCqP_nn hf₂_nn)
      calc Bm * εa * (CqP * f₂) ≤ CDS0 0 * R₀ * εa * (CqP * f₂) := h2
        _ = CDS0 0 * R₀ * εa * CqP * f₂ := by ring
    have hsplits₀ : s₀ ≤ CDS0 0 * (1 + R₀) * KE1 p * f₂ := by
      rw [hs₀_def]
      have h1 : Bm * KE1 p ≤ CDS0 0 * f₂ * KE1 p :=
        mul_le_mul_of_nonneg_right (le_trans hBm_le_Bh hBh_le_f₂) (hKE1_nn p)
      have h2 : Bm * (KE1 p * f₂) ≤ CDS0 0 * R₀ * (KE1 p * f₂) :=
        mul_le_mul_of_nonneg_right hBm_leC (mul_nonneg (hKE1_nn p) hf₂_nn)
      linarith [h1, h2]
    have hsplits₁ : s₁ ≤ CDS0 0 * (1 + R₀) * KE2 p * f₂ +
        Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀) * f₂ := by
      rw [hs₁_def]
      have h1 : Bm * KE2 p ≤ CDS0 0 * f₂ * KE2 p :=
        mul_le_mul_of_nonneg_right (le_trans hBm_le_Bh hBh_le_f₂) (hKE2_nn p)
      have h2 : Bm * (KE2 p * f₂) ≤ CDS0 0 * R₀ * (KE2 p * f₂) :=
        mul_le_mul_of_nonneg_right hBm_leC (mul_nonneg (hKE2_nn p) hf₂_nn)
      linarith [h1, h2]
    have hcrude_nn : (0:ℝ) ≤ (CCS 0 p * CJ 0 + CCS 1 p * CJ 0 +
        Real.sqrt n * CCS 0 p * CJ 1) * (1 + R₀) * f₂ := by
      have ha1 : (0:ℝ) ≤ CCS 0 p * CJ 0 := mul_nonneg (hCCS_nn 0 p) (hCJ_nn 0)
      have ha2 : (0:ℝ) ≤ CCS 1 p * CJ 0 := mul_nonneg (hCCS_nn 1 p) (hCJ_nn 0)
      have ha3 : (0:ℝ) ≤ Real.sqrt n * CCS 0 p * CJ 1 :=
        mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hCCS_nn 0 p)) (hCJ_nn 1)
      exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) hf₂_nn
    have hfinal : Real.sqrt (‖Xp‖ ^ 2 + ‖covGrad (I := I) (M := M) g₀ 0 2 Xp‖ ^ 2) ≤
        B * εa * fT (2 * p + 3) +
          ((CCS 0 p * CJ 0 + CCS 1 p * CJ 0 + Real.sqrt n * CCS 0 p * CJ 1) * (1 + R₀) +
            (CDS0 0 * R₀ * εa * CqP + CDS0 0 * (1 + R₀) * (KE1 p + KE2 p) +
              Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀))) * f₂ := by
      have hring : ((CCS 0 p * CJ 0 + CCS 1 p * CJ 0 +
          Real.sqrt n * CCS 0 p * CJ 1) * (1 + R₀) +
            (CDS0 0 * R₀ * εa * CqP + CDS0 0 * (1 + R₀) * (KE1 p + KE2 p) +
              Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀))) * f₂ =
          (CCS 0 p * CJ 0 + CCS 1 p * CJ 0 +
            Real.sqrt n * CCS 0 p * CJ 1) * (1 + R₀) * f₂ +
          (CDS0 0 * R₀ * εa * CqP * f₂ +
            (CDS0 0 * (1 + R₀) * KE1 p * f₂ + CDS0 0 * (1 + R₀) * KE2 p * f₂) +
            Real.sqrt n * CDS0 1 * CC 0 p * (1 + R₀) * f₂) := by ring
      rw [hring]
      linarith [hchain, hsplit1, hsplit2, hsplits₀, hsplits₁, hcrude_nn]
    rw [hf₂_def, hCqP_def] at hfinal
    simp only [hfT_def] at hfinal
    exact hfinal

set_option maxHeartbeats 1600000 in
private lemma bal_Etrans (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) (εa : ℝ) (hεa_nn : 0 ≤ εa) :
    ∃ KZ : ℕ → ℕ → ℝ, (∀ q m, 0 ≤ KZ q m) ∧
      ∀ (C₀ : SmoothCcTensor g₀ 2 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
              εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) →
        ∀ (q m : ℕ),
          ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 2 m
              (-(appCc (I := I) (M := M) g₀ 2 2
                    (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
                    (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))
                - appCc (I := I) (M := M) g₀ (2 + 2) 2
                    (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                    (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                      (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
                        (covGrad (I := I) (M := M) g₀ 2 2
                          (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                      (covGrad (I := I) (M := M) g₀ 0 2 T₀))
                - appCc (I := I) (M := M) g₀ (2 + 2) 2
                    (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                    (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                      (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                        (slotExtend (I := I) (M := M) g₀ 2 2
                          (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                      (covGrad (I := I) (M := M) g₀ 0 2 T₀)))‖ ≤
            KZ q m * ‖smoothCcToTensorHs (I := I) (M := M) g₀
              ((2 * m + 2 * q + 3 : ℕ) : ℝ) T₀‖ ∧
          ‖covGrad (I := I) (M := M) g₀ 0 2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 m
              (-(appCc (I := I) (M := M) g₀ 2 2
                    (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
                    (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))
                - appCc (I := I) (M := M) g₀ (2 + 2) 2
                    (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                    (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                      (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
                        (covGrad (I := I) (M := M) g₀ 2 2
                          (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                      (covGrad (I := I) (M := M) g₀ 0 2 T₀))
                - appCc (I := I) (M := M) g₀ (2 + 2) 2
                    (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                    (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                      (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                        (slotExtend (I := I) (M := M) g₀ 2 2
                          (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                      (covGrad (I := I) (M := M) g₀ 0 2 T₀))))‖ ≤
            KZ q m * ‖smoothCcToTensorHs (I := I) (M := M) g₀
              ((2 * m + 2 * q + 4 : ℕ) : ℝ) T₀‖ := by
  classical
  obtain ⟨CB1, hCB1_nn, hCB1⟩ := bal_block1 (I := I) (M := M) g₀ a ha_super hR₀
    Kc hKc_nn εa hεa_nn
  obtain ⟨CB23, hCB23_nn, hCB23⟩ := bal_block23 (I := I) (M := M) g₀ a ha_super hR₀
    Kc hKc_nn εa hεa_nn
  obtain ⟨c02, hc02_nn, hc02⟩ := bal_Ccore (I := I) (M := M) g₀ 0 2
  set CBtot : ℕ → ℕ → ℝ := fun q j => CB1 q j + 2 * CB23 q j with hCBtot_def
  have hCBtot_nn : ∀ q j, 0 ≤ CBtot q j := fun q j => by
    have := hCB1_nn q j
    have := hCB23_nn q j
    rw [hCBtot_def]
    dsimp only
    linarith
  refine ⟨fun q m => (CBtot q (2 * m) + c02 m * ∑ b ∈ Finset.range (2 * m), CBtot q b) +
      (CBtot q (2 * m + 1) + c02 m * ∑ b ∈ Finset.range (2 * m + 1), CBtot q b),
    fun q m => ?_, ?_⟩
  · have h1 := hCBtot_nn q (2 * m)
    have h2 := hCBtot_nn q (2 * m + 1)
    have h3 : (0:ℝ) ≤ ∑ b ∈ Finset.range (2 * m), CBtot q b :=
      Finset.sum_nonneg (fun b _ => hCBtot_nn q b)
    have h4 : (0:ℝ) ≤ ∑ b ∈ Finset.range (2 * m + 1), CBtot q b :=
      Finset.sum_nonneg (fun b _ => hCBtot_nn q b)
    have := hc02_nn m
    have := mul_nonneg (hc02_nn m) h3
    have := mul_nonneg (hc02_nn m) h4
    linarith
  intro C₀ T₀ hball henv q m
  set fT : ℕ → ℝ := fun k => ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ) T₀‖
    with hfT_def
  have hfT_nn : ∀ k, 0 ≤ fT k := fun k => norm_nonneg _
  have hfT_mono : ∀ {k k' : ℕ}, k ≤ k' → fT k ≤ fT k' := fun {k k'} h =>
    bal_fmono (I := I) (M := M) g₀ T₀ h
  set Eq : SmoothCcTensor g₀ 0 2 :=
    -(appCc (I := I) (M := M) g₀ 2 2
          (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))
      - appCc (I := I) (M := M) g₀ (2 + 2) 2
          (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
          (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2)
            (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
              (covGrad (I := I) (M := M) g₀ 2 2
                (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
            (covGrad (I := I) (M := M) g₀ 0 2 T₀))
      - appCc (I := I) (M := M) g₀ (2 + 2) 2
          (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
          (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2)
            (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
              (slotExtend (I := I) (M := M) g₀ 2 2
                (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
            (covGrad (I := I) (M := M) g₀ 0 2 T₀)) with hEq_def
  have hjets : ∀ j : ℕ, ‖iteratedCovGrad (I := I) g₀ 0 2 j Eq‖ ≤
      CBtot q j * fT (j + 2 * q + 3) := by
    intro j
    have hsplit : iteratedCovGrad (I := I) g₀ 0 2 j Eq =
        -(iteratedCovGrad (I := I) g₀ 0 2 j (appCc (I := I) (M := M) g₀ 2 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)))
          - iteratedCovGrad (I := I) g₀ 0 2 j (appCc (I := I) (M := M) g₀ (2 + 2) 2
              (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
              (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
                  (covGrad (I := I) (M := M) g₀ 2 2
                    (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                (covGrad (I := I) (M := M) g₀ 0 2 T₀)))
          - iteratedCovGrad (I := I) g₀ 0 2 j (appCc (I := I) (M := M) g₀ (2 + 2) 2
              (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
              (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                  (slotExtend (I := I) (M := M) g₀ 2 2
                    (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                (covGrad (I := I) (M := M) g₀ 0 2 T₀))) := by
      rw [hEq_def, iteratedCovGrad_sub, iteratedCovGrad_sub, iteratedCovGrad_neg]
    rw [hsplit]
    have h1 := hCB1 C₀ T₀ hball henv q j
    have h23 := hCB23 C₀ T₀ hball henv q j
    have hn1 := norm_sub_le
      (-(iteratedCovGrad (I := I) g₀ 0 2 j (appCc (I := I) (M := M) g₀ 2 2
          (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)))
        - iteratedCovGrad (I := I) g₀ 0 2 j (appCc (I := I) (M := M) g₀ (2 + 2) 2
            (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
            (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2)
              (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
                (covGrad (I := I) (M := M) g₀ 2 2
                  (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
              (covGrad (I := I) (M := M) g₀ 0 2 T₀))))
      (iteratedCovGrad (I := I) g₀ 0 2 j (appCc (I := I) (M := M) g₀ (2 + 2) 2
          (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
          (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2)
            (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
              (slotExtend (I := I) (M := M) g₀ 2 2
                (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
            (covGrad (I := I) (M := M) g₀ 0 2 T₀))))
    have hn2 := norm_sub_le
      (-(iteratedCovGrad (I := I) g₀ 0 2 j (appCc (I := I) (M := M) g₀ 2 2
          (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))))
      (iteratedCovGrad (I := I) g₀ 0 2 j (appCc (I := I) (M := M) g₀ (2 + 2) 2
          (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
          (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2)
            (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
              (covGrad (I := I) (M := M) g₀ 2 2
                (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
            (covGrad (I := I) (M := M) g₀ 0 2 T₀))))
    rw [norm_neg] at hn2
    have hfold : CBtot q j * fT (j + 2 * q + 3) =
        CB1 q j * fT (j + 2 * q + 3) + CB23 q j * fT (j + 2 * q + 3) +
          CB23 q j * fT (j + 2 * q + 3) := by
      rw [hCBtot_def]
      dsimp only
      ring
    rw [hfold]
    have hfeq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 2 * q + 3 : ℕ) : ℝ) T₀‖ =
        fT (j + 2 * q + 3) := rfl
    rw [hfeq] at h1 h23
    linarith [h1, h23.1, h23.2, hn1, hn2]
  have hcore := hc02 m Eq
  constructor
  · refine le_trans hcore.1 ?_
    have htop : ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * m) Eq‖ ≤
        CBtot q (2 * m) * fT (2 * m + 2 * q + 3) := hjets (2 * m)
    have hlow : ∑ b ∈ Finset.range (2 * m), ‖iteratedCovGrad (I := I) g₀ 0 2 b Eq‖ ≤
        (∑ b ∈ Finset.range (2 * m), CBtot q b) * fT (2 * m + 2 * q + 3) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun b hb => ?_)
      have hbm := Finset.mem_range.mp hb
      refine le_trans (hjets b) ?_
      exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hCBtot_nn q b)
    have h2 := mul_le_mul_of_nonneg_left hlow (hc02_nn m)
    have hnn : 0 ≤ (CBtot q (2 * m + 1) + c02 m * ∑ b ∈ Finset.range (2 * m + 1),
        CBtot q b) * fT (2 * m + 2 * q + 3) := by
      have h3 : (0:ℝ) ≤ ∑ b ∈ Finset.range (2 * m + 1), CBtot q b :=
        Finset.sum_nonneg (fun b _ => hCBtot_nn q b)
      exact mul_nonneg (by
        have := hCBtot_nn q (2 * m + 1)
        have := mul_nonneg (hc02_nn m) h3
        linarith) (hfT_nn _)
    have hgoalf : ‖smoothCcToTensorHs (I := I) (M := M) g₀
        ((2 * m + 2 * q + 3 : ℕ) : ℝ) T₀‖ = fT (2 * m + 2 * q + 3) := rfl
    rw [hgoalf]
    nlinarith [htop, h2]
  · refine le_trans hcore.2 ?_
    have htop : ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * m + 1) Eq‖ ≤
        CBtot q (2 * m + 1) * fT (2 * m + 2 * q + 4) := by
      refine le_trans (hjets (2 * m + 1)) ?_
      exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hCBtot_nn q (2 * m + 1))
    have hlow : ∑ b ∈ Finset.range (2 * m + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 b Eq‖ ≤
        (∑ b ∈ Finset.range (2 * m + 1), CBtot q b) * fT (2 * m + 2 * q + 4) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun b hb => ?_)
      have hbm := Finset.mem_range.mp hb
      refine le_trans (hjets b) ?_
      exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hCBtot_nn q b)
    have h2 := mul_le_mul_of_nonneg_left hlow (hc02_nn m)
    have hnn : 0 ≤ (CBtot q (2 * m) + c02 m * ∑ b ∈ Finset.range (2 * m),
        CBtot q b) * fT (2 * m + 2 * q + 4) := by
      have h3 : (0:ℝ) ≤ ∑ b ∈ Finset.range (2 * m), CBtot q b :=
        Finset.sum_nonneg (fun b _ => hCBtot_nn q b)
      exact mul_nonneg (by
        have := hCBtot_nn q (2 * m)
        have := mul_nonneg (hc02_nn m) h3
        linarith) (hfT_nn _)
    have hgoalf : ‖smoothCcToTensorHs (I := I) (M := M) g₀
        ((2 * m + 2 * q + 4 : ℕ) : ℝ) T₀‖ = fT (2 * m + 2 * q + 4) := rfl
    rw [hgoalf]
    nlinarith [htop, h2]
end BalLadder

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 1600000 in

private lemma appCc_armZeroTwoArm_oneMinusConnLapIter_l2_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i)
    (εa : ℝ) (hεa_nn : 0 ≤ εa) (Λa : ℝ) (hΛa_nn : 0 ≤ Λa) :
    ∃ Kop : ℕ → ℝ, (∀ p, 0 ≤ Kop p) ∧
      ∀ (C₀ : SmoothCcTensor g₀ (2 + 0) 2) (T₀ : SmoothCcTensor g₀ 0 2) (B : ℝ),
        0 ≤ B →
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T₀.toSection x) ≤ B ^ 2) →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 0) 2 x (C₀.toSection x) ≤ Λa ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
              εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) →
        ∀ p : ℕ,
          ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p
              (appCc (I := I) (M := M) g₀ (2 + 0) 2 C₀
                (iteratedCovGrad (I := I) g₀ 0 2 0 T₀))‖ ≤
            B * εa *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 2) T₀‖ +
              Kop p *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 1) T₀‖ ∧
          ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p
              (appCc (I := I) (M := M) g₀ (2 + 0) 2 C₀
                (iteratedCovGrad (I := I) g₀ 0 2 0 T₀))‖ ^ 2 +
            ‖covGrad (I := I) (M := M) g₀ 0 2
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p
                (appCc (I := I) (M := M) g₀ (2 + 0) 2 C₀
                  (iteratedCovGrad (I := I) g₀ 0 2 0 T₀)))‖ ^ 2 ≤
            (B * εa *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 3) T₀‖ +
              Kop p *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 2) T₀‖) ^ 2 := by
  classical
  obtain ⟨KTe, hKTe_nn, hKTe⟩ := bal_top (I := I) (M := M) g₀ a ha_super hR₀
    Kc hKc_nn εa hεa_nn
  obtain ⟨KTo, hKTo_nn, hKTo⟩ := bal_top_odd (I := I) (M := M) g₀ a ha_super hR₀
    Kc hKc_nn εa hεa_nn
  obtain ⟨KZ, hKZ_nn, hKZ⟩ := bal_Etrans (I := I) (M := M) g₀ a ha_super hR₀
    Kc hKc_nn εa hεa_nn
  refine ⟨fun p => KTe p + KTo p +
      2 * ∑ q ∈ Finset.range p, KZ q (p - 1 - q),
    fun p => by
      have h1 : (0:ℝ) ≤ ∑ q ∈ Finset.range p, KZ q (p - 1 - q) :=
        Finset.sum_nonneg (fun q _ => hKZ_nn q (p - 1 - q))
      have := hKTe_nn p
      have := hKTo_nn p
      linarith, ?_⟩
  intro C₀ T₀ B hB hball hdata _hsup henv p
  set fT : ℕ → ℝ := fun k => ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ) T₀‖
    with hfT_def
  have hfT_nn : ∀ k, 0 ≤ fT k := fun k => norm_nonneg _
  have hfT_mono : ∀ {k k' : ℕ}, k ≤ k' → fT k ≤ fT k' := fun {k k'} h =>
    bal_fmono (I := I) (M := M) g₀ T₀ h
  have hKZsum_nn : (0:ℝ) ≤ ∑ q ∈ Finset.range p, KZ q (p - 1 - q) :=
    Finset.sum_nonneg (fun q _ => hKZ_nn q (p - 1 - q))
  have htransport := bal_transport (I := I) (M := M) g₀ C₀ T₀ p
  have hA_eq : oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p
      (appCc (I := I) (M := M) g₀ (2 + 0) 2 C₀
        (iteratedCovGrad (I := I) g₀ 0 2 0 T₀)) =
      appCc (I := I) (M := M) g₀ 2 2 (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p C₀) T₀ +
        ∑ q ∈ Finset.range p, oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (p - 1 - q)
          (-(appCc (I := I) (M := M) g₀ 2 2 (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))
            - appCc (I := I) (M := M) g₀ (2 + 2) 2 (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                  (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
                    (covGrad (I := I) (M := M) g₀ 2 2
                      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                  (covGrad (I := I) (M := M) g₀ 0 2 T₀))
            - appCc (I := I) (M := M) g₀ (2 + 2) 2 (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                  (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                    (slotExtend (I := I) (M := M) g₀ 2 2
                      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                  (covGrad (I := I) (M := M) g₀ 0 2 T₀))) := htransport
  have hStop := hKTe C₀ T₀ B hB hball hdata henv p
  have hSodd := hKTo C₀ T₀ B hB hball hdata henv p
  have hZbound : ∀ q ∈ Finset.range p,
      ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (p - 1 - q)
          (-(appCc (I := I) (M := M) g₀ 2 2 (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))
            - appCc (I := I) (M := M) g₀ (2 + 2) 2 (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                  (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
                    (covGrad (I := I) (M := M) g₀ 2 2
                      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                  (covGrad (I := I) (M := M) g₀ 0 2 T₀))
            - appCc (I := I) (M := M) g₀ (2 + 2) 2 (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                  (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                    (slotExtend (I := I) (M := M) g₀ 2 2
                      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                  (covGrad (I := I) (M := M) g₀ 0 2 T₀)))‖ ≤
        KZ q (p - 1 - q) * fT (2 * p + 1) ∧
      ‖covGrad (I := I) (M := M) g₀ 0 2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (p - 1 - q)
          (-(appCc (I := I) (M := M) g₀ 2 2 (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))
            - appCc (I := I) (M := M) g₀ (2 + 2) 2 (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                  (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
                    (covGrad (I := I) (M := M) g₀ 2 2
                      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                  (covGrad (I := I) (M := M) g₀ 0 2 T₀))
            - appCc (I := I) (M := M) g₀ (2 + 2) 2 (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                  (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                    (slotExtend (I := I) (M := M) g₀ 2 2
                      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                  (covGrad (I := I) (M := M) g₀ 0 2 T₀))))‖ ≤
        KZ q (p - 1 - q) * fT (2 * p + 2) := by
    intro q hq
    have hqp := Finset.mem_range.mp hq
    have h := hKZ C₀ T₀ hball henv q (p - 1 - q)
    have hidx1 : (2 * (p - 1 - q) + 2 * q + 3 : ℕ) = 2 * p + 1 := by omega
    have hidx2 : (2 * (p - 1 - q) + 2 * q + 4 : ℕ) = 2 * p + 2 := by omega
    rw [hidx1, hidx2] at h
    exact h
  set Zf : ℕ → SmoothCcTensor g₀ 0 2 := fun q =>
    oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (p - 1 - q)
      (-(appCc (I := I) (M := M) g₀ 2 2 (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))
        - appCc (I := I) (M := M) g₀ (2 + 2) 2 (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
            (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2)
              (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
                (covGrad (I := I) (M := M) g₀ 2 2
                  (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
              (covGrad (I := I) (M := M) g₀ 0 2 T₀))
        - appCc (I := I) (M := M) g₀ (2 + 2) 2 (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
            (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 2)
              (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                (slotExtend (I := I) (M := M) g₀ 2 2
                  (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
              (covGrad (I := I) (M := M) g₀ 0 2 T₀)))
    with hZf_def
  constructor
  · have hgc2 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 2) T₀‖ =
        fT (2 * p + 2) :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    have hgc1 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 1) T₀‖ =
        fT (2 * p + 1) :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [hgc2, hgc1, hA_eq]
    refine le_trans (norm_add_le _ _) ?_
    have hsum : ‖∑ q ∈ Finset.range p, Zf q‖ ≤ ∑ q ∈ Finset.range p, ‖Zf q‖ :=
      norm_sum_le (Finset.range p) Zf
    have hsum2 : ∑ q ∈ Finset.range p, ‖Zf q‖ ≤
        (∑ q ∈ Finset.range p, KZ q (p - 1 - q)) * fT (2 * p + 1) := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum (fun q hq => (hZbound q hq).1)
    have htopfe : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 2 : ℕ) : ℝ) T₀‖ =
        fT (2 * p + 2) := rfl
    have htopfo : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 1 : ℕ) : ℝ) T₀‖ =
        fT (2 * p + 1) := rfl
    rw [htopfe, htopfo] at hStop
    have hKTo_extra : (0:ℝ) ≤ KTo p * fT (2 * p + 1) :=
      mul_nonneg (hKTo_nn p) (hfT_nn _)
    have hKZ_extra : (0:ℝ) ≤ (∑ q ∈ Finset.range p, KZ q (p - 1 - q)) * fT (2 * p + 1) :=
      mul_nonneg hKZsum_nn (hfT_nn _)
    nlinarith [hStop, le_trans hsum hsum2]
  · have hgc3 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 3) T₀‖ =
        fT (2 * p + 3) :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    have hgc2 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 2) T₀‖ =
        fT (2 * p + 2) :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [hgc3, hgc2, hA_eq]
    set Xp : SmoothCcTensor g₀ 0 2 := appCc (I := I) (M := M) g₀ 2 2
      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p C₀) T₀ with hXp_def
    set S : SmoothCcTensor g₀ 0 2 := ∑ q ∈ Finset.range p, Zf q with hS_def
    have hcovsplit : covGrad (I := I) (M := M) g₀ 0 2 (Xp + S) =
        covGrad (I := I) (M := M) g₀ 0 2 Xp + covGrad (I := I) (M := M) g₀ 0 2 S :=
      covGrad_add (I := I) (M := M) g₀ 0 2 Xp S
    have hnorm1 : ‖Xp + S‖ ≤ ‖Xp‖ + ‖S‖ := norm_add_le _ _
    have hnorm2 : ‖covGrad (I := I) (M := M) g₀ 0 2 (Xp + S)‖ ≤
        ‖covGrad (I := I) (M := M) g₀ 0 2 Xp‖ + ‖covGrad (I := I) (M := M) g₀ 0 2 S‖ := by
      rw [hcovsplit]
      exact norm_add_le _ _
    have hmono := bal_sqrt_mono_pair (norm_nonneg (Xp + S))
      (norm_nonneg (covGrad (I := I) (M := M) g₀ 0 2 (Xp + S))) hnorm1 hnorm2
    have htwo := bal_sqrt_pair_two ‖Xp‖ ‖S‖ ‖covGrad (I := I) (M := M) g₀ 0 2 Xp‖
      ‖covGrad (I := I) (M := M) g₀ 0 2 S‖ (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg _) (norm_nonneg _)
    have hSpair : Real.sqrt (‖S‖ ^ 2 + ‖covGrad (I := I) (M := M) g₀ 0 2 S‖ ^ 2) ≤
        ‖S‖ + ‖covGrad (I := I) (M := M) g₀ 0 2 S‖ := by
      have h := bal_sqrt_pair_two ‖S‖ 0 0 ‖covGrad (I := I) (M := M) g₀ 0 2 S‖
        (norm_nonneg _) (le_refl 0) (le_refl 0) (norm_nonneg _)
      simpa using h
    have hSnorm : ‖S‖ ≤ (∑ q ∈ Finset.range p, KZ q (p - 1 - q)) * fT (2 * p + 2) := by
      rw [hS_def]
      refine le_trans (norm_sum_le _ _) ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun q hq => ?_)
      refine le_trans (hZbound q hq).1 ?_
      exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hKZ_nn q (p - 1 - q))
    have hGSnorm : ‖covGrad (I := I) (M := M) g₀ 0 2 S‖ ≤
        (∑ q ∈ Finset.range p, KZ q (p - 1 - q)) * fT (2 * p + 2) := by
      rw [hS_def]
      have hmapc : covGrad (I := I) (M := M) g₀ 0 2 (∑ q ∈ Finset.range p, Zf q) =
          ∑ q ∈ Finset.range p, covGrad (I := I) (M := M) g₀ 0 2 (Zf q) :=
        map_sum (AddMonoidHom.mk' (covGrad (I := I) (M := M) g₀ 0 2)
          (covGrad_add (I := I) (M := M) g₀ 0 2)) Zf (Finset.range p)
      rw [hmapc]
      refine le_trans (norm_sum_le _ _) ?_
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum (fun q hq => (hZbound q hq).2)
    have htopfo : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 3 : ℕ) : ℝ) T₀‖ =
        fT (2 * p + 3) := rfl
    have htopfe : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 2 : ℕ) : ℝ) T₀‖ =
        fT (2 * p + 2) := rfl
    rw [htopfo, htopfe] at hSodd
    have hchain : Real.sqrt (‖Xp + S‖ ^ 2 +
        ‖covGrad (I := I) (M := M) g₀ 0 2 (Xp + S)‖ ^ 2) ≤
        B * εa * fT (2 * p + 3) +
          (KTe p + KTo p + 2 * ∑ q ∈ Finset.range p, KZ q (p - 1 - q)) *
            fT (2 * p + 2) := by
      refine le_trans hmono (le_trans htwo ?_)
      have hKTe_extra : (0:ℝ) ≤ KTe p * fT (2 * p + 2) :=
        mul_nonneg (hKTe_nn p) (hfT_nn _)
      have h1 := le_trans hSpair (add_le_add hSnorm hGSnorm)
      nlinarith [hSodd, h1]
    have hLHS_nn : 0 ≤ ‖Xp + S‖ ^ 2 +
        ‖covGrad (I := I) (M := M) g₀ 0 2 (Xp + S)‖ ^ 2 := by positivity
    have hRHS_nn : 0 ≤ B * εa * fT (2 * p + 3) +
        (KTe p + KTo p + 2 * ∑ q ∈ Finset.range p, KZ q (p - 1 - q)) * fT (2 * p + 2) := by
      have h1 : (0:ℝ) ≤ B * εa * fT (2 * p + 3) :=
        mul_nonneg (mul_nonneg hB hεa_nn) (hfT_nn _)
      have h2 : (0:ℝ) ≤ (KTe p + KTo p +
          2 * ∑ q ∈ Finset.range p, KZ q (p - 1 - q)) * fT (2 * p + 2) := by
        have := hKTe_nn p
        have := hKTo_nn p
        exact mul_nonneg (by linarith) (hfT_nn _)
      linarith
    have hsq : ‖Xp + S‖ ^ 2 + ‖covGrad (I := I) (M := M) g₀ 0 2 (Xp + S)‖ ^ 2 =
        Real.sqrt (‖Xp + S‖ ^ 2 +
          ‖covGrad (I := I) (M := M) g₀ 0 2 (Xp + S)‖ ^ 2) ^ 2 :=
      (Real.sq_sqrt hLHS_nn).symm
    rw [hsq]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hchain 2

private lemma appCc_armZeroTwoArm_spectralCore
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i)
    (εa : ℝ) (hεa_nn : 0 ≤ εa) (Λa : ℝ) (hΛa_nn : 0 ≤ Λa) :
    ∃ Cop : ℕ → ℝ, (∀ m, 0 ≤ Cop m) ∧
      ∀ (C₀ : SmoothCcTensor g₀ (2 + 0) 2) (T₀ : SmoothCcTensor g₀ 0 2) (B : ℝ),
        0 ≤ B →
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T₀.toSection x) ≤ B ^ 2) →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 0) 2 x (C₀.toSection x) ≤ Λa ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
              εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) →
        ∀ m : ℕ,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
              (appCc (I := I) (M := M) g₀ (2 + 0) 2 C₀
                (iteratedCovGrad (I := I) g₀ 0 2 0 T₀))‖ ≤
            B * εa *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ +
              Cop m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T₀‖ := by
  classical
  obtain ⟨Kop, hKop_nn, hKop⟩ :=
    appCc_armZeroTwoArm_oneMinusConnLapIter_l2_le (I := I) (M := M) g₀ a ha_super hR₀
      Kc hKc_nn εa hεa_nn Λa hΛa_nn
  refine ⟨fun m => Kop (m / 2), fun m => hKop_nn (m / 2),
    fun C₀ T₀ B hB_nn hball hdata hsup henv m => ?_⟩
  have hlad := hKop C₀ T₀ B hB_nn hball hdata hsup henv
  rcases Nat.even_or_odd m with ⟨p, hp⟩ | ⟨p, hp⟩
  · have hm2 : m = 2 * p := by omega
    subst hm2
    have hidx : 2 * p / 2 = p := by omega
    simp only [hidx]
    have heven := smoothCcToTensorHs_even_norm_eq_toL2_iter (I := I) (M := M) g₀ p
      (appCc (I := I) (M := M) g₀ (2 + 0) 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 T₀))
    rw [SmoothCcTensor.norm_toL2] at heven
    rw [heven]
    exact (hlad p).1
  · subst hp
    have hidx : (2 * p + 1) / 2 = p := by omega
    simp only [hidx]
    set Y : SmoothCcTensor g₀ 0 2 :=
      appCc (I := I) (M := M) g₀ (2 + 0) 2 C₀
        (iteratedCovGrad (I := I) g₀ 0 2 0 T₀) with hY_def
    have hodd := smoothCcToTensorHs_odd_norm_sq_eq_toL2_iter_add_covGrad
      (I := I) (M := M) g₀ p Y
    rw [SmoothCcTensor.norm_toL2, SmoothCcTensor.norm_toL2] at hodd
    have h2 := (hlad p).2
    have hc2 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p + 1 : ℕ) : ℝ) + 2) T₀‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 3) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    have hc1 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p + 1 : ℕ) : ℝ) + 1) T₀‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 2) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [hc2, hc1]
    set R : ℝ := B * εa *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 3) T₀‖ +
      Kop p * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 2) T₀‖
      with hR_def
    have hR_nn : 0 ≤ R := by
      rw [hR_def]
      exact add_nonneg (mul_nonneg (mul_nonneg hB_nn hεa_nn) (norm_nonneg _))
        (mul_nonneg (hKop_nn p) (norm_nonneg _))
    have hsq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 1 : ℕ) : ℝ) Y‖ ^ 2 ≤
        R ^ 2 := by
      rw [hodd]
      exact h2
    calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 1 : ℕ) : ℝ) Y‖
        = Real.sqrt (‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 1 : ℕ) : ℝ) Y‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (R ^ 2) := Real.sqrt_le_sqrt hsq
      _ = R := Real.sqrt_sq hR_nn

private lemma appCc_armZeroTwoArmCoeff_opNorm_core
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i)
    (εa : ℝ) (hεa_nn : 0 ≤ εa) (Λa : ℝ) (hΛa_nn : 0 ≤ Λa) :
    ∃ Cop : ℕ → ℝ, (∀ m, 0 ≤ Cop m) ∧
      ∀ (C₀ : SmoothCcTensor g₀ (2 + 0) 2) (T₀ : SmoothCcTensor g₀ 0 2) (δ : ℝ),
        0 ≤ δ →
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T₀ x v w = ccTensorBilin (I := I) g₀ T₀ x w v) →
        gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 0) 2 x (C₀.toSection x) ≤ Λa ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
              εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) →
        ∀ m : ℕ,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
              (appCc (I := I) (M := M) g₀ (2 + 0) 2 C₀
                (iteratedCovGrad (I := I) g₀ 0 2 0 T₀))‖ ≤
            Real.sqrt (Module.finrank ℝ E) * εa * δ *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ +
              Cop m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T₀‖ := by
  classical
  obtain ⟨Cop, hCop_nn, hcore⟩ :=
    appCc_armZeroTwoArm_spectralCore (I := I) (M := M) g₀ a ha_super hR₀ Kc hKc_nn
      εa hεa_nn Λa hΛa_nn
  refine ⟨Cop, hCop_nn, fun C₀ T₀ δ hδ_nn hball hTsymm hfibre hsup hjet m => ?_⟩
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
  · haveI := hM
    have hB_nn : 0 ≤ Real.sqrt (Module.finrank ℝ E) * δ :=
      mul_nonneg (Real.sqrt_nonneg _) hδ_nn
    have hdata : ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T₀.toSection x) ≤
          (Real.sqrt (Module.finrank ℝ E) * δ) ^ 2 := by
      intro x
      have h := armZeroTwoArm_data_fibreNormSq_le (I := I) (M := M) g₀ T₀ hTsymm hfibre x
      have hsq : (Real.sqrt (Module.finrank ℝ E) * δ) ^ 2 =
          (Module.finrank ℝ E : ℝ) * δ ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
      rw [hsq]; exact h
    have hmain := hcore C₀ T₀ (Real.sqrt (Module.finrank ℝ E) * δ) hB_nn hball hdata hsup hjet m
    have htop : Real.sqrt (Module.finrank ℝ E) * δ * εa =
        Real.sqrt (Module.finrank ℝ E) * εa * δ := by ring
    rw [htop] at hmain
    exact hmain

private theorem exists_smoothCcToTensorHs_appCc_armZeroTwoArmCoeff_opNorm_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i)
    (εa : ℝ) (hεa_nn : 0 ≤ εa) (Λa : ℝ) (hΛa_nn : 0 ≤ Λa) :
    ∃ εB : ℝ, 0 ≤ εB ∧
      (0 ≤ δ → εB ≤ 2 * Real.sqrt (Module.finrank ℝ E) * εa * δ) ∧
    ∃ Cop : ℕ → ℝ, (∀ m, 0 ≤ Cop m) ∧
      ∀ (C₀ : SmoothCcTensor g₀ (2 + 0) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T₀ x v w = ccTensorBilin (I := I) g₀ T₀ x w v) →
        gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 0) 2 x (C₀.toSection x) ≤
            Λa ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
              εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) →
        ∀ m : ℕ,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
              (appCc (I := I) (M := M) g₀ (2 + 0) 2 C₀
                (iteratedCovGrad (I := I) g₀ 0 2 0 T₀))‖ ≤
            εB * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ +
              Cop m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T₀‖ := by
  classical
  obtain ⟨Cop, hCop_nn, hcore⟩ :=
    appCc_armZeroTwoArmCoeff_opNorm_core (I := I) (M := M) g₀ a ha_super hR₀
      Kc hKc_nn εa hεa_nn Λa hΛa_nn
  refine ⟨Real.sqrt (Module.finrank ℝ E) * εa * max δ 0,
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hεa_nn) (le_max_right _ _),
    fun hδ_nn => ?_, Cop, hCop_nn, fun C₀ T₀ hball hTsymm hfibre hsup hjet m => ?_⟩
  · rw [max_eq_left hδ_nn]
    have hnn : 0 ≤ Real.sqrt (Module.finrank ℝ E) * εa * δ :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hεa_nn) hδ_nn
    nlinarith [hnn]
  · rcases isEmpty_or_nonempty M with hM | hM
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
    · haveI := hM
      have hδ_nn : 0 ≤ δ :=
        armZeroTwoArm_delta_nonneg (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T₀) hfibre
      rw [max_eq_left hδ_nn]
      exact hcore C₀ T₀ δ hδ_nn hball hTsymm hfibre hsup hjet m

set_option maxHeartbeats 1000000 in

theorem exists_deTurckSmoothRemainderDiff_eq_principalCometricArm_add_smallThirdArm_add_tame
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ εwrap : ℝ, 0 ≤ εwrap ∧
      (0 ≤ δ → εwrap ≤ 32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 * (δ / (1 - δ))) ∧
    ∃ Cthird Ctame : ℕ → ℝ, (∀ k, 0 ≤ Cthird k) ∧ (∀ k, 0 ≤ Ctame k) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2)
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T₀ x v w = ccTensorBilin (I := I) g₀ T₀ x w v)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ∃ third tame : SmoothCcTensor g₀ 0 2,
          deTurckSmoothRemainder (I := I) g₀ g_bg T₀
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) -
            deTurckSmoothRemainder (I := I) g₀ g_bg
              (0 : SmoothCcTensor g₀ 0 2)
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
              (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                (by
                  rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                      from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                    tensorHs_norm_smul]
                  simpa using hR₀)) =
            deTurckPrincipalCometricArm (I := I) (M := M) g₀
              (tensorSectionRealizeMetric (I := I) g₀ T₀
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)) T₀
              + third + tame ∧
          (∀ k : ℕ,
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) third‖ ≤
              εwrap * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) + 1) T₀‖ +
                Cthird k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖) ∧
          (∀ k : ℕ,
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) tame‖ ≤
              Ctame k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖) := by
  classical
  obtain ⟨εC, hεC_nn, hεC_cap, hεC_cap', Kc, hKc_nn, εa, hεa_nn, hεa_cap, Λa, hΛa_nn,
    Ctame, hCtame_nn, htame⟩ :=
    exists_smoothCcToTensorHs_deTurckSmoothRemainderDiff_sub_principalCometricArm_smallThirdArm_tame_le
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  obtain ⟨Cop, hCop_nn, hH3⟩ :=
    exists_smoothCcToTensorHs_appCc_fibreSmallCoeff_opNorm_le
      (I := I) (M := M) g₀ a ha_super hR₀ εC hεC_nn Kc hKc_nn
  obtain ⟨εB, hεB_nn, hεB_cap, CopB, hCopB_nn, hB'⟩ :=
    exists_smoothCcToTensorHs_appCc_armZeroTwoArmCoeff_opNorm_le
      (I := I) (M := M) g₀ a ha_super hR₀ (δ := δ) Kc hKc_nn εa hεa_nn Λa hΛa_nn
  refine ⟨deTurckArmFibreConst (Module.finrank ℝ E) * εC + εB,
    add_nonneg (mul_nonneg (deTurckArmFibreConst_nonneg _) hεC_nn) hεB_nn,
    fun hδ_nn => ?_,
    fun k => Cop (a + k - 1) + CopB (a + k - 1), Ctame,
    fun k => add_nonneg (hCop_nn _) (hCopB_nn _), hCtame_nn, fun T₀ hTsymm hball => ?_⟩
  · have hδ_lt1 : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
    have hκ_nn : 0 ≤ δ / (1 - δ) := div_nonneg hδ_nn (by linarith)
    have hδκ : δ ≤ δ / (1 - δ) := by
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 - δ)]
      nlinarith [sq_nonneg δ]
    have hf_nn : 0 ≤ deTurckArmFibreConst (Module.finrank ℝ E) :=
      deTurckArmFibreConst_nonneg _
    have h1 : deTurckArmFibreConst (Module.finrank ℝ E) * εC ≤
        28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 * (δ / (1 - δ)) := by
      calc deTurckArmFibreConst (Module.finrank ℝ E) * εC
          ≤ deTurckArmFibreConst (Module.finrank ℝ E) *
              (28 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) :=
            mul_le_mul_of_nonneg_left (hεC_cap' hδ_nn) hf_nn
        _ = 28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 * (δ / (1 - δ)) := by ring
    have h2sq_nn : (0 : ℝ) ≤ 2 * Real.sqrt (Module.finrank ℝ E) * εa :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hεa_nn
    have h2 : εB ≤ (32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
        28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2) * (δ / (1 - δ)) := by
      refine le_trans (hεB_cap hδ_nn) ?_
      calc 2 * Real.sqrt (Module.finrank ℝ E) * εa * δ
          ≤ 2 * Real.sqrt (Module.finrank ℝ E) * εa * (δ / (1 - δ)) :=
            mul_le_mul_of_nonneg_left hδκ h2sq_nn
        _ ≤ (32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
              28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2) * (δ / (1 - δ)) :=
            mul_le_mul_of_nonneg_right hεa_cap hκ_nn
    calc deTurckArmFibreConst (Module.finrank ℝ E) * εC + εB
        ≤ 28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 * (δ / (1 - δ)) +
            (32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
              28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2) * (δ / (1 - δ)) :=
          add_le_add h1 h2
      _ = 32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 * (δ / (1 - δ)) := by ring
  obtain ⟨C₂, C₀, hC₂sup, hC₂jet, hC₀sup, hC₀jet, hHsbound⟩ := htame T₀ hTsymm hball
  refine ⟨appCc (I := I) (M := M) g₀ (2 + 2) 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) +
      appCc (I := I) (M := M) g₀ (2 + 0) 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 T₀),
    deTurckSmoothRemainder (I := I) g₀ g_bg T₀
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
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)) T₀ -
      appCc (I := I) (M := M) g₀ (2 + 2) 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) -
      appCc (I := I) (M := M) g₀ (2 + 0) 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 T₀),
    by abel, fun k => ?_, hHsbound⟩
  · have hm1 : (a : ℝ) + (k : ℝ) - 1 = ((a + k - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (show 1 ≤ a + k by omega)]; push_cast; ring
    have hm2 : (a : ℝ) + (k : ℝ) + 1 = ((a + k - 1 : ℕ) : ℝ) + 2 := by
      rw [← hm1]; ring
    have hm3 : (a : ℝ) + (k : ℝ) = ((a + k - 1 : ℕ) : ℝ) + 1 := by
      rw [← hm1]; ring
    rw [hm1, hm2, hm3, smoothCcToTensorHs_add]
    refine le_trans (norm_add_le _ _) ?_
    have hA := hH3 C₂ T₀ hball hC₂sup hC₂jet (a + k - 1)
    have hB2 := hB' C₀ T₀ hball hTsymm (hδ_fibre T₀ hball) hC₀sup hC₀jet (a + k - 1)
    linarith [hA, hB2]

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end

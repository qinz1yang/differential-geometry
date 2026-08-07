import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalCometricExtraction
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.DirichletSpectralBochnerGap
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralNormLIterateLadder
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.AppCcJetWindowTame
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricDifferenceSlotPairing
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricInverseDifferenceMultiplier
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.OperatorFieldPairingIBP
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorDirichletCurrentGreenIdentityRS
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.RoughLaplacianAppCcCommutation
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev
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

private local instance tensorRSNormedAddCommGroupOfRiemannianBundle
    (r s : ℕ) [Bundle.RiemannianBundle (fun y : M => Tensor0SBundle.TensorRSSpace r s I y)]
      (x : M) :
    NormedAddCommGroup (Tensor0SBundle.TensorRSSpace r s I x) :=
  Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
    (E := fun y : M => Tensor0SBundle.TensorRSSpace r s I y) x

theorem smoothCcToTensorHs_zero_norm_eq (g₀ : SmoothRiemannianMetric I M)
    (X : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ 0 X‖ =
      ‖SmoothCcTensor.toL2 X‖ := by
  classical
  have hnn_lhs : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ 0 X‖ := norm_nonneg _
  have hnn_rhs : 0 ≤ ‖SmoothCcTensor.toL2 X‖ := norm_nonneg _
  have hsq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ 0 X‖ ^ 2 =
      ‖SmoothCcTensor.toL2 X‖ ^ 2 := by
    rw [tensorHs.norm_sq_eq_tsum]
    rw [show (fun i => tensorSobolevWeight (I := I) (M := M) i (0 : ℝ) *
          ((smoothCcToTensorHs (I := I) (M := M) g₀ 0 X).coeff i) ^ 2) =
        fun i => (tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (SmoothCcTensor.toL2 X) i) ^ 2 by
      funext i
      rw [tensorSobolevWeight_zero, one_mul, smoothCcToTensorHs_coeff]]
    exact tensorParseval_l2Coeff_ofCompact_sq (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
      (SmoothCcTensor.toL2 X)
  nlinarith [hsq, hnn_lhs, hnn_rhs, sq_nonneg
    (‖smoothCcToTensorHs (I := I) (M := M) g₀ 0 X‖ - ‖SmoothCcTensor.toL2 X‖)]

theorem smoothCcToTensorHs_norm_order_congr (g₀ : SmoothRiemannianMetric I M)
    {σ σ' : ℝ} (h : σ = σ') (T : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ T‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ' T‖ := by
  subst h; rfl

theorem smoothCcToTensorHs_inner_order_congr (g₀ : SmoothRiemannianMetric I M)
    {σ σ' : ℝ} (h : σ = σ') (S T : SmoothCcTensor g₀ 0 2) :
    (inner ℝ (smoothCcToTensorHs (I := I) (M := M) g₀ σ S)
        (smoothCcToTensorHs (I := I) (M := M) g₀ σ T) : ℝ) =
      (inner ℝ (smoothCcToTensorHs (I := I) (M := M) g₀ σ' S)
        (smoothCcToTensorHs (I := I) (M := M) g₀ σ' T) : ℝ) := by
  subst h; rfl

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma weight_natCast [SigmaCompactSpace M] (g₀ : SmoothRiemannianMetric I M)
    (i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 2) (n : ℕ) :
    tensorSobolevWeight (I := I) (M := M) i ((n : ℕ) : ℝ) =
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ n := by
  unfold tensorSobolevWeight
  rw [Real.rpow_natCast]

private lemma smoothCcToTensorHs_rawConnLap_coeff (g₀ : SmoothRiemannianMetric I M)
    (σ : ℝ) (T₀ : SmoothCcTensor g₀ 0 2)
    (i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 2) :
    (smoothCcToTensorHs (I := I) (M := M) g₀ σ
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)).coeff i =
      -(TensorEigenIdx.lambda (I := I) (M := M) i) *
        (smoothCcToTensorHs (I := I) (M := M) g₀ σ T₀).coeff i := by
  classical
  have hdiag := tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter (I := I) (M := M) g₀
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2) T₀ i 1
  have hiter1 : oneMinusConnLapSmoothIter (I := I) g₀ 0 2 1 T₀ =
      oneMinusConnLapSmooth (I := I) g₀ 0 2 T₀ := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, oneMinusConnLapSmoothIter_succ,
      oneMinusConnLapSmoothIter_zero]
  have hsub : SmoothCcTensor.toL2 (oneMinusConnLapSmooth (I := I) g₀ 0 2 T₀) =
      SmoothCcTensor.toL2 T₀ -
        SmoothCcTensor.toL2 (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀) := by
    unfold oneMinusConnLapSmooth
    exact map_sub _ _ _
  rw [hiter1, hsub] at hdiag
  rw [tensorL2Coeff_eq_inner, inner_sub_right, ← tensorL2Coeff_eq_inner,
    ← tensorL2Coeff_eq_inner] at hdiag
  rw [smoothCcToTensorHs_coeff, smoothCcToTensorHs_coeff]
  rw [pow_one] at hdiag
  linear_combination -hdiag

private lemma smoothCcToTensorHs_two_le_connLap_add (g₀ : SmoothRiemannianMetric I M)
    (T₀ : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) T₀‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ +
        Real.sqrt 2 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀‖ := by
  classical
  have hsum2 : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i ((2 : ℕ) : ℝ) *
      ((smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) T₀).coeff i) ^ 2) :=
    (smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) T₀).weighted_summable
  have hsum0 : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i (0 : ℝ) *
      ((smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)).coeff i) ^ 2) :=
    (smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)).weighted_summable
  have hsum1 : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i ((1 : ℕ) : ℝ) *
      ((smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀).coeff i) ^ 2) :=
    (smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀).weighted_summable
  have hsq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) T₀‖ ^ 2 ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ ^ 2 +
        2 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀‖ ^ 2 := by
    rw [tensorHs.norm_sq_eq_tsum, tensorHs.norm_sq_eq_tsum, tensorHs.norm_sq_eq_tsum]
    have hterm : ∀ i, tensorSobolevWeight (I := I) (M := M) i ((2 : ℕ) : ℝ) *
        ((smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) T₀).coeff i) ^ 2 ≤
        tensorSobolevWeight (I := I) (M := M) i (0 : ℝ) *
            ((smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)).coeff i) ^ 2 +
          2 * (tensorSobolevWeight (I := I) (M := M) i ((1 : ℕ) : ℝ) *
            ((smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀).coeff i) ^ 2) := by
      intro i
      have hlam_nn : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
        tensor_lambda_nonneg (I := I) (M := M) i
      have hcoeff2 : (smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) T₀).coeff i =
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀).coeff i := rfl
      rw [smoothCcToTensorHs_rawConnLap_coeff (I := I) (M := M) g₀ (0 : ℝ) T₀ i,
        weight_natCast, weight_natCast, tensorSobolevWeight_zero, hcoeff2]
      have hcoeff0 : (smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ) T₀).coeff i =
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀).coeff i := rfl
      rw [hcoeff0]
      set lam := TensorEigenIdx.lambda (I := I) (M := M) i
      set ci := (smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀).coeff i
      have hsq_ci : 0 ≤ ci ^ 2 := sq_nonneg _
      nlinarith [hsq_ci, hlam_nn]
    calc (∑' i, tensorSobolevWeight (I := I) (M := M) i ((2 : ℕ) : ℝ) *
          ((smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) T₀).coeff i) ^ 2)
        ≤ ∑' i, (tensorSobolevWeight (I := I) (M := M) i (0 : ℝ) *
              ((smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)).coeff i) ^ 2 +
            2 * (tensorSobolevWeight (I := I) (M := M) i ((1 : ℕ) : ℝ) *
              ((smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀).coeff i) ^ 2)) :=
          Summable.tsum_le_tsum hterm hsum2 (hsum0.add (hsum1.mul_left 2))
      _ = (∑' i, tensorSobolevWeight (I := I) (M := M) i (0 : ℝ) *
              ((smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)).coeff i) ^ 2) +
            2 * ∑' i, tensorSobolevWeight (I := I) (M := M) i ((1 : ℕ) : ℝ) *
              ((smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀).coeff i) ^ 2 := by
          rw [Summable.tsum_add hsum0 (hsum1.mul_left 2), tsum_mul_left]
  have hb_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ := norm_nonneg _
  have hc_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀‖ :=
    norm_nonneg _
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt2_nn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  refine le_of_sq_le_sq ?_ (by positivity)
  nlinarith [hsq, hs2, mul_nonneg (mul_nonneg hsqrt2_nn hb_nn) hc_nn]

lemma delta_nonneg_of_ball_gFibreOpBound [Nonempty M] (g₀ : SmoothRiemannianMetric I M)
    (a : ℕ) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) {δ : ℝ}
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    0 ≤ δ := by
  have hzero_ball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
      (0 : SmoothCcTensor g₀ 0 2)‖ ≤ R₀ := by
    have h0 : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (0 : SmoothCcTensor g₀ 0 2) = 0 := by
      refine tensorHs.ext (funext fun i => ?_)
      rw [smoothCcToTensorHs_coeff, tensorHs.zero_coeff,
        show SmoothCcTensor.toL2 (0 : SmoothCcTensor g₀ 0 2) =
          (0 : TensorL2 0 2 g₀) from map_zero _,
        tensorL2Coeff_eq_inner, inner_zero_right]
    rw [h0, norm_zero]
    exact hR₀
  obtain ⟨x₀⟩ := ‹Nonempty M›
  obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
    haveI : Nontrivial (TangentSpace I x₀) := by
      have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
        have hrk : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
        rw [hrk]; exact Nat.pos_of_ne_zero (NeZero.ne _)
      exact Module.nontrivial_of_finrank_pos hfr
    exact exists_ne 0
  have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
  have hbound := hδ_fibre (0 : SmoothCcTensor g₀ 0 2) hzero_ball x₀ v v
  have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
  have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2) x₀ v v| :=
    abs_nonneg _
  by_contra hδc
  have hδc' : δ < 0 := lt_of_not_ge hδc
  have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
    have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 :=
      mul_neg_of_neg_of_pos hδc' hsqrt_pos
    exact mul_neg_of_neg_of_pos h1 hsqrt_pos
  linarith [le_trans habs_nn hbound]

theorem arm_realize_Hs_norm_zero_le [Nonempty M]
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ Clower : ℝ, 0 ≤ Clower ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀
              (tensorSectionRealizeMetric (I := I) g₀ T₀
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                (hδ_fibre T₀ hball)) T₀)‖ ≤
          deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ +
            Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℝ) + 1) T₀‖ := by
  classical
  have hδ_lt1 : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
  have h1δ : (0 : ℝ) < 1 - δ := by linarith
  have hδ_nn : 0 ≤ δ := delta_nonneg_of_ball_gFibreOpBound (I := I) (M := M) g₀ a hR₀ hδ_fibre
  have hκ_nn : 0 ≤ δ / (1 - δ) := div_nonneg hδ_nn h1δ.le
  have hCE_nn : 0 ≤ deTurckArmFibreConst (Module.finrank ℝ E) :=
    deTurckArmFibreConst_nonneg _
  obtain ⟨Cgap, hCgap_nn, hgap⟩ :=
    exists_iteratedCovGrad_l2NormSq_le_smoothCcToTensorHs_succ_add_lower
      (I := I) (M := M) g₀ 1
  refine ⟨deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
      (Real.sqrt 2 + Real.sqrt Cgap), by positivity, fun T₀ hball => ?_⟩
  set g₁ := tensorSectionRealizeMetric (I := I) g₀ T₀
    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) with hg₁_def
  set armT := deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ T₀ with harm_def
  have hHs0 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ) armT‖ = ‖armT‖ := by
    rw [smoothCcToTensorHs_zero_norm_eq, SmoothCcTensor.norm_toL2]
  have h615 : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (armT.toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ 3 * (δ / (1 - δ)) ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
            ((iteratedCovGrad (I := I) g₀ 0 2 2 T₀).toSection x) := fun x =>
    riemannianFiberNormSq_deTurckPrincipalCometricArm_le (I := I) (M := M) g₀ g₁
      (fun y => ccTensorBilinSymm (I := I) g₀ T₀ y)
      (fun y v w => tensorSectionRealizeMetric_inner (I := I) g₀ T₀
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) y v w)
      hδ_lt1 hδ_nn (hδ_fibre T₀ hball) T₀ x
  have hFint : MeasureTheory.Integrable
      (fun x => (Module.finrank ℝ E : ℝ) ^ 3 * (δ / (1 - δ)) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
          ((iteratedCovGrad (I := I) g₀ 0 2 2 T₀).toSection x))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 4
      (iteratedCovGrad (I := I) g₀ 0 2 2 T₀)).const_mul _
  have hsq1 : ‖armT‖ ^ 2 ≤ (Module.finrank ℝ E : ℝ) ^ 3 * (δ / (1 - δ)) ^ 2 *
      ‖iteratedCovGrad (I := I) g₀ 0 2 2 T₀‖ ^ 2 := by
    have h1 := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
      (I := I) (M := M) g₀ 0 2 armT _ hFint h615
    rw [MeasureTheory.integral_const_mul] at h1
    have hbridge := tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
      (I := I) (M := M) g₀ 0 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T₀)
    rw [← hbridge, ← SmoothCcTensor.norm_def (I := I) (M := M)] at h1
    exact h1
  have harm_le : ‖armT‖ ≤ deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
      ‖iteratedCovGrad (I := I) g₀ 0 2 2 T₀‖ := by
    have hrhs_nn : 0 ≤ deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
        ‖iteratedCovGrad (I := I) g₀ 0 2 2 T₀‖ := by positivity
    refine le_of_sq_le_sq ?_ hrhs_nn
    have hexp : (deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
        ‖iteratedCovGrad (I := I) g₀ 0 2 2 T₀‖) ^ 2 =
        deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 * (δ / (1 - δ)) ^ 2 *
          ‖iteratedCovGrad (I := I) g₀ 0 2 2 T₀‖ ^ 2 := by ring
    rw [hexp, sq_deTurckArmFibreConst]
    exact hsq1
  have hgap1 := hgap T₀
  rw [SmoothCcTensor.norm_toL2] at hgap1
  have hgap' : ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + 1) T₀‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T₀‖ +
        Real.sqrt Cgap * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀‖ := by
    have hb_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T₀‖ :=
      norm_nonneg _
    have hc_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀‖ :=
      norm_nonneg _
    have hsqrt_nn : 0 ≤ Real.sqrt Cgap := Real.sqrt_nonneg _
    refine le_of_sq_le_sq ?_ (by positivity)
    have hsC : Real.sqrt Cgap ^ 2 = Cgap := Real.sq_sqrt hCgap_nn
    nlinarith [hgap1, mul_nonneg (mul_nonneg hsqrt_nn hb_nn) hc_nn]
  have htwo1 : ‖iteratedCovGrad (I := I) g₀ 0 2 2 T₀‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + 1) T₀‖ := rfl
  have hcast2 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T₀‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) T₀‖ :=
    smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
  have htwo := smoothCcToTensorHs_two_le_connLap_add (I := I) (M := M) g₀ T₀
  have hcast1 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℝ) + 1) T₀‖ :=
    smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
  have hCEκ_nn : 0 ≤ deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) :=
    mul_nonneg hCE_nn hκ_nn
  have hjets : ‖iteratedCovGrad (I := I) g₀ 0 2 2 T₀‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ +
        (Real.sqrt 2 + Real.sqrt Cgap) *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℝ) + 1) T₀‖ := by
    rw [← hcast1]
    calc ‖iteratedCovGrad (I := I) g₀ 0 2 2 T₀‖
        = ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + 1) T₀‖ := htwo1
      _ ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T₀‖ +
            Real.sqrt Cgap * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀‖ :=
          hgap'
      _ = ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) T₀‖ +
            Real.sqrt Cgap * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀‖ := by
          rw [hcast2]
      _ ≤ (‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ +
            Real.sqrt 2 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀‖) +
            Real.sqrt Cgap * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀‖ := by
          linarith [htwo]
      _ = ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ +
            (Real.sqrt 2 + Real.sqrt Cgap) *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀‖ := by ring
  have hchain : ‖armT‖ ≤ deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
      (‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ +
        (Real.sqrt 2 + Real.sqrt Cgap) *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℝ) + 1) T₀‖) :=
    le_trans harm_le (mul_le_mul_of_nonneg_left hjets hCEκ_nn)
  rw [hHs0]
  calc ‖armT‖
      ≤ deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
          (‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ +
            (Real.sqrt 2 + Real.sqrt Cgap) *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℝ) + 1) T₀‖) := hchain
    _ = deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ +
        deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
            (Real.sqrt 2 + Real.sqrt Cgap) *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℝ) + 1) T₀‖ := by ring

private lemma smoothCcToTensorHs_connLap_shift_le (g₀ : SmoothRiemannianMetric I M)
    (k : ℕ) (u : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)‖ +
        Real.sqrt 2 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) u‖ := by
  classical
  have hsumA : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i ((k + 2 : ℕ) : ℝ) *
      ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u).coeff i) ^ 2) :=
    (smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u).weighted_summable
  have hsumB : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i ((k : ℕ) : ℝ) *
      ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)).coeff i) ^ 2) :=
    (smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)).weighted_summable
  have hsumC : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i ((k + 1 : ℕ) : ℝ) *
      ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) u).coeff i) ^ 2) :=
    (smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) u).weighted_summable
  have hsq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u‖ ^ 2 ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)‖ ^ 2 +
        2 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) u‖ ^ 2 := by
    rw [tensorHs.norm_sq_eq_tsum, tensorHs.norm_sq_eq_tsum, tensorHs.norm_sq_eq_tsum]
    have hterm : ∀ i, tensorSobolevWeight (I := I) (M := M) i ((k + 2 : ℕ) : ℝ) *
        ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u).coeff i) ^ 2 ≤
        tensorSobolevWeight (I := I) (M := M) i ((k : ℕ) : ℝ) *
            ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)).coeff i) ^ 2 +
          2 * (tensorSobolevWeight (I := I) (M := M) i ((k + 1 : ℕ) : ℝ) *
            ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) u).coeff i) ^ 2) := by
      intro i
      have hlam_nn : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
        tensor_lambda_nonneg (I := I) (M := M) i
      rw [smoothCcToTensorHs_rawConnLap_coeff (I := I) (M := M) g₀ ((k : ℕ) : ℝ) u i,
        weight_natCast (I := I) (M := M) g₀ i (k + 2),
        weight_natCast (I := I) (M := M) g₀ i k,
        weight_natCast (I := I) (M := M) g₀ i (k + 1)]
      set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
      set ci := (smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) u).coeff i with hci_def
      have hc2 : (smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u).coeff i = ci := rfl
      have hc0 : (smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ) u).coeff i = ci := rfl
      rw [hc2, hc0]
      have hbase_nn : (0 : ℝ) ≤ (1 + lam) ^ k := by positivity
      have e2 : (1 + lam) ^ (k + 2) = (1 + lam) ^ k * (1 + lam) ^ 2 := by rw [pow_add]
      have e1 : (1 + lam) ^ (k + 1) = (1 + lam) ^ k * (1 + lam) := by rw [pow_succ]
      rw [e2, e1]
      nlinarith [hbase_nn, sq_nonneg ci, hlam_nn,
        mul_nonneg hbase_nn (sq_nonneg ci),
        mul_nonneg (mul_nonneg hbase_nn (sq_nonneg ci)) hlam_nn]
    calc (∑' i, tensorSobolevWeight (I := I) (M := M) i ((k + 2 : ℕ) : ℝ) *
          ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u).coeff i) ^ 2)
        ≤ ∑' i, (tensorSobolevWeight (I := I) (M := M) i ((k : ℕ) : ℝ) *
              ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)).coeff i) ^ 2 +
            2 * (tensorSobolevWeight (I := I) (M := M) i ((k + 1 : ℕ) : ℝ) *
              ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) u).coeff i) ^ 2)) :=
          Summable.tsum_le_tsum hterm hsumA (hsumB.add (hsumC.mul_left 2))
      _ = (∑' i, tensorSobolevWeight (I := I) (M := M) i ((k : ℕ) : ℝ) *
              ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)).coeff i) ^ 2) +
            2 * ∑' i, tensorSobolevWeight (I := I) (M := M) i ((k + 1 : ℕ) : ℝ) *
              ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) u).coeff i) ^ 2 := by
          rw [Summable.tsum_add hsumB (hsumC.mul_left 2), tsum_mul_left]
  have hb_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)‖ := norm_nonneg _
  have hc_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) u‖ := norm_nonneg _
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt2_nn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  refine le_of_sq_le_sq ?_ (by positivity)
  nlinarith [hsq, hs2, mul_nonneg (mul_nonneg hsqrt2_nn hb_nn) hc_nn]

lemma smoothCcToTensorHs_rawConnLap_order_le (g₀ : SmoothRiemannianMetric I M)
    (k : ℕ) (u : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u‖ := by
  classical
  have hnn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u‖ := norm_nonneg _
  have hsq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)‖ ^ 2 ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u‖ ^ 2 := by
    rw [tensorHs.norm_sq_eq_tsum, tensorHs.norm_sq_eq_tsum]
    refine Summable.tsum_le_tsum (fun i => ?_)
      ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)).weighted_summable)
      ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u).weighted_summable)
    have hlam_nn : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
      tensor_lambda_nonneg (I := I) (M := M) i
    rw [smoothCcToTensorHs_rawConnLap_coeff (I := I) (M := M) g₀ ((k : ℕ) : ℝ) u i,
      weight_natCast (I := I) (M := M) g₀ i k, weight_natCast (I := I) (M := M) g₀ i (k + 2)]
    set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
    set ci := (smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u).coeff i with hci_def
    have hc : (smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ) u).coeff i = ci := rfl
    rw [hc]
    have hbase_nn : (0 : ℝ) ≤ (1 + lam) ^ k := by positivity
    have e2 : (1 + lam) ^ (k + 2) = (1 + lam) ^ k * (1 + lam) ^ 2 := by rw [pow_add]
    rw [e2]
    nlinarith [hbase_nn, sq_nonneg ci, hlam_nn, mul_nonneg hbase_nn (sq_nonneg ci)]
  exact le_of_sq_le_sq hsq hnn

lemma smoothCcToTensorHs_norm_mono (g₀ : SmoothRiemannianMetric I M)
    {σ τ : ℝ} (hστ : σ ≤ τ) (w : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ w‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ τ w‖ := by
  have hbσ : smoothCcToTensorHs (I := I) (M := M) g₀ σ w =
      ccSpectralEmbed (I := I) (M := M) g₀ σ w := tensorHs.ext (funext fun i => rfl)
  have hbτ : smoothCcToTensorHs (I := I) (M := M) g₀ τ w =
      ccSpectralEmbed (I := I) (M := M) g₀ τ w := tensorHs.ext (funext fun i => rfl)
  rw [hbσ, hbτ]
  exact ccSpectralEmbed_norm_mono (I := I) (M := M) g₀ hστ w

lemma iteratedCovGrad_le_connLap_add (g₀ : SmoothRiemannianMetric I M) (k : ℕ) :
    ∃ Cj : ℝ, 0 ≤ Cj ∧ ∀ (S : SmoothCcTensor g₀ 0 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 (k + 2) S‖ ≤
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ +
          Cj * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) S‖ := by
  classical
  obtain ⟨Cgap, hCgap_nn, hgap⟩ :=
    exists_iteratedCovGrad_l2NormSq_le_smoothCcToTensorHs_succ_add_lower (I := I) (M := M) g₀
      (k + 1)
  refine ⟨Real.sqrt 2 + Real.sqrt Cgap, by positivity, fun S => ?_⟩
  have hgapS := hgap S
  have hJeq : SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (k + 1 + 1) S) =
      SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (k + 2) S) := rfl
  rw [hJeq, SmoothCcTensor.norm_toL2] at hgapS
  have hcast_succ : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((k + 1 : ℕ) : ℝ) + 1) S‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) S‖ :=
    smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) S
  have hb_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) S‖ := norm_nonneg _
  have hc_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) S‖ := norm_nonneg _
  have hjet_two : ‖iteratedCovGrad (I := I) g₀ 0 2 (k + 2) S‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) S‖ +
        Real.sqrt Cgap * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) S‖ := by
    have hsqrt_nn : 0 ≤ Real.sqrt Cgap := Real.sqrt_nonneg _
    have hsC : Real.sqrt Cgap ^ 2 = Cgap := Real.sq_sqrt hCgap_nn
    rw [← hcast_succ]
    refine le_of_sq_le_sq ?_ (by positivity)
    nlinarith [hgapS, hsC, mul_nonneg (mul_nonneg hsqrt_nn
      (norm_nonneg (smoothCcToTensorHs (I := I) (M := M) g₀ (((k + 1 : ℕ) : ℝ) + 1) S)))
      hc_nn, hcast_succ, hb_nn, hc_nn]
  have hshift := smoothCcToTensorHs_connLap_shift_le (I := I) (M := M) g₀ k S
  calc ‖iteratedCovGrad (I := I) g₀ 0 2 (k + 2) S‖
      ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) S‖ +
          Real.sqrt Cgap * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) S‖ :=
        hjet_two
    _ ≤ (‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ +
          Real.sqrt 2 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) S‖) +
          Real.sqrt Cgap * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) S‖ := by
        linarith [hshift]
    _ = ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ +
          (Real.sqrt 2 + Real.sqrt Cgap) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) S‖ := by ring

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
lemma arm_l2_le (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (S : SmoothCcTensor g₀ 0 2) :
    ‖deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S‖ ≤
      deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
        ‖iteratedCovGrad (I := I) g₀ 0 2 2 S‖ := by
  classical
  have hκ_nn : 0 ≤ δ / (1 - δ) := div_nonneg hδ_nn (by linarith)
  have h615 : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          ((deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S).toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ 3 * (δ / (1 - δ)) ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
            ((iteratedCovGrad (I := I) g₀ 0 2 2 S).toSection x) := fun x =>
    riemannianFiberNormSq_deTurckPrincipalCometricArm_le (I := I) (M := M) g₀ g₁ h htie
      hδ_lt hδ_nn hδ S x
  have hFint : MeasureTheory.Integrable
      (fun x => (Module.finrank ℝ E : ℝ) ^ 3 * (δ / (1 - δ)) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
          ((iteratedCovGrad (I := I) g₀ 0 2 2 S).toSection x))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 4
      (iteratedCovGrad (I := I) g₀ 0 2 2 S)).const_mul _
  have hsq1 : ‖deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) ^ 3 * (δ / (1 - δ)) ^ 2 *
        ‖iteratedCovGrad (I := I) g₀ 0 2 2 S‖ ^ 2 := by
    have h1 := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
      (I := I) (M := M) g₀ 0 2 (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S) _ hFint h615
    rw [MeasureTheory.integral_const_mul] at h1
    have hbridge := tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
      (I := I) (M := M) g₀ 0 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S)
    rw [← hbridge, ← SmoothCcTensor.norm_def (I := I) (M := M)] at h1
    exact h1
  have hrhs_nn : 0 ≤ deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
      ‖iteratedCovGrad (I := I) g₀ 0 2 2 S‖ :=
    mul_nonneg (mul_nonneg (deTurckArmFibreConst_nonneg _) hκ_nn) (norm_nonneg _)
  refine le_of_sq_le_sq ?_ hrhs_nn
  have hexp : (deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
      ‖iteratedCovGrad (I := I) g₀ 0 2 2 S‖) ^ 2 =
      deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 * (δ / (1 - δ)) ^ 2 *
        ‖iteratedCovGrad (I := I) g₀ 0 2 2 S‖ ^ 2 := by ring
  rw [hexp, sq_deTurckArmFibreConst]
  exact hsq1

omit [BoundarylessManifold I M] in
lemma arm_covGrad_slotExtend_l2_le (g₀ g₁ : SmoothRiemannianMetric I M)
    {κ : ℝ} (hκ_nn : 0 ≤ κ)
    (hC : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
      ((deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁).toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ 3 * κ ^ 2)
    (S : SmoothCcTensor g₀ 0 2) :
    ‖operatorFieldApply (I := I) (M := M) g₀ 5 3
        (slotExtend (I := I) (M := M) g₀ 4 2
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 3 S)‖ ≤
      deTurckArmFibreConst (Module.finrank ℝ E) * κ *
        ‖iteratedCovGrad (I := I) g₀ 0 2 3 S‖ := by
  classical
  set C := deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁ with hC_def
  set W := iteratedCovGrad (I := I) g₀ 0 2 3 S with hW_def
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
          ((operatorFieldApply (I := I) (M := M) g₀ 5 3 (slotExtend (I := I) (M := M) g₀ 4 2 C)
            W).toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ 3 * κ ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 5 x (W.toSection x) := by
    intro x
    refine le_trans (riemannianFiberNormSq_comp_slotExtend_le (I := I) (M := M) g₀ 4 2 C W x) ?_
    exact mul_le_mul_of_nonneg_right (hC x)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 5 x _)
  have hFint : MeasureTheory.Integrable
      (fun x => (Module.finrank ℝ E : ℝ) ^ 3 * κ ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 5 x (W.toSection x))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 5 W).const_mul _
  have hsq : ‖operatorFieldApply (I := I) (M := M) g₀ 5 3 (slotExtend (I := I) (M := M) g₀ 4 2 C) W‖
    ^ 2 ≤
      (Module.finrank ℝ E : ℝ) ^ 3 * κ ^ 2 * ‖W‖ ^ 2 := by
    have h1 := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
      (I := I) (M := M) g₀ 0 3
      (operatorFieldApply (I := I) (M := M) g₀ 5 3 (slotExtend (I := I) (M := M) g₀ 4 2 C) W) _
        hFint hpt
    rw [MeasureTheory.integral_const_mul] at h1
    have hbridge := tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
      (I := I) (M := M) g₀ 0 5 W
    rw [← hbridge, ← SmoothCcTensor.norm_def (I := I) (M := M)] at h1
    exact h1
  have hrhs_nn : 0 ≤ deTurckArmFibreConst (Module.finrank ℝ E) * κ * ‖W‖ :=
    mul_nonneg (mul_nonneg (deTurckArmFibreConst_nonneg _) hκ_nn) (norm_nonneg _)
  refine le_of_sq_le_sq ?_ hrhs_nn
  have hexp : (deTurckArmFibreConst (Module.finrank ℝ E) * κ * ‖W‖) ^ 2 =
      deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 * κ ^ 2 * ‖W‖ ^ 2 := by ring
  rw [hexp, sq_deTurckArmFibreConst]
  exact hsq

lemma hs_norm_family_shift (g₀ : SmoothRiemannianMetric I M)
    (T₀ : SmoothCcTensor g₀ 0 2) :
    ∀ (p σ : ℕ),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((σ : ℕ) : ℝ)
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p T₀)‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((σ + 2 * p : ℕ) : ℝ) T₀‖ := by
  intro p
  induction p with
  | zero => intro σ; simp only [oneMinusConnLapSmoothIter_zero, Nat.mul_zero, Nat.add_zero]
  | succ p ih =>
    intro σ
    rw [oneMinusConnLapSmoothIter_succ]
    calc
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (σ : ℝ)
          (oneMinusConnLapSmooth (I := I) g₀ 0 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p T₀))‖ =
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((σ + 2 : ℕ) : ℝ)
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p T₀)‖ :=
        by
          exact (smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap
            (E := E) (H := H) (I := I) (M := M) g₀ σ
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p T₀)).symm
      _ = ‖smoothCcToTensorHs (I := I) (M := M) g₀
          (((σ + 2) + 2 * p : ℕ) : ℝ) T₀‖ := ih (σ + 2)
      _ = ‖smoothCcToTensorHs (I := I) (M := M) g₀
          ((σ + 2 * (p + 1) : ℕ) : ℝ) T₀‖ :=
        smoothCcToTensorHs_norm_order_congr
          (I := I) (M := M) g₀ (by push_cast; ring) T₀

lemma hs_extreme_interp {f : ℕ → ℝ} (hf_nn : ∀ k, 0 ≤ f k)
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

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma iteratedCovGrad_norm_comp (g₀ : SmoothRiemannianMetric I M) (r s l m : ℕ)
    (Ψ : SmoothCcTensor g₀ r s) :
    ‖iteratedCovGrad (I := I) g₀ r (s + l) m (iteratedCovGrad (I := I) g₀ r s l Ψ)‖ =
      ‖iteratedCovGrad (I := I) g₀ r s (l + m) Ψ‖ := by
  have hnn1 : 0 ≤ ‖iteratedCovGrad (I := I) g₀ r (s + l) m
      (iteratedCovGrad (I := I) g₀ r s l Ψ)‖ := norm_nonneg _
  have hnn2 : 0 ≤ ‖iteratedCovGrad (I := I) g₀ r s (l + m) Ψ‖ := norm_nonneg _
  have hsq : ‖iteratedCovGrad (I := I) g₀ r (s + l) m
        (iteratedCovGrad (I := I) g₀ r s l Ψ)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ r s (l + m) Ψ‖ ^ 2 := by
    simp only [SmoothCcTensor.norm_def]
    rw [tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ r
      ((s + l) + m),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ r
        (s + (l + m))]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ r s l m Ψ x
  nlinarith [hsq, hnn1, hnn2,
    sq_nonneg (‖iteratedCovGrad (I := I) g₀ r (s + l) m (iteratedCovGrad (I := I) g₀ r s l Ψ)‖ -
      ‖iteratedCovGrad (I := I) g₀ r s (l + m) Ψ‖)]

lemma hs_logConvex (g₀ : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g₀ 0 2) (k : ℕ) :
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

end Spectral
end Analysis
end DifferentialGeometry

end

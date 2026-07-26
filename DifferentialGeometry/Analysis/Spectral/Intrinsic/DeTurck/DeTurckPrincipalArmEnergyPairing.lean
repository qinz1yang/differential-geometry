import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalCometricExtraction
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricDifferenceSlotPairing
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.OperatorFieldPairingIBP
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorDirichletCurrentGreenIdentityRS
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.FaithfulH1Embedding
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ConnLapPairing
import DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.EigenBasis
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Geometry.Connection.TensorNabla.SlotInsertCovariantNaturality
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.DirichletSpectralBochnerGap
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedAppCcLeibniz
import DifferentialGeometry.Geometry.Connection.TensorNabla.EndoCovariantDerivativeSelfAdjoint
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.SlotInsertSelfAdjointPairing
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HomFieldActionL2JetBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.CovDivergenceRoughLaplacianCommutation
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.SlotSwapPairingCalculus
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.HomFieldCurvatureJetDecomposition

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
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
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

theorem tensorL2Inner_eq_tsum_l2Coeff_cross_arm
    (g₀ : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g₀ 0 2) :
    tensorL2Inner (I := I) (M := M) g₀ 0 2 A.toFun B.toFun =
      ∑' i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2,
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 A) i *
          tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 B) i := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcompact_def
  set b := tensorResolventHilbertEigenbasisSigma (I := I) (M := M) h_compact with hb_def
  have hinner_eq : tensorL2Inner (I := I) (M := M) g₀ 0 2 A.toFun B.toFun =
      (⟪SmoothCcTensor.toL2 A, SmoothCcTensor.toL2 B⟫_ℝ : ℝ) := by
    rw [DifferentialGeometry.Integral.L2.SmoothCcTensor.inner_toL2
      (I := I) (M := M) A B]
    exact (SmoothCcTensor.inner_def (I := I) (M := M) A B).symm
  rw [hinner_eq]
  have h_par := b.tsum_inner_mul_inner (SmoothCcTensor.toL2 A) (SmoothCcTensor.toL2 B)
  rw [← h_par]
  refine tsum_congr (fun i => ?_)
  rw [tensorL2Coeff_eq_inner (I := I) (M := M) h_compact (SmoothCcTensor.toL2 A) i,
    tensorL2Coeff_eq_inner (I := I) (M := M) h_compact (SmoothCcTensor.toL2 B) i]
  rw [show (⟪SmoothCcTensor.toL2 A, b i⟫_ℝ : ℝ) = ⟪b i, SmoothCcTensor.toL2 A⟫_ℝ from
    real_inner_comm _ _]

private theorem spectralPairing_tsum_eq_oneMinusConnLapIter_l2Inner
    (g₀ : SmoothRiemannianMetric I M) (n : ℕ)
    (u₀ : SmoothCcTensor g₀ 0 2) (A : SmoothCcTensor g₀ 0 2) :
    ∑' i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g₀ 0 2,
        tensorSobolevWeight (I := I) (M := M) i ((n : ℕ) : ℝ) *
          ((smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀).coeff i *
            (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) A).coeff i) =
      tensorL2Inner (I := I) (M := M) g₀ 0 2
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
        A.toFun := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcompact_def
  rw [tensorL2Inner_eq_tsum_l2Coeff_cross_arm (I := I) (M := M) g₀
    (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀) A]
  refine tsum_congr (fun i => ?_)
  rw [smoothCcToTensorHs_coeff, smoothCcToTensorHs_coeff]
  rw [tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter (I := I) (M := M) g₀ h_compact u₀ i n]
  have hweight : tensorSobolevWeight (I := I) (M := M) i ((n : ℕ) : ℝ) =
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ n := by
    unfold tensorSobolevWeight
    rw [Real.rpow_natCast]
  rw [hweight]
  ring

private noncomputable def negGInvDiffSlotApplied
    (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (W : TensorRSSpace 0 (s + 1) I x) : TensorRSSpace 0 (s + 1) I x :=
  TensorRSSpace.ofCLM
    ((slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
        (-gInvDiffRaisedEndo (I := I) g₀ g₁ x)).comp
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from W))

private theorem slotInsertEndoFib_neg_left (s : ℕ) (k : Fin s) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) :
    slotInsertEndoFib (I := I) (M := M) s k x (-Λ) =
      - slotInsertEndoFib (I := I) (M := M) s k x Λ := by
  rw [show (-Λ) = (-1 : ℝ) • Λ from by rw [neg_one_smul],
    slotInsertEndoFib_smul_left (I := I) (M := M) s k x (-1 : ℝ) Λ, neg_one_smul]

private theorem negGInvDiffSlotApplied_eq_neg
    (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (W : TensorRSSpace 0 (s + 1) I x) :
    negGInvDiffSlotApplied (I := I) g₀ g₁ s x W =
      - gInvDiffSlotApplied (I := I) g₀ g₁ s x W := by
  rw [negGInvDiffSlotApplied, gInvDiffSlotApplied,
    slotInsertEndoFib_neg_left (I := I) (M := M) (s + 1) 0 x
      (gInvDiffRaisedEndo (I := I) g₀ g₁ x),
    ContinuousLinearMap.neg_comp]
  rfl

private theorem toModel_negGInvDiffSlotApplied_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (W : TensorRSSpace 0 (s + 1) I x) :
    TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
        (negGInvDiffSlotApplied (I := I) g₀ g₁ s x W) =
      - TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
          (gInvDiffSlotApplied (I := I) g₀ g₁ s x W) := by
  rw [negGInvDiffSlotApplied_eq_neg (I := I) g₀ g₁ s x W, TensorRSSpace.toModel_neg]

private theorem negGInvDiffRaisedEndo_g0_self_adjoint
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (a b : TangentSpace I x) :
    g₀.inner x ((-gInvDiffRaisedEndo (I := I) g₀ g₁ x) a) b
      = g₀.inner x a ((-gInvDiffRaisedEndo (I := I) g₀ g₁ x) b) := by
  simp only [ContinuousLinearMap.neg_apply, map_neg]
  rw [gInvDiffRaisedEndo_g0_self_adjoint (I := I) g₀ g₁ x a b]

private theorem negGInvDiffRaisedEndo_inner_self_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : gFibreOpBound (I := I) g₀ h δ)
    (x : M) (v : TangentSpace I x) :
    g₀.inner x ((-gInvDiffRaisedEndo (I := I) g₀ g₁ x) v) v
      ≤ (δ / (1 - δ)) * g₀.inner x v v := by
  rw [ContinuousLinearMap.neg_apply, map_neg]
  have hbnd := abs_inner_gInvDiffRaisedEndo_le (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x v v
  have hv_nn : 0 ≤ g₀.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g₀ x v
  have hsq : Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v) = g₀.inner x v v := by
    rw [← Real.sqrt_mul hv_nn, Real.sqrt_mul_self hv_nn]
  have hle : -g₀.inner x (gInvDiffRaisedEndo (I := I) g₀ g₁ x v) v
      ≤ |g₀.inner x (gInvDiffRaisedEndo (I := I) g₀ g₁ x v) v| := neg_le_abs _
  calc -g₀.inner x (gInvDiffRaisedEndo (I := I) g₀ g₁ x v) v
      ≤ |g₀.inner x (gInvDiffRaisedEndo (I := I) g₀ g₁ x v) v| := hle
    _ ≤ (δ / (1 - δ)) * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v)) := hbnd
    _ = (δ / (1 - δ)) * g₀.inner x v v := by rw [hsq]

private theorem tensorInnerPointwise_negGInvDiffSlot_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : gFibreOpBound (I := I) g₀ h δ)
    (s : ℕ) (x : M) (W : TensorRSSpace 0 (s + 1) I x) :
    tensorInnerPointwise (I := I) (M := M) g₀ 0 (s + 1) x
        (TensorRSSpace.toModel W)
        (TensorRSSpace.toModel (negGInvDiffSlotApplied (I := I) g₀ g₁ s x W))
      ≤ (δ / (1 - δ)) * tensorInnerPointwise (I := I) (M := M) g₀ 0 (s + 1) x
          (TensorRSSpace.toModel W) (TensorRSSpace.toModel W) := by
  obtain ⟨e, bse, hbse, horth⟩ :=
    DifferentialGeometry.Analysis.Sobolev.TensorHilbert.exists_orthoFrame_basis_E
      (I := I) (M := M) g₀ x
  exact DifferentialGeometry.Analysis.Sobolev.TensorHilbert.tensorInnerPointwise_slotΛ_le
    (I := I) (M := M) g₀ s x (-gInvDiffRaisedEndo (I := I) g₀ g₁ x)
    (negGInvDiffRaisedEndo_g0_self_adjoint (I := I) g₀ g₁ x)
    (fun v => negGInvDiffRaisedEndo_inner_self_le (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x v)
    W e bse hbse horth

theorem rawConnLap_selfAdjoint (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T v : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r s (rawTensorConnLapSmooth (I := I) g r s T).toFun v.toFun =
      tensorL2Inner (I := I) (M := M) g r s T.toFun
        (rawTensorConnLapSmooth (I := I) g r s v).toFun := by
  have hTv := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs
    (I := I) (M := M) g r s T v
  have hvT := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs
    (I := I) (M := M) g r s v T
  have hsymm1 := tensorL2Inner_symm (I := I) (M := M) g r (s + 1)
    (covGrad (I := I) (M := M) g r s T).toFun (covGrad (I := I) (M := M) g r s v).toFun
  have hsymm2 := tensorL2Inner_symm (I := I) (M := M) g r s
    (rawTensorConnLapSmooth (I := I) g r s v).toFun T.toFun
  rw [hsymm1, hvT] at hTv; rw [← hsymm2]; linarith [hTv]

private theorem tensorL2Inner_sub_left_smoothCc (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ T : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r s (S₁.toFun - S₂.toFun) T.toFun =
      tensorL2Inner (I := I) (M := M) g r s S₁.toFun T.toFun -
        tensorL2Inner (I := I) (M := M) g r s S₂.toFun T.toFun := by
  have hsub : (S₁.toFun - S₂.toFun) = S₁.toFun + (-1 : ℝ) • S₂.toFun := by
    funext x
    rw [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
    module
  have hint2 : MeasureTheory.Integrable (fun x =>
      tensorInnerPointwise (I := I) (M := M) g r s x (((-1 : ℝ) • S₂.toFun) x) (T.toFun x))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hbase := DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) S₂ T
    have heq : (fun x => tensorInnerPointwise (I := I) (M := M) g r s x
          (((-1 : ℝ) • S₂.toFun) x) (T.toFun x))
        = (fun x => (-1 : ℝ) * tensorInnerPointwise (I := I) (M := M) g r s x
          (S₂.toFun x) (T.toFun x)) := by
      funext x
      show tensorInnerPointwise (I := I) (M := M) g r s x ((-1 : ℝ) • S₂.toFun x) (T.toFun x) = _
      rw [tensorInnerPointwise_smul_left]
    rw [heq]
    exact hbase.const_mul (-1 : ℝ)
  rw [hsub, tensorL2Inner_add_left (I := I) (M := M) g r s S₁.toFun ((-1 : ℝ) • S₂.toFun) T.toFun
    (DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) S₁ T) hint2,
    tensorL2Inner_smul_left]
  ring

private theorem tensorL2Inner_sub_right_smoothCc (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T₁ T₂ : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r s S.toFun (T₁.toFun - T₂.toFun) =
      tensorL2Inner (I := I) (M := M) g r s S.toFun T₁.toFun -
        tensorL2Inner (I := I) (M := M) g r s S.toFun T₂.toFun := by
  have hsub : (T₁.toFun - T₂.toFun) = T₁.toFun + (-1 : ℝ) • T₂.toFun := by
    funext x
    rw [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
    module
  have hint2 : MeasureTheory.Integrable (fun x =>
      tensorInnerPointwise (I := I) (M := M) g r s x (S.toFun x) (((-1 : ℝ) • T₂.toFun) x))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hbase := DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) S T₂
    have heq : (fun x => tensorInnerPointwise (I := I) (M := M) g r s x
          (S.toFun x) (((-1 : ℝ) • T₂.toFun) x))
        = (fun x => (-1 : ℝ) * tensorInnerPointwise (I := I) (M := M) g r s x
          (S.toFun x) (T₂.toFun x)) := by
      funext x
      show tensorInnerPointwise (I := I) (M := M) g r s x (S.toFun x) ((-1 : ℝ) • T₂.toFun x) = _
      rw [tensorInnerPointwise_smul_right]
    rw [heq]
    exact hbase.const_mul (-1 : ℝ)
  rw [hsub, tensorL2Inner_add_right (I := I) (M := M) g r s S.toFun T₁.toFun ((-1 : ℝ) • T₂.toFun)
    (DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) S T₁) hint2,
    tensorL2Inner_smul_right]
  ring

private noncomputable def armPrincipalSlotPairing
    (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ) (u₀ : SmoothCcTensor g₀ 0 2) : ℝ :=
  tensorL2Inner (I := I) (M := M) g₀ 0 ((2 + n) + 1)
    (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
      ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀).toSection x))
    (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
      (negGInvDiffSlotApplied
        (I := I) g₀ g₁ (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀).toSection x)))

private theorem armPrincipalSlotPairing_eq_neg_inner
    (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ) (u₀ : SmoothCcTensor g₀ 0 2) :
    armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ =
      - (⟪iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀,
          appCc (I := I) (M := M) g₀ ((2 + n) + 1) ((2 + n) + 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ (2 + n)
              (gInvDiffRaisedEndoField (I := I) (M := M) g₀ g₁))
            (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀)⟫_ℝ : ℝ) := by
  classical
  set A : SmoothCcTensor g₀ 0 ((2 + n) + 1) :=
    iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀ with hA_def
  set B : SmoothCcTensor g₀ 0 ((2 + n) + 1) :=
    appCc (I := I) (M := M) g₀ ((2 + n) + 1) ((2 + n) + 1)
      (slotInsertEndoCc (I := I) (M := M) g₀ (2 + n)
        (gInvDiffRaisedEndoField (I := I) (M := M) g₀ g₁)) A with hB_def
  have hBfun : ∀ x : M,
      B.toFun x =
        TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
          (gInvDiffSlotApplied (I := I) g₀ g₁ (2 + n) x (A.toSection x)) := fun x => rfl
  rw [SmoothCcTensor.inner_def (I := I) (M := M) A B]
  rw [armPrincipalSlotPairing]
  have heq :
      (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
          (negGInvDiffSlotApplied (I := I) g₀ g₁ (2 + n) x (A.toSection x)))
        = (fun x => - B.toFun x) := by
    funext x
    rw [hBfun x,
      toModel_negGInvDiffSlotApplied_eq (I := I) g₀ g₁ (2 + n) x (A.toSection x)]
  rw [show (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x)) = A.toFun from rfl,
    heq]
  have hsmul : (fun x => - B.toFun x) = (-1 : ℝ) • B.toFun := by
    funext x; rw [Pi.smul_apply, neg_one_smul]
  rw [hsmul,
    tensorL2Inner_smul_right (I := I) (M := M) g₀ 0 ((2 + n) + 1) (-1 : ℝ) A.toFun B.toFun]
  ring

set_option linter.unusedSectionVars false in
private lemma armResidual_vecTail_cons {α : Type*} {n : ℕ} (a : α) (w : Fin n → α) :
    Matrix.vecTail (Fin.cons a w) = w := by
  funext j
  simp [Matrix.vecTail, Fin.cons_succ]

set_option linter.unusedSectionVars false in
private lemma armResidual_toModel_sum {s : ℕ} (b : M) {ι : Type*} (fs : Finset ι)
    (f : ι → Tensor0SSpace s I b) :
    Tensor0SSpace.toModel (∑ i ∈ fs, f i) = ∑ i ∈ fs, Tensor0SSpace.toModel (f i) :=
  map_sum (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) s b) f fs

set_option linter.unusedSectionVars false in
private lemma armResidual_model_slot0_linear {s : ℕ} {ι : Type*} (fs : Finset ι)
    (T : Tensor0SBundle.Tensor0SModel (s + 1) ℝ E) (c : ι → ℝ) (f : ι → E)
    (rest : Fin s → E) :
    T (Fin.cons (∑ j ∈ fs, c j • f j) rest) = ∑ j ∈ fs, c j * T (Fin.cons (f j) rest) := by
  have h : ∀ u : E, T (Fin.cons u rest) =
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 1) => E) ℝ) T u) rest := by
    intro u
    rw [continuousMultilinearCurryLeftEquiv_apply]
  rw [h, map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul, ← h]

set_option linter.unusedSectionVars false in
private lemma armResidual_model_slot1_linear {s : ℕ} {ι : Type*} (fs : Finset ι)
    (T : Tensor0SBundle.Tensor0SModel (s + 1 + 1) ℝ E) (a : E) (c : ι → ℝ) (f : ι → E)
    (rest : Fin s → E) :
    T (Fin.cons a (Fin.cons (∑ j ∈ fs, c j • f j) rest)) =
      ∑ j ∈ fs, c j * T (Fin.cons a (Fin.cons (f j) rest)) := by
  have hcur : ∀ w : Fin (s + 1) → E,
      T (Fin.cons a w) =
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 1 + 1) => E) ℝ) T a) w := by
    intro w
    rw [continuousMultilinearCurryLeftEquiv_apply]
  rw [hcur,
    armResidual_model_slot0_linear (E := E) fs
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 1 + 1) => E) ℝ) T a)
      c f rest]
  exact Finset.sum_congr rfl fun j _ => by rw [hcur]

set_option linter.unusedSectionVars false in
private lemma armResidual_orthoFrame_expansion (g₀ : SmoothRiemannianMetric I M) (b : M)
    (u : TangentSpace I b) :
    u = ∑ i : Fin (Module.finrank ℝ E),
      g₀.inner b u (smoothOrthoFrame (I := I) g₀ b i b) •
        smoothOrthoFrame (I := I) g₀ b i b := by
  classical
  have horth : ∀ a c : Fin (Module.finrank ℝ E),
      g₀.inner b (smoothOrthoFrame (I := I) g₀ b a b)
        (smoothOrthoFrame (I := I) g₀ b c b) = if a = c then 1 else 0 :=
    fun a c => smoothOrthoFrame_orthonormal_at_center (I := I) g₀ b a c
  have he_li : LinearIndependent ℝ (fun i => smoothOrthoFrame (I := I) g₀ b i b) := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g₀.inner b (smoothOrthoFrame (I := I) g₀ b k b)
        (∑ j ∈ fs, c j • smoothOrthoFrame (I := I) g₀ b j b) = 0 := by
      rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g₀.inner b (smoothOrthoFrame (I := I) g₀ b k b)
        (c j • smoothOrthoFrame (I := I) g₀ b j b) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [(g₀.inner b (smoothOrthoFrame (I := I) g₀ b k b)).map_smul (c j),
        smul_eq_mul, horth k j]
    rw [Finset.sum_congr rfl h_pull, Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rwa [if_pos rfl, mul_one] at h_zero
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ E :=
    Fintype.card_fin _
  set bse := basisOfLinearIndependentOfCardEqFinrank he_li hcard with hbse_def
  have hbse : ∀ i, bse i = smoothOrthoFrame (I := I) g₀ b i b :=
    fun i => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he_li hcard) i
  have hcoeff : ∀ j : Fin (Module.finrank ℝ E),
      g₀.inner b u (smoothOrthoFrame (I := I) g₀ b j b) = bse.repr u j := by
    intro j
    rw [g₀.symm b u (smoothOrthoFrame (I := I) g₀ b j b)]
    conv_lhs => rw [← bse.sum_repr u]
    rw [map_sum]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => by
      rw [(g₀.inner b (smoothOrthoFrame (I := I) g₀ b j b)).map_smul (bse.repr u i),
        smul_eq_mul, hbse i, horth j i])]
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    · rw [if_pos rfl, mul_one]
    · intro i _ hij
      rw [if_neg (fun h => hij h.symm), mul_zero]
  calc u = ∑ i : Fin (Module.finrank ℝ E), bse.repr u i • bse i := (bse.sum_repr u).symm
    _ = ∑ i : Fin (Module.finrank ℝ E),
        g₀.inner b u (smoothOrthoFrame (I := I) g₀ b i b) •
          smoothOrthoFrame (I := I) g₀ b i b := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcoeff i, hbse i]

set_option linter.unusedSectionVars false in
private lemma armResidual_toModel_contract_covariant (s : ℕ) (b : M) (v : TangentSpace I b)
    (A : TensorRSSpace 0 (s + 1) I b) (D : Tensor0SSpace 0 I b) (m : Fin s → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace s I b from
          Tensor0SBundle.contract_covariant 0 s b v A) D) m =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (s + 1) I b from A) D)
        (Fin.cons ((v : TangentSpace I b) : E) m) :=
  rfl

set_option linter.unusedSectionVars false in
private lemma armResidual_covDivergence_toSection (g₀ : SmoothRiemannianMetric I M)
    (s : ℕ) (V : SmoothCcTensor g₀ 0 (s + 1)) (b : M) :
    ((covDivergence (I := I) (M := M) g₀ s V).toSection b : TensorRSSpace 0 s I b) =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SBundle.contract_covariant 0 s b (smoothOrthoFrame (I := I) g₀ b i b)
          (tensorCovDerivAt (I := I) (M := M) g₀ 0 (s + 1) V b
            (smoothOrthoFrame (I := I) g₀ b i b)) := by
  classical
  rw [covDivergence_toSection_apply (I := I) (M := M) g₀ s V b]
  rw [covDivergenceRaw]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hSmooth_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : M => TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z
        (smoothOrthoFrame (I := I) g₀ b i z)) b :=
    (smoothOrthoFrame_smooth (I := I) g₀ b i).contMDiffAt.mdifferentiableAt (by simp)
  rw [codiffPsi_apply (I := I) (M := M) g₀ s V b hSmooth_at hSmooth_at]
  rw [tensorCovDerivAt_def (I := I) (M := M) g₀ 0 (s + 1) V b
    (smoothOrthoFrame (I := I) g₀ b i b)]

set_option linter.unusedSectionVars false in
private lemma armResidual_toModel_doubleTraceFib (g₀ : SmoothRiemannianMetric I M) (b : M)
    (W : Tensor0SSpace (2 + 2) I b) (m : Fin 2 → E) :
    Tensor0SSpace.toModel (DeTurck.cometricDoubleTraceFib (I := I) g₀ 2 b W) m =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel W
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m)) := by
  classical
  rw [DeTurck.cometricDoubleTraceFib_eq_orthoFrame_diag (I := I) g₀ 2 b
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) b) W]
  rw [armResidual_toModel_sum (I := I) (M := M) b Finset.univ
    (fun i => Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 b
      (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (2 + 1) b W
        (smoothOrthoFrame (I := I) g₀ b i b))
      (smoothOrthoFrame (I := I) g₀ b i b))]
  rw [ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (2 + 1) b W
      (smoothOrthoFrame (I := I) g₀ b i b))
    (v0 := ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E)) (vs := m)]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (T := W)
    (v0 := ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E))
    (vs := Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m)]

set_option linter.unusedSectionVars false in
private lemma armResidual_slot01_transpose (g₀ g₁ : SmoothRiemannianMetric I M) (b : M)
    (T : Tensor0SBundle.Tensor0SModel (2 + 1 + 1) ℝ E) (m : Fin 2 → E) :
    (∑ i : Fin (Module.finrank ℝ E),
        T (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E)
            (Fin.cons ((gInvDiffRaisedEndo (I := I) g₀ g₁ b
                (smoothOrthoFrame (I := I) g₀ b i b) : TangentSpace I b) : E) m))) =
      ∑ i : Fin (Module.finrank ℝ E),
        T (Fin.cons ((gInvDiffRaisedEndo (I := I) g₀ g₁ b
              (smoothOrthoFrame (I := I) g₀ b i b) : TangentSpace I b) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m)) := by
  classical
  set e : Fin (Module.finrank ℝ E) → TangentSpace I b :=
    fun i => smoothOrthoFrame (I := I) g₀ b i b with he
  set Λ : TangentSpace I b →L[ℝ] TangentSpace I b :=
    gInvDiffRaisedEndo (I := I) g₀ g₁ b with hΛ
  have hadj : ∀ a c : TangentSpace I b, g₀.inner b (Λ a) c = g₀.inner b a (Λ c) :=
    fun a c => gInvDiffRaisedEndo_g0_self_adjoint (I := I) g₀ g₁ b a c
  have hexp : ∀ v : TangentSpace I b,
      v = ∑ j : Fin (Module.finrank ℝ E), g₀.inner b v (e j) • e j :=
    fun v => armResidual_orthoFrame_expansion (I := I) (M := M) g₀ b v
  have hL : ∀ i : Fin (Module.finrank ℝ E),
      T (Fin.cons ((e i : TangentSpace I b) : E)
          (Fin.cons ((Λ (e i) : TangentSpace I b) : E) m)) =
        ∑ j : Fin (Module.finrank ℝ E), g₀.inner b (Λ (e i)) (e j) *
          T (Fin.cons ((e i : TangentSpace I b) : E)
              (Fin.cons ((e j : TangentSpace I b) : E) m)) := by
    intro i
    conv_lhs => rw [hexp (Λ (e i))]
    exact armResidual_model_slot1_linear (E := E) Finset.univ T ((e i : TangentSpace I b) : E)
      (fun j => g₀.inner b (Λ (e i)) (e j)) (fun j => ((e j : TangentSpace I b) : E)) m
  have hR : ∀ i : Fin (Module.finrank ℝ E),
      T (Fin.cons ((Λ (e i) : TangentSpace I b) : E)
          (Fin.cons ((e i : TangentSpace I b) : E) m)) =
        ∑ j : Fin (Module.finrank ℝ E), g₀.inner b (Λ (e i)) (e j) *
          T (Fin.cons ((e j : TangentSpace I b) : E)
              (Fin.cons ((e i : TangentSpace I b) : E) m)) := by
    intro i
    conv_lhs => rw [hexp (Λ (e i))]
    exact armResidual_model_slot0_linear (E := E) Finset.univ T
      (fun j => g₀.inner b (Λ (e i)) (e j)) (fun j => ((e j : TangentSpace I b) : E))
      (Fin.cons ((e i : TangentSpace I b) : E) m)
  rw [Finset.sum_congr rfl (fun i _ => hL i), Finset.sum_congr rfl (fun i _ => hR i)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hco : g₀.inner b (Λ (e j)) (e i) = g₀.inner b (Λ (e i)) (e j) := by
    rw [hadj (e j) (e i), g₀.symm b (e j) (Λ (e i))]
  rw [hco]

set_option linter.unusedSectionVars false in
private lemma armResidual_covGrad_eval (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g₀ 0 s) (b : M) (D : Tensor0SSpace 0 I b)
    (v0 : E) (vs : Fin s → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (s + 1) I b from
          (covGrad (I := I) (M := M) g₀ 0 s W).toSection b) D) (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace s I b from
          tensorCovDerivAt (I := I) (M := M) g₀ 0 s W b v0) D) vs := by
  have h := covGrad_toSection_apply_eval (I := I) (M := M) g₀ 0 s W b D (Fin.cons v0 vs)
  have ht : Matrix.vecTail (Fin.cons v0 vs : Fin (s + 1) → TangentSpace I b) = vs := by
    funext j
    rfl
  exact h.trans (congrArg (fun w : Fin s → E =>
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace s I b from
        tensorCovDerivAt (I := I) (M := M) g₀ 0 s W b v0) D) w) ht)

set_option linter.unusedSectionVars false in
private lemma armResidual_contract_term_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (u₀ : SmoothCcTensor g₀ 0 2) (b : M) (D : Tensor0SSpace 0 I b) (m : Fin 2 → E)
    (i : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from
          Tensor0SBundle.contract_covariant 0 2 b (smoothOrthoFrame (I := I) g₀ b i b)
            (tensorCovDerivAt (I := I) (M := M) g₀ 0 (2 + 1)
              (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ 2
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁))
                (covGrad (I := I) (M := M) g₀ 0 2 u₀)) b
              (smoothOrthoFrame (I := I) g₀ b i b))) D) m =
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
            (covGrad (I := I) (M := M) g₀ 0 2 u₀).toSection b) D)
          (Fin.cons
            ((((endoCovariantDerivative (I := I) (M := M) g₀)
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁) b
                  (smoothOrthoFrame (I := I) g₀ b i b))
                (smoothOrthoFrame (I := I) g₀ b i b) : TangentSpace I b) : E) m) +
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace ((2 + 1) + 1) I b from
            (covGrad (I := I) (M := M) g₀ 0 (2 + 1)
              (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toSection b) D)
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E)
            (Fin.cons ((gInvDiffRaisedEndo (I := I) g₀ g₁ b
                (smoothOrthoFrame (I := I) g₀ b i b) : TangentSpace I b) : E) m)) := by
  classical
  set ei : TangentSpace I b := smoothOrthoFrame (I := I) g₀ b i b with hei
  set Du : SmoothCcTensor g₀ 0 (2 + 1) := covGrad (I := I) (M := M) g₀ 0 2 u₀ with hDu
  set Λf := gInvDiffRaisedEndoField (I := I) g₀ g₁ with hΛf
  rw [armResidual_toModel_contract_covariant (I := I) (M := M) 2 b ei _ D m]
  have hderiv := tensorCovDerivAt_appCc_eq (I := I) (M := M) g₀ (2 + 1) (2 + 1)
    (slotInsertEndoCc (I := I) (M := M) g₀ 2 Λf) Du b ((ei : TangentSpace I b) : E)
  rw [hderiv]
  rw [show ((((show Tensor0SSpace (2 + 1) I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
          tensorCovDerivAt (I := I) (M := M) g₀ (2 + 1) (2 + 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ 2 Λf) b ((ei : TangentSpace I b) : E)).comp
          (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from Du.toSection b) +
        (show Tensor0SSpace (2 + 1) I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
          (slotInsertEndoCc (I := I) (M := M) g₀ 2 Λf).toSection b).comp
          (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
            tensorCovDerivAt (I := I) (M := M) g₀ 0 (2 + 1) Du b
              ((ei : TangentSpace I b) : E))) : TensorRSSpace 0 (2 + 1) I b)) D =
      (show Tensor0SSpace (2 + 1) I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
          tensorCovDerivAt (I := I) (M := M) g₀ (2 + 1) (2 + 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ 2 Λf) b ((ei : TangentSpace I b) : E))
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from Du.toSection b) D) +
      (show Tensor0SSpace (2 + 1) I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
          (slotInsertEndoCc (I := I) (M := M) g₀ 2 Λf).toSection b)
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
          tensorCovDerivAt (I := I) (M := M) g₀ 0 (2 + 1) Du b
            ((ei : TangentSpace I b) : E)) D) from rfl]
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  congr 1
  · rw [tensorCovDerivAt_slotInsertEndoCc_eq (I := I) (M := M) g₀ 2 Λf b
      ((ei : TangentSpace I b) : E)]
    rw [slotInsertEndoFib_apply_eval (I := I) (M := M) (2 + 1) 0 b
      ((endoCovariantDerivative (I := I) (M := M) g₀) Λf b ((ei : TangentSpace I b) : E))
      ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from Du.toSection b) D)
      (Fin.cons ((ei : TangentSpace I b) : E) m)]
    rw [Fin.cons_zero, Fin.update_cons_zero]
  · rw [slotInsertEndoCc_toSection (I := I) (M := M) g₀ 2 Λf b]
    rw [slotInsertEndoFib_apply_eval (I := I) (M := M) (2 + 1) 0 b (Λf b)
      ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
        tensorCovDerivAt (I := I) (M := M) g₀ 0 (2 + 1) Du b
          ((ei : TangentSpace I b) : E)) D)
      (Fin.cons ((ei : TangentSpace I b) : E) m)]
    rw [Fin.cons_zero, Fin.update_cons_zero]
    exact (armResidual_covGrad_eval (I := I) (M := M) g₀ (2 + 1) Du b D
      ((ei : TangentSpace I b) : E)
      (Fin.cons ((Λf b (ei : TangentSpace I b) : TangentSpace I b) : E) m)).symm

set_option linter.unusedSectionVars false in
private lemma armResidual_arm_toModel_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (u₀ : SmoothCcTensor g₀ 0 2) (b : M) (D : Tensor0SSpace 0 I b) (m : Fin 2 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from
          (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toSection b) D) m =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace ((2 + 1) + 1) I b from
            (covGrad (I := I) (M := M) g₀ 0 (2 + 1)
              (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toSection b) D)
          (Fin.cons ((gInvDiffRaisedEndo (I := I) g₀ g₁ b
              (smoothOrthoFrame (I := I) g₀ b i b) : TangentSpace I b) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m)) := by
  classical
  rw [deTurckPrincipalCometricArm,
    deTurckPrincipalCometricCoeff_eq_appCcRS_doubleTrace_slotInsertEndo (I := I) (M := M) g₀ g₁]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from
        (appCc (I := I) (M := M) g₀ 4 2
          (DifferentialGeometry.Integral.Connection.appCcRS (I := I) (M := M) g₀ 4 4 2
            (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
            (DifferentialGeometry.Integral.Connection.slotInsertEndoCc (I := I) (M := M) g₀ 3
              (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
          (iteratedCovGrad (I := I) g₀ 0 2 2 u₀)).toSection b) D) m =
    Tensor0SSpace.toModel
      (DeTurck.cometricDoubleTraceFib (I := I) g₀ 2 b
        (slotInsertEndoFib (I := I) (M := M) (3 + 1) 0 b
          (gInvDiffRaisedEndoField (I := I) g₀ g₁ b)
          ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 4 I b from
            (iteratedCovGrad (I := I) g₀ 0 2 2 u₀).toSection b) D))) m from rfl]
  rw [armResidual_toModel_doubleTraceFib (I := I) (M := M) g₀ b
    (slotInsertEndoFib (I := I) (M := M) (3 + 1) 0 b
      (gInvDiffRaisedEndoField (I := I) g₀ g₁ b)
      ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 4 I b from
        (iteratedCovGrad (I := I) g₀ 0 2 2 u₀).toSection b) D)) m]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [slotInsertEndoFib_apply_eval (I := I) (M := M) (3 + 1) 0 b
    (gInvDiffRaisedEndoField (I := I) g₀ g₁ b)
    ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 4 I b from
      (iteratedCovGrad (I := I) g₀ 0 2 2 u₀).toSection b) D)
    (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E)
      (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m))]
  rw [Fin.cons_zero, Fin.update_cons_zero]
  rfl

set_option linter.unusedSectionVars false in
private lemma armResidual_gTerm_toModel_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (u₀ : SmoothCcTensor g₀ 0 2) (b : M) (D : Tensor0SSpace 0 I b) (m : Fin 2 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from
          (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0)
            (appCcRS (I := I) (M := M) g₀ (2 + 1) ((2 + 1) + 1) (2 + 0)
              (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
              (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ 2
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁))))
            (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toSection b) D) m =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
            (covGrad (I := I) (M := M) g₀ 0 2 u₀).toSection b) D)
          (Fin.cons
            ((((endoCovariantDerivative (I := I) (M := M) g₀)
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁) b
                  (smoothOrthoFrame (I := I) g₀ b i b))
                (smoothOrthoFrame (I := I) g₀ b i b) : TangentSpace I b) : E) m) := by
  classical
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from
        (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0)
          (appCcRS (I := I) (M := M) g₀ (2 + 1) ((2 + 1) + 1) (2 + 0)
            (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
            (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 2
                (gInvDiffRaisedEndoField (I := I) g₀ g₁))))
          (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toSection b) D) m =
    Tensor0SSpace.toModel
      (DeTurck.cometricDoubleTraceFib (I := I) g₀ 2 b
        ((show Tensor0SSpace (2 + 1) I b →L[ℝ] Tensor0SSpace ((2 + 1) + 1) I b from
          (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ 2
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection b)
          ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
            (covGrad (I := I) (M := M) g₀ 0 2 u₀).toSection b) D))) m from rfl]
  rw [armResidual_toModel_doubleTraceFib (I := I) (M := M) g₀ b
    ((show Tensor0SSpace (2 + 1) I b →L[ℝ] Tensor0SSpace ((2 + 1) + 1) I b from
      (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ 2
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection b)
      ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
        (covGrad (I := I) (M := M) g₀ 0 2 u₀).toSection b) D)) m]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hstep : Tensor0SSpace.toModel
      ((show Tensor0SSpace (2 + 1) I b →L[ℝ] Tensor0SSpace ((2 + 1) + 1) I b from
        (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 2
            (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection b)
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
          (covGrad (I := I) (M := M) g₀ 0 2 u₀).toSection b) D))
      (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E)
        (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m)) =
      Tensor0SSpace.toModel
        (slotInsertEndoFib (I := I) (M := M) (2 + 1) 0 b
          ((endoCovariantDerivative (I := I) (M := M) g₀)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁) b
            (smoothOrthoFrame (I := I) g₀ b i b))
          ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
            (covGrad (I := I) (M := M) g₀ 0 2 u₀).toSection b) D))
        (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m) := by
    have h := covGrad_slotInsertEndoCc_toSection_eq (I := I) (M := M) g₀ 2
      (gInvDiffRaisedEndoField (I := I) g₀ g₁) b
      ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
        (covGrad (I := I) (M := M) g₀ 0 2 u₀).toSection b) D)
      (Fin.cons (smoothOrthoFrame (I := I) g₀ b i b)
        (Fin.cons (smoothOrthoFrame (I := I) g₀ b i b) m))
    have ht : Matrix.vecTail (Fin.cons (smoothOrthoFrame (I := I) g₀ b i b)
        (Fin.cons (smoothOrthoFrame (I := I) g₀ b i b) m) :
          Fin (2 + 1 + 1) → TangentSpace I b) =
        (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m :
          Fin (2 + 1) → E) := by
      funext j
      refine Fin.cases ?_ (fun j' => ?_) j
      · rfl
      · rfl
    exact h.trans (congrArg (fun w : Fin (2 + 1) → E =>
      Tensor0SSpace.toModel
        (slotInsertEndoFib (I := I) (M := M) (2 + 1) 0 b
          ((endoCovariantDerivative (I := I) (M := M) g₀)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁) b
            (smoothOrthoFrame (I := I) g₀ b i b))
          ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
            (covGrad (I := I) (M := M) g₀ 0 2 u₀).toSection b) D)) w) ht)
  rw [hstep]
  have happ : Tensor0SSpace.toModel
      (slotInsertEndoFib (I := I) (M := M) (2 + 1) 0 b
        ((endoCovariantDerivative (I := I) (M := M) g₀)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁) b
          (smoothOrthoFrame (I := I) g₀ b i b))
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
          (covGrad (I := I) (M := M) g₀ 0 2 u₀).toSection b) D))
      (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
          (covGrad (I := I) (M := M) g₀ 0 2 u₀).toSection b) D)
        (Function.update
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m) 0
          (((endoCovariantDerivative (I := I) (M := M) g₀)
              (gInvDiffRaisedEndoField (I := I) g₀ g₁) b
              (smoothOrthoFrame (I := I) g₀ b i b))
            ((Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m :
              Fin (2 + 1) → E) 0))) :=
    slotInsertEndoFib_apply_eval (I := I) (M := M) (2 + 1) 0 b _ _ _
  rw [happ]
  rw [show ((Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m :
      Fin (2 + 1) → E) 0) = ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E)
    from rfl]
  rw [Fin.update_cons_zero]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
private theorem armResidual_covDivergence_split (g₀ g₁ : SmoothRiemannianMetric I M)
    (u₀ : SmoothCcTensor g₀ 0 2) :
    covDivergence (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 2 (gInvDiffRaisedEndoField (I := I) g₀ g₁))
          (covGrad (I := I) (M := M) g₀ 0 2 u₀)) =
      deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀ +
        appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0)
          (appCcRS (I := I) (M := M) g₀ (2 + 1) ((2 + 1) + 1) (2 + 0)
            (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
            (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 2
                (gInvDiffRaisedEndoField (I := I) g₀ g₁))))
          (covGrad (I := I) (M := M) g₀ 0 2 u₀) := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro b
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext fun m => ?_
  beta_reduce
  set P : SmoothCcTensor g₀ 0 (2 + 1) :=
    appCc (I := I) (M := M) g₀ (2 + 1) (2 + 1)
      (slotInsertEndoCc (I := I) (M := M) g₀ 2 (gInvDiffRaisedEndoField (I := I) g₀ g₁))
      (covGrad (I := I) (M := M) g₀ 0 2 u₀) with hP
  set Garm : SmoothCcTensor g₀ 0 (2 + 0) :=
    appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0)
      (appCcRS (I := I) (M := M) g₀ (2 + 1) ((2 + 1) + 1) (2 + 0)
        (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
        (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 2
            (gInvDiffRaisedEndoField (I := I) g₀ g₁))))
      (covGrad (I := I) (M := M) g₀ 0 2 u₀) with hGarm
  rw [show ((deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀ + Garm).toSection b :
      TensorRSSpace 0 2 I b) =
    ((deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toSection b :
      TensorRSSpace 0 2 I b) + (Garm.toSection b : TensorRSSpace 0 2 I b) from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [show ((((deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toSection b :
        TensorRSSpace 0 2 I b) + (Garm.toSection b : TensorRSSpace 0 2 I b) :
        TensorRSSpace 0 2 I b)) D =
    (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from
      (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toSection b) D +
    (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from Garm.toSection b) D from rfl]
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  rw [armResidual_covDivergence_toSection (I := I) (M := M) g₀ 2 P b]
  rw [show ((∑ i : Fin (Module.finrank ℝ E),
      Tensor0SBundle.contract_covariant 0 2 b (smoothOrthoFrame (I := I) g₀ b i b)
        (tensorCovDerivAt (I := I) (M := M) g₀ 0 (2 + 1) P b
          (smoothOrthoFrame (I := I) g₀ b i b)) : TensorRSSpace 0 2 I b)) D =
    ∑ i : Fin (Module.finrank ℝ E),
      (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from
        Tensor0SBundle.contract_covariant 0 2 b (smoothOrthoFrame (I := I) g₀ b i b)
          (tensorCovDerivAt (I := I) (M := M) g₀ 0 (2 + 1) P b
            (smoothOrthoFrame (I := I) g₀ b i b))) D from by
    exact ContinuousLinearMap.sum_apply _ _ _]
  rw [armResidual_toModel_sum (I := I) (M := M) b Finset.univ
    (fun i => (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from
      Tensor0SBundle.contract_covariant 0 2 b (smoothOrthoFrame (I := I) g₀ b i b)
        (tensorCovDerivAt (I := I) (M := M) g₀ 0 (2 + 1) P b
          (smoothOrthoFrame (I := I) g₀ b i b))) D)]
  rw [ContinuousMultilinearMap.sum_apply]
  rw [hP]
  rw [Finset.sum_congr rfl (fun i _ =>
    armResidual_contract_term_eq (I := I) (M := M) g₀ g₁ u₀ b D m i)]
  rw [Finset.sum_add_distrib]
  rw [armResidual_arm_toModel_eq (I := I) (M := M) g₀ g₁ u₀ b D m]
  rw [hGarm]
  rw [armResidual_gTerm_toModel_eq (I := I) (M := M) g₀ g₁ u₀ b D m]
  rw [armResidual_slot01_transpose (I := I) (M := M) g₀ g₁ b
    (Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace ((2 + 1) + 1) I b from
        (covGrad (I := I) (M := M) g₀ 0 (2 + 1)
          (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toSection b) D)) m]
  exact add_comm _ _

def edgeArmCoeff (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ (2 + 1) (2 + 0) :=
  -(appCcRS (I := I) (M := M) g₀ (2 + 1) ((2 + 1) + 1) (2 + 0)
    (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
    (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
      (slotInsertEndoCc (I := I) (M := M) g₀ 2
        (gInvDiffRaisedEndoField (I := I) g₀ g₁))))

private theorem deTurckArm_residual_ibp_zero
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    ∀ (u₀ : SmoothCcTensor g₀ 0 2),
      tensorL2Inner (I := I) (M := M) g₀ 0 2
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 0 u₀).toFun
          (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun -
        armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ 0 u₀ =
      (⟪iteratedCovGrad (I := I) g₀ 0 2 0 u₀,
          appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0) (edgeArmCoeff (I := I) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 1 u₀)⟫_ℝ : ℝ) := by
  classical
  intro u₀
  set G₀ : SmoothCcTensor g₀ (2 + 1) (2 + 0) :=
    appCcRS (I := I) (M := M) g₀ (2 + 1) ((2 + 1) + 1) (2 + 0)
      (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
      (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ 2
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))) with hG₀
  rw [edgeArmCoeff, ← hG₀]
  set Du : SmoothCcTensor g₀ 0 (2 + 1) := covGrad (I := I) (M := M) g₀ 0 2 u₀ with hDu
  set P : SmoothCcTensor g₀ 0 (2 + 1) :=
    appCc (I := I) (M := M) g₀ (2 + 1) (2 + 1)
      (slotInsertEndoCc (I := I) (M := M) g₀ 2 (gInvDiffRaisedEndoField (I := I) g₀ g₁))
      Du with hP
  rw [armPrincipalSlotPairing_eq_neg_inner (I := I) (M := M) g₀ g₁ 0 u₀, sub_neg_eq_add,
    oneMinusConnLapSmoothIter_zero]
  have hslot : (⟪iteratedCovGrad (I := I) g₀ 0 2 (0 + 1) u₀,
      appCc (I := I) (M := M) g₀ ((2 + 0) + 1) ((2 + 0) + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + 0)
          (gInvDiffRaisedEndoField (I := I) (M := M) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (0 + 1) u₀)⟫_ℝ : ℝ) =
      tensorL2Inner (I := I) (M := M) g₀ 0 (2 + 1) Du.toFun P.toFun := by
    rw [hDu, hP]
    exact SmoothCcTensor.inner_def (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 2 (0 + 1) u₀)
      (appCc (I := I) (M := M) g₀ ((2 + 0) + 1) ((2 + 0) + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + 0)
          (gInvDiffRaisedEndoField (I := I) (M := M) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (0 + 1) u₀))
  rw [hslot]
  have hgreen := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence
    (I := I) (M := M) g₀ 2 u₀ P
  have hsplit := armResidual_covDivergence_split (I := I) (M := M) g₀ g₁ u₀
  have hfun : (covDivergence (I := I) (M := M) g₀ 2 P).toFun =
      (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun +
        (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du).toFun := by
    rw [hP, hDu, hG₀, hsplit, SmoothCcTensor.toFun_add]
  rw [hfun] at hgreen
  rw [tensorL2Inner_add_right (I := I) (M := M) g₀ 0 2 u₀.toFun
    (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun
    (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du).toFun
    (DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) u₀ (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀))
    (DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) u₀ (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du))] at hgreen
  have hrhs : (⟪iteratedCovGrad (I := I) g₀ 0 2 0 u₀,
      appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0) (-G₀)
        (iteratedCovGrad (I := I) g₀ 0 2 1 u₀)⟫_ℝ : ℝ) =
      - tensorL2Inner (I := I) (M := M) g₀ 0 (2 + 0) u₀.toFun
        (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du).toFun := by
    have hinner := SmoothCcTensor.inner_def (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 2 0 u₀)
      (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0) (-G₀)
        (iteratedCovGrad (I := I) g₀ 0 2 1 u₀))
    rw [hinner]
    rw [show (iteratedCovGrad (I := I) g₀ 0 2 1 u₀ : SmoothCcTensor g₀ 0 (2 + 1)) = Du from rfl]
    rw [appCc_neg_left (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du,
      SmoothCcTensor.toFun_neg]
    rw [show (-(appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du).toFun) =
        (-1 : ℝ) • (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du).toFun from by
      funext x
      rw [Pi.neg_apply, Pi.smul_apply, neg_one_smul]]
    rw [tensorL2Inner_smul_right]
    rw [show (iteratedCovGrad (I := I) g₀ 0 2 0 u₀).toFun = u₀.toFun from rfl]
    ring
  rw [hrhs]
  have hDuFun : Du.toFun = (covGrad (I := I) (M := M) g₀ 0 2 u₀).toFun := rfl
  rw [hDuFun]
  have hY : tensorL2Inner (I := I) (M := M) g₀ 0 (2 + 0) u₀.toFun
      (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du).toFun =
    tensorL2Inner (I := I) (M := M) g₀ 0 2 u₀.toFun
      (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du).toFun := rfl
  linarith [hgreen, hY]

theorem edgeArm_ibp (g₀ g₁ : SmoothRiemannianMetric I M)
    (u₀ : SmoothCcTensor g₀ 0 2) :
    tensorL2Inner (I := I) (M := M) g₀ 0 2
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 0 u₀).toFun
        (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun -
      armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ 0 u₀ =
    (⟪iteratedCovGrad (I := I) g₀ 0 2 0 u₀,
        appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0) (edgeArmCoeff (I := I) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 1 u₀)⟫_ℝ : ℝ) :=
  deTurckArm_residual_ibp_zero (I := I) (M := M) g₀ g₁ u₀

private theorem armJet_norm_comp (g₀ : SmoothRiemannianMetric I M) (s j i : ℕ)
    (S : SmoothCcTensor g₀ 0 s) :
    ‖iteratedCovGrad (I := I) g₀ 0 (s + j) i (iteratedCovGrad (I := I) g₀ 0 s j S)‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 s (j + i) S‖ := by
  have h1 : ‖iteratedCovGrad (I := I) g₀ 0 (s + j) i (iteratedCovGrad (I := I) g₀ 0 s j S)‖ =
      tensorL2Norm (I := I) (M := M) g₀ 0 ((s + j) + i)
        (iteratedCovGrad (I := I) g₀ 0 (s + j) i
          (iteratedCovGrad (I := I) g₀ 0 s j S)).toFun :=
    SmoothCcTensor.norm_def (I := I) (M := M) _
  have h2 : ‖iteratedCovGrad (I := I) g₀ 0 s (j + i) S‖ =
      tensorL2Norm (I := I) (M := M) g₀ 0 (s + (j + i))
        (iteratedCovGrad (I := I) g₀ 0 s (j + i) S).toFun :=
    SmoothCcTensor.norm_def (I := I) (M := M) _
  have hsq :
      ‖iteratedCovGrad (I := I) g₀ 0 (s + j) i (iteratedCovGrad (I := I) g₀ 0 s j S)‖ ^ 2 =
        ‖iteratedCovGrad (I := I) g₀ 0 s (j + i) S‖ ^ 2 := by
    rw [h1, h2,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀
        ((s + j) + i)
        (iteratedCovGrad (I := I) g₀ 0 (s + j) i (iteratedCovGrad (I := I) g₀ 0 s j S)),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀
        (s + (j + i)) (iteratedCovGrad (I := I) g₀ 0 s (j + i) S)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 s j i S x
  have ha : (0 : ℝ) ≤
      ‖iteratedCovGrad (I := I) g₀ 0 (s + j) i (iteratedCovGrad (I := I) g₀ 0 s j S)‖ :=
    norm_nonneg _
  have hb : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 0 s (j + i) S‖ := norm_nonneg _
  rw [← Real.sqrt_sq ha, ← Real.sqrt_sq hb, hsq]

private theorem armJet_norm_order_congr (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    {n n' : ℕ} (h : n = n') (S : SmoothCcTensor g₀ 0 s) :
    ‖iteratedCovGrad (I := I) g₀ 0 s n S‖ = ‖iteratedCovGrad (I := I) g₀ 0 s n' S‖ := by
  subst h
  rfl

private theorem armJet_appCcRS_norm_le (g₀ : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : SmoothCcTensor g₀ b c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ V : SmoothCcTensor g₀ 0 b,
      ‖appCcRS (I := I) (M := M) g₀ 0 b c Φ V‖ ≤ C * ‖V‖ := by
  classical
  obtain ⟨Cop, hCop_nn, hCop⟩ :=
    exists_uniform_riemannianFiberNormSq_appCcRS_le (I := I) (M := M) g₀ 0 b c Φ
  refine ⟨Real.sqrt Cop, Real.sqrt_nonneg _, fun V => ?_⟩
  set Z : SmoothCcTensor g₀ 0 c := appCcRS (I := I) (M := M) g₀ 0 b c Φ V with hZ_def
  have hZn : ‖Z‖ = tensorL2Norm (I := I) (M := M) g₀ 0 c Z.toFun :=
    SmoothCcTensor.norm_def (I := I) (M := M) Z
  have hVn : ‖V‖ = tensorL2Norm (I := I) (M := M) g₀ 0 b V.toFun :=
    SmoothCcTensor.norm_def (I := I) (M := M) V
  have hZL2 : ‖Z‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 c x (Z.toSection x)
        ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [hZn, tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ c Z]
  have hVL2 : ‖V‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 b x (V.toSection x)
        ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [hVn, tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ b V]
  have hpt : ∀ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 c x (Z.toSection x) ≤
      Cop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 b x (V.toSection x) :=
    fun x => hCop V x
  have hVint : MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 b x (V.toSection x))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    DifferentialGeometry.Integral.Connection.integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g₀ 0 b V
  have hZsq_le : ‖Z‖ ^ 2 ≤ Cop * ‖V‖ ^ 2 := by
    rw [hZL2, hVL2]
    have hg_int : MeasureTheory.Integrable
        (fun x => Cop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 b x (V.toSection x))
        (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      hVint.const_mul Cop
    have hmono :=
      MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun x => riemannianFiberNormSq_nonneg (I := I) (M := M)
          g₀ 0 c x _)) hg_int
        (Filter.Eventually.of_forall hpt)
    rw [integral_const_mul] at hmono
    linarith
  have hVnn : 0 ≤ ‖V‖ := norm_nonneg _
  have hZnn : 0 ≤ ‖Z‖ := norm_nonneg _
  rw [← Real.sqrt_sq hZnn]
  calc Real.sqrt (‖Z‖ ^ 2) ≤ Real.sqrt (Cop * ‖V‖ ^ 2) := Real.sqrt_le_sqrt hZsq_le
    _ = Real.sqrt Cop * ‖V‖ := by
        rw [Real.sqrt_mul hCop_nn, Real.sqrt_sq hVnn]

private theorem armJet_iteratedCovGrad_appCc_le (g₀ : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : SmoothCcTensor g₀ b c) :
    ∃ Cf : ℕ → ℝ, (∀ q, 0 ≤ Cf q) ∧ ∀ (q : ℕ) (W : SmoothCcTensor g₀ 0 b),
      ‖iteratedCovGrad (I := I) g₀ 0 c q (appCc (I := I) (M := M) g₀ b c Φ W)‖ ≤
        Cf q * ∑ k ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ 0 b k W‖ := by
  classical
  choose CC hCC_nn hCC using fun (q k : ℕ) =>
    armJet_appCcRS_norm_le (I := I) (M := M) g₀ (b + k) (c + q)
      (appCcLeibnizPsi (I := I) (M := M) g₀ b c Φ q k)
  refine ⟨fun q => ∑ k ∈ Finset.range (q + 1), CC q k,
    fun q => Finset.sum_nonneg (fun k _ => hCC_nn q k), fun q W => ?_⟩
  rw [iteratedCovGrad_appCc_eq (I := I) (M := M) g₀ b c Φ W q]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ k ∈ Finset.range (q + 1),
      ‖appCcRS (I := I) (M := M) g₀ 0 (b + k) (c + q)
          (appCcLeibnizPsi (I := I) (M := M) g₀ b c Φ q k)
          (iteratedCovGrad (I := I) g₀ 0 b k W)‖ ≤
        CC q k * ∑ j ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ 0 b j W‖ := by
    intro k hk
    refine le_trans (hCC q k (iteratedCovGrad (I := I) g₀ 0 b k W)) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCC_nn q k)
    exact Finset.single_le_sum
      (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 b j W‖)
      (fun j _ => norm_nonneg _) hk
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul]

private theorem armJet_lapGrad_commutator_le
    (g₀ : SmoothRiemannianMetric I M) (m : ℕ) :
    ∀ s : ℕ, ∃ Cfun : ℕ → ℝ, (∀ p, 0 ≤ Cfun p) ∧
      ∀ (p : ℕ) (S : SmoothCcTensor g₀ 0 s),
        ‖iteratedCovGrad (I := I) g₀ 0 (s + m) p
            (rawTensorConnLapSmooth (I := I) g₀ 0 (s + m)
                (iteratedCovGrad (I := I) g₀ 0 s m S) -
              iteratedCovGrad (I := I) g₀ 0 s m
                (rawTensorConnLapSmooth (I := I) g₀ 0 s S))‖ ≤
          Cfun p * ∑ a ∈ Finset.range (m + p + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ := by
  classical
  induction m with
  | zero =>
    intro s
    refine ⟨fun _ => 0, fun _ => le_refl _, fun p S => ?_⟩
    have hcomm0 :
        rawTensorConnLapSmooth (I := I) g₀ 0 (s + 0)
            (iteratedCovGrad (I := I) g₀ 0 s 0 S) -
            iteratedCovGrad (I := I) g₀ 0 s 0
              (rawTensorConnLapSmooth (I := I) g₀ 0 s S) =
          (0 : SmoothCcTensor g₀ 0 (s + 0)) := by
      simp only [iteratedCovGrad_zero, Nat.add_zero, sub_self]
    rw [hcomm0]
    have hz : iteratedCovGrad (I := I) g₀ 0 (s + 0) p (0 : SmoothCcTensor g₀ 0 (s + 0)) =
        (0 : SmoothCcTensor g₀ 0 (s + 0 + p)) := by
      have := iteratedCovGrad_sub (I := I) (M := M) g₀ 0 (s + 0) p
        (0 : SmoothCcTensor g₀ 0 (s + 0)) (0 : SmoothCcTensor g₀ 0 (s + 0))
      simpa using this
    rw [hz, norm_zero]
    exact mul_nonneg (le_refl 0) (Finset.sum_nonneg (fun a _ => norm_nonneg _))
  | succ m ih =>
    intro s
    obtain ⟨Cm, hCm_nn, hCm⟩ := ih s
    obtain ⟨K, hK_nn, hK⟩ :=
      exists_iteratedCovGrad_pointwiseTensorCurv_l2Norm_le (I := I) (M := M) g₀ (s + m)
    refine ⟨fun p => K p + Cm (p + 1), fun p => add_nonneg (hK_nn p) (hCm_nn (p + 1)),
      fun p S => ?_⟩
    have hsplit :
        rawTensorConnLapSmooth (I := I) g₀ 0 (s + (m + 1))
            (iteratedCovGrad (I := I) g₀ 0 s (m + 1) S) -
            iteratedCovGrad (I := I) g₀ 0 s (m + 1)
              (rawTensorConnLapSmooth (I := I) g₀ 0 s S) =
          pointwiseTensorCurv (I := I) (M := M) g₀ (s + m)
              (iteratedCovGrad (I := I) g₀ 0 s m S) +
            covGrad (I := I) (M := M) g₀ 0 (s + m)
              (rawTensorConnLapSmooth (I := I) g₀ 0 (s + m)
                  (iteratedCovGrad (I := I) g₀ 0 s m S) -
                iteratedCovGrad (I := I) g₀ 0 s m
                  (rawTensorConnLapSmooth (I := I) g₀ 0 s S)) := by
      rw [iteratedCovGrad_succ (I := I) (M := M) g₀ 0 s m S,
        iteratedCovGrad_succ (I := I) (M := M) g₀ 0 s m
          (rawTensorConnLapSmooth (I := I) g₀ 0 s S)]
      change rawTensorConnLapSmooth (I := I) g₀ 0 (s + m + 1)
            (covGrad (I := I) (M := M) g₀ 0 (s + m)
              (iteratedCovGrad (I := I) g₀ 0 s m S)) -
          covGrad (I := I) (M := M) g₀ 0 (s + m)
            (iteratedCovGrad (I := I) g₀ 0 s m
              (rawTensorConnLapSmooth (I := I) g₀ 0 s S)) =
        pointwiseTensorCurv (I := I) (M := M) g₀ (s + m)
            (iteratedCovGrad (I := I) g₀ 0 s m S) +
          covGrad (I := I) (M := M) g₀ 0 (s + m)
            (rawTensorConnLapSmooth (I := I) g₀ 0 (s + m)
                (iteratedCovGrad (I := I) g₀ 0 s m S) -
              iteratedCovGrad (I := I) g₀ 0 s m
                (rawTensorConnLapSmooth (I := I) g₀ 0 s S))
      rw [pointwiseTensorCurv_commutator_eq (I := I) (M := M) g₀ (s + m)
          (iteratedCovGrad (I := I) g₀ 0 s m S),
        covGrad_sub (I := I) (M := M) g₀ 0 (s + m)]
      abel
    set comm_m : SmoothCcTensor g₀ 0 (s + m) :=
      rawTensorConnLapSmooth (I := I) g₀ 0 (s + m)
          (iteratedCovGrad (I := I) g₀ 0 s m S) -
        iteratedCovGrad (I := I) g₀ 0 s m
          (rawTensorConnLapSmooth (I := I) g₀ 0 s S) with hcomm_m
    set gradm : SmoothCcTensor g₀ 0 (s + m) := iteratedCovGrad (I := I) g₀ 0 s m S
      with hgradm
    set fullSum : ℝ := ∑ a ∈ Finset.range (m + 1 + p + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ with hfullSum
    have hfullSum_nn : 0 ≤ fullSum :=
      Finset.sum_nonneg (fun a _ => norm_nonneg _)
    rw [hsplit, iteratedCovGrad_add (I := I) (M := M) g₀ 0 (s + (m + 1)) p]
    refine le_trans (norm_add_le _ _) ?_
    have harm1 :
        ‖iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) gradm)‖ ≤
          K p * fullSum := by
      have hKb := hK p gradm
      have hreindex : ∀ a, ‖iteratedCovGrad (I := I) g₀ 0 (s + m) a gradm‖ =
          ‖iteratedCovGrad (I := I) g₀ 0 s (m + a) S‖ := by
        intro a
        rw [hgradm, armJet_norm_comp (I := I) (M := M) g₀ s m a S]
      rw [Finset.sum_congr rfl (fun a _ => hreindex a)] at hKb
      have hsub : ∑ a ∈ Finset.range (p + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 s (m + a) S‖ ≤ fullSum := by
        rw [hfullSum]
        have hIco : ∑ a ∈ Finset.range (p + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 s (m + a) S‖ =
            ∑ b ∈ Finset.Ico m (m + (p + 2)),
              ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ := by
          rw [Finset.sum_Ico_eq_sum_range]
          refine Finset.sum_congr ?_ (fun a _ => rfl)
          congr 1
          omega
        rw [hIco]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun b _ _ => norm_nonneg _)
        intro b hb
        rw [Finset.mem_Ico] at hb
        rw [Finset.mem_range]
        omega
      calc ‖iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
              (pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) gradm)‖
          ≤ K p * ∑ a ∈ Finset.range (p + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 s (m + a) S‖ := hKb
        _ ≤ K p * fullSum := mul_le_mul_of_nonneg_left hsub (hK_nn p)
    have harm2 :
        ‖iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
            (covGrad (I := I) (M := M) g₀ 0 (s + m) comm_m)‖ ≤
          Cm (p + 1) * fullSum := by
      have hcomp :
          ‖iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
              (covGrad (I := I) (M := M) g₀ 0 (s + m) comm_m)‖ =
            ‖iteratedCovGrad (I := I) g₀ 0 (s + m) (p + 1) comm_m‖ := by
        have h := armJet_norm_comp (I := I) (M := M) g₀ (s + m) 1 p comm_m
        rw [Nat.add_comm 1 p] at h
        exact h
      rw [hcomp]
      have hCmb := hCm (p + 1) S
      rw [← hcomm_m] at hCmb
      have hsum_eq : ∑ a ∈ Finset.range (m + (p + 1) + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ = fullSum := by
        rw [hfullSum, show m + (p + 1) + 1 = m + 1 + p + 1 from by omega]
      rw [hsum_eq] at hCmb
      exact hCmb
    have hfinal : K p * fullSum + Cm (p + 1) * fullSum =
        (K p + Cm (p + 1)) * fullSum := by ring
    calc ‖iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) gradm)‖ +
          ‖iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
            (covGrad (I := I) (M := M) g₀ 0 (s + m) comm_m)‖
        ≤ K p * fullSum + Cm (p + 1) * fullSum := add_le_add harm1 harm2
      _ = (K p + Cm (p + 1)) * fullSum := hfinal

private theorem armJet_iterGrad_rawConnLap_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) :
    ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 s,
        ‖iteratedCovGrad (I := I) g₀ 0 s a (rawTensorConnLapSmooth (I := I) g₀ 0 s S)‖ ≤
          C * ∑ b ∈ Finset.range (a + 3), ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ := by
  intro s
  obtain ⟨K, hK_one, hK⟩ :=
    exists_rawConnLap_l2Norm_le_secondCovGrad_l2Norm_gen (I := I) (M := M) g₀
  obtain ⟨Cfun, hCfun_nn, hCfun⟩ :=
    armJet_lapGrad_commutator_le (I := I) (M := M) g₀ a s
  have hK_nn : 0 ≤ K := le_trans (by norm_num) hK_one
  refine ⟨K + Cfun 0, add_nonneg hK_nn (hCfun_nn 0), fun S => ?_⟩
  set FULL : ℝ := ∑ b ∈ Finset.range (a + 3), ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ with hFULL
  have hFULL_nn : 0 ≤ FULL := Finset.sum_nonneg (fun b _ => norm_nonneg _)
  have hlap_second :
      ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + a)
          (iteratedCovGrad (I := I) g₀ 0 s a S)‖ ≤
        K * ‖iteratedCovGrad (I := I) g₀ 0 s (a + 2) S‖ := by
    have hgen := hK (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S)
    rw [DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm (I := I) (M := M) g₀
        (rawTensorConnLapSmooth (I := I) g₀ 0 (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S)),
      DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm (I := I) (M := M) g₀
        (covGrad (I := I) (M := M) g₀ 0 (s + a + 1)
          (covGrad (I := I) (M := M) g₀ 0 (s + a)
            (iteratedCovGrad (I := I) g₀ 0 s a S)))] at hgen
    have hcomp :
        ‖covGrad (I := I) (M := M) g₀ 0 (s + a + 1)
            (covGrad (I := I) (M := M) g₀ 0 (s + a)
              (iteratedCovGrad (I := I) g₀ 0 s a S))‖ =
          ‖iteratedCovGrad (I := I) g₀ 0 s (a + 2) S‖ := by
      have h := armJet_norm_comp (I := I) (M := M) g₀ s a 2 S
      have heq :
          iteratedCovGrad (I := I) g₀ 0 (s + a) 2 (iteratedCovGrad (I := I) g₀ 0 s a S) =
            covGrad (I := I) (M := M) g₀ 0 (s + a + 1)
              (covGrad (I := I) (M := M) g₀ 0 (s + a)
                (iteratedCovGrad (I := I) g₀ 0 s a S)) :=
        rfl
      rw [heq] at h
      rw [h]
    rw [hcomp] at hgen
    exact hgen
  have hcomm :
      ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + a)
          (iteratedCovGrad (I := I) g₀ 0 s a S) -
          iteratedCovGrad (I := I) g₀ 0 s a
            (rawTensorConnLapSmooth (I := I) g₀ 0 s S)‖ ≤
        Cfun 0 * ∑ b ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ := by
    have h := hCfun 0 S
    simpa only [iteratedCovGrad_zero, Nat.add_zero] using h
  have htri :
      ‖iteratedCovGrad (I := I) g₀ 0 s a (rawTensorConnLapSmooth (I := I) g₀ 0 s S)‖ ≤
        ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + a)
            (iteratedCovGrad (I := I) g₀ 0 s a S)‖ +
          ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + a)
              (iteratedCovGrad (I := I) g₀ 0 s a S) -
            iteratedCovGrad (I := I) g₀ 0 s a
              (rawTensorConnLapSmooth (I := I) g₀ 0 s S)‖ := by
    have := norm_sub_le
      (rawTensorConnLapSmooth (I := I) g₀ 0 (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S))
      (rawTensorConnLapSmooth (I := I) g₀ 0 (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S) -
        iteratedCovGrad (I := I) g₀ 0 s a (rawTensorConnLapSmooth (I := I) g₀ 0 s S))
    simpa using this
  have hsecond_le : ‖iteratedCovGrad (I := I) g₀ 0 s (a + 2) S‖ ≤ FULL := by
    rw [hFULL]
    refine Finset.single_le_sum
      (f := fun b => ‖iteratedCovGrad (I := I) g₀ 0 s b S‖)
      (fun b _ => norm_nonneg _) ?_
    rw [Finset.mem_range]
    omega
  have hsub_le : ∑ b ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ ≤ FULL := by
    rw [hFULL]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun b _ _ => norm_nonneg _)
    intro b hb
    rw [Finset.mem_range] at hb ⊢
    omega
  calc ‖iteratedCovGrad (I := I) g₀ 0 s a (rawTensorConnLapSmooth (I := I) g₀ 0 s S)‖
      ≤ ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + a)
            (iteratedCovGrad (I := I) g₀ 0 s a S)‖ +
          ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + a)
              (iteratedCovGrad (I := I) g₀ 0 s a S) -
            iteratedCovGrad (I := I) g₀ 0 s a
              (rawTensorConnLapSmooth (I := I) g₀ 0 s S)‖ := htri
    _ ≤ K * ‖iteratedCovGrad (I := I) g₀ 0 s (a + 2) S‖ +
          Cfun 0 * ∑ b ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ :=
        add_le_add hlap_second hcomm
    _ ≤ K * FULL + Cfun 0 * FULL :=
        add_le_add (mul_le_mul_of_nonneg_left hsecond_le hK_nn)
          (mul_le_mul_of_nonneg_left hsub_le (hCfun_nn 0))
    _ = (K + Cfun 0) * FULL := by ring

private theorem armJet_iteratedCovGrad_iterL_le (g₀ : SmoothRiemannianMetric I M) (s a : ℕ) :
    ∃ Cf : ℕ → ℝ, (∀ p, 0 ≤ Cf p) ∧ ∀ (p : ℕ) (v : SmoothCcTensor g₀ 0 s),
      ‖iteratedCovGrad (I := I) g₀ 0 s p (oneMinusConnLapSmoothIter (I := I) g₀ 0 s a v)‖ ≤
        Cf p * ∑ q ∈ Finset.range (p + 2 * a + 1), ‖iteratedCovGrad (I := I) g₀ 0 s q v‖ := by
  classical
  induction a with
  | zero =>
    refine ⟨fun _ => 1, fun _ => zero_le_one, fun p v => ?_⟩
    rw [oneMinusConnLapSmoothIter_zero, one_mul]
    refine Finset.single_le_sum
      (f := fun q => ‖iteratedCovGrad (I := I) g₀ 0 s q v‖)
      (fun q _ => norm_nonneg _) ?_
    rw [Finset.mem_range]
    omega
  | succ a ih =>
    obtain ⟨Cf, hCf_nn, hCf⟩ := ih
    choose C5 hC5_nn hC5 using fun p => armJet_iterGrad_rawConnLap_le (I := I) (M := M) g₀ p s
    refine ⟨fun p => Cf p + C5 p * ∑ b ∈ Finset.range (p + 3), Cf b, fun p => ?_, fun p v => ?_⟩
    · exact add_nonneg (hCf_nn p)
        (mul_nonneg (hC5_nn p) (Finset.sum_nonneg (fun b _ => hCf_nn b)))
    · set X : SmoothCcTensor g₀ 0 s := oneMinusConnLapSmoothIter (I := I) g₀ 0 s a v with hX_def
      have hsucc : oneMinusConnLapSmoothIter (I := I) g₀ 0 s (a + 1) v =
          X - rawTensorConnLapSmooth (I := I) g₀ 0 s X := by
        rw [oneMinusConnLapSmoothIter_succ]
        rfl
      rw [hsucc, iteratedCovGrad_sub (I := I) (M := M) g₀ 0 s p]
      refine le_trans (norm_sub_le _ _) ?_
      set SFULL : ℝ := ∑ q ∈ Finset.range (p + 2 * (a + 1) + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 s q v‖ with hSFULL
      have hSFULL_nn : 0 ≤ SFULL := Finset.sum_nonneg (fun q _ => norm_nonneg _)
      have hmono : ∀ {m : ℕ}, m ≤ p + 2 * (a + 1) + 1 →
          ∑ q ∈ Finset.range m, ‖iteratedCovGrad (I := I) g₀ 0 s q v‖ ≤ SFULL := by
        intro m hm
        rw [hSFULL]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun q _ _ => norm_nonneg _)
        exact Finset.range_subset_range.mpr hm
      have h1 : ‖iteratedCovGrad (I := I) g₀ 0 s p X‖ ≤ Cf p * SFULL := by
        refine le_trans (hCf p v) ?_
        exact mul_le_mul_of_nonneg_left (hmono (by omega)) (hCf_nn p)
      have h2 : ‖iteratedCovGrad (I := I) g₀ 0 s p (rawTensorConnLapSmooth (I := I) g₀ 0 s X)‖ ≤
          C5 p * ((∑ b ∈ Finset.range (p + 3), Cf b) * SFULL) := by
        refine le_trans (hC5 p X) ?_
        refine mul_le_mul_of_nonneg_left ?_ (hC5_nn p)
        have hb : ∀ b ∈ Finset.range (p + 3),
            ‖iteratedCovGrad (I := I) g₀ 0 s b X‖ ≤ Cf b * SFULL := by
          intro b hb
          rw [Finset.mem_range] at hb
          refine le_trans (hCf b v) ?_
          exact mul_le_mul_of_nonneg_left (hmono (by omega)) (hCf_nn b)
        refine le_trans (Finset.sum_le_sum hb) ?_
        rw [← Finset.sum_mul]
      calc ‖iteratedCovGrad (I := I) g₀ 0 s p X‖ +
            ‖iteratedCovGrad (I := I) g₀ 0 s p (rawTensorConnLapSmooth (I := I) g₀ 0 s X)‖
          ≤ Cf p * SFULL + C5 p * ((∑ b ∈ Finset.range (p + 3), Cf b) * SFULL) :=
            add_le_add h1 h2
        _ = (Cf p + C5 p * ∑ b ∈ Finset.range (p + 3), Cf b) * SFULL := by ring

private theorem armJet_abs_pairing_le (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g₀ 0 s) :
    |tensorL2Inner (I := I) (M := M) g₀ 0 s A.toFun B.toFun| ≤ ‖A‖ * ‖B‖ := by
  have h := SmoothCcTensor.inner_def (I := I) (M := M) A B
  rw [← h]
  exact abs_real_inner_le_norm A B

private theorem armJet_jetSum_mono (g₀ : SmoothRiemannianMetric I M) (s : ℕ) {m m' : ℕ}
    (h : m ≤ m') (v : SmoothCcTensor g₀ 0 s) :
    ∑ q ∈ Finset.range m, ‖iteratedCovGrad (I := I) g₀ 0 s q v‖ ≤
      ∑ q ∈ Finset.range m', ‖iteratedCovGrad (I := I) g₀ 0 s q v‖ :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h)
    (fun _ _ _ => norm_nonneg _)

private theorem armJet_jetSum_covGrad_le (g₀ : SmoothRiemannianMetric I M) (s m : ℕ)
    (v : SmoothCcTensor g₀ 0 s) :
    ∑ q ∈ Finset.range m,
        ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) q (covGrad (I := I) (M := M) g₀ 0 s v)‖ ≤
      ∑ q ∈ Finset.range (m + 1), ‖iteratedCovGrad (I := I) g₀ 0 s q v‖ := by
  have hterm : ∀ q : ℕ,
      ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) q (covGrad (I := I) (M := M) g₀ 0 s v)‖ =
        ‖iteratedCovGrad (I := I) g₀ 0 s (q + 1) v‖ := by
    intro q
    have h0 : covGrad (I := I) (M := M) g₀ 0 s v = iteratedCovGrad (I := I) g₀ 0 s 1 v := rfl
    rw [h0, armJet_norm_comp (I := I) (M := M) g₀ s 1 q v]
    exact armJet_norm_order_congr (I := I) (M := M) g₀ s (by omega) v
  rw [Finset.sum_congr rfl (fun q _ => hterm q)]
  have h := Finset.sum_range_succ' (fun q => ‖iteratedCovGrad (I := I) g₀ 0 s q v‖) m
  have h0 : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 s 0 v‖ := norm_nonneg _
  linarith [h]

private theorem armJet_jetProduct_le (g₀ : SmoothRiemannianMetric I M) (n p q : ℕ)
    (hp : p ≤ n + 2) (hq : q ≤ n + 2) (hpq : p + q ≤ 2 * n + 3)
    (u₀ : SmoothCcTensor g₀ 0 2) :
    (∑ j ∈ Finset.range p, ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
      (∑ j ∈ Finset.range q, ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) ≤
    (∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
      (∑ j ∈ Finset.range (n + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) := by
  have hnn : ∀ m : ℕ, 0 ≤ ∑ j ∈ Finset.range m, ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ :=
    fun m => Finset.sum_nonneg (fun j _ => norm_nonneg _)
  rcases le_total p q with hle | hle
  · have hp' : p ≤ n + 1 := by omega
    exact mul_le_mul (armJet_jetSum_mono (I := I) (M := M) g₀ 2 hp' u₀)
      (armJet_jetSum_mono (I := I) (M := M) g₀ 2 hq u₀) (hnn q) (hnn (n + 1))
  · have hq' : q ≤ n + 1 := by omega
    calc (∑ j ∈ Finset.range p, ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
          (∑ j ∈ Finset.range q, ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)
        = (∑ j ∈ Finset.range q, ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
          (∑ j ∈ Finset.range p, ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) := mul_comm _ _
      _ ≤ (∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
          (∑ j ∈ Finset.range (n + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) :=
        mul_le_mul (armJet_jetSum_mono (I := I) (M := M) g₀ 2 hq' u₀)
          (armJet_jetSum_mono (I := I) (M := M) g₀ 2 hp u₀) (hnn p) (hnn (n + 1))

private theorem arm_g0Term_abs_le_jetProduct (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u₀ : SmoothCcTensor g₀ 0 2,
      |tensorL2Inner (I := I) (M := M) g₀ 0 2
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
          (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0)
            (appCcRS (I := I) (M := M) g₀ (2 + 1) ((2 + 1) + 1) (2 + 0)
              (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
              (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ 2
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁))))
            (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toFun| ≤
      C * ((∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
        (∑ j ∈ Finset.range (n + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
  classical
  set a : ℕ := n / 2 with ha_def
  set b : ℕ := n - n / 2 with hb_def
  set Gf : SmoothCcTensor g₀ (2 + 1) (2 + 0) :=
    appCcRS (I := I) (M := M) g₀ (2 + 1) ((2 + 1) + 1) (2 + 0)
      (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
      (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ 2
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))) with hGf_def
  obtain ⟨CfL, hCfL_nn, hCfL⟩ := armJet_iteratedCovGrad_iterL_le (I := I) (M := M) g₀ 2 b
  obtain ⟨CfR, hCfR_nn, hCfR⟩ := armJet_iteratedCovGrad_iterL_le (I := I) (M := M) g₀ 2 a
  obtain ⟨CfG, hCfG_nn, hCfG⟩ :=
    armJet_iteratedCovGrad_appCc_le (I := I) (M := M) g₀ (2 + 1) (2 + 0) Gf
  refine ⟨CfL 0 * (CfR 0 * ∑ q ∈ Finset.range (2 * a + 1), CfG q), ?_, fun u₀ => ?_⟩
  · exact mul_nonneg (hCfL_nn 0)
      (mul_nonneg (hCfR_nn 0) (Finset.sum_nonneg (fun q _ => hCfG_nn q)))
  · set GT : SmoothCcTensor g₀ 0 (2 + 0) :=
      appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0) Gf (covGrad (I := I) (M := M) g₀ 0 2 u₀)
      with hGT_def
    have hsym := oneMinusConnLapSmoothIter_l2Inner_sym_split (I := I) (M := M) g₀ 0 2 a b u₀ GT
    have hab : a + b = n := by omega
    rw [hab] at hsym
    rw [hsym]
    have hL : ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 2 b u₀‖ ≤
        CfL 0 * ∑ q ∈ Finset.range (2 * b + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 q u₀‖ := by
      have h := hCfL 0 u₀
      simpa only [Nat.zero_add] using h
    have hR : ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 2 a GT‖ ≤
        CfR 0 * ((∑ q ∈ Finset.range (2 * a + 1), CfG q) *
          ∑ k ∈ Finset.range (2 * a + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 k u₀‖) := by
      have h0 := hCfR 0 GT
      simp only [Nat.zero_add] at h0
      refine le_trans h0 ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCfR_nn 0)
      have hq : ∀ q ∈ Finset.range (2 * a + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 q GT‖ ≤
            CfG q * ∑ k ∈ Finset.range (2 * a + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 k u₀‖ := by
        intro q hqmem
        rw [Finset.mem_range] at hqmem
        have hstep := hCfG q (covGrad (I := I) (M := M) g₀ 0 2 u₀)
        rw [← hGT_def] at hstep
        refine le_trans hstep ?_
        refine mul_le_mul_of_nonneg_left ?_ (hCfG_nn q)
        refine le_trans (armJet_jetSum_mono (I := I) (M := M) g₀ (2 + 1)
          (show q + 1 ≤ 2 * a + 1 by omega) (covGrad (I := I) (M := M) g₀ 0 2 u₀)) ?_
        exact armJet_jetSum_covGrad_le (I := I) (M := M) g₀ 2 (2 * a + 1) u₀
      refine le_trans (Finset.sum_le_sum hq) ?_
      rw [← Finset.sum_mul]
    have habs := armJet_abs_pairing_le (I := I) (M := M) g₀ 2
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 b u₀)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 a GT)
    refine le_trans habs ?_
    have hLnn : 0 ≤ CfL 0 * ∑ q ∈ Finset.range (2 * b + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 q u₀‖ :=
      mul_nonneg (hCfL_nn 0) (Finset.sum_nonneg (fun q _ => norm_nonneg _))
    calc ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 2 b u₀‖ *
          ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 2 a GT‖
        ≤ (CfL 0 * ∑ q ∈ Finset.range (2 * b + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 q u₀‖) *
            (CfR 0 * ((∑ q ∈ Finset.range (2 * a + 1), CfG q) *
              ∑ k ∈ Finset.range (2 * a + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 k u₀‖)) :=
          mul_le_mul hL hR (norm_nonneg _) hLnn
      _ = (CfL 0 * (CfR 0 * ∑ q ∈ Finset.range (2 * a + 1), CfG q)) *
            ((∑ q ∈ Finset.range (2 * b + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 q u₀‖) *
              (∑ k ∈ Finset.range (2 * a + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 k u₀‖)) := by
          ring
      _ ≤ (CfL 0 * (CfR 0 * ∑ q ∈ Finset.range (2 * a + 1), CfG q)) *
            ((∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
              (∑ j ∈ Finset.range (n + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
          refine mul_le_mul_of_nonneg_left ?_ ?_
          · exact armJet_jetProduct_le (I := I) (M := M) g₀ n (2 * b + 1) (2 * a + 2)
              (by omega) (by omega) (by omega) u₀
          · exact mul_nonneg (hCfL_nn 0)
              (mul_nonneg (hCfR_nn 0) (Finset.sum_nonneg (fun q _ => hCfG_nn q)))

private theorem armLadder_pairing_transport (g : SmoothRiemannianMetric I M) (σ a r : ℕ)
    (hr : r ≤ a) (X Y : SmoothCcTensor g 0 σ) :
    tensorL2Inner (I := I) (M := M) g 0 σ
        (oneMinusConnLapSmoothIter (I := I) g 0 σ a X).toFun Y.toFun =
      tensorL2Inner (I := I) (M := M) g 0 σ
        (oneMinusConnLapSmoothIter (I := I) g 0 σ (a - r) X).toFun
        (oneMinusConnLapSmoothIter (I := I) g 0 σ r Y).toFun := by
  have hsplit : oneMinusConnLapSmoothIter (I := I) g 0 σ a X =
      oneMinusConnLapSmoothIter (I := I) g 0 σ r
        (oneMinusConnLapSmoothIter (I := I) g 0 σ (a - r) X) := by
    rw [← oneMinusConnLapSmoothIter_add (I := I) (M := M) g 0 σ r (a - r) X]
    congr 1
    omega
  rw [hsplit]
  exact oneMinusConnLapSmoothIter_l2Inner_selfAdjoint (I := I) (M := M) g 0 σ r
    (oneMinusConnLapSmoothIter (I := I) g 0 σ (a - r) X) Y

private theorem armLadder_pairing_abs_le_transport (g : SmoothRiemannianMetric I M)
    (σ a r : ℕ) (hr : r ≤ a) (X Y : SmoothCcTensor g 0 σ) :
    |tensorL2Inner (I := I) (M := M) g 0 σ
        (oneMinusConnLapSmoothIter (I := I) g 0 σ a X).toFun Y.toFun| ≤
      ‖oneMinusConnLapSmoothIter (I := I) g 0 σ (a - r) X‖ *
        ‖oneMinusConnLapSmoothIter (I := I) g 0 σ r Y‖ := by
  rw [armLadder_pairing_transport (I := I) (M := M) g σ a r hr X Y]
  exact armJet_abs_pairing_le (I := I) (M := M) g σ
    (oneMinusConnLapSmoothIter (I := I) g 0 σ (a - r) X)
    (oneMinusConnLapSmoothIter (I := I) g 0 σ r Y)

private theorem armAsm_l2Inner_zero_left (g : SmoothRiemannianMetric I M) (σ : ℕ)
    (Z : SmoothCcTensor g 0 σ) :
    tensorL2Inner (I := I) (M := M) g 0 σ (0 : SmoothCcTensor g 0 σ).toFun Z.toFun = 0 := by
  rw [SmoothCcTensor.toFun_zero]
  exact tensorL2Inner_zero_left (I := I) (M := M) g 0 σ Z.toFun

private theorem armAsm_l2Inner_zero_right (g : SmoothRiemannianMetric I M) (σ : ℕ)
    (Z : SmoothCcTensor g 0 σ) :
    tensorL2Inner (I := I) (M := M) g 0 σ Z.toFun (0 : SmoothCcTensor g 0 σ).toFun = 0 := by
  rw [SmoothCcTensor.toFun_zero]
  exact tensorL2Inner_zero_right (I := I) (M := M) g 0 σ Z.toFun

private theorem armAsm_l2Inner_add_left (g : SmoothRiemannianMetric I M) (σ : ℕ)
    (A B Z : SmoothCcTensor g 0 σ) :
    tensorL2Inner (I := I) (M := M) g 0 σ (A + B).toFun Z.toFun =
      tensorL2Inner (I := I) (M := M) g 0 σ A.toFun Z.toFun +
        tensorL2Inner (I := I) (M := M) g 0 σ B.toFun Z.toFun := by
  have hAB : A + B = A - (0 - B) := by abel
  rw [hAB, SmoothCcTensor.toFun_sub,
    tensorL2Inner_sub_left_smoothCc (I := I) (M := M) g 0 σ A (0 - B) Z,
    SmoothCcTensor.toFun_sub,
    tensorL2Inner_sub_left_smoothCc (I := I) (M := M) g 0 σ 0 B Z,
    armAsm_l2Inner_zero_left (I := I) (M := M) g σ Z]
  ring

private theorem armAsm_l2Inner_add_right (g : SmoothRiemannianMetric I M) (σ : ℕ)
    (Z A B : SmoothCcTensor g 0 σ) :
    tensorL2Inner (I := I) (M := M) g 0 σ Z.toFun (A + B).toFun =
      tensorL2Inner (I := I) (M := M) g 0 σ Z.toFun A.toFun +
        tensorL2Inner (I := I) (M := M) g 0 σ Z.toFun B.toFun := by
  have hAB : A + B = A - (0 - B) := by abel
  rw [hAB, SmoothCcTensor.toFun_sub,
    tensorL2Inner_sub_right_smoothCc (I := I) (M := M) g 0 σ Z A (0 - B),
    SmoothCcTensor.toFun_sub,
    tensorL2Inner_sub_right_smoothCc (I := I) (M := M) g 0 σ Z 0 B,
    armAsm_l2Inner_zero_right (I := I) (M := M) g σ Z]
  ring

private theorem armAsm_l2Inner_sum_left (g : SmoothRiemannianMetric I M) (σ c : ℕ)
    (f : ℕ → SmoothCcTensor g 0 σ) (Z : SmoothCcTensor g 0 σ) :
    tensorL2Inner (I := I) (M := M) g 0 σ (∑ i ∈ Finset.range c, f i).toFun Z.toFun =
      ∑ i ∈ Finset.range c, tensorL2Inner (I := I) (M := M) g 0 σ (f i).toFun Z.toFun := by
  induction c with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty, Finset.sum_empty]
    exact armAsm_l2Inner_zero_left (I := I) (M := M) g σ Z
  | succ d ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ,
      armAsm_l2Inner_add_left (I := I) (M := M) g σ (∑ i ∈ Finset.range d, f i) (f d) Z, ih]

private theorem armAsm_sum_window_le (P w : ℕ) (φ A B : ℕ → ℝ)
    (hφ_nn : ∀ c, 0 ≤ φ c) (hB_nn : ∀ e, 0 ≤ B e)
    (h : ∀ c, c < P → A c ≤ φ c * ∑ e ∈ Finset.range (c + w + 1), B e) :
    ∑ c ∈ Finset.range P, A c ≤
      (∑ c ∈ Finset.range P, φ c) * ∑ e ∈ Finset.range (P + w), B e := by
  have hterm : ∀ c ∈ Finset.range P,
      A c ≤ φ c * ∑ e ∈ Finset.range (P + w), B e := by
    intro c hc
    rw [Finset.mem_range] at hc
    refine le_trans (h c hc) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hφ_nn c)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun e _ _ => hB_nn e)
    exact Finset.range_subset_range.mpr (by omega)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul]

private theorem armAsm_iterL_norm_le (g₀ : SmoothRiemannianMetric I M) (σ a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : SmoothCcTensor g₀ 0 σ,
      ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 σ a v‖ ≤
        C * ∑ q ∈ Finset.range (2 * a + 1), ‖iteratedCovGrad (I := I) g₀ 0 σ q v‖ := by
  obtain ⟨Cf, hCf_nn, hCf⟩ := armJet_iteratedCovGrad_iterL_le (I := I) (M := M) g₀ σ a
  refine ⟨Cf 0, hCf_nn 0, fun v => ?_⟩
  have h := hCf 0 v
  simpa only [Nat.zero_add, iteratedCovGrad_zero] using h

private theorem armAsm_shifted_jetSum_le (g₀ : SmoothRiemannianMetric I M) (base c : ℕ)
    (u₀ : SmoothCcTensor g₀ 0 2) :
    ∑ a ∈ Finset.range c,
        ‖iteratedCovGrad (I := I) g₀ 0 (2 + base) a
          (iteratedCovGrad (I := I) g₀ 0 2 base u₀)‖ ≤
      ∑ j ∈ Finset.range (c + base), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ := by
  have hterm : ∀ a ∈ Finset.range c,
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + base) a
          (iteratedCovGrad (I := I) g₀ 0 2 base u₀)‖ =
        ‖iteratedCovGrad (I := I) g₀ 0 2 (base + a) u₀‖ :=
    fun a _ => armJet_norm_comp (I := I) (M := M) g₀ 2 base a u₀
  rw [Finset.sum_congr rfl hterm]
  have hIco : ∑ a ∈ Finset.range c, ‖iteratedCovGrad (I := I) g₀ 0 2 (base + a) u₀‖ =
      ∑ b ∈ Finset.Ico base (base + c), ‖iteratedCovGrad (I := I) g₀ 0 2 b u₀‖ := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr ?_ (fun a _ => rfl)
    congr 1
    omega
  rw [hIco]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun b _ _ => norm_nonneg _)
  intro b hb
  rw [Finset.mem_Ico] at hb
  rw [Finset.mem_range]
  omega

private theorem armAsm_appCc_jet_window (g₀ : SmoothRiemannianMetric I M) (base c : ℕ)
    (Φ : SmoothCcTensor g₀ (2 + base) c) :
    ∃ cc : ℕ → ℝ, (∀ p, 0 ≤ cc p) ∧ ∀ (u₀ : SmoothCcTensor g₀ 0 2) (p : ℕ),
      ‖iteratedCovGrad (I := I) g₀ 0 c p
          (appCc (I := I) (M := M) g₀ (2 + base) c Φ
            (iteratedCovGrad (I := I) g₀ 0 2 base u₀))‖ ≤
        cc p * ∑ j ∈ Finset.range (p + base + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ := by
  obtain ⟨Cf, hCf_nn, hCf⟩ := armJet_iteratedCovGrad_appCc_le (I := I) (M := M) g₀ (2 + base) c Φ
  refine ⟨Cf, hCf_nn, fun u₀ p => ?_⟩
  refine le_trans (hCf p (iteratedCovGrad (I := I) g₀ 0 2 base u₀)) ?_
  refine mul_le_mul_of_nonneg_left ?_ (hCf_nn p)
  have hsh := armAsm_shifted_jetSum_le (I := I) (M := M) g₀ base (p + 1) u₀
  rw [show p + 1 + base = p + base + 1 from by omega] at hsh
  exact hsh

private theorem armAsm_appFullSec_jet_window (g₀ : SmoothRiemannianMetric I M) (base c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) 0 (2 + base) c I) :
    ∃ cc : ℕ → ℝ, (∀ p, 0 ≤ cc p) ∧ ∀ (u₀ : SmoothCcTensor g₀ 0 2) (p : ℕ),
      ‖iteratedCovGrad (I := I) g₀ 0 c p
          (appFullSec (I := I) (M := M) g₀ 0 (2 + base) c Q
            (iteratedCovGrad (I := I) g₀ 0 2 base u₀))‖ ≤
        cc p * ∑ j ∈ Finset.range (p + base + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ := by
  obtain ⟨cq, hcq_nn, hcq⟩ :=
    exists_appFullSec_iteratedCovGrad_l2_window_bound (I := I) (M := M) g₀ 0 (2 + base) c Q
  refine ⟨cq, hcq_nn, fun u₀ p => ?_⟩
  refine le_trans (hcq (iteratedCovGrad (I := I) g₀ 0 2 base u₀) p) ?_
  refine mul_le_mul_of_nonneg_left ?_ (hcq_nn p)
  have hsh := armAsm_shifted_jetSum_le (I := I) (M := M) g₀ base (p + 1) u₀
  rw [show p + 1 + base = p + base + 1 from by omega] at hsh
  exact hsh

private theorem armAsm_appCc_appFullSec_jet_window (g₀ : SmoothRiemannianMetric I M)
    (base b2 c2 : ℕ) (Q : HomTensorRSField (E := E) (M := M) 0 (2 + base) b2 I)
    (Φ : SmoothCcTensor g₀ b2 c2) :
    ∃ cc : ℕ → ℝ, (∀ p, 0 ≤ cc p) ∧ ∀ (u₀ : SmoothCcTensor g₀ 0 2) (p : ℕ),
      ‖iteratedCovGrad (I := I) g₀ 0 c2 p
          (appCc (I := I) (M := M) g₀ b2 c2 Φ
            (appFullSec (I := I) (M := M) g₀ 0 (2 + base) b2 Q
              (iteratedCovGrad (I := I) g₀ 0 2 base u₀)))‖ ≤
        cc p * ∑ j ∈ Finset.range (p + base + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ := by
  obtain ⟨Cf, hCf_nn, hCf⟩ := armJet_iteratedCovGrad_appCc_le (I := I) (M := M) g₀ b2 c2 Φ
  obtain ⟨cq, hcq_nn, hcq⟩ :=
    armAsm_appFullSec_jet_window (I := I) (M := M) g₀ base b2 Q
  refine ⟨fun p => Cf p * ∑ e ∈ Finset.range (p + 1), cq e,
    fun p => mul_nonneg (hCf_nn p) (Finset.sum_nonneg fun e _ => hcq_nn e),
    fun u₀ p => ?_⟩
  refine le_trans (hCf p (appFullSec (I := I) (M := M) g₀ 0 (2 + base) b2 Q
    (iteratedCovGrad (I := I) g₀ 0 2 base u₀))) ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (hCf_nn p)
  have hwin := armAsm_sum_window_le (p + 1) base cq
    (fun e => ‖iteratedCovGrad (I := I) g₀ 0 b2 e
      (appFullSec (I := I) (M := M) g₀ 0 (2 + base) b2 Q
        (iteratedCovGrad (I := I) g₀ 0 2 base u₀))‖)
    (fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)
    hcq_nn (fun _ => norm_nonneg _) (fun e _ => hcq u₀ e)
  rw [show p + 1 + base = p + base + 1 from by omega] at hwin
  exact hwin

private theorem armAsm_covGrad_appCc_jet_window (g₀ : SmoothRiemannianMetric I M) (base : ℕ)
    (Φ : SmoothCcTensor g₀ (2 + base) (2 + base)) :
    ∃ cc : ℕ → ℝ, (∀ p, 0 ≤ cc p) ∧ ∀ (u₀ : SmoothCcTensor g₀ 0 2) (p : ℕ),
      ‖iteratedCovGrad (I := I) g₀ 0 ((2 + base) + 1) p
          (covGrad (I := I) (M := M) g₀ 0 (2 + base)
            (appCc (I := I) (M := M) g₀ (2 + base) (2 + base) Φ
              (iteratedCovGrad (I := I) g₀ 0 2 base u₀)))‖ ≤
        cc p * ∑ j ∈ Finset.range (p + base + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ := by
  obtain ⟨Cf, hCf_nn, hCf⟩ :=
    armJet_iteratedCovGrad_appCc_le (I := I) (M := M) g₀ (2 + base) (2 + base) Φ
  refine ⟨fun p => Cf (1 + p), fun p => hCf_nn (1 + p), fun u₀ p => ?_⟩
  have hnc : ‖iteratedCovGrad (I := I) g₀ 0 ((2 + base) + 1) p
      (covGrad (I := I) (M := M) g₀ 0 (2 + base)
        (appCc (I := I) (M := M) g₀ (2 + base) (2 + base) Φ
          (iteratedCovGrad (I := I) g₀ 0 2 base u₀)))‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + base) (1 + p)
        (appCc (I := I) (M := M) g₀ (2 + base) (2 + base) Φ
          (iteratedCovGrad (I := I) g₀ 0 2 base u₀))‖ :=
    armJet_norm_comp (I := I) (M := M) g₀ (2 + base) 1 p
      (appCc (I := I) (M := M) g₀ (2 + base) (2 + base) Φ
        (iteratedCovGrad (I := I) g₀ 0 2 base u₀))
  rw [hnc]
  refine le_trans (hCf (1 + p) (iteratedCovGrad (I := I) g₀ 0 2 base u₀)) ?_
  refine mul_le_mul_of_nonneg_left ?_ (hCf_nn (1 + p))
  have hsh := armAsm_shifted_jetSum_le (I := I) (M := M) g₀ base (1 + p + 1) u₀
  rw [show 1 + p + 1 + base = p + base + 2 from by omega] at hsh
  exact hsh

private theorem armAsm_abs_add4_sub_le (a b c d e : ℝ) :
    |a + b + c + d - e| ≤ |a| + |b| + |c| + |d| + |e| := by
  calc |a + b + c + d - e| = |a + b + c + d + -e| := by rw [sub_eq_add_neg]
    _ ≤ |a + b + c + d| + |-e| := abs_add_le _ _
    _ ≤ |a + b + c| + |d| + |-e| := add_le_add_left (abs_add_le _ _) _
    _ ≤ |a + b| + |c| + |d| + |-e| :=
        add_le_add_left (add_le_add_left (abs_add_le _ _) _) _
    _ ≤ |a| + |b| + |c| + |d| + |-e| :=
        add_le_add_left (add_le_add_left (add_le_add_left (abs_add_le _ _) _) _) _
    _ = |a| + |b| + |c| + |d| + |e| := by rw [abs_neg]

private theorem armAsm_transport_pairing_jet_le (g₀ : SmoothRiemannianMetric I M)
    (σ a r dX dY NA NB : ℕ) (hr : r ≤ a)
    (hNA : 2 * (a - r) + dX ≤ NA) (hNB : 2 * r + dY ≤ NB)
    (cX cY : ℕ → ℝ) (hcX_nn : ∀ p, 0 ≤ cX p) (hcY_nn : ∀ p, 0 ≤ cY p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u₀ : SmoothCcTensor g₀ 0 2) (X Y : SmoothCcTensor g₀ 0 σ),
      (∀ p, ‖iteratedCovGrad (I := I) g₀ 0 σ p X‖ ≤
        cX p * ∑ j ∈ Finset.range (p + dX + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) →
      (∀ p, ‖iteratedCovGrad (I := I) g₀ 0 σ p Y‖ ≤
        cY p * ∑ j ∈ Finset.range (p + dY + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) →
      |tensorL2Inner (I := I) (M := M) g₀ 0 σ
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ a X).toFun Y.toFun| ≤
        C * ((∑ j ∈ Finset.range (NA + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
          (∑ j ∈ Finset.range (NB + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
  classical
  obtain ⟨CL, hCL_nn, hCL⟩ := armAsm_iterL_norm_le (I := I) (M := M) g₀ σ (a - r)
  obtain ⟨CR, hCR_nn, hCR⟩ := armAsm_iterL_norm_le (I := I) (M := M) g₀ σ r
  refine ⟨(CL * ∑ p ∈ Finset.range (2 * (a - r) + 1), cX p) *
      (CR * ∑ p ∈ Finset.range (2 * r + 1), cY p),
    mul_nonneg (mul_nonneg hCL_nn (Finset.sum_nonneg fun p _ => hcX_nn p))
      (mul_nonneg hCR_nn (Finset.sum_nonneg fun p _ => hcY_nn p)),
    fun u₀ X Y hX hY => ?_⟩
  have hXb : ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 σ (a - r) X‖ ≤
      (CL * ∑ p ∈ Finset.range (2 * (a - r) + 1), cX p) *
        ∑ j ∈ Finset.range (NA + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ := by
    refine le_trans (hCL X) ?_
    have h1 : ∑ p ∈ Finset.range (2 * (a - r) + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 σ p X‖ ≤
        (∑ p ∈ Finset.range (2 * (a - r) + 1), cX p) *
          ∑ j ∈ Finset.range (2 * (a - r) + 1 + dX),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ :=
      armAsm_sum_window_le (2 * (a - r) + 1) dX cX
        (fun p => ‖iteratedCovGrad (I := I) g₀ 0 σ p X‖)
        (fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)
        hcX_nn (fun _ => norm_nonneg _) (fun p _ => hX p)
    refine le_trans (mul_le_mul_of_nonneg_left h1 hCL_nn) ?_
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_
      (mul_nonneg hCL_nn (Finset.sum_nonneg fun p _ => hcX_nn p))
    exact armJet_jetSum_mono (I := I) (M := M) g₀ 2 (by omega) u₀
  have hYb : ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 σ r Y‖ ≤
      (CR * ∑ p ∈ Finset.range (2 * r + 1), cY p) *
        ∑ j ∈ Finset.range (NB + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ := by
    refine le_trans (hCR Y) ?_
    have h1 : ∑ p ∈ Finset.range (2 * r + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 σ p Y‖ ≤
        (∑ p ∈ Finset.range (2 * r + 1), cY p) *
          ∑ j ∈ Finset.range (2 * r + 1 + dY),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ :=
      armAsm_sum_window_le (2 * r + 1) dY cY
        (fun p => ‖iteratedCovGrad (I := I) g₀ 0 σ p Y‖)
        (fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)
        hcY_nn (fun _ => norm_nonneg _) (fun p _ => hY p)
    refine le_trans (mul_le_mul_of_nonneg_left h1 hCR_nn) ?_
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_
      (mul_nonneg hCR_nn (Finset.sum_nonneg fun p _ => hcY_nn p))
    exact armJet_jetSum_mono (I := I) (M := M) g₀ 2 (by omega) u₀
  refine le_trans
    (armLadder_pairing_abs_le_transport (I := I) (M := M) g₀ σ a r hr X Y) ?_
  calc ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 σ (a - r) X‖ *
        ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 σ r Y‖
      ≤ ((CL * ∑ p ∈ Finset.range (2 * (a - r) + 1), cX p) *
          ∑ j ∈ Finset.range (NA + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
        ((CR * ∑ p ∈ Finset.range (2 * r + 1), cY p) *
          ∑ j ∈ Finset.range (NB + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) :=
        mul_le_mul hXb hYb (norm_nonneg _) (le_trans (norm_nonneg _) hXb)
    _ = (CL * ∑ p ∈ Finset.range (2 * (a - r) + 1), cX p) *
          (CR * ∑ p ∈ Finset.range (2 * r + 1), cY p) *
        ((∑ j ∈ Finset.range (NA + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
          (∑ j ∈ Finset.range (NB + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
        ring

set_option backward.isDefEq.respectTransparency false in
private theorem armSwap_appFullSec_sub_right (g : SmoothRiemannianMetric I M) (t : ℕ)
    (F : HomTensorRSField (E := E) (M := M) 0 (t + 2) (t + 2) I)
    (A B : SmoothCcTensor g 0 (t + 2)) :
    appFullSec (I := I) (M := M) g 0 (t + 2) (t + 2) F (A - B) =
      appFullSec (I := I) (M := M) g 0 (t + 2) (t + 2) F A -
        appFullSec (I := I) (M := M) g 0 (t + 2) (t + 2) F B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((appFullSec (I := I) (M := M) g 0 (t + 2) (t + 2) F A -
      appFullSec (I := I) (M := M) g 0 (t + 2) (t + 2) F B).toSection x) =
    (appFullSec (I := I) (M := M) g 0 (t + 2) (t + 2) F A).toSection x -
      (appFullSec (I := I) (M := M) g 0 (t + 2) (t + 2) F B).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [appFullSec_toSection, appFullSec_toSection, appFullSec_toSection]
  rw [show ((A - B).toSection x : TensorRSSpace 0 (t + 2) I x) =
      A.toSection x - B.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  exact map_sub _ _ _

private theorem armSwap_oneMinusConnLapSmooth_comm (g : SmoothRiemannianMetric I M) (t : ℕ)
    (F : HomTensorRSField (E := E) (M := M) 0 (t + 2) (t + 2) I)
    (hF : ∀ (x : M) (T : TensorRSSpace 0 (t + 2) I x) (D : Tensor0SSpace 0 I x)
      (a b : TangentSpace I x) (w : Fin t → TangentSpace I x),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 2) I x from
            (show TensorRSSpace 0 (t + 2) I x →L[ℝ] TensorRSSpace 0 (t + 2) I x from F x) T) D)
          (Fin.cons a (Fin.cons b w)) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 2) I x from T) D)
          (Fin.cons b (Fin.cons a w)))
    (U : SmoothCcTensor g 0 (t + 2)) :
    oneMinusConnLapSmooth (I := I) g 0 (t + 2)
        (appFullSec (I := I) (M := M) g 0 (t + 2) (t + 2) F U) =
      appFullSec (I := I) (M := M) g 0 (t + 2) (t + 2) F
        (oneMinusConnLapSmooth (I := I) g 0 (t + 2) U) := by
  unfold oneMinusConnLapSmooth
  rw [appFullSec_swap_rawConnLap_comm (I := I) (M := M) g t F hF U,
    armSwap_appFullSec_sub_right (I := I) (M := M) g t F U
      (rawTensorConnLapSmooth (I := I) g 0 (t + 2) U)]

private theorem armSwap_iterL_comm (g : SmoothRiemannianMetric I M) (t : ℕ)
    (F : HomTensorRSField (E := E) (M := M) 0 (t + 2) (t + 2) I)
    (hF : ∀ (x : M) (T : TensorRSSpace 0 (t + 2) I x) (D : Tensor0SSpace 0 I x)
      (a b : TangentSpace I x) (w : Fin t → TangentSpace I x),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 2) I x from
            (show TensorRSSpace 0 (t + 2) I x →L[ℝ] TensorRSSpace 0 (t + 2) I x from F x) T) D)
          (Fin.cons a (Fin.cons b w)) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 2) I x from T) D)
          (Fin.cons b (Fin.cons a w)))
    (k : ℕ) (U : SmoothCcTensor g 0 (t + 2)) :
    oneMinusConnLapSmoothIter (I := I) g 0 (t + 2) k
        (appFullSec (I := I) (M := M) g 0 (t + 2) (t + 2) F U) =
      appFullSec (I := I) (M := M) g 0 (t + 2) (t + 2) F
        (oneMinusConnLapSmoothIter (I := I) g 0 (t + 2) k U) := by
  induction k with
  | zero => simp only [oneMinusConnLapSmoothIter_zero]
  | succ d ih =>
    rw [oneMinusConnLapSmoothIter_succ, ih,
      armSwap_oneMinusConnLapSmooth_comm (I := I) (M := M) g t F hF
        (oneMinusConnLapSmoothIter (I := I) g 0 (t + 2) d U),
      oneMinusConnLapSmoothIter_succ]

private theorem armLadder_oneMinusConnLapSmooth_sub (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (A B : SmoothCcTensor g r s) :
    oneMinusConnLapSmooth (I := I) g r s (A - B) =
      oneMinusConnLapSmooth (I := I) g r s A - oneMinusConnLapSmooth (I := I) g r s B := by
  unfold oneMinusConnLapSmooth
  rw [rawTensorConnLapSmooth_sub (I := I) (M := M) g r s A B]
  abel

private theorem armLadder_iterL_sub (g : SmoothRiemannianMetric I M) (r s : ℕ) (j : ℕ)
    (A B : SmoothCcTensor g r s) :
    oneMinusConnLapSmoothIter (I := I) g r s j (A - B) =
      oneMinusConnLapSmoothIter (I := I) g r s j A -
        oneMinusConnLapSmoothIter (I := I) g r s j B := by
  induction j with
  | zero => simp only [oneMinusConnLapSmoothIter_zero]
  | succ d ih =>
    rw [oneMinusConnLapSmoothIter_succ, ih,
      armLadder_oneMinusConnLapSmooth_sub (I := I) (M := M) g r s,
      oneMinusConnLapSmoothIter_succ, oneMinusConnLapSmoothIter_succ]

private theorem armComm_ptc_pairing_abs_le (g₀ : SmoothRiemannianMetric I M)
    (σ i q dS dZ NA NB : ℕ) (hNA : i + q + 2 + dS ≤ NA) (hNB : i + q + dZ ≤ NB)
    (cS cZ : ℕ → ℝ) (hcS_nn : ∀ p, 0 ≤ cS p) (hcZ_nn : ∀ p, 0 ≤ cZ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u₀ : SmoothCcTensor g₀ 0 2) (S : SmoothCcTensor g₀ 0 σ)
      (Z : SmoothCcTensor g₀ 0 (σ + 1)),
      (∀ p, ‖iteratedCovGrad (I := I) g₀ 0 σ p S‖ ≤
        cS p * ∑ j ∈ Finset.range (p + dS + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) →
      (∀ p, ‖iteratedCovGrad (I := I) g₀ 0 (σ + 1) p Z‖ ≤
        cZ p * ∑ j ∈ Finset.range (p + dZ + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) →
      |tensorL2Inner (I := I) (M := M) g₀ 0 (σ + 1)
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i
            (pointwiseTensorCurv (I := I) (M := M) g₀ σ
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S))).toFun Z.toFun| ≤
        C * ((∑ j ∈ Finset.range (NA + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
          (∑ j ∈ Finset.range (NB + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
  classical
  rcases le_or_gt q i with hqi | hiq
  · obtain ⟨Kp, hKp_nn, hKp⟩ :=
      exists_iteratedCovGrad_pointwiseTensorCurv_l2Norm_le (I := I) (M := M) g₀ σ
    obtain ⟨CfQ, hCfQ_nn, hCfQ⟩ := armJet_iteratedCovGrad_iterL_le (I := I) (M := M) g₀ σ q
    obtain ⟨CL, hCL_nn, hCL⟩ :=
      armAsm_iterL_norm_le (I := I) (M := M) g₀ (σ + 1) (i - (i + q) / 2)
    obtain ⟨CR, hCR_nn, hCR⟩ :=
      armAsm_iterL_norm_le (I := I) (M := M) g₀ (σ + 1) ((i + q) / 2)
    refine ⟨(CL * ((∑ c ∈ Finset.range (2 * (i - (i + q) / 2) + 1), Kp c) *
        ((∑ e ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1), CfQ e) *
          ∑ p ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q), cS p))) *
      (CR * ∑ p ∈ Finset.range (2 * ((i + q) / 2) + 1), cZ p),
      mul_nonneg (mul_nonneg hCL_nn (mul_nonneg
          (Finset.sum_nonneg fun c _ => hKp_nn c)
          (mul_nonneg (Finset.sum_nonneg fun e _ => hCfQ_nn e)
            (Finset.sum_nonneg fun p _ => hcS_nn p))))
        (mul_nonneg hCR_nn (Finset.sum_nonneg fun p _ => hcZ_nn p)),
      fun u₀ S Z hS hZ => ?_⟩
    have hLb : ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) (i - (i + q) / 2)
        (pointwiseTensorCurv (I := I) (M := M) g₀ σ
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S))‖ ≤
        (CL * ((∑ c ∈ Finset.range (2 * (i - (i + q) / 2) + 1), Kp c) *
          ((∑ e ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1), CfQ e) *
            ∑ p ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q), cS p))) *
          ∑ j ∈ Finset.range (NA + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ := by
      refine le_trans (hCL (pointwiseTensorCurv (I := I) (M := M) g₀ σ
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S))) ?_
      have h1 : ∑ c ∈ Finset.range (2 * (i - (i + q) / 2) + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 (σ + 1) c
            (pointwiseTensorCurv (I := I) (M := M) g₀ σ
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S))‖ ≤
          (∑ c ∈ Finset.range (2 * (i - (i + q) / 2) + 1), Kp c) *
            ∑ e ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 σ e
                (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S)‖ :=
        armAsm_sum_window_le (2 * (i - (i + q) / 2) + 1) 1 Kp
          (fun c => ‖iteratedCovGrad (I := I) g₀ 0 (σ + 1) c
            (pointwiseTensorCurv (I := I) (M := M) g₀ σ
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S))‖)
          (fun e => ‖iteratedCovGrad (I := I) g₀ 0 σ e
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S)‖)
          hKp_nn (fun _ => norm_nonneg _)
          (fun c _ => hKp c (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S))
      have h2 : ∑ e ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 σ e
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S)‖ ≤
          (∑ e ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1), CfQ e) *
            ∑ p ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q),
              ‖iteratedCovGrad (I := I) g₀ 0 σ p S‖ :=
        armAsm_sum_window_le (2 * (i - (i + q) / 2) + 1 + 1) (2 * q) CfQ
          (fun e => ‖iteratedCovGrad (I := I) g₀ 0 σ e
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S)‖)
          (fun p => ‖iteratedCovGrad (I := I) g₀ 0 σ p S‖)
          hCfQ_nn (fun _ => norm_nonneg _) (fun e _ => hCfQ e S)
      have h3 : ∑ p ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q),
          ‖iteratedCovGrad (I := I) g₀ 0 σ p S‖ ≤
          (∑ p ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q), cS p) *
            ∑ j ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q + dS),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ :=
        armAsm_sum_window_le (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q) dS cS
          (fun p => ‖iteratedCovGrad (I := I) g₀ 0 σ p S‖)
          (fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)
          hcS_nn (fun _ => norm_nonneg _) (fun p _ => hS p)
      have h4 : ∑ j ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q + dS),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ ≤
          ∑ j ∈ Finset.range (NA + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ :=
        armJet_jetSum_mono (I := I) (M := M) g₀ 2 (by omega) u₀
      calc CL * ∑ c ∈ Finset.range (2 * (i - (i + q) / 2) + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 (σ + 1) c
              (pointwiseTensorCurv (I := I) (M := M) g₀ σ
                (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S))‖
          ≤ CL * ((∑ c ∈ Finset.range (2 * (i - (i + q) / 2) + 1), Kp c) *
              ((∑ e ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1), CfQ e) *
                ((∑ p ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q), cS p) *
                  ∑ j ∈ Finset.range (NA + 1),
                    ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖))) := by
            refine mul_le_mul_of_nonneg_left ?_ hCL_nn
            refine le_trans h1 ?_
            refine mul_le_mul_of_nonneg_left ?_
              (Finset.sum_nonneg fun c _ => hKp_nn c)
            refine le_trans h2 ?_
            refine mul_le_mul_of_nonneg_left ?_
              (Finset.sum_nonneg fun e _ => hCfQ_nn e)
            refine le_trans h3 ?_
            exact mul_le_mul_of_nonneg_left h4
              (Finset.sum_nonneg fun p _ => hcS_nn p)
        _ = (CL * ((∑ c ∈ Finset.range (2 * (i - (i + q) / 2) + 1), Kp c) *
              ((∑ e ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1), CfQ e) *
                ∑ p ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q), cS p))) *
            ∑ j ∈ Finset.range (NA + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ := by
            ring
    have hRb : ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) ((i + q) / 2) Z‖ ≤
        (CR * ∑ p ∈ Finset.range (2 * ((i + q) / 2) + 1), cZ p) *
          ∑ j ∈ Finset.range (NB + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ := by
      refine le_trans (hCR Z) ?_
      have h1 : ∑ p ∈ Finset.range (2 * ((i + q) / 2) + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 (σ + 1) p Z‖ ≤
          (∑ p ∈ Finset.range (2 * ((i + q) / 2) + 1), cZ p) *
            ∑ j ∈ Finset.range (2 * ((i + q) / 2) + 1 + dZ),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ :=
        armAsm_sum_window_le (2 * ((i + q) / 2) + 1) dZ cZ
          (fun p => ‖iteratedCovGrad (I := I) g₀ 0 (σ + 1) p Z‖)
          (fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)
          hcZ_nn (fun _ => norm_nonneg _) (fun p _ => hZ p)
      refine le_trans (mul_le_mul_of_nonneg_left h1 hCR_nn) ?_
      rw [← mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_
        (mul_nonneg hCR_nn (Finset.sum_nonneg fun p _ => hcZ_nn p))
      exact armJet_jetSum_mono (I := I) (M := M) g₀ 2 (by omega) u₀
    refine le_trans (armLadder_pairing_abs_le_transport (I := I) (M := M) g₀ (σ + 1) i
      ((i + q) / 2) (by omega)
      (pointwiseTensorCurv (I := I) (M := M) g₀ σ
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S)) Z) ?_
    calc ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) (i - (i + q) / 2)
          (pointwiseTensorCurv (I := I) (M := M) g₀ σ
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S))‖ *
          ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) ((i + q) / 2) Z‖
        ≤ ((CL * ((∑ c ∈ Finset.range (2 * (i - (i + q) / 2) + 1), Kp c) *
            ((∑ e ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1), CfQ e) *
              ∑ p ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q), cS p))) *
            ∑ j ∈ Finset.range (NA + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
          ((CR * ∑ p ∈ Finset.range (2 * ((i + q) / 2) + 1), cZ p) *
            ∑ j ∈ Finset.range (NB + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) :=
          mul_le_mul hLb hRb (norm_nonneg _) (le_trans (norm_nonneg _) hLb)
      _ = (CL * ((∑ c ∈ Finset.range (2 * (i - (i + q) / 2) + 1), Kp c) *
            ((∑ e ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1), CfQ e) *
              ∑ p ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q), cS p))) *
          (CR * ∑ p ∈ Finset.range (2 * ((i + q) / 2) + 1), cZ p) *
          ((∑ j ∈ Finset.range (NA + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
            (∑ j ∈ Finset.range (NB + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
          ring
  · obtain ⟨KK, hKK_nn, hKK⟩ :=
      exists_iteratedCovGrad_rawConnLap_covDivergence_commutator_l2_le (I := I) (M := M) g₀ σ
    obtain ⟨CfI, hCfI_nn, hCfI⟩ :=
      armJet_iteratedCovGrad_iterL_le (I := I) (M := M) g₀ (σ + 1) i
    obtain ⟨CL, hCL_nn, hCL⟩ :=
      armAsm_iterL_norm_le (I := I) (M := M) g₀ σ (q - (q - i - 1) / 2)
    obtain ⟨CR, hCR_nn, hCR⟩ :=
      armAsm_iterL_norm_le (I := I) (M := M) g₀ σ ((q - i - 1) / 2)
    refine ⟨(CL * ∑ p ∈ Finset.range (2 * (q - (q - i - 1) / 2) + 1), cS p) *
      (CR * ((∑ c ∈ Finset.range (2 * ((q - i - 1) / 2) + 1), KK c) *
        ((∑ e ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1), CfI e) *
          ∑ b ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i), cZ b))),
      mul_nonneg (mul_nonneg hCL_nn (Finset.sum_nonneg fun p _ => hcS_nn p))
        (mul_nonneg hCR_nn (mul_nonneg (Finset.sum_nonneg fun c _ => hKK_nn c)
          (mul_nonneg (Finset.sum_nonneg fun e _ => hCfI_nn e)
            (Finset.sum_nonneg fun b _ => hcZ_nn b)))),
      fun u₀ S Z hS hZ => ?_⟩
    have h1 : tensorL2Inner (I := I) (M := M) g₀ 0 (σ + 1)
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i
          (pointwiseTensorCurv (I := I) (M := M) g₀ σ
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S))).toFun Z.toFun =
      tensorL2Inner (I := I) (M := M) g₀ 0 (σ + 1)
        (pointwiseTensorCurv (I := I) (M := M) g₀ σ
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S)).toFun
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z).toFun := by
      have h := armLadder_pairing_transport (I := I) (M := M) g₀ (σ + 1) i i le_rfl
        (pointwiseTensorCurv (I := I) (M := M) g₀ σ
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S)) Z
      rw [Nat.sub_self, oneMinusConnLapSmoothIter_zero] at h
      exact h
    have h2 := pointwiseTensorCurv_l2Inner_eq_covDivergence_commutator (I := I) (M := M) g₀ σ
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 σ q S)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)
    rw [h1, h2]
    have hLb : ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 σ (q - (q - i - 1) / 2) S‖ ≤
        (CL * ∑ p ∈ Finset.range (2 * (q - (q - i - 1) / 2) + 1), cS p) *
          ∑ j ∈ Finset.range (NA + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ := by
      refine le_trans (hCL S) ?_
      have hw : ∑ p ∈ Finset.range (2 * (q - (q - i - 1) / 2) + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 σ p S‖ ≤
          (∑ p ∈ Finset.range (2 * (q - (q - i - 1) / 2) + 1), cS p) *
            ∑ j ∈ Finset.range (2 * (q - (q - i - 1) / 2) + 1 + dS),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ :=
        armAsm_sum_window_le (2 * (q - (q - i - 1) / 2) + 1) dS cS
          (fun p => ‖iteratedCovGrad (I := I) g₀ 0 σ p S‖)
          (fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)
          hcS_nn (fun _ => norm_nonneg _) (fun p _ => hS p)
      refine le_trans (mul_le_mul_of_nonneg_left hw hCL_nn) ?_
      rw [← mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_
        (mul_nonneg hCL_nn (Finset.sum_nonneg fun p _ => hcS_nn p))
      exact armJet_jetSum_mono (I := I) (M := M) g₀ 2 (by omega) u₀
    have hRb : ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 σ ((q - i - 1) / 2)
        (rawTensorConnLapSmooth (I := I) g₀ 0 σ
            (covDivergence (I := I) (M := M) g₀ σ
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)) -
          covDivergence (I := I) (M := M) g₀ σ
            (rawTensorConnLapSmooth (I := I) g₀ 0 (σ + 1)
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)))‖ ≤
        (CR * ((∑ c ∈ Finset.range (2 * ((q - i - 1) / 2) + 1), KK c) *
          ((∑ e ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1), CfI e) *
            ∑ b ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i), cZ b))) *
          ∑ j ∈ Finset.range (NB + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ := by
      refine le_trans (hCR (rawTensorConnLapSmooth (I := I) g₀ 0 σ
          (covDivergence (I := I) (M := M) g₀ σ
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)) -
        covDivergence (I := I) (M := M) g₀ σ
          (rawTensorConnLapSmooth (I := I) g₀ 0 (σ + 1)
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)))) ?_
      have h1' : ∑ c ∈ Finset.range (2 * ((q - i - 1) / 2) + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 σ c
            (rawTensorConnLapSmooth (I := I) g₀ 0 σ
                (covDivergence (I := I) (M := M) g₀ σ
                  (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)) -
              covDivergence (I := I) (M := M) g₀ σ
                (rawTensorConnLapSmooth (I := I) g₀ 0 (σ + 1)
                  (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)))‖ ≤
          (∑ c ∈ Finset.range (2 * ((q - i - 1) / 2) + 1), KK c) *
            ∑ e ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 (σ + 1) e
                (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)‖ :=
        armAsm_sum_window_le (2 * ((q - i - 1) / 2) + 1) 1 KK
          (fun c => ‖iteratedCovGrad (I := I) g₀ 0 σ c
            (rawTensorConnLapSmooth (I := I) g₀ 0 σ
                (covDivergence (I := I) (M := M) g₀ σ
                  (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)) -
              covDivergence (I := I) (M := M) g₀ σ
                (rawTensorConnLapSmooth (I := I) g₀ 0 (σ + 1)
                  (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)))‖)
          (fun e => ‖iteratedCovGrad (I := I) g₀ 0 (σ + 1) e
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)‖)
          hKK_nn (fun _ => norm_nonneg _)
          (fun c _ => hKK c (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z))
      have h2' : ∑ e ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 (σ + 1) e
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)‖ ≤
          (∑ e ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1), CfI e) *
            ∑ b ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i),
              ‖iteratedCovGrad (I := I) g₀ 0 (σ + 1) b Z‖ :=
        armAsm_sum_window_le (2 * ((q - i - 1) / 2) + 1 + 1) (2 * i) CfI
          (fun e => ‖iteratedCovGrad (I := I) g₀ 0 (σ + 1) e
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)‖)
          (fun b => ‖iteratedCovGrad (I := I) g₀ 0 (σ + 1) b Z‖)
          hCfI_nn (fun _ => norm_nonneg _) (fun e _ => hCfI e Z)
      have h3' : ∑ b ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i),
          ‖iteratedCovGrad (I := I) g₀ 0 (σ + 1) b Z‖ ≤
          (∑ b ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i), cZ b) *
            ∑ j ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i + dZ),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ :=
        armAsm_sum_window_le (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i) dZ cZ
          (fun b => ‖iteratedCovGrad (I := I) g₀ 0 (σ + 1) b Z‖)
          (fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)
          hcZ_nn (fun _ => norm_nonneg _) (fun b _ => hZ b)
      have h4' : ∑ j ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i + dZ),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ ≤
          ∑ j ∈ Finset.range (NB + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ :=
        armJet_jetSum_mono (I := I) (M := M) g₀ 2 (by omega) u₀
      calc CR * ∑ c ∈ Finset.range (2 * ((q - i - 1) / 2) + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 σ c
              (rawTensorConnLapSmooth (I := I) g₀ 0 σ
                  (covDivergence (I := I) (M := M) g₀ σ
                    (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)) -
                covDivergence (I := I) (M := M) g₀ σ
                  (rawTensorConnLapSmooth (I := I) g₀ 0 (σ + 1)
                    (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)))‖
          ≤ CR * ((∑ c ∈ Finset.range (2 * ((q - i - 1) / 2) + 1), KK c) *
              ((∑ e ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1), CfI e) *
                ((∑ b ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i), cZ b) *
                  ∑ j ∈ Finset.range (NB + 1),
                    ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖))) := by
            refine mul_le_mul_of_nonneg_left ?_ hCR_nn
            refine le_trans h1' ?_
            refine mul_le_mul_of_nonneg_left ?_
              (Finset.sum_nonneg fun c _ => hKK_nn c)
            refine le_trans h2' ?_
            refine mul_le_mul_of_nonneg_left ?_
              (Finset.sum_nonneg fun e _ => hCfI_nn e)
            refine le_trans h3' ?_
            exact mul_le_mul_of_nonneg_left h4'
              (Finset.sum_nonneg fun b _ => hcZ_nn b)
        _ = (CR * ((∑ c ∈ Finset.range (2 * ((q - i - 1) / 2) + 1), KK c) *
              ((∑ e ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1), CfI e) *
                ∑ b ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i), cZ b))) *
            ∑ j ∈ Finset.range (NB + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ := by
            ring
    refine le_trans (armLadder_pairing_abs_le_transport (I := I) (M := M) g₀ σ q
      ((q - i - 1) / 2) (by omega) S
      (rawTensorConnLapSmooth (I := I) g₀ 0 σ
          (covDivergence (I := I) (M := M) g₀ σ
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)) -
        covDivergence (I := I) (M := M) g₀ σ
          (rawTensorConnLapSmooth (I := I) g₀ 0 (σ + 1)
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)))) ?_
    calc ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 σ (q - (q - i - 1) / 2) S‖ *
          ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 σ ((q - i - 1) / 2)
            (rawTensorConnLapSmooth (I := I) g₀ 0 σ
                (covDivergence (I := I) (M := M) g₀ σ
                  (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)) -
              covDivergence (I := I) (M := M) g₀ σ
                (rawTensorConnLapSmooth (I := I) g₀ 0 (σ + 1)
                  (oneMinusConnLapSmoothIter (I := I) g₀ 0 (σ + 1) i Z)))‖
        ≤ ((CL * ∑ p ∈ Finset.range (2 * (q - (q - i - 1) / 2) + 1), cS p) *
            ∑ j ∈ Finset.range (NA + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
          ((CR * ((∑ c ∈ Finset.range (2 * ((q - i - 1) / 2) + 1), KK c) *
              ((∑ e ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1), CfI e) *
                ∑ b ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i), cZ b))) *
            ∑ j ∈ Finset.range (NB + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) :=
          mul_le_mul hLb hRb (norm_nonneg _) (le_trans (norm_nonneg _) hLb)
      _ = (CL * ∑ p ∈ Finset.range (2 * (q - (q - i - 1) / 2) + 1), cS p) *
          (CR * ((∑ c ∈ Finset.range (2 * ((q - i - 1) / 2) + 1), KK c) *
            ((∑ e ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1), CfI e) *
              ∑ b ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i), cZ b))) *
          ((∑ j ∈ Finset.range (NA + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
            (∑ j ∈ Finset.range (NB + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
          ring

private theorem armStep_pairing_diff_abs_le (g₀ g₁ : SmoothRiemannianMetric I M) (m k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u₀ : SmoothCcTensor g₀ 0 2,
      |tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1)
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1) (k + 1)
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)).toFun
          (appCc (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)).toFun -
        tensorL2Inner (I := I) (M := M) g₀ 0 (2 + (m + 1) + 1)
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + (m + 1) + 1) k
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)).toFun
          (appCc (I := I) (M := M) g₀ (2 + (m + 1) + 1) (2 + (m + 1) + 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ (2 + (m + 1))
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)).toFun| ≤
      C * ((∑ j ∈ Finset.range (m + k + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
        (∑ j ∈ Finset.range (m + k + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨F, R, hF, hE2⟩ :=
    exists_secondCovGrad_swap_ricciDefect_homField (I := I) (M := M) g₀ 0 (2 + m)
  obtain ⟨cWm, hcWm_nn, hcWm⟩ := armAsm_appCc_jet_window (I := I) (M := M) g₀ (m + 1)
    (2 + m + 1)
    (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m) (gInvDiffRaisedEndoField (I := I) g₀ g₁))
  obtain ⟨cDWm, hcDWm_nn, hcDWm⟩ := armAsm_covGrad_appCc_jet_window (I := I) (M := M) g₀ (m + 1)
    (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m) (gInvDiffRaisedEndoField (I := I) g₀ g₁))
  obtain ⟨cGY, hcGY_nn, hcGY⟩ := armAsm_appCc_jet_window (I := I) (M := M) g₀ (m + 1)
    (2 + m + 1 + 1)
    (covGrad (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
      (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m) (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
  obtain ⟨cDD, hcDD_nn, hcDD⟩ :=
    armAsm_appFullSec_jet_window (I := I) (M := M) g₀ m ((2 + m) + 2) R
  obtain ⟨cD2Y, hcD2Y_nn, hcD2Y⟩ := armAsm_appCc_appFullSec_jet_window (I := I) (M := M) g₀ m
    ((2 + m) + 2) (2 + m + 1 + 1) R
    (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
      (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m) (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
  obtain ⟨cWm', hcWm'_nn, hcWm'⟩ := armAsm_appCc_jet_window (I := I) (M := M) g₀ (m + 1 + 1)
    (2 + (m + 1) + 1)
    (slotInsertEndoCc (I := I) (M := M) g₀ (2 + (m + 1))
      (gInvDiffRaisedEndoField (I := I) g₀ g₁))
  have hV1win : ∀ (u₀ : SmoothCcTensor g₀ 0 2) (p : ℕ),
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + m + 1) p
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)‖ ≤
        (1 : ℝ) * ∑ j ∈ Finset.range (p + (m + 1) + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ := by
    intro u₀ p
    rw [one_mul]
    have h := armJet_norm_comp (I := I) (M := M) g₀ 2 (m + 1) p u₀
    calc ‖iteratedCovGrad (I := I) g₀ 0 (2 + m + 1) p
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)‖ =
        ‖iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + p) u₀‖ := h
      _ ≤ ∑ j ∈ Finset.range (p + (m + 1) + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ :=
        Finset.single_le_sum (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)
          (fun j _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
  have hCVwin : ∀ (u₀ : SmoothCcTensor g₀ 0 2) (p : ℕ),
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + m + 1 + 1) p
          (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))‖ ≤
        (1 : ℝ) * ∑ j ∈ Finset.range (p + (m + 1 + 1) + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ := by
    intro u₀ p
    rw [one_mul]
    have h := armJet_norm_comp (I := I) (M := M) g₀ 2 (m + 1 + 1) p u₀
    calc ‖iteratedCovGrad (I := I) g₀ 0 (2 + m + 1 + 1) p
          (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))‖ =
        ‖iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1 + p) u₀‖ := h
      _ ≤ ∑ j ∈ Finset.range (p + (m + 1 + 1) + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ :=
        Finset.single_le_sum (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)
          (fun j _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
  obtain ⟨CA, hCA_nn, hCA⟩ := armAsm_transport_pairing_jet_le (I := I) (M := M) g₀
    (2 + m + 1) k (k / 2) (m + 1) (m + 1) (m + k + 2) (m + k + 1)
    (by omega) (by omega) (by omega) (fun _ => (1 : ℝ)) cWm (fun _ => zero_le_one) hcWm_nn
  obtain ⟨CD1, hCD1_nn, hCD1⟩ := armAsm_transport_pairing_jet_le (I := I) (M := M) g₀
    (2 + m + 1 + 1) k (k / 2) m (m + 1 + 1) (m + k + 1) (m + k + 2)
    (by omega) (by omega) (by omega) cDD cWm' hcDD_nn hcWm'_nn
  obtain ⟨CD2, hCD2_nn, hCD2⟩ := armAsm_transport_pairing_jet_le (I := I) (M := M) g₀
    (2 + m + 1 + 1) k (k - k / 2) (m + 1 + 1) m (m + k + 2) (m + k + 1)
    (by omega) (by omega) (by omega) (fun _ => (1 : ℝ)) cD2Y (fun _ => zero_le_one) hcD2Y_nn
  have hGEx : ∃ CG : ℝ, 0 ≤ CG ∧ ∀ u₀ : SmoothCcTensor g₀ 0 2,
      |tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
            (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
              (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
          (appCcRS (I := I) (M := M) g₀ 0 (2 + m + 1) (2 + m + 1 + 1)
            (covGrad (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
                (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)).toFun| ≤
        CG * ((∑ j ∈ Finset.range (m + k + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
          (∑ j ∈ Finset.range (m + k + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
    by_cases hk2 : k % 2 = 0
    · obtain ⟨CG, hCG_nn, hCG⟩ := armAsm_transport_pairing_jet_le (I := I) (M := M) g₀
        (2 + m + 1 + 1) k (k / 2) (m + 1 + 1) (m + 1) (m + k + 2) (m + k + 1)
        (by omega) (by omega) (by omega) (fun _ => (1 : ℝ)) cGY (fun _ => zero_le_one) hcGY_nn
      refine ⟨CG, hCG_nn, fun u₀ => ?_⟩
      have h := hCG u₀
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))
        (appCc (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1 + 1)
          (covGrad (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
              (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))
        (hCVwin u₀) (fun p => hcGY u₀ p)
      rw [show m + k + 2 + 1 = m + k + 3 from by omega,
        show m + k + 1 + 1 = m + k + 2 from by omega] at h
      rw [appCcRS_zero_eq_appCc (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1 + 1)
        (covGrad (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)]
      calc |tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
              (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
                (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
            (appCc (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1 + 1)
              (covGrad (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
              (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)).toFun|
          ≤ CG * ((∑ j ∈ Finset.range (m + k + 3),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
              (∑ j ∈ Finset.range (m + k + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := h
        _ = CG * ((∑ j ∈ Finset.range (m + k + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
              (∑ j ∈ Finset.range (m + k + 3),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by ring
    · obtain ⟨CG, hCG_nn, hCG⟩ := armAsm_transport_pairing_jet_le (I := I) (M := M) g₀
        (2 + m + 1 + 1) k (k - k / 2) (m + 1 + 1) (m + 1) (m + k + 1) (m + k + 2)
        (by omega) (by omega) (by omega) (fun _ => (1 : ℝ)) cGY (fun _ => zero_le_one) hcGY_nn
      refine ⟨CG, hCG_nn, fun u₀ => ?_⟩
      have h := hCG u₀
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))
        (appCc (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1 + 1)
          (covGrad (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
              (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))
        (hCVwin u₀) (fun p => hcGY u₀ p)
      rw [show m + k + 1 + 1 = m + k + 2 from by omega,
        show m + k + 2 + 1 = m + k + 3 from by omega] at h
      rw [appCcRS_zero_eq_appCc (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1 + 1)
        (covGrad (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)]
      exact h
  obtain ⟨CG, hCG_nn, hCGb⟩ := hGEx
  have hCiEx : ∀ i : ℕ, ∃ Ci : ℝ, 0 ≤ Ci ∧ ∀ u₀ : SmoothCcTensor g₀ 0 2, i < k →
      |tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) i
            (pointwiseTensorCurv (I := I) (M := M) g₀ (2 + m + 1)
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1) (k - 1 - i)
                (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)))).toFun
          (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
            (appCc (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
                (gInvDiffRaisedEndoField (I := I) g₀ g₁))
              (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun| ≤
        Ci * ((∑ j ∈ Finset.range (m + k + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
          (∑ j ∈ Finset.range (m + k + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
    intro i
    by_cases hik : i < k
    · obtain ⟨Ci, hCi_nn, hCi⟩ := armComm_ptc_pairing_abs_le (I := I) (M := M) g₀
        (2 + m + 1) i (k - 1 - i) (m + 1) (m + 2) (m + k + 2) (m + k + 1)
        (by omega) (by omega) (fun _ => (1 : ℝ)) cDWm (fun _ => zero_le_one) hcDWm_nn
      refine ⟨Ci, hCi_nn, fun u₀ _ => ?_⟩
      have h := hCi u₀ (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (appCc (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)))
        (hV1win u₀) (fun p => hcDWm u₀ p)
      rw [show m + k + 2 + 1 = m + k + 3 from by omega,
        show m + k + 1 + 1 = m + k + 2 from by omega] at h
      calc |tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) i
              (pointwiseTensorCurv (I := I) (M := M) g₀ (2 + m + 1)
                (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1) (k - 1 - i)
                  (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)))).toFun
            (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
              (appCc (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁))
                (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun|
          ≤ Ci * ((∑ j ∈ Finset.range (m + k + 3),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
              (∑ j ∈ Finset.range (m + k + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := h
        _ = Ci * ((∑ j ∈ Finset.range (m + k + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
              (∑ j ∈ Finset.range (m + k + 3),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by ring
    · exact ⟨0, le_rfl, fun u₀ hik' => absurd hik' hik⟩
  choose Ci hCi_nn hCi using hCiEx
  refine ⟨CA + CG + CD1 + CD2 + ∑ i ∈ Finset.range k, Ci i,
    add_nonneg (add_nonneg (add_nonneg (add_nonneg hCA_nn hCG_nn) hCD1_nn) hCD2_nn)
      (Finset.sum_nonneg fun i _ => hCi_nn i),
    fun u₀ => ?_⟩
  have hDir : tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1) (k + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)).toFun
      (appCc (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)).toFun =
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1) k
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)).toFun
      (appCc (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)).toFun +
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1) k
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
      (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
        (appCc (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁))
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun := by
    rw [oneMinusConnLapSmoothIter_succ]
    exact oneMinusConnLapSmooth_l2Inner_eq_add_covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1) k
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))
      (appCc (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))
  have hsplit1 : tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1) k
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
      (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
        (appCc (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁))
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun =
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
      (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
        (appCc (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁))
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun +
    ∑ i ∈ Finset.range k,
      tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) i
          (pointwiseTensorCurv (I := I) (M := M) g₀ (2 + m + 1)
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1) (k - 1 - i)
              (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)))).toFun
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (appCc (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun := by
    rw [covGrad_iterL (I := I) (M := M) g₀ (2 + m + 1) k
      (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀),
      armAsm_l2Inner_add_left (I := I) (M := M) g₀ (2 + m + 1 + 1),
      armAsm_l2Inner_sum_left (I := I) (M := M) g₀ (2 + m + 1 + 1) k]
  have hgradW : covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
      (appCc (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)) =
    appCcRS (I := I) (M := M) g₀ 0 (2 + m + 1) (2 + m + 1 + 1)
      (covGrad (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
      (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀) +
    appCcRS (I := I) (M := M) g₀ 0 (2 + m + 1 + 1) (2 + m + 1 + 1)
      (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
      (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)) := by
    rw [← appCcRS_zero_eq_appCc (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
      (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
        (gInvDiffRaisedEndoField (I := I) g₀ g₁))
      (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)]
    exact covGrad_appCcRS_eq (I := I) (M := M) g₀ 0 (2 + m + 1) (2 + m + 1)
      (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
        (gInvDiffRaisedEndoField (I := I) g₀ g₁))
      (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)
  have hMainSplit : tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
      (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
        (appCc (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁))
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun =
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
      (appCcRS (I := I) (M := M) g₀ 0 (2 + m + 1) (2 + m + 1 + 1)
        (covGrad (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)).toFun +
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
      (appCcRS (I := I) (M := M) g₀ 0 (2 + m + 1 + 1) (2 + m + 1 + 1)
        (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun := by
    rw [hgradW, armAsm_l2Inner_add_right (I := I) (M := M) g₀ (2 + m + 1 + 1)]
  have hE2v : covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
      (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀) =
    appFullSec (I := I) (M := M) g₀ 0 ((2 + m) + 2) ((2 + m) + 2) F
      (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)) +
    appFullSec (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
      (iteratedCovGrad (I := I) g₀ 0 2 m u₀) :=
    hE2 (iteratedCovGrad (I := I) g₀ 0 2 m u₀)
  have hPsplit : appCcRS (I := I) (M := M) g₀ 0 (2 + m + 1 + 1) (2 + m + 1 + 1)
      (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
      (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)) =
    appCcRS (I := I) (M := M) g₀ 0 (2 + m + 1 + 1) (2 + m + 1 + 1)
      (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
      (appFullSec (I := I) (M := M) g₀ 0 ((2 + m) + 2) ((2 + m) + 2) F
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))) +
    appCcRS (I := I) (M := M) g₀ 0 (2 + m + 1 + 1) (2 + m + 1 + 1)
      (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
      (appFullSec (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
        (iteratedCovGrad (I := I) g₀ 0 2 m u₀)) := by
    conv_lhs => rw [hE2v]
    exact appCcRS_add_right (I := I) (M := M) g₀ 0 (2 + m + 1 + 1) (2 + m + 1 + 1)
      (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
      (appFullSec (I := I) (M := M) g₀ 0 ((2 + m) + 2) ((2 + m) + 2) F
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)))
      (appFullSec (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
        (iteratedCovGrad (I := I) g₀ 0 2 m u₀))
  have hsplitP : tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
      (appCcRS (I := I) (M := M) g₀ 0 (2 + m + 1 + 1) (2 + m + 1 + 1)
        (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun =
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
      (appCcRS (I := I) (M := M) g₀ 0 (2 + m + 1 + 1) (2 + m + 1 + 1)
        (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
        (appFullSec (I := I) (M := M) g₀ 0 ((2 + m) + 2) ((2 + m) + 2) F
          (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)))).toFun +
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
      (appCcRS (I := I) (M := M) g₀ 0 (2 + m + 1 + 1) (2 + m + 1 + 1)
        (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
        (appFullSec (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
          (iteratedCovGrad (I := I) g₀ 0 2 m u₀))).toFun := by
    rw [hPsplit, armAsm_l2Inner_add_right (I := I) (M := M) g₀ (2 + m + 1 + 1)]
  have hconj : appCcRS (I := I) (M := M) g₀ 0 (2 + m + 1 + 1) (2 + m + 1 + 1)
      (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
      (appFullSec (I := I) (M := M) g₀ 0 ((2 + m) + 2) ((2 + m) + 2) F
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))) =
    appFullSec (I := I) (M := M) g₀ 0 ((2 + m) + 2) ((2 + m) + 2) F
      (appCc (I := I) (M := M) g₀ (2 + (m + 1) + 1) (2 + (m + 1) + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + (m + 1))
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)) := by
    rw [appCcRS_zero_eq_appCc (I := I) (M := M) g₀ (2 + m + 1 + 1) (2 + m + 1 + 1)
      (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
      (appFullSec (I := I) (M := M) g₀ 0 ((2 + m) + 2) ((2 + m) + 2) F
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)))]
    exact appCc_slotExtend_slotInsert_appFullSec_swap_conj (I := I) (M := M) g₀ (2 + m)
      (gInvDiffRaisedEndoField (I := I) g₀ g₁) F hF
      (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))
  have hhop : tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
      (appCcRS (I := I) (M := M) g₀ 0 (2 + m + 1 + 1) (2 + m + 1 + 1)
        (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
        (appFullSec (I := I) (M := M) g₀ 0 ((2 + m) + 2) ((2 + m) + 2) F
          (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)))).toFun =
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (appFullSec (I := I) (M := M) g₀ 0 ((2 + m) + 2) ((2 + m) + 2) F
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
          (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)))).toFun
      (appCc (I := I) (M := M) g₀ (2 + (m + 1) + 1) (2 + (m + 1) + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + (m + 1))
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)).toFun := by
    rw [hconj]
    exact (appFullSec_swap_l2Inner_hop (I := I) (M := M) g₀ (2 + m) F hF
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)))
      (appCc (I := I) (M := M) g₀ (2 + (m + 1) + 1) (2 + (m + 1) + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + (m + 1))
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀))).symm
  have hσiter : appFullSec (I := I) (M := M) g₀ 0 ((2 + m) + 2) ((2 + m) + 2) F
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))) =
    oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
      (appFullSec (I := I) (M := M) g₀ 0 ((2 + m) + 2) ((2 + m) + 2) F
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))) :=
    (armSwap_iterL_comm (I := I) (M := M) g₀ (2 + m) F hF k
      (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).symm
  have hσsub : appFullSec (I := I) (M := M) g₀ 0 ((2 + m) + 2) ((2 + m) + 2) F
      (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)) =
    covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
      (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀) -
    appFullSec (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
      (iteratedCovGrad (I := I) g₀ 0 2 m u₀) :=
    eq_sub_of_add_eq hE2v.symm
  have hitersub : oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
      (appFullSec (I := I) (M := M) g₀ 0 ((2 + m) + 2) ((2 + m) + 2) F
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))) =
    oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
      (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)) -
    oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
      (appFullSec (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
        (iteratedCovGrad (I := I) g₀ 0 2 m u₀)) := by
    rw [hσsub]
    exact armLadder_iterL_sub (I := I) (M := M) g₀ 0 (2 + m + 1 + 1) k
      (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))
      (appFullSec (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
        (iteratedCovGrad (I := I) g₀ 0 2 m u₀))
  have hlast : tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
          (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)) -
        oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
          (appFullSec (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
            (iteratedCovGrad (I := I) g₀ 0 2 m u₀))).toFun
      (appCc (I := I) (M := M) g₀ (2 + (m + 1) + 1) (2 + (m + 1) + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + (m + 1))
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)).toFun =
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
      (appCc (I := I) (M := M) g₀ (2 + (m + 1) + 1) (2 + (m + 1) + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + (m + 1))
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)).toFun -
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (appFullSec (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
          (iteratedCovGrad (I := I) g₀ 0 2 m u₀))).toFun
      (appCc (I := I) (M := M) g₀ (2 + (m + 1) + 1) (2 + (m + 1) + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + (m + 1))
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)).toFun := by
    rw [SmoothCcTensor.toFun_sub]
    exact tensorL2Inner_sub_left_smoothCc (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)))
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (appFullSec (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
          (iteratedCovGrad (I := I) g₀ 0 2 m u₀)))
      (appCc (I := I) (M := M) g₀ (2 + (m + 1) + 1) (2 + (m + 1) + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + (m + 1))
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀))
  have hbr : tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
      (appCc (I := I) (M := M) g₀ (2 + (m + 1) + 1) (2 + (m + 1) + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + (m + 1))
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)).toFun =
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + (m + 1) + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + (m + 1) + 1) k
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)).toFun
      (appCc (I := I) (M := M) g₀ (2 + (m + 1) + 1) (2 + (m + 1) + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + (m + 1))
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)).toFun := rfl
  have hPσ : tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
      (appCcRS (I := I) (M := M) g₀ 0 (2 + m + 1 + 1) (2 + m + 1 + 1)
        (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
        (appFullSec (I := I) (M := M) g₀ 0 ((2 + m) + 2) ((2 + m) + 2) F
          (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)))).toFun =
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + (m + 1) + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + (m + 1) + 1) k
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)).toFun
      (appCc (I := I) (M := M) g₀ (2 + (m + 1) + 1) (2 + (m + 1) + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + (m + 1))
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)).toFun -
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (appFullSec (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
          (iteratedCovGrad (I := I) g₀ 0 2 m u₀))).toFun
      (appCc (I := I) (M := M) g₀ (2 + (m + 1) + 1) (2 + (m + 1) + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + (m + 1))
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)).toFun := by
    rw [hhop, hσiter, hitersub, hlast, hbr]
  have hEq : tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1) (k + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)).toFun
      (appCc (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)).toFun -
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + (m + 1) + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + (m + 1) + 1) k
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)).toFun
      (appCc (I := I) (M := M) g₀ (2 + (m + 1) + 1) (2 + (m + 1) + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + (m + 1))
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)).toFun =
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1) k
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)).toFun
      (appCc (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)).toFun +
    (∑ i ∈ Finset.range k,
      tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) i
          (pointwiseTensorCurv (I := I) (M := M) g₀ (2 + m + 1)
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1) (k - 1 - i)
              (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)))).toFun
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (appCc (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun) +
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
      (appCcRS (I := I) (M := M) g₀ 0 (2 + m + 1) (2 + m + 1 + 1)
        (covGrad (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)).toFun +
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
      (appCcRS (I := I) (M := M) g₀ 0 (2 + m + 1 + 1) (2 + m + 1 + 1)
        (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
        (appFullSec (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
          (iteratedCovGrad (I := I) g₀ 0 2 m u₀))).toFun -
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (appFullSec (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
          (iteratedCovGrad (I := I) g₀ 0 2 m u₀))).toFun
      (appCc (I := I) (M := M) g₀ (2 + (m + 1) + 1) (2 + (m + 1) + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + (m + 1))
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)).toFun := by
    linarith [hDir, hsplit1, hMainSplit, hsplitP, hPσ]
  rw [hEq]
  have hA2 : |tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1) k
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)).toFun
      (appCc (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)).toFun| ≤
      CA * ((∑ j ∈ Finset.range (m + k + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
        (∑ j ∈ Finset.range (m + k + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
    have h := hCA u₀ (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)
      (appCc (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))
      (hV1win u₀) (fun p => hcWm u₀ p)
    rw [show m + k + 2 + 1 = m + k + 3 from by omega,
      show m + k + 1 + 1 = m + k + 2 from by omega] at h
    refine le_trans h (le_of_eq ?_)
    ring
  have hD1b : |tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (appFullSec (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
          (iteratedCovGrad (I := I) g₀ 0 2 m u₀))).toFun
      (appCc (I := I) (M := M) g₀ (2 + (m + 1) + 1) (2 + (m + 1) + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + (m + 1))
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀)).toFun| ≤
      CD1 * ((∑ j ∈ Finset.range (m + k + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
        (∑ j ∈ Finset.range (m + k + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
    have h := hCD1 u₀
      (appFullSec (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
        (iteratedCovGrad (I := I) g₀ 0 2 m u₀))
      (appCc (I := I) (M := M) g₀ (2 + (m + 1) + 1) (2 + (m + 1) + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + (m + 1))
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1 + 1) u₀))
      (fun p => hcDD u₀ p) (fun p => hcWm' u₀ p)
    rw [show m + k + 1 + 1 = m + k + 2 from by omega,
      show m + k + 2 + 1 = m + k + 3 from by omega] at h
    exact h
  have hD2b : |tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) k
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun
      (appCcRS (I := I) (M := M) g₀ 0 (2 + m + 1 + 1) (2 + m + 1 + 1)
        (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
        (appFullSec (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
          (iteratedCovGrad (I := I) g₀ 0 2 m u₀))).toFun| ≤
      CD2 * ((∑ j ∈ Finset.range (m + k + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
        (∑ j ∈ Finset.range (m + k + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
    have h := hCD2 u₀
      (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))
      (appCc (I := I) (M := M) g₀ (2 + m + 1 + 1) (2 + m + 1 + 1)
        (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
        (appFullSec (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
          (iteratedCovGrad (I := I) g₀ 0 2 m u₀)))
      (hCVwin u₀) (fun p => hcD2Y u₀ p)
    rw [show m + k + 2 + 1 = m + k + 3 from by omega,
      show m + k + 1 + 1 = m + k + 2 from by omega] at h
    rw [appCcRS_zero_eq_appCc (I := I) (M := M) g₀ (2 + m + 1 + 1) (2 + m + 1 + 1)
      (slotExtend (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
      (appFullSec (I := I) (M := M) g₀ 0 (2 + m) ((2 + m) + 2) R
        (iteratedCovGrad (I := I) g₀ 0 2 m u₀))]
    refine le_trans h (le_of_eq ?_)
    ring
  have hCsum : ∑ i ∈ Finset.range k,
      |tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) i
          (pointwiseTensorCurv (I := I) (M := M) g₀ (2 + m + 1)
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1) (k - 1 - i)
              (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)))).toFun
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (appCc (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun| ≤
      (∑ i ∈ Finset.range k, Ci i) *
        ((∑ j ∈ Finset.range (m + k + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
          (∑ j ∈ Finset.range (m + k + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
    refine le_trans (Finset.sum_le_sum
      (fun i hi => hCi i u₀ (Finset.mem_range.mp hi))) ?_
    rw [← Finset.sum_mul]
  refine le_trans ?_ (le_of_eq (show
      (CA + (∑ i ∈ Finset.range k, Ci i) + CG + CD2 + CD1) *
        ((∑ j ∈ Finset.range (m + k + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
          (∑ j ∈ Finset.range (m + k + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) =
      (CA + CG + CD1 + CD2 + ∑ i ∈ Finset.range k, Ci i) *
        ((∑ j ∈ Finset.range (m + k + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
          (∑ j ∈ Finset.range (m + k + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) from
    by ring))
  refine le_trans (armAsm_abs_add4_sub_le _ _ _ _ _) ?_
  have hSabs : |∑ i ∈ Finset.range k,
      tensorL2Inner (I := I) (M := M) g₀ 0 (2 + m + 1 + 1)
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1 + 1) i
          (pointwiseTensorCurv (I := I) (M := M) g₀ (2 + m + 1)
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + m + 1) (k - 1 - i)
              (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀)))).toFun
        (covGrad (I := I) (M := M) g₀ 0 (2 + m + 1)
          (appCc (I := I) (M := M) g₀ (2 + m + 1) (2 + m + 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ (2 + m)
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))
            (iteratedCovGrad (I := I) g₀ 0 2 (m + 1) u₀))).toFun| ≤
      (∑ i ∈ Finset.range k, Ci i) *
        ((∑ j ∈ Finset.range (m + k + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
          (∑ j ∈ Finset.range (m + k + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) :=
    le_trans (Finset.abs_sum_le_sum_abs _ _) hCsum
  exact le_trans
    (add_le_add (add_le_add (add_le_add (add_le_add hA2 hSabs) (hCGb u₀)) hD2b) hD1b)
    (le_of_eq (by ring))

private theorem oneMinusConnLapIter_dirichletSlotForm_add_armPrincipalSlotPairing_abs_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u₀ : SmoothCcTensor g₀ 0 2,
      |tensorL2Inner (I := I) (M := M) g₀ 0 (2 + 1)
          (covGrad (I := I) (M := M) g₀ 0 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀)).toFun
          (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ 2
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))
            (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toFun +
        armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀| ≤
      C * ((∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
        (∑ j ∈ Finset.range (n + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
  classical
  obtain ⟨cW0, hcW0_nn, hcW0⟩ := armAsm_appCc_jet_window (I := I) (M := M) g₀ 1 (2 + 1)
    (slotInsertEndoCc (I := I) (M := M) g₀ 2 (gInvDiffRaisedEndoField (I := I) g₀ g₁))
  have hCbEx : ∀ i : ℕ, ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ u₀ : SmoothCcTensor g₀ 0 2, i < n →
      |tensorL2Inner (I := I) (M := M) g₀ 0 (2 + 1)
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + 1) i
            (pointwiseTensorCurv (I := I) (M := M) g₀ 2
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (n - 1 - i) u₀))).toFun
          (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ 2
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))
            (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toFun| ≤
        Cb * ((∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
          (∑ j ∈ Finset.range (n + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
    intro i
    by_cases hi : i < n
    · obtain ⟨Cb, hCb_nn, hCb⟩ := armComm_ptc_pairing_abs_le (I := I) (M := M) g₀ 2 i
        (n - 1 - i) 0 1 (n + 1) n (by omega) (by omega)
        (fun _ => (1 : ℝ)) cW0 (fun _ => zero_le_one) hcW0_nn
      refine ⟨Cb, hCb_nn, fun u₀ _ => ?_⟩
      have hSwin : ∀ p, ‖iteratedCovGrad (I := I) g₀ 0 2 p u₀‖ ≤
          (1 : ℝ) * ∑ j ∈ Finset.range (p + 0 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ := by
        intro p
        rw [one_mul]
        exact Finset.single_le_sum
          (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)
          (fun j _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
      have h := hCb u₀ u₀
        (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 2
            (gInvDiffRaisedEndoField (I := I) g₀ g₁))
          (covGrad (I := I) (M := M) g₀ 0 2 u₀))
        hSwin (fun p => hcW0 u₀ p)
      rw [show n + 1 + 1 = n + 2 from by omega] at h
      refine le_trans h (le_of_eq ?_)
      ring
    · exact ⟨0, le_rfl, fun u₀ hi' => absurd hi' hi⟩
  choose Cb hCb_nn hCb using hCbEx
  choose Cs hCs_nn hCs using fun μ : ℕ =>
    armStep_pairing_diff_abs_le (I := I) (M := M) g₀ g₁ μ (n - 1 - μ)
  refine ⟨(∑ i ∈ Finset.range n, Cb i) + ∑ μ ∈ Finset.range n, Cs μ,
    add_nonneg (Finset.sum_nonneg fun i _ => hCb_nn i)
      (Finset.sum_nonneg fun μ _ => hCs_nn μ),
    fun u₀ => ?_⟩
  set H : ℕ → ℝ := fun μ => tensorL2Inner (I := I) (M := M) g₀ 0 (2 + μ + 1)
    (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + μ + 1) (n - μ)
      (iteratedCovGrad (I := I) g₀ 0 2 (μ + 1) u₀)).toFun
    (appCc (I := I) (M := M) g₀ (2 + μ + 1) (2 + μ + 1)
      (slotInsertEndoCc (I := I) (M := M) g₀ (2 + μ)
        (gInvDiffRaisedEndoField (I := I) g₀ g₁))
      (iteratedCovGrad (I := I) g₀ 0 2 (μ + 1) u₀)).toFun with hH
  have htele : ∑ μ ∈ Finset.range n, (H μ - H (μ + 1)) = H 0 - H n :=
    Finset.sum_range_sub' H n
  have hH0 : H 0 = tensorL2Inner (I := I) (M := M) g₀ 0 (2 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + 1) n
        (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toFun
      (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ 2
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toFun := by
    simp only [hH]
    rw [Nat.sub_zero]
    rfl
  have hPSP : armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ = - H n := by
    simp only [hH]
    rw [show n - n = 0 from Nat.sub_self n, oneMinusConnLapSmoothIter_zero,
      armPrincipalSlotPairing_eq_neg_inner (I := I) (M := M) g₀ g₁ n u₀,
      SmoothCcTensor.inner_def]
    rfl
  have hbase : tensorL2Inner (I := I) (M := M) g₀ 0 (2 + 1)
      (covGrad (I := I) (M := M) g₀ 0 2
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀)).toFun
      (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ 2
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toFun =
    tensorL2Inner (I := I) (M := M) g₀ 0 (2 + 1)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + 1) n
        (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toFun
      (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ 2
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toFun +
    ∑ i ∈ Finset.range n,
      tensorL2Inner (I := I) (M := M) g₀ 0 (2 + 1)
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + 1) i
          (pointwiseTensorCurv (I := I) (M := M) g₀ 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (n - 1 - i) u₀))).toFun
        (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 2
            (gInvDiffRaisedEndoField (I := I) g₀ g₁))
          (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toFun := by
    rw [covGrad_iterL (I := I) (M := M) g₀ 2 n u₀,
      armAsm_l2Inner_add_left (I := I) (M := M) g₀ (2 + 1),
      armAsm_l2Inner_sum_left (I := I) (M := M) g₀ (2 + 1) n]
  have hgoal_eq : tensorL2Inner (I := I) (M := M) g₀ 0 (2 + 1)
      (covGrad (I := I) (M := M) g₀ 0 2
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀)).toFun
      (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ 2
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))
        (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toFun +
      armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ =
    (∑ i ∈ Finset.range n,
      tensorL2Inner (I := I) (M := M) g₀ 0 (2 + 1)
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + 1) i
          (pointwiseTensorCurv (I := I) (M := M) g₀ 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (n - 1 - i) u₀))).toFun
        (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 2
            (gInvDiffRaisedEndoField (I := I) g₀ g₁))
          (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toFun) +
    ∑ μ ∈ Finset.range n, (H μ - H (μ + 1)) := by
    linarith [hbase, hH0, hPSP, htele]
  rw [hgoal_eq]
  have hstepb : ∀ μ ∈ Finset.range n, |H μ - H (μ + 1)| ≤
      Cs μ * ((∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
        (∑ j ∈ Finset.range (n + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
    intro μ hμ
    rw [Finset.mem_range] at hμ
    have h := hCs μ u₀
    rw [show μ + (n - 1 - μ) + 2 = n + 1 from by omega,
      show μ + (n - 1 - μ) + 3 = n + 2 from by omega] at h
    simp only [hH]
    rw [show n - μ = n - 1 - μ + 1 from by omega,
      show n - (μ + 1) = n - 1 - μ from by omega]
    exact h
  have hbaseb : ∀ i ∈ Finset.range n,
      |tensorL2Inner (I := I) (M := M) g₀ 0 (2 + 1)
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 (2 + 1) i
          (pointwiseTensorCurv (I := I) (M := M) g₀ 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (n - 1 - i) u₀))).toFun
        (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 2
            (gInvDiffRaisedEndoField (I := I) g₀ g₁))
          (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toFun| ≤
      Cb i * ((∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
        (∑ j ∈ Finset.range (n + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) :=
    fun i hi => hCb i u₀ (Finset.mem_range.mp hi)
  refine le_trans (abs_add_le _ _) ?_
  refine le_trans (add_le_add (Finset.abs_sum_le_sum_abs _ _)
    (Finset.abs_sum_le_sum_abs _ _)) ?_
  refine le_trans (add_le_add (Finset.sum_le_sum hbaseb) (Finset.sum_le_sum hstepb)) ?_
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← add_mul]

private theorem oneMinusConnLapIter_arm_sub_armPrincipalSlotPairing_le_jetProduct
    (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u₀ : SmoothCcTensor g₀ 0 2,
      tensorL2Inner (I := I) (M := M) g₀ 0 2
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
          (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun -
        armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ ≤
      C * ((∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) *
        (∑ j ∈ Finset.range (n + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖)) := by
  classical
  obtain ⟨C₁, hC₁_nn, h₁⟩ :=
    oneMinusConnLapIter_dirichletSlotForm_add_armPrincipalSlotPairing_abs_le
      (I := I) (M := M) g₀ g₁ n
  obtain ⟨C₂, hC₂_nn, h₂⟩ := arm_g0Term_abs_le_jetProduct (I := I) (M := M) g₀ g₁ n
  refine ⟨C₁ + C₂, add_nonneg hC₁_nn hC₂_nn, fun u₀ => ?_⟩
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  set G₀ : SmoothCcTensor g₀ (2 + 1) (2 + 0) :=
    appCcRS (I := I) (M := M) g₀ (2 + 1) ((2 + 1) + 1) (2 + 0)
      (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
      (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ 2
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))) with hG₀
  set Du : SmoothCcTensor g₀ 0 (2 + 1) := covGrad (I := I) (M := M) g₀ 0 2 u₀ with hDu
  set P : SmoothCcTensor g₀ 0 (2 + 1) :=
    appCc (I := I) (M := M) g₀ (2 + 1) (2 + 1)
      (slotInsertEndoCc (I := I) (M := M) g₀ 2 (gInvDiffRaisedEndoField (I := I) g₀ g₁))
      Du with hP
  have hgreen := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence
    (I := I) (M := M) g₀ 2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀) P
  have hsplit := armResidual_covDivergence_split (I := I) (M := M) g₀ g₁ u₀
  have hfun : (covDivergence (I := I) (M := M) g₀ 2 P).toFun =
      (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun +
        (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du).toFun := by
    rw [hP, hDu, hG₀, hsplit, SmoothCcTensor.toFun_add]
  rw [hfun] at hgreen
  rw [tensorL2Inner_add_right (I := I) (M := M) g₀ 0 2
    (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
    (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun
    (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du).toFun
    (DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀)
      (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀))
    (DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀)
      (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du))] at hgreen
  have h₁u := h₁ u₀
  have h₂u := h₂ u₀
  rw [← hDu] at h₂u
  rw [← hDu, ← hP] at h₁u
  have habs1 : -(tensorL2Inner (I := I) (M := M) g₀ 0 (2 + 1)
      (covGrad (I := I) (M := M) g₀ 0 2
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀)).toFun P.toFun +
      armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀) ≤
      |tensorL2Inner (I := I) (M := M) g₀ 0 (2 + 1)
        (covGrad (I := I) (M := M) g₀ 0 2
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀)).toFun P.toFun +
        armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀| := neg_le_abs _
  have habs2 : -(tensorL2Inner (I := I) (M := M) g₀ 0 2
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
      (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du).toFun) ≤
      |tensorL2Inner (I := I) (M := M) g₀ 0 2
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
        (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du).toFun| := neg_le_abs _
  linarith [h₁u, h₂u, habs1, habs2, hgreen]

set_option linter.unusedVariables false in
private theorem exists_oneMinusConnLapIter_arm_sub_armPrincipalSlotPairing_jetBound_core
    [Nonempty M] (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : gFibreOpBound (I := I) g₀ h δ) :
    ∃ Clower : ℝ, 0 ≤ Clower ∧
      ∀ (u₀ : SmoothCcTensor g₀ 0 2),
        tensorL2Inner (I := I) (M := M) g₀ 0 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun -
          armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ ≤
        (1 / 4 : ℝ) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
          Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 := by
  obtain ⟨C, hC_nn, hres⟩ :=
    oneMinusConnLapIter_arm_sub_armPrincipalSlotPairing_le_jetProduct
      (I := I) (M := M) g₀ g₁ n
  obtain ⟨Cgap, hCgap_nn, hgap⟩ :=
    exists_iteratedCovGrad_l2NormSq_le_smoothCcToTensorHs_succ_add_lower
      (I := I) (M := M) g₀ n
  obtain ⟨Cjet, hCjet_nn, hjet⟩ :=
    DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_iteratedCovGrad_sum_le_smoothCcToTensorHs
      (I := I) (M := M) g₀ n
  refine ⟨(C + C ^ 2) * Cjet ^ 2 + (1 / 4) * Cgap, by positivity, fun u₀ => ?_⟩
  set Mtop := ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ with hMtop_def
  set Mlow := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ with hMlow_def
  set Jn := ∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ with hJn_def
  set X := ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀‖ with hX_def
  have hMtop_nn : 0 ≤ Mtop := norm_nonneg _
  have hMlow_nn : 0 ≤ Mlow := norm_nonneg _
  have hJn_nn : 0 ≤ Jn := Finset.sum_nonneg (fun j _ => norm_nonneg _)
  have hX_nn : 0 ≤ X := norm_nonneg _
  have hgap_u := hgap u₀
  have hjet_u := hjet u₀
  have hsum : ∑ j ∈ Finset.range (n + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ =
      Jn + X := by
    rw [hJn_def, hX_def]
    exact Finset.sum_range_succ (fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) (n + 1)
  have hres_u : tensorL2Inner (I := I) (M := M) g₀ 0 2
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
        (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun -
      armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ ≤
      C * Jn ^ 2 + C * (Jn * X) := by
    refine le_trans (hres u₀) ?_
    rw [hsum]
    have : C * (Jn * (Jn + X)) = C * Jn ^ 2 + C * (Jn * X) := by ring
    linarith [this.le, this.ge]
  have hX_toL2 : X = ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀)‖ := by
    rw [hX_def, SmoothCcTensor.norm_toL2]
  have hX_sq_le : X ^ 2 ≤ Mtop ^ 2 + Cgap * Mlow ^ 2 := by
    rw [hX_toL2]; exact hgap_u
  have hJn_le : Jn ≤ Cjet * Mlow := hjet_u
  have hJn_sq_le : Jn ^ 2 ≤ Cjet ^ 2 * Mlow ^ 2 := by
    nlinarith [hJn_nn, mul_nonneg hCjet_nn hMlow_nn]
  have hyoung : C * (Jn * X) ≤ (1 / 4) * X ^ 2 + C ^ 2 * Jn ^ 2 := by
    nlinarith [sq_nonneg (X / 2 - C * Jn)]
  have hA : (C + C ^ 2) * Jn ^ 2 ≤ (C + C ^ 2) * (Cjet ^ 2 * Mlow ^ 2) :=
    mul_le_mul_of_nonneg_left hJn_sq_le (by positivity)
  have hB : (1 / 4 : ℝ) * X ^ 2 ≤ (1 / 4) * (Mtop ^ 2 + Cgap * Mlow ^ 2) := by
    linarith [hX_sq_le]
  nlinarith [hres_u, hyoung, hA, hB]

private theorem oneMinusConnLapIter_arm_sub_armPrincipalSlotPairing_le
    [Nonempty M] (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : gFibreOpBound (I := I) g₀ h δ) :
    ∃ Clower : ℝ, 0 ≤ Clower ∧
      ∀ (u₀ : SmoothCcTensor g₀ 0 2),
        tensorL2Inner (I := I) (M := M) g₀ 0 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun -
          armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ ≤
        (1 / 4 : ℝ) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
          Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 :=
  exists_oneMinusConnLapIter_arm_sub_armPrincipalSlotPairing_jetBound_core
    (I := I) (M := M) g₀ g₁ n h htie hδ_lt hδ_nn hδ

private theorem oneMinusConnLapIter_pairing_fold
    [Nonempty M] (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : gFibreOpBound (I := I) g₀ h δ) :
    ∃ rem : SmoothCcTensor g₀ 0 2 → ℝ,
      (∀ (u₀ : SmoothCcTensor g₀ 0 2),
        tensorL2Inner (I := I) (M := M) g₀ 0 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun =
          armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ + rem u₀) ∧
      ∃ Clower : ℝ, 0 ≤ Clower ∧
        ∀ (u₀ : SmoothCcTensor g₀ 0 2),
          rem u₀ ≤
            (1 / 4 : ℝ) *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
              Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 := by
  refine ⟨fun u₀ =>
      tensorL2Inner (I := I) (M := M) g₀ 0 2
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
          (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun -
        armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀,
    fun u₀ => by ring, ?_⟩
  obtain ⟨Clower, hClower_nn, hbound⟩ :=
    oneMinusConnLapIter_arm_sub_armPrincipalSlotPairing_le
      (I := I) (M := M) g₀ g₁ n h htie hδ_lt hδ_nn hδ
  exact ⟨Clower, hClower_nn, hbound⟩

private theorem armPrincipalSlotPairing_le_dirichlet_top
    [Nonempty M] (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : gFibreOpBound (I := I) g₀ h δ)
    (u₀ : SmoothCcTensor g₀ 0 2) :
    armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ ≤
      (δ / (1 - δ)) *
        ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀)‖ ^ 2 := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  set A : SmoothCcTensor g₀ 0 ((2 + n) + 1) :=
    iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀ with hA_def
  set B : SmoothCcTensor g₀ 0 ((2 + n) + 1) :=
    appCc (I := I) (M := M) g₀ ((2 + n) + 1) ((2 + n) + 1)
      (slotInsertEndoCc (I := I) (M := M) g₀ (2 + n)
        (gInvDiffRaisedEndoField (I := I) (M := M) g₀ g₁)) A with hB_def
  have hBfun : ∀ x : M,
      B.toFun x =
        TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
          (gInvDiffSlotApplied (I := I) g₀ g₁ (2 + n) x (A.toSection x)) := by
    intro x
    rfl
  have hWS_int : Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g₀ 0 ((2 + n) + 1) x
        (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x))
        (TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
          (negGInvDiffSlotApplied (I := I) g₀ g₁ (2 + n) x (A.toSection x))))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    have hcross := DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) (g := g₀) (r := 0) (s := (2 + n) + 1) A B
    have heq :
        (fun x => tensorInnerPointwise (I := I) (M := M) g₀ 0 ((2 + n) + 1) x
            (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x))
            (TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
              (negGInvDiffSlotApplied (I := I) g₀ g₁ (2 + n) x (A.toSection x))))
          = (fun x => - tensorInnerPointwise (I := I) (M := M) g₀ 0 ((2 + n) + 1) x
              (A.toFun x) (B.toFun x)) := by
      funext x
      rw [hBfun x, SmoothCcTensor.toFun_apply,
        toModel_negGInvDiffSlotApplied_eq (I := I) g₀ g₁ (2 + n) x (A.toSection x),
        show (- TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
              (gInvDiffSlotApplied (I := I) g₀ g₁ (2 + n) x (A.toSection x)))
            = (-1 : ℝ) • TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
              (gInvDiffSlotApplied (I := I) g₀ g₁ (2 + n) x (A.toSection x)) from
          (neg_one_smul ℝ _).symm,
        tensorInnerPointwise_smul_right]
      ring
    rw [heq]
    exact hcross.neg
  have hWW_int : Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g₀ 0 ((2 + n) + 1) x
        (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x))
        (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x)))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) (g := g₀) (r := 0) (s := (2 + n) + 1) A A
  have htool := DifferentialGeometry.Analysis.Sobolev.TensorHilbert.tensorL2Inner_slotΛ_le
    (I := I) (M := M) g₀ (2 + n) (κ := δ / (1 - δ))
    (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x))
    (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
      (negGInvDiffSlotApplied (I := I) g₀ g₁ (2 + n) x (A.toSection x)))
    (fun x => tensorInnerPointwise_negGInvDiffSlot_le
      (I := I) (M := M) g₀ g₁ h htie hδ_lt hδ_nn hδ (2 + n) x (A.toSection x))
    hWS_int hWW_int
  have hnorm :
      tensorL2Inner (I := I) (M := M) g₀ 0 ((2 + n) + 1)
          (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x))
          (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x)) =
        ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀)‖ ^ 2 := by
    have hAA : tensorL2Inner (I := I) (M := M) g₀ 0 ((2 + n) + 1) A.toFun A.toFun =
        (⟪A, A⟫_ℝ : ℝ) := (SmoothCcTensor.inner_def (I := I) (M := M) A A).symm
    rw [show (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x)) = A.toFun from rfl,
      hAA, real_inner_self_eq_norm_sq, SmoothCcTensor.norm_toL2]
  have hslot :
      armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ ≤
        (δ / (1 - δ)) *
          tensorL2Inner (I := I) (M := M) g₀ 0 ((2 + n) + 1)
            (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x))
            (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x)) := htool
  rw [hnorm] at hslot
  exact hslot

theorem edgeArm_slot_le [Nonempty M]
    (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : gFibreOpBound (I := I) g₀ h δ)
    (u₀ : SmoothCcTensor g₀ 0 2) :
    armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ ≤
      (δ / (1 - δ)) *
        ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀)‖ ^ 2 :=
  armPrincipalSlotPairing_le_dirichlet_top
    (I := I) (M := M) g₀ g₁ n h htie hδ_lt hδ_nn hδ u₀

private theorem dirichlet_top_le_spectral_add_lower
    [Nonempty M] (g₀ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∃ Cgap : ℝ, 0 ≤ Cgap ∧
      ∀ (u₀ : SmoothCcTensor g₀ 0 2),
        ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀)‖ ^ 2 ≤
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
            Cgap * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 :=
  exists_iteratedCovGrad_l2NormSq_le_smoothCcToTensorHs_succ_add_lower
    (I := I) (M := M) g₀ n

private theorem oneMinusConnLapIter_l2Inner_deTurckPrincipalCometricArm_le
    [Nonempty M] (g₀ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∀ (g₁ : SmoothRiemannianMetric I M)
      (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ),
      (∀ (y : M) (v w : TangentSpace I y),
        g₁.inner y v w = g₀.inner y v w + h y v w) →
      ∀ {δ : ℝ}, δ < 1 → 0 ≤ δ → gFibreOpBound (I := I) g₀ h δ →
      ∃ Clower : ℝ, 0 ≤ Clower ∧
        ∀ (u₀ : SmoothCcTensor g₀ 0 2),
          tensorL2Inner (I := I) (M := M) g₀ 0 2
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
              (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun ≤
            (δ / (1 - δ) + 1 / 4) *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
              Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 := by
  intro g₁ h htie δ hδ_lt hδ_nn hδ
  obtain ⟨rem, hsplit, Clower₁, hClower₁_nn, hrem⟩ :=
    oneMinusConnLapIter_pairing_fold (I := I) (M := M) g₀ g₁ n h htie hδ_lt hδ_nn hδ
  obtain ⟨Cgap, hCgap_nn, hgap⟩ :=
    dirichlet_top_le_spectral_add_lower (I := I) (M := M) g₀ n
  have hκ_nn : 0 ≤ δ / (1 - δ) := div_nonneg hδ_nn (by linarith)
  refine ⟨(δ / (1 - δ)) * Cgap + Clower₁, by positivity, fun u₀ => ?_⟩
  rw [hsplit u₀]
  have htop := armPrincipalSlotPairing_le_dirichlet_top
    (I := I) (M := M) g₀ g₁ n h htie hδ_lt hδ_nn hδ u₀
  have hg := hgap u₀
  have hr := hrem u₀
  have hMnp_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 :=
    sq_nonneg _
  have hstep : armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ ≤
      (δ / (1 - δ)) *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
        (δ / (1 - δ)) * Cgap *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 := by
    calc armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀
        ≤ (δ / (1 - δ)) *
            ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀)‖ ^ 2 := htop
      _ ≤ (δ / (1 - δ)) *
            (‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
              Cgap * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hg hκ_nn
      _ = (δ / (1 - δ)) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
          (δ / (1 - δ)) * Cgap *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 := by ring
  nlinarith [hstep, hr, hMnp_nn]

theorem deTurckPrincipalCometricArm_spectralPairing_tsum_le
    [Nonempty M] (g₀ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∀ (g₁ : SmoothRiemannianMetric I M)
      (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ),
      (∀ (y : M) (v w : TangentSpace I y),
        g₁.inner y v w = g₀.inner y v w + h y v w) →
      ∀ {δ : ℝ}, δ < 1 → 0 ≤ δ → gFibreOpBound (I := I) g₀ h δ →
      ∃ Clower : ℝ, 0 ≤ Clower ∧
        ∀ (u₀ : SmoothCcTensor g₀ 0 2),
          2 * ∑' i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g₀ 0 2,
              tensorSobolevWeight (I := I) (M := M) i ((n : ℕ) : ℝ) *
                ((smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀).coeff i *
                  (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ)
                    (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀)).coeff i) ≤
            2 * (δ / (1 - δ) + 1 / 4) *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
              Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 := by
  intro g₁ h htie δ hδ_lt hδ_nn hδ
  obtain ⟨Clower, hClower_nn, hbound⟩ :=
    oneMinusConnLapIter_l2Inner_deTurckPrincipalCometricArm_le
      (I := I) (M := M) g₀ n g₁ h htie hδ_lt hδ_nn hδ
  refine ⟨2 * Clower, by positivity, fun u₀ => ?_⟩
  have hpair :=
    spectralPairing_tsum_eq_oneMinusConnLapIter_l2Inner (I := I) (M := M) g₀ n u₀
      (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀)
  rw [hpair]
  have hb := hbound u₀
  have hgoal :
      2 * (δ / (1 - δ) + 1 / 4) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
          2 * Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 =
        2 * ((δ / (1 - δ) + 1 / 4) *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
            Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2) := by
    ring
  rw [hgoal]
  linarith [hb]

theorem two_mul_inner_smoothCcToTensorHs_deTurckPrincipalCometricArm_le
    [Nonempty M] (g₀ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∀ (g₁ : SmoothRiemannianMetric I M)
      (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ),
      (∀ (y : M) (v w : TangentSpace I y),
        g₁.inner y v w = g₀.inner y v w + h y v w) →
      ∀ {δ : ℝ}, δ < 1 → 0 ≤ δ → gFibreOpBound (I := I) g₀ h δ →
      ∃ Clower : ℝ, 0 ≤ Clower ∧
        ∀ (u₀ : SmoothCcTensor g₀ 0 2),
          2 * (inner ℝ (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀)
                (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ)
                  (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀)) : ℝ) ≤
            2 * (δ / (1 - δ) + 1 / 4) *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
              Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 := by
  intro g₁ h htie δ hδ_lt hδ_nn hδ
  obtain ⟨Clower, hClower_nn, hbound⟩ :=
    deTurckPrincipalCometricArm_spectralPairing_tsum_le (I := I) (M := M) g₀ n
      g₁ h htie hδ_lt hδ_nn hδ
  refine ⟨Clower, hClower_nn, fun u₀ => ?_⟩
  have hinner :
      (inner ℝ (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀)
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ)
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀)) : ℝ) =
        ∑' i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 2,
            tensorSobolevWeight (I := I) (M := M) i ((n : ℕ) : ℝ) *
              ((smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀).coeff i *
                (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ)
                  (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀)).coeff i) :=
    tensorHs.inner_def (I := I) (M := M)
      (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀)
      (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ)
        (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀))
  rw [hinner]
  exact hbound u₀

theorem two_mul_inner_smoothCcToTensorHs_deTurckPrincipalCometricArm_lt_one
    [Nonempty M] (g₀ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∀ (g₁ : SmoothRiemannianMetric I M)
      (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ),
      (∀ (y : M) (v w : TangentSpace I y),
        g₁.inner y v w = g₀.inner y v w + h y v w) →
      ∀ {δ : ℝ}, δ ≤ 1 / 3 → 0 ≤ δ → gFibreOpBound (I := I) g₀ h δ →
      ∃ Cupper Clower : ℝ, Cupper < 1 ∧ 0 ≤ Cupper ∧ 0 ≤ Clower ∧
        ∀ (u₀ : SmoothCcTensor g₀ 0 2),
          2 * (inner ℝ (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀)
                (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ)
                  (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀)) : ℝ) ≤
            2 * Cupper *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
              Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 := by
  intro g₁ h htie δ hδ_le hδ_nn hδ
  have hδ_lt : δ < 1 := by linarith
  obtain ⟨Clower, hClower_nn, hbound⟩ :=
    two_mul_inner_smoothCcToTensorHs_deTurckPrincipalCometricArm_le
      (I := I) (M := M) g₀ n g₁ h htie hδ_lt hδ_nn hδ
  have hone_sub : (0 : ℝ) < 1 - δ := by linarith
  have hκ_le : δ / (1 - δ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hone_sub]
    linarith
  refine ⟨δ / (1 - δ) + 1 / 4, Clower, by linarith, by positivity, hClower_nn, hbound⟩

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end

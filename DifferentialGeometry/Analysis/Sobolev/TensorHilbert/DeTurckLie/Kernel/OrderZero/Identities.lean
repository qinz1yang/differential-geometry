import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference.ConnectionBicontraction
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovDerivConnectionDifferenceQuadraticBound
import DifferentialGeometry.Analysis.Sobolev.Embedding.ConvexPerturbationPointwiseC2
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.MetricPerturbationPath.Basic
import DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.FiberNormUniformBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Tensor02FiberNormBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SingleSlotOperatorFiberNormBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.ArmCoefficient.ReindexingNorm
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.JetProductIntegral
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradFibreNormPermutationInvariance
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckLinearization
import DifferentialGeometry.Geometry.Metric.DeTurck.ConnectionDifference
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.BracketDivergenceForm
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section


open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle
    ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (connectionDifferenceCovDerivBiContrFib deTurckLieConnectionDifferenceDerivativeBiContrFib_contMDiff deTurckLieCovariantDerivativeInsertionFib deTurckLieCovariantDerivativeInsertionFib_contMDiff
    deTurckLieFib deTurckLieCoeffField deTurckLieCoeffField_toSection
    deTurckConnectionDifferenceCovDeriv connectionDifference_pairing_mdiffAt connectionDifferenceCovDerivOp deTurckLieConnectionDifferenceDerivativeCovKernel_apply_extend)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def deTurckLieConnectionDifferenceDerivCoeffField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (connectionDifferenceCovDerivBiContrFib (I := I) g₁ g_bg x))
      contMDiff_toFun := deTurckLieConnectionDifferenceDerivativeBiContrFib_contMDiff (I := I) g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
@[simp] theorem deTurckLieConnectionDifferenceDerivCoeffField_toSection
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (connectionDifferenceCovDerivBiContrFib (I := I) g₁ g_bg x)) := rfl

def deTurckLieCovariantDerivativeInsertionField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (deTurckLieCovariantDerivativeInsertionFib (I := I) g₁ g_bg x))
      contMDiff_toFun := deTurckLieCovariantDerivativeInsertionFib_contMDiff (I := I) g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] theorem deTurckLieCovariantDerivativeInsertionField_toSection
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (deTurckLieCovariantDerivativeInsertionFib (I := I) g₁ g_bg x)) := rfl

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem deTurckLieConnectionDifferenceDerivCoeffField_add_deTurckLieCovariantDerivativeInsertionField
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg +
        deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g₀ g₁ g_bg =
      deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    deTurckLieConnectionDifferenceDerivCoeffField_toSection, deTurckLieCovariantDerivativeInsertionField_toSection,
    deTurckLieCoeffField_toSection]
  rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem connectionDifference_cocycle (gA gB gC : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    PDE.DeTurck.connectionDifference (I := I) gA gB x u v + PDE.DeTurck.connectionDifference (I := I) gB gC x u v =
      PDE.DeTurck.connectionDifference (I := I) gA gC x u v := by
  classical
  have hσ := smoothExtensionTangent_mdiff (I := I) x u x
  have hu : smoothExtensionTangent (I := I) x u x = u :=
    smoothExtensionTangent_eq (I := I) x u
  rw [← hu]
  rw [PDE.DeTurck.connectionDifference_apply (I := I) gA gB hσ v,
    PDE.DeTurck.connectionDifference_apply (I := I) gB gC hσ v,
    PDE.DeTurck.connectionDifference_apply (I := I) gA gC hσ v]
  abel

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckLieCovariantDerivativeA_backgroundSplit
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (X P Q : Π b : M, TangentSpace I b) (x : M)
    (hP : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (P b)) x)
    (hQ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (Q b)) x) :
    deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg X P Q x =
      covDerivConnectionDifference (I := I) g₀ g₁ X Q P x
        - covDerivConnectionDifference (I := I) g₀ g_bg X Q P x
        + PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
            (PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (P x) (Q x)) (X x)
        - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x
            (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (P x) (X x)) (Q x)
        - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (P x)
            (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (Q x) (X x)) := by
  classical
  have hσ := connectionDifference_pairing_mdiffAt (I := I) g₁ g_bg hP hQ
  have hσB := connectionDifference_pairing_mdiffAt (I := I) g_bg g₀ hP hQ
  have hsum : (fun b : M => PDE.DeTurck.connectionDifference (I := I) g₁ g₀ b (P b) (Q b)) =
      (fun b : M => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (P b) (Q b))
        + (fun b : M => PDE.DeTurck.connectionDifference (I := I) g_bg g₀ b (P b) (Q b)) := by
    funext b
    change PDE.DeTurck.connectionDifference (I := I) g₁ g₀ b (P b) (Q b) =
      PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (P b) (Q b)
        + PDE.DeTurck.connectionDifference (I := I) g_bg g₀ b (P b) (Q b)
    exact (connectionDifference_cocycle (I := I) g₁ g_bg g₀ b (P b) (Q b)).symm
  have hadd := (LeviCivita (I := I) g₀).isCovariantDerivativeOnUniv.add
    (σ := fun b : M => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (P b) (Q b))
    (σ' := fun b : M => PDE.DeTurck.connectionDifference (I := I) g_bg g₀ b (P b) (Q b)) hσ hσB
  have hsplit : (LeviCivita (I := I) g₀).toFun
      (fun b : M => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (P b) (Q b)) x (X x)
      = (LeviCivita (I := I) g₀).toFun
          (fun b : M => PDE.DeTurck.connectionDifference (I := I) g₁ g₀ b (P b) (Q b)) x (X x)
        - (LeviCivita (I := I) g₀).toFun
          (fun b : M => PDE.DeTurck.connectionDifference (I := I) g_bg g₀ b (P b) (Q b)) x (X x) := by
    have h3 : (LeviCivita (I := I) g₀).toFun
        (fun b : M => PDE.DeTurck.connectionDifference (I := I) g₁ g₀ b (P b) (Q b)) x (X x)
        = (LeviCivita (I := I) g₀).toFun
            (fun b : M => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (P b) (Q b)) x (X x)
          + (LeviCivita (I := I) g₀).toFun
            (fun b : M => PDE.DeTurck.connectionDifference (I := I) g_bg g₀ b (P b) (Q b)) x (X x) := by
      rw [hsum]
      have h2 := congrArg (fun L => L (X x)) hadd
      simpa using h2
    rw [h3]
    abel
  have hout' : (LeviCivita (I := I) g₁).toFun
      (fun b : M => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (P b) (Q b)) x (X x)
      = (LeviCivita (I := I) g₀).toFun
          (fun b : M => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (P b) (Q b)) x (X x)
        + PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
            (PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (P x) (Q x)) (X x) := by
    have h : PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
        (PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (P x) (Q x)) (X x)
        = (LeviCivita (I := I) g₁).toFun
            (fun b : M => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (P b) (Q b)) x (X x)
          - (LeviCivita (I := I) g₀).toFun
            (fun b : M => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (P b) (Q b)) x (X x) :=
      PDE.DeTurck.connectionDifference_apply (I := I) g₁ g₀ (σ := fun b : M =>
        PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (P b) (Q b)) hσ (X x)
    rw [h]
    abel
  have hinnP' : (LeviCivita (I := I) g₁).toFun P x (X x)
      = (LeviCivita (I := I) g₀).toFun P x (X x)
        + PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (P x) (X x) := by
    have h : PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (P x) (X x)
        = (LeviCivita (I := I) g₁).toFun P x (X x)
          - (LeviCivita (I := I) g₀).toFun P x (X x) :=
      PDE.DeTurck.connectionDifference_apply (I := I) g₁ g₀ (σ := P) hP (X x)
    rw [h]
    abel
  have hinnQ' : (LeviCivita (I := I) g₁).toFun Q x (X x)
      = (LeviCivita (I := I) g₀).toFun Q x (X x)
        + PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (Q x) (X x) := by
    have h : PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (Q x) (X x)
        = (LeviCivita (I := I) g₁).toFun Q x (X x)
          - (LeviCivita (I := I) g₀).toFun Q x (X x) :=
      PDE.DeTurck.connectionDifference_apply (I := I) g₁ g₀ (σ := Q) hQ (X x)
    rw [h]
    abel
  have hsplitT2 : PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x
      ((LeviCivita (I := I) g₀).toFun P x (X x)
        + PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (P x) (X x)) (Q x)
      = PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x
          ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x)
        + PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x
            (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (P x) (X x)) (Q x) := by
    rw [map_add]
    rfl
  have hsplitT3 : PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (P x)
      ((LeviCivita (I := I) g₀).toFun Q x (X x)
        + PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (Q x) (X x))
      = PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (P x)
          ((LeviCivita (I := I) g₀).toFun Q x (X x))
        + PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (P x)
            (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (Q x) (X x)) :=
    map_add _ _ _
  have hT2c : PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x
      ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x)
      = PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
          ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x)
        - PDE.DeTurck.connectionDifference (I := I) g_bg g₀ x
            ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x) := by
    have h := connectionDifference_cocycle (I := I) g₁ g_bg g₀ x
      ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x)
    rw [← h]
    abel
  have hT3c : PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (P x)
      ((LeviCivita (I := I) g₀).toFun Q x (X x))
      = PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (P x)
          ((LeviCivita (I := I) g₀).toFun Q x (X x))
        - PDE.DeTurck.connectionDifference (I := I) g_bg g₀ x (P x)
            ((LeviCivita (I := I) g₀).toFun Q x (X x)) := by
    have h := connectionDifference_cocycle (I := I) g₁ g_bg g₀ x (P x)
      ((LeviCivita (I := I) g₀).toFun Q x (X x))
    rw [← h]
    abel
  have hA : covDerivConnectionDifference (I := I) g₀ g₁ X Q P x
      = (LeviCivita (I := I) g₀).toFun
          (fun b : M => PDE.DeTurck.connectionDifference (I := I) g₁ g₀ b (P b) (Q b)) x (X x)
        - PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (P x)
            ((LeviCivita (I := I) g₀).toFun Q x (X x))
        - PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
            ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x) := rfl
  have hB : covDerivConnectionDifference (I := I) g₀ g_bg X Q P x
      = (LeviCivita (I := I) g₀).toFun
          (fun b : M => PDE.DeTurck.connectionDifference (I := I) g_bg g₀ b (P b) (Q b)) x (X x)
        - PDE.DeTurck.connectionDifference (I := I) g_bg g₀ x (P x)
            ((LeviCivita (I := I) g₀).toFun Q x (X x))
        - PDE.DeTurck.connectionDifference (I := I) g_bg g₀ x
            ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x) := rfl
  change (LeviCivita (I := I) g₁).toFun
      (fun b : M => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (P b) (Q b)) x (X x)
      - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x
          ((LeviCivita (I := I) g₁).toFun P x (X x)) (Q x)
      - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (P x)
          ((LeviCivita (I := I) g₁).toFun Q x (X x)) = _
  rw [hout', hinnP', hinnQ', hsplitT2, hsplitT3, hT2c, hT3c, hsplit, hA, hB]
  abel

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckLieConnectionDifferenceDerivativeCovKernel_backgroundSplit (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v0 p q : TangentSpace I x) :
    connectionDifferenceCovDerivOp (I := I) g₁ g_bg x v0 p q =
      covDerivConnectionDifference (I := I) g₀ g₁
          (smoothExtensionTangent (I := I) x v0)
          (smoothExtensionTangent (I := I) x q)
          (smoothExtensionTangent (I := I) x p) x
        - covDerivConnectionDifference (I := I) g₀ g_bg
            (smoothExtensionTangent (I := I) x v0)
            (smoothExtensionTangent (I := I) x q)
            (smoothExtensionTangent (I := I) x p) x
        + PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
            (PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x p q) v0
        - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x
            (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x p v0) q
        - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x p
            (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x q v0) := by
  rw [deTurckLieConnectionDifferenceDerivativeCovKernel_apply_extend (I := I) g₁ g_bg x v0 p q]
  rw [deTurckLieCovariantDerivativeA_backgroundSplit (I := I) g₀ g₁ g_bg
    (smoothExtensionTangent (I := I) x v0)
    (smoothExtensionTangent (I := I) x p)
    (smoothExtensionTangent (I := I) x q) x
    (smoothExtensionTangent_mdiff (I := I) x p x)
    (smoothExtensionTangent_mdiff (I := I) x q x)]
  simp only [smoothExtensionTangent_eq]

open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (metricPerturbationPath convexPerturbation metricPerturbationPath_inner_of_mem convexPerturbation_gFibreOpBound_abs
    abs_convex_smallConstant_lt_one metricPerturbationPathDomain)
open DifferentialGeometry.Analysis.Laplacian
  (metric_inner_cauchy_schwarz_sq)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (covGrad connectionDifference_gFibreNorm_le_iteratedCovGrad_of_lt_one deTurckLieConnectionDifferenceDerivativeBiContrFibFixedFrame_toModel)
open DifferentialGeometry.Geometry.Curvature
  (exists_covDerivConnectionDifference_gQuadratic_le_of_jetEnvelope
    abs_tensor_one_three_flat_eval_le_fibreNorm_mul_sqrt)
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
  (g0FlatCLM cotangentToDual_g0FlatCLM g0FlatCLM_apply)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem abs_metric_inner_le (g : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    |g.inner x u v| ≤ Real.sqrt (g.inner x u u) * Real.sqrt (g.inner x v v) := by
  have h2 := metric_inner_cauchy_schwarz_sq (I := I) (M := M) g x u v
  have habs : |g.inner x u v| = Real.sqrt ((g.inner x u v) ^ 2) :=
    (Real.sqrt_sq_eq_abs _).symm
  rw [habs]
  refine le_trans (Real.sqrt_le_sqrt h2) ?_
  rw [Real.sqrt_mul (metric_inner_self_nonneg (I := I) (M := M) g x u)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem sqrt_metric_inner_add_le (g : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    Real.sqrt (g.inner x (u + v) (u + v)) ≤
      Real.sqrt (g.inner x u u) + Real.sqrt (g.inner x v v) := by
  have huu := metric_inner_self_nonneg (I := I) (M := M) g x u
  have hvv := metric_inner_self_nonneg (I := I) (M := M) g x v
  have hexp : g.inner x (u + v) (u + v) =
      g.inner x u u + g.inner x u v + (g.inner x v u + g.inner x v v) := by
    simp only [map_add, add_apply]
    ring
  have hsymm : g.inner x v u = g.inner x u v := g.symm x v u
  have hcs := abs_metric_inner_le (I := I) (M := M) g x u v
  have hsq : g.inner x (u + v) (u + v) ≤
      (Real.sqrt (g.inner x u u) + Real.sqrt (g.inner x v v)) ^ 2 := by
    rw [hexp, hsymm]
    have h1 := Real.sq_sqrt huu
    have h2 := Real.sq_sqrt hvv
    have h3 := abs_le.mp hcs
    nlinarith [h3.2, Real.sqrt_nonneg (g.inner x u u), Real.sqrt_nonneg (g.inner x v v)]
  refine le_trans (Real.sqrt_le_sqrt hsq) ?_
  rw [Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem sqrt_metric_inner_sub_le (g : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    Real.sqrt (g.inner x (u - v) (u - v)) ≤
      Real.sqrt (g.inner x u u) + Real.sqrt (g.inner x v v) := by
  have hneg : g.inner x (-v) (-v) = g.inner x v v := by
    simp only [map_neg, neg_apply, neg_neg]
  have h := sqrt_metric_inner_add_le (I := I) (M := M) g x u (-v)
  rw [← sub_eq_add_neg] at h
  rw [hneg] at h
  exact h

end DifferentialGeometry.Analysis.Sobolev

end

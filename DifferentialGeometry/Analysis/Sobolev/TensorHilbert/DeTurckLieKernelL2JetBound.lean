import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Geometry.Curvature.CovDerivConnDiffQuadraticBound
import DifferentialGeometry.Analysis.Sobolev.Embedding.ConvexPerturbationPointwiseC2
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValue
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.RiemannianFiberNormSqRiemannOpDualFrameParseval
import DifferentialGeometry.Geometry.Connection.SingleSlotOperatorFiberNormBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradFibreNormPermutationInvariance
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckLinearization
import DifferentialGeometry.Geometry.Flow.DeTurckVFConnDiffVariation
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.BracketDivergenceForm

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (dLaBiContrFib dLaBiContrFib_contMDiff deTurckLieDLbFib deTurckLieDLbFib_contMDiff
    deTurckLieFib deTurckLieCoeffField deTurckLieCoeffField_toSection
    deTurckLieCovDerivA connDiff_pairing_mdiffAt dLaCovKernel dLaCovKernel_apply_extend)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def deTurckLieDLaCoeffField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (dLaBiContrFib (I := I) g₁ g_bg x))
      contMDiff_toFun := dLaBiContrFib_contMDiff (I := I) g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
@[simp] theorem deTurckLieDLaCoeffField_toSection
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (deTurckLieDLaCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (dLaBiContrFib (I := I) g₁ g_bg x)) := rfl

def deTurckLieDLbCoeffField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (deTurckLieDLbFib (I := I) g₁ g_bg x))
      contMDiff_toFun := deTurckLieDLbFib_contMDiff (I := I) g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
@[simp] theorem deTurckLieDLbCoeffField_toSection
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (deTurckLieDLbFib (I := I) g₁ g_bg x)) := rfl

set_option linter.unusedSectionVars false in
theorem deTurckLieDLaCoeffField_add_deTurckLieDLbCoeffField
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieDLaCoeffField (I := I) (M := M) g₀ g₁ g_bg +
        deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg =
      deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    deTurckLieDLaCoeffField_toSection, deTurckLieDLbCoeffField_toSection,
    deTurckLieCoeffField_toSection]
  rfl

set_option linter.unusedSectionVars false in
theorem connDiff_cocycle (gA gB gC : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    PDE.DeTurck.connDiff (I := I) gA gB x u v + PDE.DeTurck.connDiff (I := I) gB gC x u v =
      PDE.DeTurck.connDiff (I := I) gA gC x u v := by
  classical
  have hσ := smoothExtensionTangent_mdiff (I := I) x u x
  have hu : smoothExtensionTangent (I := I) x u x = u :=
    smoothExtensionTangent_eq (I := I) x u
  rw [← hu]
  rw [PDE.DeTurck.connDiff_apply (I := I) gA gB hσ v,
    PDE.DeTurck.connDiff_apply (I := I) gB gC hσ v,
    PDE.DeTurck.connDiff_apply (I := I) gA gC hσ v]
  abel

set_option linter.unusedSectionVars false in
theorem deTurckLieCovDerivA_backgroundSplit
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (X P Q : Π b : M, TangentSpace I b) (x : M)
    (hP : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (P b)) x)
    (hQ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (Q b)) x) :
    deTurckLieCovDerivA (I := I) g₁ g_bg X P Q x =
      covDerivConnDiff (I := I) g₀ g₁ X Q P x
        - covDerivConnDiff (I := I) g₀ g_bg X Q P x
        + PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (PDE.DeTurck.connDiff (I := I) g₁ g_bg x (P x) (Q x)) (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (P x) (X x)) (Q x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (P x)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Q x) (X x)) := by
  classical
  have hσ := connDiff_pairing_mdiffAt (I := I) g₁ g_bg hP hQ
  have hσB := connDiff_pairing_mdiffAt (I := I) g_bg g₀ hP hQ
  have hsum : (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (P b) (Q b)) =
      (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (P b) (Q b))
        + (fun b : M => PDE.DeTurck.connDiff (I := I) g_bg g₀ b (P b) (Q b)) := by
    funext b
    change PDE.DeTurck.connDiff (I := I) g₁ g₀ b (P b) (Q b) =
      PDE.DeTurck.connDiff (I := I) g₁ g_bg b (P b) (Q b)
        + PDE.DeTurck.connDiff (I := I) g_bg g₀ b (P b) (Q b)
    exact (connDiff_cocycle (I := I) g₁ g_bg g₀ b (P b) (Q b)).symm
  have hadd := (LeviCivita (I := I) g₀).isCovariantDerivativeOnUniv.add
    (σ := fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (P b) (Q b))
    (σ' := fun b : M => PDE.DeTurck.connDiff (I := I) g_bg g₀ b (P b) (Q b)) hσ hσB
  have hsplit : (LeviCivita (I := I) g₀).toFun
      (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (P b) (Q b)) x (X x)
      = (LeviCivita (I := I) g₀).toFun
          (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (P b) (Q b)) x (X x)
        - (LeviCivita (I := I) g₀).toFun
          (fun b : M => PDE.DeTurck.connDiff (I := I) g_bg g₀ b (P b) (Q b)) x (X x) := by
    have h3 : (LeviCivita (I := I) g₀).toFun
        (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (P b) (Q b)) x (X x)
        = (LeviCivita (I := I) g₀).toFun
            (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (P b) (Q b)) x (X x)
          + (LeviCivita (I := I) g₀).toFun
            (fun b : M => PDE.DeTurck.connDiff (I := I) g_bg g₀ b (P b) (Q b)) x (X x) := by
      rw [hsum]
      have h2 := congrArg (fun L => L (X x)) hadd
      simpa using h2
    rw [h3]
    abel
  have hout' : (LeviCivita (I := I) g₁).toFun
      (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (P b) (Q b)) x (X x)
      = (LeviCivita (I := I) g₀).toFun
          (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (P b) (Q b)) x (X x)
        + PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (PDE.DeTurck.connDiff (I := I) g₁ g_bg x (P x) (Q x)) (X x) := by
    have h : PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g_bg x (P x) (Q x)) (X x)
        = (LeviCivita (I := I) g₁).toFun
            (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (P b) (Q b)) x (X x)
          - (LeviCivita (I := I) g₀).toFun
            (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (P b) (Q b)) x (X x) :=
      PDE.DeTurck.connDiff_apply (I := I) g₁ g₀ (σ := fun b : M =>
        PDE.DeTurck.connDiff (I := I) g₁ g_bg b (P b) (Q b)) hσ (X x)
    rw [h]
    abel
  have hinnP' : (LeviCivita (I := I) g₁).toFun P x (X x)
      = (LeviCivita (I := I) g₀).toFun P x (X x)
        + PDE.DeTurck.connDiff (I := I) g₁ g₀ x (P x) (X x) := by
    have h : PDE.DeTurck.connDiff (I := I) g₁ g₀ x (P x) (X x)
        = (LeviCivita (I := I) g₁).toFun P x (X x)
          - (LeviCivita (I := I) g₀).toFun P x (X x) :=
      PDE.DeTurck.connDiff_apply (I := I) g₁ g₀ (σ := P) hP (X x)
    rw [h]
    abel
  have hinnQ' : (LeviCivita (I := I) g₁).toFun Q x (X x)
      = (LeviCivita (I := I) g₀).toFun Q x (X x)
        + PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Q x) (X x) := by
    have h : PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Q x) (X x)
        = (LeviCivita (I := I) g₁).toFun Q x (X x)
          - (LeviCivita (I := I) g₀).toFun Q x (X x) :=
      PDE.DeTurck.connDiff_apply (I := I) g₁ g₀ (σ := Q) hQ (X x)
    rw [h]
    abel
  have hsplitT2 : PDE.DeTurck.connDiff (I := I) g₁ g_bg x
      ((LeviCivita (I := I) g₀).toFun P x (X x)
        + PDE.DeTurck.connDiff (I := I) g₁ g₀ x (P x) (X x)) (Q x)
      = PDE.DeTurck.connDiff (I := I) g₁ g_bg x
          ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x)
        + PDE.DeTurck.connDiff (I := I) g₁ g_bg x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (P x) (X x)) (Q x) := by
    rw [map_add]
    rfl
  have hsplitT3 : PDE.DeTurck.connDiff (I := I) g₁ g_bg x (P x)
      ((LeviCivita (I := I) g₀).toFun Q x (X x)
        + PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Q x) (X x))
      = PDE.DeTurck.connDiff (I := I) g₁ g_bg x (P x)
          ((LeviCivita (I := I) g₀).toFun Q x (X x))
        + PDE.DeTurck.connDiff (I := I) g₁ g_bg x (P x)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Q x) (X x)) :=
    map_add _ _ _
  have hT2c : PDE.DeTurck.connDiff (I := I) g₁ g_bg x
      ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x)
      = PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x)
        - PDE.DeTurck.connDiff (I := I) g_bg g₀ x
            ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x) := by
    have h := connDiff_cocycle (I := I) g₁ g_bg g₀ x
      ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x)
    rw [← h]
    abel
  have hT3c : PDE.DeTurck.connDiff (I := I) g₁ g_bg x (P x)
      ((LeviCivita (I := I) g₀).toFun Q x (X x))
      = PDE.DeTurck.connDiff (I := I) g₁ g₀ x (P x)
          ((LeviCivita (I := I) g₀).toFun Q x (X x))
        - PDE.DeTurck.connDiff (I := I) g_bg g₀ x (P x)
            ((LeviCivita (I := I) g₀).toFun Q x (X x)) := by
    have h := connDiff_cocycle (I := I) g₁ g_bg g₀ x (P x)
      ((LeviCivita (I := I) g₀).toFun Q x (X x))
    rw [← h]
    abel
  have hA : covDerivConnDiff (I := I) g₀ g₁ X Q P x
      = (LeviCivita (I := I) g₀).toFun
          (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (P b) (Q b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (P x)
            ((LeviCivita (I := I) g₀).toFun Q x (X x))
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x) := rfl
  have hB : covDerivConnDiff (I := I) g₀ g_bg X Q P x
      = (LeviCivita (I := I) g₀).toFun
          (fun b : M => PDE.DeTurck.connDiff (I := I) g_bg g₀ b (P b) (Q b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) g_bg g₀ x (P x)
            ((LeviCivita (I := I) g₀).toFun Q x (X x))
        - PDE.DeTurck.connDiff (I := I) g_bg g₀ x
            ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x) := rfl
  change (LeviCivita (I := I) g₁).toFun
      (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (P b) (Q b)) x (X x)
      - PDE.DeTurck.connDiff (I := I) g₁ g_bg x
          ((LeviCivita (I := I) g₁).toFun P x (X x)) (Q x)
      - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (P x)
          ((LeviCivita (I := I) g₁).toFun Q x (X x)) = _
  rw [hout', hinnP', hinnQ', hsplitT2, hsplitT3, hT2c, hT3c, hsplit, hA, hB]
  abel

set_option linter.unusedSectionVars false in
theorem dLaCovKernel_backgroundSplit (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v0 p q : TangentSpace I x) :
    dLaCovKernel (I := I) g₁ g_bg x v0 p q =
      covDerivConnDiff (I := I) g₀ g₁
          (smoothExtensionTangent (I := I) x v0)
          (smoothExtensionTangent (I := I) x q)
          (smoothExtensionTangent (I := I) x p) x
        - covDerivConnDiff (I := I) g₀ g_bg
            (smoothExtensionTangent (I := I) x v0)
            (smoothExtensionTangent (I := I) x q)
            (smoothExtensionTangent (I := I) x p) x
        + PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (PDE.DeTurck.connDiff (I := I) g₁ g_bg x p q) v0
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v0) q
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x p
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0) := by
  rw [dLaCovKernel_apply_extend (I := I) g₁ g_bg x v0 p q]
  rw [deTurckLieCovDerivA_backgroundSplit (I := I) g₀ g₁ g_bg
    (smoothExtensionTangent (I := I) x v0)
    (smoothExtensionTangent (I := I) x p)
    (smoothExtensionTangent (I := I) x q) x
    (smoothExtensionTangent_mdiff (I := I) x p x)
    (smoothExtensionTangent_mdiff (I := I) x q x)]
  simp only [smoothExtensionTangent_eq]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (realizedFam convexPerturbation realizedFam_inner_of_mem convexPerturbation_gFibreOpBound_abs
    abs_convex_smallConstant_lt_one realizedSmallSet)
open DifferentialGeometry.Analysis.Laplacian (metric_inner_self_nonneg metric_inner_cauchy_schwarz_sq)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (covGrad connDiff_gFibreNorm_le_iteratedCovGrad_of_lt_one dLaBiContrFibFixedFrame_toModel)
open DifferentialGeometry.Geometry.Curvature
  (exists_covDerivConnDiff_gQuadratic_le_of_jetEnvelope abs_tensor13_flat_eval_le_fibreNorm_mul_sqrt)
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
  (g0FlatCLM cotangentToDual_g0FlatCLM g0FlatCLM_apply)

set_option linter.unusedSectionVars false in
private theorem abs_metric_inner_le (g : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    |g.inner x u v| ≤ Real.sqrt (g.inner x u u) * Real.sqrt (g.inner x v v) := by
  have h2 := metric_inner_cauchy_schwarz_sq (I := I) (M := M) g x u v
  have habs : |g.inner x u v| = Real.sqrt ((g.inner x u v) ^ 2) :=
    (Real.sqrt_sq_eq_abs _).symm
  rw [habs]
  refine le_trans (Real.sqrt_le_sqrt h2) ?_
  rw [Real.sqrt_mul (metric_inner_self_nonneg (I := I) (M := M) g x u)]

set_option linter.unusedSectionVars false in
private theorem sqrt_metric_inner_add_le (g : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    Real.sqrt (g.inner x (u + v) (u + v)) ≤
      Real.sqrt (g.inner x u u) + Real.sqrt (g.inner x v v) := by
  have huu := metric_inner_self_nonneg (I := I) (M := M) g x u
  have hvv := metric_inner_self_nonneg (I := I) (M := M) g x v
  have hexp : g.inner x (u + v) (u + v) =
      g.inner x u u + g.inner x u v + (g.inner x v u + g.inner x v v) := by
    simp only [map_add, ContinuousLinearMap.add_apply]
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

set_option linter.unusedSectionVars false in
private theorem sqrt_metric_inner_sub_le (g : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    Real.sqrt (g.inner x (u - v) (u - v)) ≤
      Real.sqrt (g.inner x u u) + Real.sqrt (g.inner x v v) := by
  have hneg : g.inner x (-v) (-v) = g.inner x v v := by
    simp only [map_neg, ContinuousLinearMap.neg_apply, neg_neg]
  have h := sqrt_metric_inner_add_le (I := I) (M := M) g x u (-v)
  rw [← sub_eq_add_neg] at h
  rw [hneg] at h
  exact h

set_option linter.unusedSectionVars false in
private theorem gFibreOpBound_mono_of_le (g₀ : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    {δ δ' : ℝ} (hle : δ ≤ δ')
    (hb : gFibreOpBound (I := I) (M := M) g₀ h δ) :
    gFibreOpBound (I := I) (M := M) g₀ h δ' := by
  intro y a b
  refine le_trans (hb y a b) ?_
  have hnn : 0 ≤ Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc δ * Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b)
      = δ * (Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b)) := by ring
    _ ≤ δ' * (Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b)) :=
        mul_le_mul_of_nonneg_right hle hnn
    _ = δ' * Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b) := by ring

set_option linter.unusedSectionVars false in
private theorem abs_g1_inner_le_two_sqrt (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    {δs : ℝ} (hδs1 : δs ≤ 1)
    (hb : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δs)
    (x : M) (u w : TangentSpace I x) :
    |g₁.inner x u w| ≤
      2 * (Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x w w)) := by
  rw [htie x u w]
  refine le_trans (abs_add_le _ _) ?_
  have h1 := abs_metric_inner_le (I := I) (M := M) g₀ x u w
  have h2 := hb x u w
  have hnn : 0 ≤ Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x w w) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [h1, h2, hnn]

set_option linter.unusedSectionVars false in
private theorem coframeS_one_eq_g0FlatCLM_local
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K : Fin 1 → Fin n) :
    coframeS (I := I) (M := M) g₀ x 1 e K = g0FlatCLM (I := I) g₀ x (e (K 0)) := by
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply, cotangentToDual_apply,
    cotangentToDual_apply]
  rw [show coframeS (I := I) (M := M) g₀ x 1 e K (fun _ : Fin 1 => w) =
      ∏ k : Fin 1, g₀.inner x (e (K k)) w from coframeS_apply (I := I) (M := M) g₀ x 1 e K _]
  rw [Fin.prod_univ_one]
  rw [g0FlatCLM_apply, dualToCotangent_apply]
  rfl

set_option linter.unusedSectionVars false in
private theorem toModel_coframeS_two (g₀ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K : Fin 2 → Fin n)
    (p q : TangentSpace I x) :
    Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 2 e K) ![(p : E), (q : E)] =
      g₀.inner x (e (K 0)) p * g₀.inner x (e (K 1)) q := by
  rw [show Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 2 e K) ![(p : E), (q : E)] =
      coframeS (I := I) (M := M) g₀ x 2 e K ![p, q] from rfl]
  rw [coframeS_apply (I := I) (M := M) g₀ x 2 e K ![p, q], Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

set_option linter.unusedSectionVars false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
private theorem abs_tensor12_flat_eval_le_fibreNorm_mul_sqrt_local
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (W : TensorRSSpace 1 2 I x) (d a b : TangentSpace I x) :
    letI : Bundle.RiemannianBundle
        (fun y : M => Tensor0SBundle.TensorRSSpace 1 2 I y) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 1 2
    |Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
          (g0FlatCLM (I := I) g₀ x d))
        (Fin.cons a ![b])| ≤
      ‖(W : Tensor0SBundle.TensorRSSpace 1 2 I x)‖ *
        Real.sqrt (g₀.inner x d d) *
        Real.sqrt (g₀.inner x a a) * Real.sqrt (g₀.inner x b b) := by
  classical
  letI instTens : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 1 2 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 1 2
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr, _hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  set vec : Fin 2 → TangentSpace I x := ![a, b] with hvec_def
  set coef : (Fin 1 → Fin n) × (Fin 2 → Fin n) → ℝ :=
    fun p => g₀.inner x (e (p.1 0)) d * ∏ i : Fin 2, g₀.inner x (e (p.2 i)) (vec i) with hcoef_def
  set comp : (Fin 1 → Fin n) × (Fin 2 → Fin n) → ℝ :=
    fun p => fiberNormSqComponent (I := I) (M := M) g₀ x 1 2 W n e p.1 p.2 with hcomp_def
  have hcompval : ∀ (K : Fin 1 → Fin n) (J : Fin 2 → Fin n),
      fiberNormSqComponent (I := I) (M := M) g₀ x 1 2 W n e K J =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
            (g0FlatCLM (I := I) g₀ x (e (K 0))))
          (fun i : Fin 2 => e (J i)) := by
    intro K J
    rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 1 2 W n e K J =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
            (coframeS (I := I) (M := M) g₀ x 1 e K))
          (fun i : Fin 2 => e (J i)) from rfl]
    rw [coframeS_one_eq_g0FlatCLM_local (I := I) (M := M) g₀ x e K]
  have hWd : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
        (g0FlatCLM (I := I) g₀ x d) =
      ∑ k : Fin n, g₀.inner x (e k) d •
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
          (g0FlatCLM (I := I) g₀ x (e k)) := by
    have hflat : g0FlatCLM (I := I) g₀ x d =
        ∑ k : Fin n, g₀.inner x (e k) d • g0FlatCLM (I := I) g₀ x (e k) := by
      conv_lhs => rw [hrepr d]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [map_smul]
    rw [hflat, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_smul]
  have hexp : ∀ i : Fin 2, vec i = ∑ j : Fin n, g₀.inner x (e j) (vec i) • e j :=
    fun i => hrepr (vec i)
  have hvalue : Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
          (g0FlatCLM (I := I) g₀ x d))
        (Fin.cons a ![b]) =
      ∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), coef p * comp p := by
    change Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
          (g0FlatCLM (I := I) g₀ x d)) vec =
        ∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), coef p * comp p
    rw [hWd]
    rw [show Tensor0SSpace.toModel
          (∑ k : Fin n, g₀.inner x (e k) d •
            (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
              (g0FlatCLM (I := I) g₀ x (e k))) =
        ∑ k : Fin n, g₀.inner x (e k) d •
          Tensor0SSpace.toModel
            ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
              (g0FlatCLM (I := I) g₀ x (e k))) from by
      rw [← Tensor0SSpace.toModelL_apply, map_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [map_smul, Tensor0SSpace.toModelL_apply]]
    rw [ContinuousMultilinearMap.sum_apply]
    have hterm : ∀ k : Fin n,
        (g₀.inner x (e k) d •
          Tensor0SSpace.toModel
            ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
              (g0FlatCLM (I := I) g₀ x (e k)))) vec =
        ∑ J : Fin 2 → Fin n,
          (g₀.inner x (e k) d * ∏ i : Fin 2, g₀.inner x (e (J i)) (vec i)) *
            fiberNormSqComponent (I := I) (M := M) g₀ x 1 2 W n e (fun _ => k) J := by
      intro k
      rw [ContinuousMultilinearMap.smul_apply]
      set B2 : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ :=
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
            (g0FlatCLM (I := I) g₀ x (e k))) with hB2_def
      set coefJ : (Fin 2 → Fin n) → ℝ :=
        fun J => ∏ i : Fin 2, g₀.inner x (e (J i)) (vec i) with hcoefJ_def
      set compJ : (Fin 2 → Fin n) → ℝ :=
        fun J => B2 (fun i : Fin 2 => (show E from e (J i))) with hcompJ_def
      have hexp' : ∀ i : Fin 2, (show E from vec i) =
          ∑ j : Fin n, g₀.inner x (e j) (vec i) • (show E from e j) :=
        fun i => hexp i
      have hB2val : B2 vec = ∑ J : Fin 2 → Fin n, coefJ J * compJ J := by
        have hrw : B2 vec = B2 (fun i : Fin 2 =>
            ∑ j : Fin n, g₀.inner x (e j) (vec i) • (show E from e j)) := by
          congr 1
          funext i
          exact hexp' i
        rw [hrw, ContinuousMultilinearMap.map_sum]
        refine Finset.sum_congr rfl (fun J _ => ?_)
        rw [hcoefJ_def, hcompJ_def]
        rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]
      rw [hB2val, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun J _ => ?_)
      rw [hcompJ_def, hcompval (fun _ => k) J, ← hB2_def, hcoefJ_def]
      ring
    rw [Finset.sum_congr rfl (fun k _ => hterm k)]
    rw [show (∑ k : Fin n, ∑ J : Fin 2 → Fin n,
          (g₀.inner x (e k) d * ∏ i : Fin 2, g₀.inner x (e (J i)) (vec i)) *
            fiberNormSqComponent (I := I) (M := M) g₀ x 1 2 W n e (fun _ => k) J) =
        ∑ K : Fin 1 → Fin n, ∑ J : Fin 2 → Fin n,
          (g₀.inner x (e (K 0)) d * ∏ i : Fin 2, g₀.inner x (e (J i)) (vec i)) *
            fiberNormSqComponent (I := I) (M := M) g₀ x 1 2 W n e K J from by
      refine (Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n)).symm _ _ (fun k => ?_))
      refine Finset.sum_congr rfl (fun J _ => ?_)
      have hKeq : (Equiv.funUnique (Fin 1) (Fin n)).symm k = (fun _ : Fin 1 => k) := rfl
      rw [hKeq]]
    rw [← Fintype.sum_prod_type']
  rw [hvalue]
  have hCS : (∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), coef p * comp p) ^ 2 ≤
      (∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), coef p ^ 2) *
        ∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), comp p ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ coef comp
  have hdd_nn : 0 ≤ g₀.inner x d d := metric_inner_self_nonneg (I := I) (M := M) g₀ x d
  have haa_nn : 0 ≤ g₀.inner x a a := metric_inner_self_nonneg (I := I) (M := M) g₀ x a
  have hbb_nn : 0 ≤ g₀.inner x b b := metric_inner_self_nonneg (I := I) (M := M) g₀ x b
  have hcoefsq : (∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), coef p ^ 2) =
      g₀.inner x d d * (g₀.inner x a a * g₀.inner x b b) := by
    have hpow : ∀ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), coef p ^ 2 =
        g₀.inner x (e (p.1 0)) d ^ 2 *
          ∏ i : Fin 2, g₀.inner x (e (p.2 i)) (vec i) ^ 2 := by
      intro p
      rw [hcoef_def, mul_pow, ← Finset.prod_pow]
    rw [Finset.sum_congr rfl (fun p _ => hpow p)]
    rw [Fintype.sum_prod_type]
    rw [show (∑ K : Fin 1 → Fin n, ∑ J : Fin 2 → Fin n,
          g₀.inner x (e (K 0)) d ^ 2 * ∏ i : Fin 2, g₀.inner x (e (J i)) (vec i) ^ 2) =
        (∑ K : Fin 1 → Fin n, g₀.inner x (e (K 0)) d ^ 2) *
          ∑ J : Fin 2 → Fin n, ∏ i : Fin 2, g₀.inner x (e (J i)) (vec i) ^ 2 from by
      rw [Finset.sum_mul_sum]]
    have hKsum : (∑ K : Fin 1 → Fin n, g₀.inner x (e (K 0)) d ^ 2) = g₀.inner x d d := by
      rw [← hpars d]
      rw [show (∑ K : Fin 1 → Fin n, g₀.inner x (e (K 0)) d ^ 2) =
          ∑ k : Fin n, g₀.inner x (e k) d ^ 2 from by
        rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin n))
          (fun k : Fin n => g₀.inner x (e k) d ^ 2)]
        rfl]
    have hJsum : (∑ J : Fin 2 → Fin n, ∏ i : Fin 2, g₀.inner x (e (J i)) (vec i) ^ 2) =
        g₀.inner x a a * g₀.inner x b b := by
      rw [show (∑ J : Fin 2 → Fin n, ∏ i : Fin 2, g₀.inner x (e (J i)) (vec i) ^ 2) =
          ∑ J ∈ Fintype.piFinset (fun _ : Fin 2 => (Finset.univ : Finset (Fin n))),
            ∏ i : Fin 2, g₀.inner x (e (J i)) (vec i) ^ 2 from by
        rw [Fintype.piFinset_univ]]
      rw [← Finset.prod_univ_sum (fun _ : Fin 2 => (Finset.univ : Finset (Fin n)))
        (fun i j => g₀.inner x (e j) (vec i) ^ 2)]
      rw [Fin.prod_univ_two]
      rw [hpars (vec 0), hpars (vec 1)]
      have h0 : vec 0 = a := rfl
      have h1 : vec 1 = b := rfl
      rw [h0, h1]
    rw [hKsum, hJsum]
  have hcompsq : (∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), comp p ^ 2) =
      ‖(W : Tensor0SBundle.TensorRSSpace 1 2 I x)‖ ^ 2 := by
    rw [← riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 1 2 x W]
    rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 1 2 x W e bse hnE hbse horth]
    rw [Fintype.sum_prod_type]
  have hnorm_nn : 0 ≤ ‖(W : Tensor0SBundle.TensorRSSpace 1 2 I x)‖ := norm_nonneg _
  have habs_sq : (∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), coef p * comp p) ^ 2 ≤
      ‖(W : Tensor0SBundle.TensorRSSpace 1 2 I x)‖ ^ 2 *
        (g₀.inner x d d * (g₀.inner x a a * g₀.inner x b b)) := by
    calc (∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), coef p * comp p) ^ 2
        ≤ (∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), coef p ^ 2) *
            ∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), comp p ^ 2 := hCS
      _ = (g₀.inner x d d * (g₀.inner x a a * g₀.inner x b b)) *
            ‖(W : Tensor0SBundle.TensorRSSpace 1 2 I x)‖ ^ 2 := by
            rw [hcoefsq, hcompsq]
      _ = ‖(W : Tensor0SBundle.TensorRSSpace 1 2 I x)‖ ^ 2 *
            (g₀.inner x d d * (g₀.inner x a a * g₀.inner x b b)) := by ring
  rw [← Real.sqrt_sq (abs_nonneg (∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), coef p * comp p)),
    sq_abs]
  rw [show ‖(W : Tensor0SBundle.TensorRSSpace 1 2 I x)‖ *
        Real.sqrt (g₀.inner x d d) *
        Real.sqrt (g₀.inner x a a) * Real.sqrt (g₀.inner x b b) =
      Real.sqrt (‖(W : Tensor0SBundle.TensorRSSpace 1 2 I x)‖ ^ 2 *
        (g₀.inner x d d * (g₀.inner x a a * g₀.inner x b b))) from ?_]
  · exact Real.sqrt_le_sqrt habs_sq
  · rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hnorm_nn]
    rw [Real.sqrt_mul hdd_nn, Real.sqrt_mul haa_nn]
    ring

set_option linter.unusedSectionVars false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
private theorem exists_fixed_connDiff_sqrt_bound (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : M) (v w : TangentSpace I x),
      Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g_bg g₀ x v w)
          (PDE.DeTurck.connDiff (I := I) g_bg g₀ x v w)) ≤
        C * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by
  classical
  obtain ⟨K, hK0, hK⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M)
    g₀ 1 2 (connDiffSection (I := I) g_bg g₀)
  refine ⟨Real.sqrt K, Real.sqrt_nonneg _, ?_⟩
  intro x v w
  letI instW : Bundle.RiemannianBundle (fun y : M => Tensor0SBundle.TensorRSSpace 1 2 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 1 2
  set cd : TangentSpace I x := PDE.DeTurck.connDiff (I := I) g_bg g₀ x v w with hcd_def
  set W : TensorRSSpace 1 2 I x := connDiffFib (I := I) g_bg g₀ x with hW_def
  have hval : Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
        (g0FlatCLM (I := I) g₀ x cd)) (Fin.cons (v : E) ![(w : E)]) = g₀.inner x cd cd := by
    rw [show Tensor0SSpace.toModel ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
          (g0FlatCLM (I := I) g₀ x cd)) (Fin.cons (v : E) ![(w : E)]) =
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
            connDiffFib (I := I) g_bg g₀ x)
          (g0FlatCLM (I := I) g₀ x cd)) ![v, w] from rfl]
    rw [connDiffFib_apply_eval (I := I) g_bg g₀ x (g0FlatCLM (I := I) g₀ x cd) ![v, w]]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show (g0FlatCLM (I := I) g₀ x cd)
          (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) g_bg g₀ x v w) =
        cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₀ x cd)
          (PDE.DeTurck.connDiff (I := I) g_bg g₀ x v w) from
      (cotangentToDual_apply (I := I) (x := x) _ _).symm]
    rw [cotangentToDual_g0FlatCLM (I := I) g₀ x cd]
  have habs := abs_tensor12_flat_eval_le_fibreNorm_mul_sqrt_local (I := I) (M := M)
    g₀ x W cd v w
  rw [hval] at habs
  have hcdcd_nn : 0 ≤ g₀.inner x cd cd := metric_inner_self_nonneg (I := I) (M := M) g₀ x cd
  rw [abs_of_nonneg hcdcd_nn] at habs
  have hWnorm : ‖(W : Tensor0SBundle.TensorRSSpace 1 2 I x)‖ ≤ Real.sqrt K := by
    have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x W ≤ K := by
      have h := hK x
      rw [connDiffSection_toSection] at h
      rw [hW_def]
      exact h
    have h1 : ‖(W : Tensor0SBundle.TensorRSSpace 1 2 I x)‖ ^ 2 ≤ K := by
      rw [← riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 1 2 x W]
      exact h2
    calc ‖(W : Tensor0SBundle.TensorRSSpace 1 2 I x)‖
        = Real.sqrt (‖(W : Tensor0SBundle.TensorRSSpace 1 2 I x)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt K := Real.sqrt_le_sqrt h1
  set NA : ℝ := Real.sqrt (g₀.inner x cd cd) with hNA_def
  have hNA_nn : 0 ≤ NA := Real.sqrt_nonneg _
  have hAA_sq : g₀.inner x cd cd = NA ^ 2 := by rw [hNA_def, Real.sq_sqrt hcdcd_nn]
  set Sv : ℝ := Real.sqrt (g₀.inner x v v) with hSv_def
  set Sw : ℝ := Real.sqrt (g₀.inner x w w) with hSw_def
  have hSv_nn : 0 ≤ Sv := Real.sqrt_nonneg _
  have hSw_nn : 0 ≤ Sw := Real.sqrt_nonneg _
  set NW : ℝ := ‖(W : Tensor0SBundle.TensorRSSpace 1 2 I x)‖ with hNW_def
  have hNW_nn : 0 ≤ NW := norm_nonneg _
  have hprim' : NA ^ 2 ≤ NW * NA * Sv * Sw := by
    rw [← hAA_sq]
    exact habs
  have hNA_le : NA ≤ NW * Sv * Sw := by
    rcases eq_or_lt_of_le hNA_nn with hNA0 | hNApos
    · rw [← hNA0]
      positivity
    · have hkey : NA * NA ≤ NA * (NW * Sv * Sw) := by
        rw [show NA * NA = NA ^ 2 from by ring]
        refine le_trans hprim' ?_
        apply le_of_eq; ring
      exact le_of_mul_le_mul_left hkey hNApos
  calc NA ≤ NW * Sv * Sw := hNA_le
    _ ≤ Real.sqrt K * Sv * Sw := by
        have hprod_nn : 0 ≤ Sv * Sw := mul_nonneg hSv_nn hSw_nn
        nlinarith [hWnorm, hprod_nn, hSv_nn, hSw_nn, hNW_nn]

set_option linter.unusedSectionVars false in
private theorem covGrad_connDiffSection_flat_eval_eq_inner_local
    (g₀ g_c : SmoothRiemannianMetric I M) (x : M) (v w u : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g_c g₀)).toSection x)
          (g0FlatCLM (I := I) g₀ x
            (covDerivConnDiff (I := I) g₀ g_c
              (smoothExtensionTangent (I := I) x v)
              (smoothExtensionTangent (I := I) x w)
              (smoothExtensionTangent (I := I) x u) x)))
        (Fin.cons v (Fin.cons u ![w])) =
      g₀.inner x
        (covDerivConnDiff (I := I) g₀ g_c
          (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x w)
          (smoothExtensionTangent (I := I) x u) x)
        (covDerivConnDiff (I := I) g₀ g_c
          (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x w)
          (smoothExtensionTangent (I := I) x u) x) := by
  classical
  set A : TangentSpace I x :=
    covDerivConnDiff (I := I) g₀ g_c
      (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent (I := I) x w)
      (smoothExtensionTangent (I := I) x u) x with hA_def
  set Xsec : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent_contMDiff (I := I) x v) with hXsec_def
  set Ysec : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x u)
      (smoothExtensionTangent_contMDiff (I := I) x u) with hYsec_def
  set Zsec : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x w)
      (smoothExtensionTangent_contMDiff (I := I) x w) with hZsec_def
  have hXx : Xsec x = v := smoothExtensionTangent_eq (I := I) x v
  have hYx : Ysec x = u := smoothExtensionTangent_eq (I := I) x u
  have hZx : Zsec x = w := smoothExtensionTangent_eq (I := I) x w
  have hA_bridge : covDerivConnDiff (I := I) g₀ g_c Xsec Zsec Ysec x = A := by
    rw [hA_def]; rfl
  obtain ⟨om, hom⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := Tensor0SModel 1 ℝ E) (V := fun y : M => Tensor0SSpace 1 I y) x
    (g0FlatCLM (I := I) g₀ x A)
  have hbridge := connDiffSection_covGrad_eq_covDerivConnDiff (I := I) g_c g₀ om Xsec Ysec Zsec x
  rw [hom, hXx, hYx, hZx, hA_bridge] at hbridge
  have hflatA : (g0FlatCLM (I := I) g₀ x A) (fun _ : Fin 1 => A) = g₀.inner x A A := by
    rw [show (g0FlatCLM (I := I) g₀ x A) (fun _ : Fin 1 => A) =
        cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₀ x A) A from
      (cotangentToDual_apply (I := I) (x := x) _ _).symm]
    rw [cotangentToDual_g0FlatCLM (I := I) g₀ x A A]
  rw [hflatA] at hbridge
  rw [hA_def]
  exact hbridge

set_option linter.unusedSectionVars false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
private theorem exists_fixed_covDerivConnDiff_sqrt_bound
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : M) (v w u : TangentSpace I x),
      Real.sqrt (g₀.inner x
          (covDerivConnDiff (I := I) g₀ g_bg
            (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent (I := I) x u) x)
          (covDerivConnDiff (I := I) g₀ g_bg
            (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent (I := I) x u) x)) ≤
        C * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) *
          Real.sqrt (g₀.inner x u u) := by
  classical
  obtain ⟨K, hK0, hK⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M)
    g₀ 1 3 (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g_bg g₀))
  refine ⟨Real.sqrt K, Real.sqrt_nonneg _, ?_⟩
  intro x v w u
  letI instW : Bundle.RiemannianBundle (fun y : M => Tensor0SBundle.TensorRSSpace 1 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 1 3
  set W : Tensor0SBundle.TensorRSSpace 1 3 I x :=
    (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g_bg g₀)).toSection x
    with hW_def
  set A : TangentSpace I x :=
    covDerivConnDiff (I := I) g₀ g_bg
      (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent (I := I) x w)
      (smoothExtensionTangent (I := I) x u) x with hA_def
  have hAA_nn : 0 ≤ g₀.inner x A A := metric_inner_self_nonneg (I := I) (M := M) g₀ x A
  set NA : ℝ := Real.sqrt (g₀.inner x A A) with hNA_def
  have hNA_nn : 0 ≤ NA := Real.sqrt_nonneg _
  have hbridge := covGrad_connDiffSection_flat_eval_eq_inner_local (I := I) (M := M)
    g₀ g_bg x v w u
  rw [← hA_def, ← hW_def] at hbridge
  have hprim := abs_tensor13_flat_eval_le_fibreNorm_mul_sqrt (I := I) (M := M) g₀ x W A v u w
  rw [hbridge] at hprim
  rw [abs_of_nonneg hAA_nn] at hprim
  have hAA_sq : g₀.inner x A A = NA ^ 2 := by rw [hNA_def, Real.sq_sqrt hAA_nn]
  set Sv : ℝ := Real.sqrt (g₀.inner x v v) with hSv_def
  set Sw : ℝ := Real.sqrt (g₀.inner x w w) with hSw_def
  set Su : ℝ := Real.sqrt (g₀.inner x u u) with hSu_def
  have hSv_nn : 0 ≤ Sv := Real.sqrt_nonneg _
  have hSw_nn : 0 ≤ Sw := Real.sqrt_nonneg _
  have hSu_nn : 0 ≤ Su := Real.sqrt_nonneg _
  set NW : ℝ := ‖(W : Tensor0SBundle.TensorRSSpace 1 3 I x)‖ with hNW_def
  have hNW_nn : 0 ≤ NW := norm_nonneg _
  have hWnorm : NW ≤ Real.sqrt K := by
    have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 3 x W ≤ K := hK x
    have h1 : NW ^ 2 ≤ K := by
      rw [hNW_def, ← riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 1 3 x W]
      exact h2
    calc NW = Real.sqrt (NW ^ 2) := (Real.sqrt_sq hNW_nn).symm
      _ ≤ Real.sqrt K := Real.sqrt_le_sqrt h1
  have hprim' : NA ^ 2 ≤ NW * NA * Sv * Su * Sw := by
    rw [← hAA_sq]
    exact hprim
  have hNA_le : NA ≤ NW * Sv * Sw * Su := by
    rcases eq_or_lt_of_le hNA_nn with hNA0 | hNApos
    · rw [← hNA0]
      positivity
    · have hkey : NA * NA ≤ NA * (NW * Sv * Su * Sw) := by
        rw [show NA * NA = NA ^ 2 from by ring]
        refine le_trans hprim' ?_
        apply le_of_eq; ring
      have hcancel := le_of_mul_le_mul_left hkey hNApos
      calc NA ≤ NW * Sv * Su * Sw := hcancel
        _ = NW * Sv * Sw * Su := by ring
  calc NA ≤ NW * Sv * Sw * Su := hNA_le
    _ ≤ Real.sqrt K * Sv * Sw * Su := by
        have hprod_nn : 0 ≤ Sv * Sw * Su := by positivity
        nlinarith [hWnorm, hprod_nn, hSv_nn, hSw_nn, hSu_nn, hNW_nn]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem deTurckLieDLaCoeffField_realizedFam_rfns_order0_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              ((deTurckLieDLaCoeffField (I := I) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x) ≤ Λ := by
  classical
  set δ₁ : ℝ := max δ₀ 0 with hδ₁_def
  have hδ₁_nn : 0 ≤ δ₁ := le_max_right _ _
  have hδ₁_lt : δ₁ < 1 := max_lt hδ₀ one_pos
  have hcoeff : 0 < 1 - δ₁ := by linarith
  set κ : ℝ := Real.sqrt (1 / (1 - δ₁)) with hκ_def
  have hκ_nn : 0 ≤ κ := Real.sqrt_nonneg _
  obtain ⟨Csob, hCsob_nn, hCsob⟩ :=
    DifferentialGeometry.PDE.RicciFlow.exists_Csob_convexPerturbation_pointwise_C2_le
      (I := I) (M := M) g₀ a ha_super
  set B : ℝ := Csob * R with hB_def
  have hB_nn : 0 ≤ B := mul_nonneg hCsob_nn hR
  obtain ⟨Cq, hCq_nn, hCq⟩ :=
    exists_covDerivConnDiff_gQuadratic_le_of_jetEnvelope (I := I) (M := M) g₀
      (δ₀ := δ₁) hδ₁_lt B hB_nn
  obtain ⟨Cbg, hCbg_nn, hCbg⟩ :=
    exists_fixed_covDerivConnDiff_sqrt_bound (I := I) (M := M) g₀ g_bg
  obtain ⟨Cc, hCc_nn, hCc⟩ := exists_fixed_connDiff_sqrt_bound (I := I) (M := M) g₀ g_bg
  obtain ⟨Ca0, hCa0_nn, hCa0⟩ :=
    connDiff_gFibreNorm_le_iteratedCovGrad_of_lt_one (I := I) (M := M) g₀ hδ₁_nn hδ₁_lt
  set CaB : ℝ := Ca0 * B with hCaB_def
  have hCaB_nn : 0 ≤ CaB := mul_nonneg hCa0_nn hB_nn
  set CK : ℝ := (Cq + Cbg + 3 * (CaB * (CaB + Cc))) * (κ * κ) with hCK_def
  have hCK_nn : 0 ≤ CK := by
    rw [hCK_def]
    refine mul_nonneg ?_ (mul_nonneg hκ_nn hκ_nn)
    have h3 : 0 ≤ CaB * (CaB + Cc) := mul_nonneg hCaB_nn (add_nonneg hCaB_nn hCc_nn)
    linarith [hCq_nn, hCbg_nn, h3]
  refine ⟨((Module.finrank ℝ E : ℝ) ^ 2) ^ 2 *
      ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * (4 * CK * (κ * κ)))) ^ 2,
    by positivity, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  obtain ⟨hs0, hs1⟩ := hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    abs_convex_smallConstant_lt_one hδ_lt hδ'_lt ⟨hs0, hs1⟩
  set g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hg₁
  set P : SmoothCcTensor g₀ 0 2 := convexPerturbation (I := I) g₀ T T' s with hP_def
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w := by
    intro y v w
    rw [hg₁, hP_def]
    exact realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hs_mem y v w
  have hδs_raw : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P)
      (|1 - s| * δ' + |s| * δ) := by
    rw [hP_def]
    exact convexPerturbation_gFibreOpBound_abs (I := I) g₀ T T' hδ hδ' s
  set δP : ℝ := max (|1 - s| * δ' + |s| * δ) 0 with hδP_def
  have hδP_nn : 0 ≤ δP := le_max_right _ _
  have hδP_bound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δP :=
    gFibreOpBound_mono_of_le (I := I) (M := M) g₀ _ (le_max_left _ _) hδs_raw
  have hδP_le : δP ≤ δ₁ := by
    refine max_le ?_ hδ₁_nn
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - s), abs_of_nonneg hs0]
    have h1 : δ' ≤ δ₁ := le_trans hδ'_le (le_max_left _ _)
    have h2 : δ ≤ δ₁ := le_trans hδ_le (le_max_left _ _)
    nlinarith [h1, h2]
  have hδP_lt1 : δP < 1 := lt_of_le_of_lt hδP_le hδ₁_lt
  have henv := hCsob T T' hR hTball hT'ball s ⟨hs0, hs1⟩ x
  rw [← hP_def, ← hB_def] at henv
  letI inst03 : Bundle.RiemannianBundle (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  set N1 : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ with hN1_def
  have hN1_le : N1 ≤ B := by
    have hterms : ∀ k ∈ Finset.range 3, (0 : ℝ) ≤
        (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + k) I b) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + k)
        ‖(iteratedCovGrad (I := I) g₀ 0 2 k P).toSection x‖) := by
      intro k _
      letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + k) I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + k)
      exact norm_nonneg _
    have h1 := Finset.single_le_sum hterms (by norm_num : (1:ℕ) ∈ Finset.range 3)
    have h2 := le_trans h1 henv
    rw [← hN1_def] at h2
    exact h2
  have hquad : ∀ v w u : TangentSpace I x,
      Real.sqrt (g₀.inner x
          (covDerivConnDiff (I := I) g₀ g₁
            (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent (I := I) x u) x)
          (covDerivConnDiff (I := I) g₀ g₁
            (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent (I := I) x u) x)) ≤
        Cq * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) *
          Real.sqrt (g₀.inner x u u) := by
    intro v w u
    exact hCq g₁ P (δ := δP) (le_trans hδP_le (le_max_left _ _)) hδP_bound htie x henv v w u
  have hconn_g1 : ∀ u v : TangentSpace I x,
      Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v)) ≤
      CaB * (Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v)) := by
    intro u v
    have h := hCa0 g₁ P htie (δ := δP) hδP_le hδP_nn hδP_bound x u v
    rw [← hN1_def] at h
    refine le_trans h ?_
    have hsu : 0 ≤ Real.sqrt (g₀.inner x u u) := Real.sqrt_nonneg _
    have hsv : 0 ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
    have hN1_nn : 0 ≤ N1 := norm_nonneg _
    calc Ca0 * N1 * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v)
        ≤ Ca0 * B * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v) := by
          have hmono : Ca0 * N1 ≤ Ca0 * B := mul_le_mul_of_nonneg_left hN1_le hCa0_nn
          have h1 : Ca0 * N1 * Real.sqrt (g₀.inner x u u) ≤
              Ca0 * B * Real.sqrt (g₀.inner x u u) :=
            mul_le_mul_of_nonneg_right hmono hsu
          exact mul_le_mul_of_nonneg_right h1 hsv
      _ = CaB * (Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v)) := by
          rw [hCaB_def]; ring
  have hcocy : ∀ u v : TangentSpace I x,
      PDE.DeTurck.connDiff (I := I) g₁ g_bg x u v =
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v -
          PDE.DeTurck.connDiff (I := I) g_bg g₀ x u v :=
    fun u v => eq_sub_of_add_eq (connDiff_cocycle (I := I) g₁ g_bg g₀ x u v)
  have hconn_gbg : ∀ u v : TangentSpace I x,
      Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g_bg x u v)
        (PDE.DeTurck.connDiff (I := I) g₁ g_bg x u v)) ≤
      (CaB + Cc) * (Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v)) := by
    intro u v
    rw [hcocy u v]
    refine le_trans (sqrt_metric_inner_sub_le (I := I) (M := M) g₀ x _ _) ?_
    have h1 := hconn_g1 u v
    have h2 := hCc x u v
    calc Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v))
          + Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g_bg g₀ x u v)
            (PDE.DeTurck.connDiff (I := I) g_bg g₀ x u v))
        ≤ CaB * (Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v))
          + Cc * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v) := add_le_add h1 h2
      _ = (CaB + Cc) * (Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v)) := by ring
  have hpinch : ∀ a' : Fin (Module.finrank ℝ E),
      Real.sqrt (g₀.inner x (smoothOrthoFrame (I := I) g₁ x a' x)
        (smoothOrthoFrame (I := I) g₁ x a' x)) ≤ κ := by
    intro a'
    set Ba : TangentSpace I x := smoothOrthoFrame (I := I) g₁ x a' x with hBa
    have hg1BB : g₁.inner x Ba Ba = 1 := by
      have h := smoothOrthoFrame_orthonormal_at_center (I := I) g₁ x a' a'
      rw [if_pos rfl] at h
      exact h
    have hBB_nn : 0 ≤ g₀.inner x Ba Ba := metric_inner_self_nonneg (I := I) (M := M) g₀ x Ba
    have hsq : Real.sqrt (g₀.inner x Ba Ba) * Real.sqrt (g₀.inner x Ba Ba) =
        g₀.inner x Ba Ba := Real.mul_self_sqrt hBB_nn
    have hpert' : |ccTensorBilinSymm (I := I) g₀ P x Ba Ba| ≤ δP * g₀.inner x Ba Ba := by
      calc |ccTensorBilinSymm (I := I) g₀ P x Ba Ba|
          ≤ δP * Real.sqrt (g₀.inner x Ba Ba) * Real.sqrt (g₀.inner x Ba Ba) :=
            hδP_bound x Ba Ba
        _ = δP * g₀.inner x Ba Ba := by rw [mul_assoc, hsq]
    have htie' := htie x Ba Ba
    rw [hg1BB] at htie'
    have hlow : g₀.inner x Ba Ba - δP * g₀.inner x Ba Ba ≤ 1 := by
      have h1 := (abs_le.mp hpert').1
      linarith [htie'.symm]
    have hBB_le : g₀.inner x Ba Ba ≤ 1 / (1 - δ₁) := by
      have hδP1 : 1 - δ₁ ≤ 1 - δP := by linarith [hδP_le]
      have h2 : (1 - δP) * g₀.inner x Ba Ba ≤ 1 := by nlinarith [hlow]
      have h3 : (1 - δ₁) * g₀.inner x Ba Ba ≤ (1 - δP) * g₀.inner x Ba Ba :=
        mul_le_mul_of_nonneg_right hδP1 hBB_nn
      rw [le_div_iff₀ hcoeff]
      nlinarith [h2, h3]
    calc Real.sqrt (g₀.inner x Ba Ba) ≤ Real.sqrt (1 / (1 - δ₁)) := Real.sqrt_le_sqrt hBB_le
      _ = κ := by rw [hκ_def]
  have hkernel : ∀ (v0 : TangentSpace I x), g₀.inner x v0 v0 = 1 →
      ∀ a' b' : Fin (Module.finrank ℝ E),
      Real.sqrt (g₀.inner x
        (dLaCovKernel (I := I) g₁ g_bg x v0 (smoothOrthoFrame (I := I) g₁ x a' x)
          (smoothOrthoFrame (I := I) g₁ x b' x))
        (dLaCovKernel (I := I) g₁ g_bg x v0 (smoothOrthoFrame (I := I) g₁ x a' x)
          (smoothOrthoFrame (I := I) g₁ x b' x))) ≤ CK := by
    intro v0 hv0 a' b'
    set Ba : TangentSpace I x := smoothOrthoFrame (I := I) g₁ x a' x with hBa
    set Bb : TangentSpace I x := smoothOrthoFrame (I := I) g₁ x b' x with hBb
    have hBa_le : Real.sqrt (g₀.inner x Ba Ba) ≤ κ := hpinch a'
    have hBb_le : Real.sqrt (g₀.inner x Bb Bb) ≤ κ := hpinch b'
    have hBa_nn : 0 ≤ Real.sqrt (g₀.inner x Ba Ba) := Real.sqrt_nonneg _
    have hBb_nn : 0 ≤ Real.sqrt (g₀.inner x Bb Bb) := Real.sqrt_nonneg _
    have hv0_sqrt : Real.sqrt (g₀.inner x v0 v0) = 1 := by rw [hv0, Real.sqrt_one]
    rw [dLaCovKernel_backgroundSplit (I := I) g₀ g₁ g_bg x v0 Ba Bb]
    set A1 : TangentSpace I x := covDerivConnDiff (I := I) g₀ g₁
      (smoothExtensionTangent (I := I) x v0)
      (smoothExtensionTangent (I := I) x Bb)
      (smoothExtensionTangent (I := I) x Ba) x with hA1
    set A2 : TangentSpace I x := covDerivConnDiff (I := I) g₀ g_bg
      (smoothExtensionTangent (I := I) x v0)
      (smoothExtensionTangent (I := I) x Bb)
      (smoothExtensionTangent (I := I) x Ba) x with hA2
    set Q1 : TangentSpace I x := PDE.DeTurck.connDiff (I := I) g₁ g₀ x
      (PDE.DeTurck.connDiff (I := I) g₁ g_bg x Ba Bb) v0 with hQ1
    set Q2 : TangentSpace I x := PDE.DeTurck.connDiff (I := I) g₁ g_bg x
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Ba v0) Bb with hQ2
    set Q3 : TangentSpace I x := PDE.DeTurck.connDiff (I := I) g₁ g_bg x Ba
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Bb v0) with hQ3
    have t1 := sqrt_metric_inner_sub_le (I := I) (M := M) g₀ x (A1 - A2 + Q1 - Q2) Q3
    have t2 := sqrt_metric_inner_sub_le (I := I) (M := M) g₀ x (A1 - A2 + Q1) Q2
    have t3 := sqrt_metric_inner_add_le (I := I) (M := M) g₀ x (A1 - A2) Q1
    have t4 := sqrt_metric_inner_sub_le (I := I) (M := M) g₀ x A1 A2
    have hA1_le : Real.sqrt (g₀.inner x A1 A1) ≤ Cq * (κ * κ) := by
      have h := hquad v0 Bb Ba
      rw [hv0_sqrt] at h
      refine le_trans h ?_
      calc Cq * 1 * Real.sqrt (g₀.inner x Bb Bb) * Real.sqrt (g₀.inner x Ba Ba)
          ≤ Cq * 1 * κ * κ := by
            have h1 : Cq * 1 * Real.sqrt (g₀.inner x Bb Bb) ≤ Cq * 1 * κ :=
              mul_le_mul_of_nonneg_left hBb_le (by linarith [hCq_nn])
            have h2 : Cq * 1 * Real.sqrt (g₀.inner x Bb Bb) * Real.sqrt (g₀.inner x Ba Ba) ≤
                Cq * 1 * κ * Real.sqrt (g₀.inner x Ba Ba) :=
              mul_le_mul_of_nonneg_right h1 hBa_nn
            refine le_trans h2 ?_
            exact mul_le_mul_of_nonneg_left hBa_le (by positivity)
        _ = Cq * (κ * κ) := by ring
    have hA2_le : Real.sqrt (g₀.inner x A2 A2) ≤ Cbg * (κ * κ) := by
      have h := hCbg x v0 Bb Ba
      rw [hv0_sqrt] at h
      refine le_trans h ?_
      calc Cbg * 1 * Real.sqrt (g₀.inner x Bb Bb) * Real.sqrt (g₀.inner x Ba Ba)
          ≤ Cbg * 1 * κ * κ := by
            have h1 : Cbg * 1 * Real.sqrt (g₀.inner x Bb Bb) ≤ Cbg * 1 * κ :=
              mul_le_mul_of_nonneg_left hBb_le (by linarith [hCbg_nn])
            have h2 : Cbg * 1 * Real.sqrt (g₀.inner x Bb Bb) * Real.sqrt (g₀.inner x Ba Ba) ≤
                Cbg * 1 * κ * Real.sqrt (g₀.inner x Ba Ba) :=
              mul_le_mul_of_nonneg_right h1 hBa_nn
            refine le_trans h2 ?_
            exact mul_le_mul_of_nonneg_left hBa_le (by positivity)
        _ = Cbg * (κ * κ) := by ring
    have hin_bg : Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g_bg x Ba Bb)
        (PDE.DeTurck.connDiff (I := I) g₁ g_bg x Ba Bb)) ≤ (CaB + Cc) * (κ * κ) := by
      refine le_trans (hconn_gbg Ba Bb) ?_
      have hmul : Real.sqrt (g₀.inner x Ba Ba) * Real.sqrt (g₀.inner x Bb Bb) ≤ κ * κ := by
        have h1 : Real.sqrt (g₀.inner x Ba Ba) * Real.sqrt (g₀.inner x Bb Bb) ≤
            κ * Real.sqrt (g₀.inner x Bb Bb) := mul_le_mul_of_nonneg_right hBa_le hBb_nn
        refine le_trans h1 ?_
        exact mul_le_mul_of_nonneg_left hBb_le hκ_nn
      exact mul_le_mul_of_nonneg_left hmul (add_nonneg hCaB_nn hCc_nn)
    have hQ1_le : Real.sqrt (g₀.inner x Q1 Q1) ≤ CaB * ((CaB + Cc) * (κ * κ)) := by
      have h := hconn_g1 (PDE.DeTurck.connDiff (I := I) g₁ g_bg x Ba Bb) v0
      rw [hv0_sqrt, mul_one] at h
      refine le_trans h ?_
      exact mul_le_mul_of_nonneg_left hin_bg hCaB_nn
    have hin2 : Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Ba v0)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Ba v0)) ≤ CaB * κ := by
      have h := hconn_g1 Ba v0
      rw [hv0_sqrt, mul_one] at h
      refine le_trans h ?_
      exact mul_le_mul_of_nonneg_left hBa_le hCaB_nn
    have hQ2_le : Real.sqrt (g₀.inner x Q2 Q2) ≤ (CaB + Cc) * (CaB * (κ * κ)) := by
      have h := hconn_gbg (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Ba v0) Bb
      refine le_trans h ?_
      have hmul : Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Ba v0)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Ba v0)) * Real.sqrt (g₀.inner x Bb Bb) ≤
          (CaB * κ) * κ := by
        have h1 : Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Ba v0)
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Ba v0)) * Real.sqrt (g₀.inner x Bb Bb) ≤
            (CaB * κ) * Real.sqrt (g₀.inner x Bb Bb) := mul_le_mul_of_nonneg_right hin2 hBb_nn
        refine le_trans h1 ?_
        exact mul_le_mul_of_nonneg_left hBb_le (by positivity)
      refine le_trans (mul_le_mul_of_nonneg_left hmul (add_nonneg hCaB_nn hCc_nn)) ?_
      apply le_of_eq
      ring
    have hin3 : Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Bb v0)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Bb v0)) ≤ CaB * κ := by
      have h := hconn_g1 Bb v0
      rw [hv0_sqrt, mul_one] at h
      refine le_trans h ?_
      exact mul_le_mul_of_nonneg_left hBb_le hCaB_nn
    have hQ3_le : Real.sqrt (g₀.inner x Q3 Q3) ≤ (CaB + Cc) * (CaB * (κ * κ)) := by
      have h := hconn_gbg Ba (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Bb v0)
      refine le_trans h ?_
      have hmul : Real.sqrt (g₀.inner x Ba Ba) *
          Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Bb v0)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Bb v0)) ≤ κ * (CaB * κ) := by
        have h1 : Real.sqrt (g₀.inner x Ba Ba) *
            Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Bb v0)
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Bb v0)) ≤
            κ * Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Bb v0)
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Bb v0)) :=
          mul_le_mul_of_nonneg_right hBa_le (Real.sqrt_nonneg _)
        refine le_trans h1 ?_
        exact mul_le_mul_of_nonneg_left hin3 hκ_nn
      refine le_trans (mul_le_mul_of_nonneg_left hmul (add_nonneg hCaB_nn hCc_nn)) ?_
      apply le_of_eq
      ring
    have hchain : Real.sqrt (g₀.inner x (A1 - A2 + Q1 - Q2 - Q3) (A1 - A2 + Q1 - Q2 - Q3)) ≤
        Real.sqrt (g₀.inner x A1 A1) + Real.sqrt (g₀.inner x A2 A2) +
          Real.sqrt (g₀.inner x Q1 Q1) + Real.sqrt (g₀.inner x Q2 Q2) +
          Real.sqrt (g₀.inner x Q3 Q3) := by
      refine le_trans t1 ?_
      have s2 := le_trans t2 (by linarith [t3, t4] :
        Real.sqrt (g₀.inner x (A1 - A2 + Q1) (A1 - A2 + Q1)) +
            Real.sqrt (g₀.inner x Q2 Q2) ≤
          Real.sqrt (g₀.inner x A1 A1) + Real.sqrt (g₀.inner x A2 A2) +
            Real.sqrt (g₀.inner x Q1 Q1) + Real.sqrt (g₀.inner x Q2 Q2))
      linarith [s2]
    refine le_trans hchain ?_
    rw [hCK_def]
    nlinarith [hA1_le, hA2_le, hQ1_le, hQ2_le, hQ3_le]
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr, _hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := hn
  have hunit : ∀ i : Fin n, g₀.inner x (e i) (e i) = 1 := by
    intro i
    have h := horth i i
    rw [if_pos rfl] at h
    exact h
  have hunit_sqrt : ∀ i : Fin n, Real.sqrt (g₀.inner x (e i) (e i)) = 1 := by
    intro i
    rw [hunit i, Real.sqrt_one]
  rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 2 2 x
    ((deTurckLieDLaCoeffField (I := I) g₀ g₁ g_bg).toSection x) e bse hnE hbse horth]
  have heach : ∀ (K : Fin 2 → Fin n) (J : Fin 2 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
        ((deTurckLieDLaCoeffField (I := I) g₀ g₁ g_bg).toSection x) n e K J) ^ 2 ≤
      ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * (4 * CK * (κ * κ)))) ^ 2 := by
    intro K J
    have hcomp_eq : fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
        ((deTurckLieDLaCoeffField (I := I) g₀ g₁ g_bg).toSection x) n e K J =
      Tensor0SSpace.toModel
        ((dLaBiContrFib (I := I) g₁ g_bg x) (coframeS (I := I) (M := M) g₀ x 2 e K))
        (fun i : Fin 2 => (e (J i) : E)) := rfl
    have hmodel : Tensor0SSpace.toModel
        ((dLaBiContrFib (I := I) g₁ g_bg x) (coframeS (I := I) (M := M) g₀ x 2 e K))
        (fun i : Fin 2 => (e (J i) : E)) =
      (-1 : ℝ) * ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
        (g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x (e (J 0))
            (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
            (e (J 1))
          + g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x (e (J 1))
            (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
            (e (J 0))) *
          Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 2 e K)
            ![(smoothOrthoFrame (I := I) g₁ x a' x : E),
              (smoothOrthoFrame (I := I) g₁ x b' x : E)] :=
      dLaBiContrFibFixedFrame_toModel (I := I) g₁ g_bg (smoothOrthoFrame (I := I) g₁ x) x
        (coframeS (I := I) (M := M) g₀ x 2 e K) (fun i : Fin 2 => (e (J i) : E))
    have hsingle : ∀ a' b' : Fin (Module.finrank ℝ E),
        |(g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x (e (J 0))
            (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
            (e (J 1))
          + g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x (e (J 1))
            (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
            (e (J 0))) *
          Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 2 e K)
            ![(smoothOrthoFrame (I := I) g₁ x a' x : E),
              (smoothOrthoFrame (I := I) g₁ x b' x : E)]| ≤ 4 * CK * (κ * κ) := by
      intro a' b'
      rw [abs_mul]
      have hK01 : |g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x (e (J 0))
          (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
          (e (J 1))| ≤ 2 * CK := by
        refine le_trans (abs_g1_inner_le_two_sqrt (I := I) (M := M) g₀ g₁ P htie
          (le_of_lt hδP_lt1) hδP_bound x _ _) ?_
        rw [hunit_sqrt (J 1), mul_one]
        have h := hkernel (e (J 0)) (hunit (J 0)) a' b'
        linarith
      have hK10 : |g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x (e (J 1))
          (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
          (e (J 0))| ≤ 2 * CK := by
        refine le_trans (abs_g1_inner_le_two_sqrt (I := I) (M := M) g₀ g₁ P htie
          (le_of_lt hδP_lt1) hδP_bound x _ _) ?_
        rw [hunit_sqrt (J 0), mul_one]
        have h := hkernel (e (J 1)) (hunit (J 1)) a' b'
        linarith
      have hfac1 : |g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x (e (J 0))
          (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
          (e (J 1))
          + g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x (e (J 1))
            (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
            (e (J 0))| ≤ 4 * CK := by
        refine le_trans (abs_add_le _ _) ?_
        linarith [hK01, hK10]
      have hfac2 : |Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 2 e K)
          ![(smoothOrthoFrame (I := I) g₁ x a' x : E),
            (smoothOrthoFrame (I := I) g₁ x b' x : E)]| ≤ κ * κ := by
        rw [toModel_coframeS_two (I := I) (M := M) g₀ x e K _ _]
        rw [abs_mul]
        have hcs1 : |g₀.inner x (e (K 0)) (smoothOrthoFrame (I := I) g₁ x a' x)| ≤ κ := by
          refine le_trans (abs_metric_inner_le (I := I) (M := M) g₀ x _ _) ?_
          rw [hunit_sqrt (K 0), one_mul]
          exact hpinch a'
        have hcs2 : |g₀.inner x (e (K 1)) (smoothOrthoFrame (I := I) g₁ x b' x)| ≤ κ := by
          refine le_trans (abs_metric_inner_le (I := I) (M := M) g₀ x _ _) ?_
          rw [hunit_sqrt (K 1), one_mul]
          exact hpinch b'
        exact mul_le_mul hcs1 hcs2 (abs_nonneg _) hκ_nn
      calc |g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x (e (J 0))
            (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
            (e (J 1))
            + g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x (e (J 1))
              (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
              (e (J 0))| *
          |Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 2 e K)
            ![(smoothOrthoFrame (I := I) g₁ x a' x : E),
              (smoothOrthoFrame (I := I) g₁ x b' x : E)]|
          ≤ (4 * CK) * (κ * κ) := by
            refine mul_le_mul hfac1 hfac2 (abs_nonneg _) ?_
            linarith [hCK_nn]
        _ = 4 * CK * (κ * κ) := by ring
    have habs_comp : |fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
        ((deTurckLieDLaCoeffField (I := I) g₀ g₁ g_bg).toSection x) n e K J| ≤
        (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * (4 * CK * (κ * κ))) := by
      rw [hcomp_eq, hmodel, neg_one_mul, abs_neg]
      calc |∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
            (g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x (e (J 0))
                (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
                (e (J 1))
              + g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x (e (J 1))
                (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
                (e (J 0))) *
              Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 2 e K)
                ![(smoothOrthoFrame (I := I) g₁ x a' x : E),
                  (smoothOrthoFrame (I := I) g₁ x b' x : E)]|
          ≤ ∑ a' : Fin (Module.finrank ℝ E), |∑ b' : Fin (Module.finrank ℝ E),
            (g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x (e (J 0))
                (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
                (e (J 1))
              + g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x (e (J 1))
                (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
                (e (J 0))) *
              Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 2 e K)
                ![(smoothOrthoFrame (I := I) g₁ x a' x : E),
                  (smoothOrthoFrame (I := I) g₁ x b' x : E)]| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
            |(g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x (e (J 0))
                (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
                (e (J 1))
              + g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x (e (J 1))
                (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
                (e (J 0))) *
              Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 2 e K)
                ![(smoothOrthoFrame (I := I) g₁ x a' x : E),
                  (smoothOrthoFrame (I := I) g₁ x b' x : E)]| :=
            Finset.sum_le_sum (fun a' _ => Finset.abs_sum_le_sum_abs _ _)
        _ ≤ ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
              (4 * CK * (κ * κ)) :=
            Finset.sum_le_sum (fun a' _ => Finset.sum_le_sum (fun b' _ => hsingle a' b'))
        _ = (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * (4 * CK * (κ * κ))) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) habs_comp 2
  calc ∑ K : Fin 2 → Fin n, ∑ J : Fin 2 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
          ((deTurckLieDLaCoeffField (I := I) g₀ g₁ g_bg).toSection x) n e K J) ^ 2
      ≤ ∑ K : Fin 2 → Fin n, ∑ J : Fin 2 → Fin n,
          ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * (4 * CK * (κ * κ)))) ^ 2 :=
        Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ => heach K J))
    _ = ((Module.finrank ℝ E : ℝ) ^ 2) ^ 2 *
        ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * (4 * CK * (κ * κ)))) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun,
          Fintype.card_fin]
        rw [hnE]
        push_cast
        ring

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

section DLaGridBrick

open Tensor0SBundle
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

set_option linter.unusedSectionVars false in
private lemma interiorProduct_toModel_eval_dla (s : ℕ) (x : M) (vv : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) (w : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x vv D) w =
      Tensor0SSpace.toModel D (Fin.cons (show E from vv) (fun k => (show E from w k))) := by
  have h1 : Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x vv D) =
      Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) s (show E from vv)
        (Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl

set_option linter.unusedSectionVars false in
private lemma toModel_om_single_eq_cotangentToDual_dla (x : M) (om : Tensor0SSpace 1 I x)
    (m : Fin 1 → TangentSpace I x) :
    Tensor0SSpace.toModel om (fun k => (m k : E)) =
      cotangentToDual (I := I) (x := x) om (m 0) := by
  rw [show (fun k : Fin 1 => (m k : E)) = (fun _ : Fin 1 => (m 0 : E)) from by
    funext k; fin_cases k; rfl]
  rw [cotangentToDual_apply]
  rfl

set_option linter.unusedSectionVars false in
private lemma cotangentToDual_eq_inner_sharp_dla (g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (ww : TangentSpace I x) :
    cotangentToDual (I := I) (x := x) om ww =
      g₀.inner x ww (inverseMetricSharpFib (I := I) g₀ x om) := by
  rw [g₀.symm x ww (inverseMetricSharpFib (I := I) g₀ x om)]
  rw [show g₀.inner x (inverseMetricSharpFib (I := I) g₀ x om) ww =
      cotangentToDualLinear (I := I) (x := x) om ww from by
    rw [← inverseMetricSharpFib_inner (I := I) g₀ x om ww]]
  rfl

set_option linter.unusedSectionVars false in
private lemma cotangentToDual_map_sub_dla (x : M) (om : Tensor0SSpace 1 I x)
    (a b : TangentSpace I x) :
    cotangentToDual (I := I) (x := x) om (a - b) =
      cotangentToDual (I := I) (x := x) om a - cotangentToDual (I := I) (x := x) om b := by
  simp only [show ∀ v : TangentSpace I x, cotangentToDual (I := I) (x := x) om v =
      cotangentToDualLinear (I := I) (x := x) om v from fun v => rfl]
  exact map_sub _ a b

set_option linter.unusedSectionVars false in
private lemma cotangentToDual_map_add_dla (x : M) (om : Tensor0SSpace 1 I x)
    (a b : TangentSpace I x) :
    cotangentToDual (I := I) (x := x) om (a + b) =
      cotangentToDual (I := I) (x := x) om a + cotangentToDual (I := I) (x := x) om b := by
  simp only [show ∀ v : TangentSpace I x, cotangentToDual (I := I) (x := x) om v =
      cotangentToDualLinear (I := I) (x := x) om v from fun v => rfl]
  exact map_add _ a b

private noncomputable def dLaCovKernelCLM (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun v0 => dLaCovKernel (I := I) g₁ g_bg x v0
      map_add' := fun v0 v0' => by
        apply ContinuousLinearMap.ext
        intro p
        apply ContinuousLinearMap.ext
        intro q
        simp only [ContinuousLinearMap.add_apply]
        exact dLaCovKernel_add_left (I := I) g₁ g_bg x v0 v0' p q
      map_smul' := fun c v0 => by
        apply ContinuousLinearMap.ext
        intro p
        apply ContinuousLinearMap.ext
        intro q
        simp only [RingHom.id_apply, ContinuousLinearMap.smul_apply]
        exact dLaCovKernel_smul_left (I := I) g₁ g_bg x c v0 p q }

set_option linter.unusedSectionVars false in
private lemma dLaCovKernelCLM_apply (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v0 p q : TangentSpace I x) :
    dLaCovKernelCLM (I := I) (M := M) g₁ g_bg x v0 p q =
      dLaCovKernel (I := I) g₁ g_bg x v0 p q := by
  rw [dLaCovKernelCLM, LinearMap.coe_toContinuousLinearMap']
  rfl

private noncomputable def dLaLoweredCovec (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 4 I x :=
  (show ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ from
    { toFun := fun m =>
        g₀.inner x (dLaCovKernelCLM (I := I) (M := M) g₁ g_bg x (m 1) (m 2) (m 3)) (m 0)
      map_update_add' := by
        have h01 : (0 : Fin 4) ≠ 1 := by decide
        have h02 : (0 : Fin 4) ≠ 2 := by decide
        have h03 : (0 : Fin 4) ≠ 3 := by decide
        have h10 : (1 : Fin 4) ≠ 0 := by decide
        have h12 : (1 : Fin 4) ≠ 2 := by decide
        have h13 : (1 : Fin 4) ≠ 3 := by decide
        have h20 : (2 : Fin 4) ≠ 0 := by decide
        have h21 : (2 : Fin 4) ≠ 1 := by decide
        have h23 : (2 : Fin 4) ≠ 3 := by decide
        have h30 : (3 : Fin 4) ≠ 0 := by decide
        have h31 : (3 : Fin 4) ≠ 1 := by decide
        have h32 : (3 : Fin 4) ≠ 2 := by decide
        intro _ m i a a'
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h02, h03, h10, h12, h13, h20, h21, h23, h30, h31, h32,
            not_false_eq_true, map_add, ContinuousLinearMap.add_apply]
      map_update_smul' := by
        have h01 : (0 : Fin 4) ≠ 1 := by decide
        have h02 : (0 : Fin 4) ≠ 2 := by decide
        have h03 : (0 : Fin 4) ≠ 3 := by decide
        have h10 : (1 : Fin 4) ≠ 0 := by decide
        have h12 : (1 : Fin 4) ≠ 2 := by decide
        have h13 : (1 : Fin 4) ≠ 3 := by decide
        have h20 : (2 : Fin 4) ≠ 0 := by decide
        have h21 : (2 : Fin 4) ≠ 1 := by decide
        have h23 : (2 : Fin 4) ≠ 3 := by decide
        have h30 : (3 : Fin 4) ≠ 0 := by decide
        have h31 : (3 : Fin 4) ≠ 1 := by decide
        have h32 : (3 : Fin 4) ≠ 2 := by decide
        intro _ m i c a
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h02, h03, h10, h12, h13, h20, h21, h23, h30, h31, h32,
            not_false_eq_true, map_smul, ContinuousLinearMap.smul_apply]
      cont := by
        have hK : Continuous (fun m : Fin 4 → TangentSpace I x =>
            dLaCovKernelCLM (I := I) (M := M) g₁ g_bg x (m 1) (m 2) (m 3)) :=
          (((dLaCovKernelCLM (I := I) (M := M) g₁ g_bg x).continuous.comp
            (continuous_apply 1)).clm_apply (continuous_apply 2)).clm_apply (continuous_apply 3)
        exact ((g₀.inner x).continuous.comp hK).clm_apply (continuous_apply 0) }
    : Tensor0SSpace 4 I x)

set_option linter.unusedSectionVars false in
@[simp] private lemma dLaLoweredCovec_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 4 → TangentSpace I x) :
    dLaLoweredCovec (I := I) g₀ g₁ g_bg x m =
      g₀.inner x (dLaCovKernel (I := I) g₁ g_bg x (m 1) (m 2) (m 3)) (m 0) := by
  change g₀.inner x (dLaCovKernelCLM (I := I) (M := M) g₁ g_bg x (m 1) (m 2) (m 3)) (m 0) = _
  rw [dLaCovKernelCLM_apply]

set_option linter.unusedSectionVars false in
private lemma dLaLoweredScalar_global (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    {V0 W p q : Π b : M, TangentSpace I b}
    (hV0 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V0))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₀.inner x
        (dLaCovKernel (I := I) g₁ g_bg x (V0 x) (p x) (q x)) (W x)) := by
  classical
  have hAsec := deTurckLieCovDerivA_section_contMDiff (I := I) g₁ g_bg V0 p q hV0 hp hq
  have hcongr : (fun x : M => g₀.inner x
        (dLaCovKernel (I := I) g₁ g_bg x (V0 x) (p x) (q x)) (W x)) =
      (fun x : M => g₀.inner x (deTurckLieCovDerivA (I := I) g₁ g_bg V0 p q x) (W x)) := by
    funext x
    rw [dLaCovKernel_apply_field3 (I := I) g₁ g_bg x V0 p q
      (hV0.contMDiffAt.mdifferentiableAt (by simp))
      (hp.contMDiffAt.mdifferentiableAt (by simp))
      (hq.contMDiffAt.mdifferentiableAt (by simp))]
  rw [hcongr]
  exact contMDiff_g_inner_of_smooth_sections (I := I) g₀
    ⟨fun b => deTurckLieCovDerivA (I := I) g₁ g_bg V0 p q b, hAsec⟩ ⟨fun b => W b, hW⟩

set_option linter.unusedSectionVars false in
private lemma dLaLoweredScalar_contMDiffAt (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (V0 V1 V2 V3 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x₀ : M) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        g₀.inner x (dLaCovKernel (I := I) g₁ g_bg x (V1 x) (V2 x) (V3 x)) (V0 x)) x₀ := by
  have hglob := dLaLoweredScalar_global (I := I) (M := M) g₀ g₁ g_bg
    (V0 := fun b => V1 b) (W := fun b => V0 b) (p := fun b => V2 b) (q := fun b => V3 b)
    V1.contMDiff V0.contMDiff V2.contMDiff V3.contMDiff
  exact hglob.contMDiffAt

set_option backward.isDefEq.respectTransparency false in
private theorem dLaLoweredCovec_section_contMDiff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SSpace 4 I z) x (dLaLoweredCovec (I := I) g₀ g₁ g_bg x)) := by
  classical
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 4
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (dLaLoweredCovec (I := I) g₀ g₁ g_bg x :
        Bundle.continuousMultilinearMap ℝ 4 E (TangentSpace I) x))).mpr ?_
  intro σ x₀
  set b := Module.finBasis ℝ E with hb
  set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₀.inner x
        (dLaCovKernel (I := I) g₁ g_bg x (Y (σ 1) x) (Y (σ 2) x) (Y (σ 3) x))
        (Y (σ 0) x)) x₀ :=
    dLaLoweredScalar_contMDiffAt (I := I) (M := M) g₀ g₁ g_bg
      (Y (σ 0)) (Y (σ 1)) (Y (σ 2)) (Y (σ 3)) x₀
  refine hscalar.congr_of_eventuallyEq ?_
  have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
  filter_upwards [h_base₁, hY] with x hx₁ hYx
  rw [continuousMultilinearMap_basis_repr]
  have hframeEq : ∀ k : Fin 4, e₁.symmL ℝ x (b (σ k)) = (Y (σ k)) x := by
    intro k
    rw [hYx (σ k), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    simp [Trivialization.basisAt]
  change dLaLoweredCovec (I := I) g₀ g₁ g_bg x (fun k => e₁.symmL ℝ x (b (σ k))) = _
  rw [dLaLoweredCovec_apply]
  rw [hframeEq 0, hframeEq 1, hframeEq 2, hframeEq 3]

private def dLaLoweredField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 4 :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 4
  ⟨fun x => dLaLoweredCovec (I := I) g₀ g₁ g_bg x,
    dLaLoweredCovec_section_contMDiff (I := I) (M := M) g₀ g₁ g_bg⟩

private def dLaLoweredCc (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 4 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (dLaLoweredField (I := I) (M := M) g₀ g₁ g_bg)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma dLaLoweredCc_unitModel (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    unitModel (I := I) (M := M) g₀ 4 (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg) x =
      Tensor0SSpace.toModel (dLaLoweredCovec (I := I) g₀ g₁ g_bg x) := by
  rw [unitModel]
  rw [show (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg).toSection x
        (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (dLaLoweredField (I := I) (M := M) g₀ g₁ g_bg x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

set_option linter.unusedSectionVars false in
private lemma dLaLoweredCc_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4 (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg) x m =
      g₀.inner x (dLaCovKernel (I := I) g₁ g_bg x (m 1) (m 2) (m 3)) (m 0) := by
  rw [dLaLoweredCc_unitModel]
  exact dLaLoweredCovec_apply (I := I) (M := M) g₀ g₁ g_bg x m

private def dLaConnArmPt (g₀ gc : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)) :=
  ⟨fun x : M => PDE.DeTurck.connDiff (I := I) gc g₀ x,
    bilinEndoField_contMDiff (I := I) (M := M)
      (fun x : M => PDE.DeTurck.connDiff (I := I) gc g₀ x)
      (fun V0 W => PDE.DeTurck.connDiff_contMDiff (I := I) gc g₀ V0.contMDiff W.contMDiff)⟩

set_option linter.unusedSectionVars false in
private lemma dLaConnArmPt_apply (g₀ gc : SmoothRiemannianMetric I M) (x : M) :
    dLaConnArmPt (I := I) (M := M) g₀ gc x = PDE.DeTurck.connDiff (I := I) gc g₀ x := rfl

private def dLaQuadCc (g₀ g_arm g_out : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 1 3 :=
  appCcRS (I := I) (M := M) g₀ 1 2 3
    (armSlotEndoPassZeroCc (I := I) (M := M) g₀ (dLaConnArmPt (I := I) (M := M) g₀ g_arm))
    (connDiffSection (I := I) g_out g₀)

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma dLaQuadCc_toModel (g₀ g_arm g_out : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (w : Fin 3 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (dLaQuadCc (I := I) (M := M) g₀ g_arm g_out).toSection x) om) w =
      cotangentToDual (I := I) (x := x) om
        (PDE.DeTurck.connDiff (I := I) g_out g₀ x
          (PDE.DeTurck.connDiff (I := I) g_arm g₀ x (w 1) (w 2)) (w 0)) := by
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (dLaQuadCc (I := I) (M := M) g₀ g_arm g_out).toSection x) om) =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (appCcRS (I := I) (M := M) g₀ 1 2 3
          (armSlotEndoPassZeroCc (I := I) (M := M) g₀
            (dLaConnArmPt (I := I) (M := M) g₀ g_arm))
          (connDiffSection (I := I) g_out g₀)).toSection x) om) from rfl]
  rw [toModel_appCcRS_armSlotEndoPassZeroCc_eval (I := I) (M := M) g₀
    (dLaConnArmPt (I := I) (M := M) g₀ g_arm) (connDiffSection (I := I) g_out g₀) x om w]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (connDiffSection (I := I) g_out g₀).toSection x) om) =
      connDiffPairing (I := I) g_out g₀ x om from rfl]
  have hchg : Tensor0SSpace.toModel (connDiffPairing (I := I) g_out g₀ x om)
      (fun j : Fin 2 => if j = 0 then
        dLaConnArmPt (I := I) (M := M) g₀ g_arm x (w 1) (w 2) else w 0) =
      connDiffPairing (I := I) g_out g₀ x om
        (fun j : Fin 2 => if j = 0 then
          dLaConnArmPt (I := I) (M := M) g₀ g_arm x (w 1) (w 2) else w 0) := rfl
  rw [hchg]
  rw [show (fun j : Fin 2 => if j = 0 then
        dLaConnArmPt (I := I) (M := M) g₀ g_arm x (w 1) (w 2) else w 0) =
      (Fin.cons (PDE.DeTurck.connDiff (I := I) g_arm g₀ x (w 1) (w 2))
        (fun _ : Fin 1 => w 0) : Fin 2 → TangentSpace I x) from by
    funext j
    refine Fin.cases ?_ ?_ j
    · rw [if_pos rfl]
      rfl
    · intro i
      rw [if_neg (Fin.succ_ne_zero i)]
      rfl]
  rw [connDiffPairing_apply]
  rw [cotangentToDual_apply]
  rfl

private def dLaKernelRaisedCc (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 1 3 :=
  covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)
    - covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g_bg g₀)
    + dLaQuadCc (I := I) (M := M) g₀ g₁ g₁
    - dLaQuadCc (I := I) (M := M) g₀ g_bg g₁
    - rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (0 : Fin 3) 2)
        (dLaQuadCc (I := I) (M := M) g₀ g₁ g₁)
    + rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (0 : Fin 3) 2)
        (dLaQuadCc (I := I) (M := M) g₀ g₁ g_bg)
    - rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3)
        (dLaQuadCc (I := I) (M := M) g₀ g₁ g₁)
    + rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3)
        (dLaQuadCc (I := I) (M := M) g₀ g₁ g_bg)

private def dLaCovectorExtensionSection (g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) :
    Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun y : M => Tensor0SSpace 1 I y)⟯ :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 1
  ⟨fun b : M => g0FlatCLM (I := I) g₀ b
      (smoothExtensionTangent (I := I) x (inverseMetricSharpFib (I := I) g₀ x om) b),
   by
     have hU : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
         (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
           (smoothExtensionTangent (I := I) x (inverseMetricSharpFib (I := I) g₀ x om) b)) :=
       smoothExtensionTangent_contMDiff (I := I) x (inverseMetricSharpFib (I := I) g₀ x om)
     exact ContMDiff.clm_bundle_apply (b := id) (g0FlatField_contMDiff (I := I) g₀) hU⟩

set_option linter.unusedSectionVars false in
private lemma dLaCovectorExtensionSection_self (g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) :
    dLaCovectorExtensionSection (I := I) (M := M) g₀ x om x = om := by
  change g0FlatCLM (I := I) g₀ x
      (smoothExtensionTangent (I := I) x (inverseMetricSharpFib (I := I) g₀ x om) x) = om
  rw [smoothExtensionTangent_eq (I := I) x (inverseMetricSharpFib (I := I) g₀ x om)]
  exact g0FlatCLM_inverseMetricSharpFib (I := I) g₀ x om

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
private theorem dLaLoweredCc_raise_repr (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    cometricRaiseSlot0Field (I := I) (M := M) g₀ 2
        (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg) =
      dLaKernelRaisedCc (I := I) (M := M) g₀ g₁ g_bg := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro om
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  have hexp_sub : ∀ (F G : SmoothCcTensor g₀ 1 3),
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from ((F - G).toSection x)) om) w =
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from (F.toSection x)) om) w -
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from (G.toSection x)) om) w := by
    intro F G
    rw [show ((F - G).toSection x) = F.toSection x - G.toSection x from by
      rw [SmoothCcTensor.toSection_sub]; rfl]
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (F.toSection x - G.toSection x)) om) =
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from F.toSection x) om -
          (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from G.toSection x) om from rfl]
    rw [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  have hexp_add : ∀ (F G : SmoothCcTensor g₀ 1 3),
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from ((F + G).toSection x)) om) w =
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from (F.toSection x)) om) w +
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from (G.toSection x)) om) w := by
    intro F G
    rw [show ((F + G).toSection x) = F.toSection x + G.toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (F.toSection x + G.toSection x)) om) =
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from F.toSection x) om +
          (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from G.toSection x) om from rfl]
    rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  have hA : ∀ (gc : SmoothRiemannianMetric I M),
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) gc g₀)).toSection x) om)
        w =
      cotangentToDual (I := I) (x := x) om
        (covDerivConnDiff (I := I) g₀ gc
          (smoothExtensionTangent (I := I) x (w 0))
          (smoothExtensionTangent (I := I) x (w 2))
          (smoothExtensionTangent (I := I) x (w 1)) x) := by
    intro gc
    have hb := connDiffSection_covGrad_eq_covDerivConnDiff (I := I) gc g₀
      (dLaCovectorExtensionSection (I := I) (M := M) g₀ x om)
      (smoothExtensionTangentSection (I := I) (M := M) x (w 0))
      (smoothExtensionTangentSection (I := I) (M := M) x (w 1))
      (smoothExtensionTangentSection (I := I) (M := M) x (w 2)) x
    rw [dLaCovectorExtensionSection_self (I := I) (M := M) g₀ x om] at hb
    rw [show smoothExtensionTangentSection (I := I) (M := M) x (w 0) x = w 0 from
      smoothExtensionTangent_eq (I := I) x (w 0)] at hb
    rw [show smoothExtensionTangentSection (I := I) (M := M) x (w 1) x = w 1 from
      smoothExtensionTangent_eq (I := I) x (w 1)] at hb
    rw [show smoothExtensionTangentSection (I := I) (M := M) x (w 2) x = w 2 from
      smoothExtensionTangent_eq (I := I) x (w 2)] at hb
    rw [show (Fin.cons (w 0) (Fin.cons (w 1) ![w 2]) : Fin 3 → TangentSpace I x) = w from by
      funext k
      refine Fin.cases rfl (fun j => ?_) k
      refine Fin.cases rfl (fun j' => ?_) j
      refine Fin.cases rfl (fun j'' => j''.elim0) j'] at hb
    rw [hb]
    rw [show covDerivConnDiff (I := I) g₀ gc
        (fun b => smoothExtensionTangentSection (I := I) (M := M) x (w 0) b)
        (fun b => smoothExtensionTangentSection (I := I) (M := M) x (w 2) b)
        (fun b => smoothExtensionTangentSection (I := I) (M := M) x (w 1) b) x =
      covDerivConnDiff (I := I) g₀ gc
        (smoothExtensionTangent (I := I) x (w 0))
        (smoothExtensionTangent (I := I) x (w 2))
        (smoothExtensionTangent (I := I) x (w 1)) x from rfl]
    exact (cotangentToDual_apply (I := I) (x := x) om _).symm
  have hswap0 : (Equiv.swap (0 : Fin 3) 2) 0 = 2 := Equiv.swap_apply_left 0 2
  have hswap1 : (Equiv.swap (0 : Fin 3) 2) 1 = 1 := by decide
  have hswap2 : (Equiv.swap (0 : Fin 3) 2) 2 = 0 := Equiv.swap_apply_right 0 2
  have hrot0 : (finRotate 3) (0 : Fin 3) = 1 := by decide
  have hrot1 : (finRotate 3) (1 : Fin 3) = 2 := by decide
  have hrot2 : (finRotate 3) (2 : Fin 3) = 0 := by decide
  have hQperm : ∀ (σ : Equiv.Perm (Fin 3)) (ga gb : SmoothRiemannianMetric I M),
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 σ
            (dLaQuadCc (I := I) (M := M) g₀ ga gb)).toSection x) om) w =
      cotangentToDual (I := I) (x := x) om
        (PDE.DeTurck.connDiff (I := I) gb g₀ x
          (PDE.DeTurck.connDiff (I := I) ga g₀ x (w (σ 1)) (w (σ 2))) (w (σ 0))) := by
    intro σ ga gb
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 σ
          (dLaQuadCc (I := I) (M := M) g₀ ga gb)).toSection x) om) =
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          rsDomDomCongr σ ((dLaQuadCc (I := I) (M := M) g₀ ga gb).toSection x)) om) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) σ
      ((dLaQuadCc (I := I) (M := M) g₀ ga gb).toSection x) om]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    exact dLaQuadCc_toModel (I := I) (M := M) g₀ ga gb x om (fun i => w (σ i))
  have hL : Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 2
          (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) om) w =
      cotangentToDual (I := I) (x := x) om
        (dLaCovKernel (I := I) g₁ g_bg x (w 0) (w 1) (w 2)) := by
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 2
          (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) om) =
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          cometricRaiseSlot0Fib g₀ 2 x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
              (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg).toSection x)
              (unitTensor (I := I) (M := M) x))) om) from by
      rw [cometricRaiseSlot0Field_toSection]]
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 2 x _ om]
    rw [interiorProduct_toModel_eval_dla (I := I) (M := M) 3 x
      (inverseMetricSharpFib (I := I) g₀ x om) _ w]
    rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
          (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg).toSection x)
          (unitTensor (I := I) (M := M) x)) =
        unitModel (I := I) (M := M) g₀ 4 (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg) x
        from rfl]
    rw [dLaLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x]
    rw [show (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x om)
        (fun k => (show E from w k)) : Fin 4 → TangentSpace I x) 0 =
        inverseMetricSharpFib (I := I) g₀ x om from rfl]
    rw [show (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x om)
        (fun k => (show E from w k)) : Fin 4 → TangentSpace I x) 1 = w 0 from rfl]
    rw [show (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x om)
        (fun k => (show E from w k)) : Fin 4 → TangentSpace I x) 2 = w 1 from rfl]
    rw [show (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x om)
        (fun k => (show E from w k)) : Fin 4 → TangentSpace I x) 3 = w 2 from rfl]
    rw [cotangentToDual_eq_inner_sharp_dla (I := I) (M := M) g₀ x om
      (dLaCovKernel (I := I) g₁ g_bg x (w 0) (w 1) (w 2))]
  rw [hL]
  rw [dLaKernelRaisedCc]
  rw [hexp_add, hexp_sub, hexp_add, hexp_sub, hexp_sub, hexp_add, hexp_sub]
  rw [hA g₁, hA g_bg]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (dLaQuadCc (I := I) (M := M) g₀ g₁ g₁).toSection x) om) w =
      cotangentToDual (I := I) (x := x) om
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) (w 2)) (w 0)) from
    dLaQuadCc_toModel (I := I) (M := M) g₀ g₁ g₁ x om w]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (dLaQuadCc (I := I) (M := M) g₀ g_bg g₁).toSection x) om) w =
      cotangentToDual (I := I) (x := x) om
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g_bg g₀ x (w 1) (w 2)) (w 0)) from
    dLaQuadCc_toModel (I := I) (M := M) g₀ g_bg g₁ x om w]
  rw [hQperm (Equiv.swap (0 : Fin 3) 2) g₁ g₁, hQperm (Equiv.swap (0 : Fin 3) 2) g₁ g_bg,
    hQperm (finRotate 3) g₁ g₁, hQperm (finRotate 3) g₁ g_bg]
  rw [hswap0, hswap1, hswap2, hrot0, hrot1, hrot2]
  rw [dLaCovKernel_backgroundSplit (I := I) g₀ g₁ g_bg x (w 0) (w 1) (w 2)]
  have hcocy : ∀ u v : TangentSpace I x,
      PDE.DeTurck.connDiff (I := I) g₁ g_bg x u v =
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v -
          PDE.DeTurck.connDiff (I := I) g_bg g₀ x u v :=
    fun u v => eq_sub_of_add_eq (connDiff_cocycle (I := I) g₁ g_bg g₀ x u v)
  rw [hcocy (w 1) (w 2)]
  rw [show PDE.DeTurck.connDiff (I := I) g₁ g₀ x
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) (w 2) -
        PDE.DeTurck.connDiff (I := I) g_bg g₀ x (w 1) (w 2)) (w 0) =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) (w 2)) (w 0) -
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g_bg g₀ x (w 1) (w 2)) (w 0) from by
    rw [map_sub]
    rfl]
  rw [hcocy (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) (w 0)) (w 2)]
  rw [show PDE.DeTurck.connDiff (I := I) g₁ g_bg x (w 1)
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 2) (w 0)) =
      PDE.DeTurck.connDiff (I := I) g₁ g_bg x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 2) (w 0)) (w 1) from
    PDE.DeTurck.connDiff_symm (I := I) g₁ g_bg x (w 1)
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 2) (w 0))]
  rw [hcocy (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 2) (w 0)) (w 1)]
  rw [cotangentToDual_map_sub_dla, cotangentToDual_map_sub_dla, cotangentToDual_map_add_dla,
    cotangentToDual_map_sub_dla, cotangentToDual_map_sub_dla, cotangentToDual_map_sub_dla,
    cotangentToDual_map_sub_dla]
  ring

set_option backward.isDefEq.respectTransparency false in
private noncomputable def dLaPerturbSharpEndoFib (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => metricSharp (I := I) g₀ x
        (ccTensorBilinSymm (I := I) g₀ T x v).toLinearMap
      map_add' := fun v v' => by
        have h : ((ccTensorBilinSymm (I := I) g₀ T x (v + v')).toLinearMap) =
            (ccTensorBilinSymm (I := I) g₀ T x v).toLinearMap +
              (ccTensorBilinSymm (I := I) g₀ T x v').toLinearMap := by
          ext w
          simp [map_add]
        rw [show metricSharp (I := I) g₀ x
            (ccTensorBilinSymm (I := I) g₀ T x (v + v')).toLinearMap =
            (metricFlatMap (I := I) g₀ x).symm
              (ccTensorBilinSymm (I := I) g₀ T x (v + v')).toLinearMap from rfl,
          h, map_add]
        rfl
      map_smul' := fun c v => by
        have h : ((ccTensorBilinSymm (I := I) g₀ T x (c • v)).toLinearMap) =
            c • (ccTensorBilinSymm (I := I) g₀ T x v).toLinearMap := by
          ext w
          simp [map_smul]
        rw [show metricSharp (I := I) g₀ x
            (ccTensorBilinSymm (I := I) g₀ T x (c • v)).toLinearMap =
            (metricFlatMap (I := I) g₀ x).symm
              (ccTensorBilinSymm (I := I) g₀ T x (c • v)).toLinearMap from rfl,
          h, map_smul]
        rfl }

set_option linter.unusedSectionVars false in
private lemma dLaPerturbSharpEndoFib_apply (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (v : TangentSpace I x) :
    dLaPerturbSharpEndoFib (I := I) (M := M) g₀ T x v =
      metricSharp (I := I) g₀ x (ccTensorBilinSymm (I := I) g₀ T x v).toLinearMap := by
  rw [dLaPerturbSharpEndoFib, LinearMap.coe_toContinuousLinearMap']
  rfl

set_option linter.unusedSectionVars false in
private lemma inner_dLaPerturbSharpEndoFib (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (v w : TangentSpace I x) :
    g₀.inner x (dLaPerturbSharpEndoFib (I := I) (M := M) g₀ T x v) w =
      ccTensorBilinSymm (I := I) g₀ T x v w := by
  rw [dLaPerturbSharpEndoFib_apply]
  exact inner_metricSharp (I := I) g₀ x
    (ccTensorBilinSymm (I := I) g₀ T x v).toLinearMap w

set_option backward.isDefEq.respectTransparency false in
private theorem dLaPerturbSharpEndoFib_contMDiff (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) x
        (dLaPerturbSharpEndoFib (I := I) (M := M) g₀ T x)) := by
  apply cotangentCov_clmSection_smooth_aux (I := I) (M := M)
    (F₂ := E) (V₂ := fun y : M => TangentSpace I y)
    (φ := fun x : M => dLaPerturbSharpEndoFib (I := I) (M := M) g₀ T x)
  intro Y
  have hcv : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => (ccTensorBilinSymm (I := I) g₀ T b (Y b)).toLinearMap
          (chartBasisVecFiber (I := I) α j b))
        (chartAt H α).source := by
    intro α j
    have hB : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) b
          (ccTensorBilinSymm (I := I) g₀ T b)) :=
      ccTensorBilinSymm_contMDiff (I := I) g₀ T
    have hBasis : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (chartBasisVec (I := I) α j)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartBasisVec_contMDiffOn (I := I) α j
    have happ : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun b : M => (⟨b,
            ccTensorBilinSymm (I := I) g₀ T b (Y b) (chartBasisVecFiber (I := I) α j b)⟩ :
            TotalSpace ℝ (Bundle.Trivial M ℝ)))
        (trivializationAt E (TangentSpace I) α).baseSet :=
      ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
        (b := id) hB.contMDiffOn Y.contMDiff.contMDiffOn hBasis
    have hbase_eq :
        (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
      trivializationAt_baseSet_eq_chartAt_source (I := I) α
    rw [hbase_eq] at happ
    intro b hb
    have hpb := happ b hb
    rw [Bundle.contMDiffWithinAt_totalSpace] at hpb
    exact hpb.2
  have hsmooth := metricSharp_contMDiff_total (I := I) g₀
    (cv := fun b : M => (ccTensorBilinSymm (I := I) g₀ T b (Y b)).toLinearMap) hcv
  refine hsmooth.congr ?_
  intro x
  change TotalSpace.mk' E x
      (metricSharp (I := I) g₀ x (ccTensorBilinSymm (I := I) g₀ T x (Y x)).toLinearMap) =
    TotalSpace.mk' E x (dLaPerturbSharpEndoFib (I := I) (M := M) g₀ T x (Y x))
  rw [dLaPerturbSharpEndoFib_apply]

private noncomputable def dLaPerturbSharpEndoField (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) where
  toFun := fun x : M => dLaPerturbSharpEndoFib (I := I) (M := M) g₀ T x
  contMDiff_toFun := dLaPerturbSharpEndoFib_contMDiff (I := I) (M := M) g₀ T

set_option linter.unusedSectionVars false in
private lemma unitModel_eq_ccTensorBilin_dla (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (b : M) (u w : TangentSpace I b) :
    unitModel (I := I) (M := M) g₀ 2 S b ![u, w] = ccTensorBilin (I := I) g₀ S b u w := by
  rw [ccTensorBilin_apply (I := I) g₀ S b u w, ccTensorModel]
  rw [show ccTensorMultilinear (I := I) g₀ S b =
      (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from S.toSection b)
        (unitZeroSec (I := I) (M := M) b) from rfl]
  rw [unitModel]
  refine congrArg _ ?_
  funext k
  fin_cases k <;> rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma dLaSlotInsert_perturbSharp_eq_raise_symmS (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) :
    slotInsertEndoCc (I := I) (M := M) g₀ 0 (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T) =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
          (symmS (I := I) (M := M) g₀ T)) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro om
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T)).toSection x) om) w =
      ccTensorBilinSymm (I := I) g₀ T x (w 0)
        (inverseMetricSharpFib (I := I) g₀ x om) := by
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T)).toSection x) om) =
        slotInsertEndoFib (I := I) (M := M) 1 0 x
          (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x) om from rfl]
    rw [slotInsertEndoFib_apply_eval]
    rw [toModel_om_single_eq_cotangentToDual_dla (I := I) (M := M) x om
      (Function.update w 0 (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x (w 0)))]
    rw [Function.update_self]
    rw [show (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x) =
        dLaPerturbSharpEndoFib (I := I) (M := M) g₀ T x from rfl]
    rw [cotangentToDual_eq_inner_sharp_dla (I := I) (M := M) g₀ x om
      (dLaPerturbSharpEndoFib (I := I) (M := M) g₀ T x (w 0))]
    rw [inner_dLaPerturbSharpEndoFib]
  rw [hLHS]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
            (symmS (I := I) (M := M) g₀ T))).toSection x) om) =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        cometricRaiseSlot0Fib g₀ 0 x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
              (symmS (I := I) (M := M) g₀ T)).toSection x)
            (unitTensor (I := I) (M := M) x))) om) from rfl]
  rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 0 x _ om]
  rw [interiorProduct_toModel_eval_dla (I := I) (M := M) 1 x
    (inverseMetricSharpFib (I := I) g₀ x om) _ w]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
          (symmS (I := I) (M := M) g₀ T)).toSection x)
        (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g₀ 2
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
          (symmS (I := I) (M := M) g₀ T)) x from rfl]
  rw [domDomCongrSection_unitModel (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
    (symmS (I := I) (M := M) g₀ T) x]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i : Fin 2 =>
      (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x om)
        (fun k => (show E from w k)) : Fin 2 → E) ((Equiv.swap (0 : Fin 2) 1) i)) =
      (![(w 0 : E), (show E from inverseMetricSharpFib (I := I) g₀ x om)] : Fin 2 → E) from by
    funext i
    fin_cases i <;> rfl]
  rw [unitModel_eq_ccTensorBilin_dla (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ T) x
    (w 0) (inverseMetricSharpFib (I := I) g₀ x om)]
  rw [ccTensorBilin_symmS (I := I) (M := M) g₀ T x]

private noncomputable def dLaLoweredPerturbCc (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 0 4 :=
  appCcRS (I := I) (M := M) g₀ 0 4 4
    (slotInsertEndoCc (I := I) (M := M) g₀ 3 (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T))
    (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)

private noncomputable def dLaLoweredG1Cc (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 0 4 :=
  dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg +
    dLaLoweredPerturbCc (I := I) (M := M) g₀ T g₁ g_bg

set_option linter.unusedSectionVars false in
private lemma unitModel_add_dla (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g₀ 0 s) (x : M) (m : Fin s → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ s (A + B) x m =
      unitModel (I := I) (M := M) g₀ s A x m + unitModel (I := I) (M := M) g₀ s B x m := by
  rw [unitModel, unitModel, unitModel]
  rw [show ((A + B).toSection x) = A.toSection x + B.toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      (A.toSection x + B.toSection x)) (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from A.toSection x)
          (unitTensor (I := I) (M := M) x) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from B.toSection x)
          (unitTensor (I := I) (M := M) x) from rfl]
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma dLaLoweredPerturbCc_unitModel_apply (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4
        (dLaLoweredPerturbCc (I := I) (M := M) g₀ T g₁ g_bg) x m =
      ccTensorBilinSymm (I := I) g₀ T x
        (dLaCovKernel (I := I) g₁ g_bg x (m 1) (m 2) (m 3)) (m 0) := by
  have hsec : unitModel (I := I) (M := M) g₀ 4
      (dLaLoweredPerturbCc (I := I) (M := M) g₀ T g₁ g_bg) x m =
      Tensor0SSpace.toModel
        (slotInsertEndoFib (I := I) (M := M) 4 0 x
          (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
            (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg).toSection x)
            (unitTensor (I := I) (M := M) x))) m := by
    rw [unitModel]
    rw [show ((dLaLoweredPerturbCc (I := I) (M := M) g₀ T g₁ g_bg).toSection x)
        (unitTensor (I := I) (M := M) x) =
        slotInsertEndoFib (I := I) (M := M) 4 0 x
          (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
            (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg).toSection x)
            (unitTensor (I := I) (M := M) x)) from by
      rw [dLaLoweredPerturbCc, appCcRS_toSection]
      rfl]
  rw [hsec]
  rw [slotInsertEndoFib_apply_eval]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
        (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg).toSection x)
        (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g₀ 4 (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg) x from rfl]
  rw [dLaLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x]
  rw [show (Function.update m 0
      (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x (m 0))) 0 =
      dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x (m 0) from Function.update_self _ _ _]
  rw [show (Function.update m 0
      (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x (m 0))) 1 = m 1 from
    Function.update_of_ne (by decide) _ _]
  rw [show (Function.update m 0
      (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x (m 0))) 2 = m 2 from
    Function.update_of_ne (by decide) _ _]
  rw [show (Function.update m 0
      (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x (m 0))) 3 = m 3 from
    Function.update_of_ne (by decide) _ _]
  rw [g₀.symm x (dLaCovKernel (I := I) g₁ g_bg x (m 1) (m 2) (m 3))
    (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x (m 0))]
  rw [show (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x) =
      dLaPerturbSharpEndoFib (I := I) (M := M) g₀ T x from rfl]
  rw [inner_dLaPerturbSharpEndoFib (I := I) (M := M) g₀ T x (m 0)
    (dLaCovKernel (I := I) g₁ g_bg x (m 1) (m 2) (m 3))]
  exact ccTensorBilinSymm_symm (I := I) g₀ T x (m 0)
    (dLaCovKernel (I := I) g₁ g_bg x (m 1) (m 2) (m 3))

private def dLaGridWin (b : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range m, Combinatorics.antidiagonalTupleGrid b k

private lemma dLaGridWin_nonneg (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (m : ℕ) :
    0 ≤ dLaGridWin b m :=
  Finset.sum_nonneg fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k

private lemma dLaGridWin_mono (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) {m m' : ℕ} (h : m ≤ m') :
    dLaGridWin b m ≤ dLaGridWin b m' :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h)
    (fun k _ _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k)

private lemma one_le_dLaGridWin (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) {m : ℕ} (hm : 1 ≤ m) :
    1 ≤ dLaGridWin b m := by
  have h1 : Combinatorics.antidiagonalTupleGrid b 0 = 1 :=
    Combinatorics.antidiagonalTupleGrid_zero b
  calc (1 : ℝ) = dLaGridWin b 1 := by
        rw [dLaGridWin, Finset.sum_range_one, h1]
    _ ≤ dLaGridWin b m := dLaGridWin_mono b hb hm

private lemma grid_le_dLaGridWin (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) {k m : ℕ} (h : k < m) :
    Combinatorics.antidiagonalTupleGrid b k ≤ dLaGridWin b m :=
  Finset.single_le_sum
    (f := fun k' => Combinatorics.antidiagonalTupleGrid b k')
    (fun k' _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k')
    (Finset.mem_range.mpr h)

private lemma single_le_grid_dla (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (j : ℕ) (hj : 1 ≤ j) :
    b j ≤ Combinatorics.antidiagonalTupleGrid b j := by
  classical
  have hmem : (fun _ : Fin 1 => j) ∈ Finset.Nat.antidiagonalTuple 1 j := by
    rw [Finset.Nat.mem_antidiagonalTuple]
    simp
  have hprod : b j = ∏ m : Fin 1, b ((fun _ : Fin 1 => j) m) := by
    rw [Fin.prod_univ_one]
  rw [hprod, Combinatorics.antidiagonalTupleGrid]
  have h1 : (∏ m : Fin 1, b ((fun _ : Fin 1 => j) m)) ≤
      ∑ e ∈ Finset.Nat.antidiagonalTuple 1 j, ∏ m : Fin 1, b (e m) :=
    Finset.single_le_sum (f := fun e : Fin 1 → ℕ => ∏ m : Fin 1, b (e m))
      (fun e _ => Finset.prod_nonneg fun m _ => hb _) hmem
  refine le_trans h1 ?_
  exact Finset.single_le_sum
    (f := fun n : ℕ => ∑ e ∈ Finset.Nat.antidiagonalTuple n j, ∏ m : Fin n, b (e m))
    (fun n _ => Finset.sum_nonneg fun e _ => Finset.prod_nonneg fun m _ => hb _)
    (Finset.mem_range.mpr (by omega : (1 : ℕ) < j + 1))

private def dLaTGridCount (j : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (j + 1), ((Finset.Nat.antidiagonalTuple n j).card : ℝ)

private lemma dLaTGridCount_nonneg (j : ℕ) : 0 ≤ dLaTGridCount j :=
  Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

private lemma prodTerm_le_antidiagonalTupleGrid_dla (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (k n : ℕ) (hn : n < k + 1) (e : Fin n → ℕ)
    (he : e ∈ Finset.Nat.antidiagonalTuple n k) :
    (∏ m : Fin n, b (e m)) ≤ Combinatorics.antidiagonalTupleGrid b k := by
  rw [Combinatorics.antidiagonalTupleGrid]
  have h1 : (∏ m : Fin n, b (e m)) ≤
      ∑ e' ∈ Finset.Nat.antidiagonalTuple n k, ∏ m : Fin n, b (e' m) :=
    Finset.single_le_sum (f := fun e' : Fin n → ℕ => ∏ m : Fin n, b (e' m))
      (fun e' _ => Finset.prod_nonneg (fun m _ => hb _)) he
  refine le_trans h1 ?_
  exact Finset.single_le_sum
    (f := fun n' : ℕ => ∑ e' ∈ Finset.Nat.antidiagonalTuple n' k, ∏ m : Fin n', b (e' m))
    (fun n' _ => Finset.sum_nonneg (fun e' _ => Finset.prod_nonneg (fun m _ => hb _)))
    (Finset.mem_range.mpr hn)

private lemma antidiagonalTupleGrid_mul_le_dla (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (j k : ℕ) :
    Combinatorics.antidiagonalTupleGrid b j * Combinatorics.antidiagonalTupleGrid b k ≤
      (dLaTGridCount j * dLaTGridCount k) * Combinatorics.antidiagonalTupleGrid b (j + k) := by
  classical
  have hpair : ∀ n ∈ Finset.range (j + 1), ∀ e ∈ Finset.Nat.antidiagonalTuple n j,
      ∀ n' ∈ Finset.range (k + 1), ∀ e' ∈ Finset.Nat.antidiagonalTuple n' k,
      (∏ m : Fin n, b (e m)) * (∏ m : Fin n', b (e' m)) ≤
        Combinatorics.antidiagonalTupleGrid b (j + k) := by
    intro n hn e he n' hn' e' he'
    have happend : (∏ m : Fin n, b (e m)) * (∏ m : Fin n', b (e' m)) =
        ∏ m : Fin (n + n'), b (Fin.append e e' m) := by
      rw [Fin.prod_univ_add]
      congr 1
      · exact Finset.prod_congr rfl (fun m _ => by rw [Fin.append_left])
      · exact Finset.prod_congr rfl (fun m _ => by rw [Fin.append_right])
    rw [happend]
    have hmem : Fin.append e e' ∈ Finset.Nat.antidiagonalTuple (n + n') (j + k) := by
      rw [Finset.Nat.mem_antidiagonalTuple] at he he' ⊢
      rw [Fin.sum_univ_add]
      have h1 : (∑ m : Fin n, Fin.append e e' (Fin.castAdd n' m)) = j := by
        rw [← he]
        exact Finset.sum_congr rfl (fun m _ => by rw [Fin.append_left])
      have h2 : (∑ m : Fin n', Fin.append e e' (Fin.natAdd n m)) = k := by
        rw [← he']
        exact Finset.sum_congr rfl (fun m _ => by rw [Fin.append_right])
      rw [h1, h2]
    have hnn' : n + n' < j + k + 1 := by
      rw [Finset.mem_range] at hn hn'
      omega
    exact prodTerm_le_antidiagonalTupleGrid_dla b hb (j + k) (n + n') hnn' _ hmem
  calc Combinatorics.antidiagonalTupleGrid b j * Combinatorics.antidiagonalTupleGrid b k
      = ∑ n ∈ Finset.range (j + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n j,
          ((∏ m : Fin n, b (e m)) * Combinatorics.antidiagonalTupleGrid b k) := by
        rw [Combinatorics.antidiagonalTupleGrid, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun n _ => by rw [Finset.sum_mul])
    _ ≤ ∑ n ∈ Finset.range (j + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n j,
          (dLaTGridCount k * Combinatorics.antidiagonalTupleGrid b (j + k)) := by
        refine Finset.sum_le_sum (fun n hn => Finset.sum_le_sum (fun e he => ?_))
        calc (∏ m : Fin n, b (e m)) * Combinatorics.antidiagonalTupleGrid b k
            = ∑ n' ∈ Finset.range (k + 1), ∑ e' ∈ Finset.Nat.antidiagonalTuple n' k,
                ((∏ m : Fin n, b (e m)) * ∏ m : Fin n', b (e' m)) := by
              rw [Combinatorics.antidiagonalTupleGrid, Finset.mul_sum]
              exact Finset.sum_congr rfl (fun n' _ => by rw [Finset.mul_sum])
          _ ≤ ∑ n' ∈ Finset.range (k + 1), ∑ e' ∈ Finset.Nat.antidiagonalTuple n' k,
                Combinatorics.antidiagonalTupleGrid b (j + k) := by
              refine Finset.sum_le_sum (fun n' hn' => Finset.sum_le_sum (fun e' he' => ?_))
              exact hpair n hn e he n' hn' e' he'
          _ = dLaTGridCount k * Combinatorics.antidiagonalTupleGrid b (j + k) := by
              rw [dLaTGridCount, Finset.sum_mul]
              exact Finset.sum_congr rfl (fun n' _ => by
                rw [Finset.sum_const, nsmul_eq_mul])
    _ = ∑ n ∈ Finset.range (j + 1), ((Finset.Nat.antidiagonalTuple n j).card : ℝ) *
          (dLaTGridCount k * Combinatorics.antidiagonalTupleGrid b (j + k)) := by
        exact Finset.sum_congr rfl (fun n _ => by rw [Finset.sum_const, nsmul_eq_mul])
    _ = (dLaTGridCount j * dLaTGridCount k) * Combinatorics.antidiagonalTupleGrid b (j + k) := by
        rw [show (dLaTGridCount j * dLaTGridCount k) *
            Combinatorics.antidiagonalTupleGrid b (j + k) =
            dLaTGridCount j *
              (dLaTGridCount k * Combinatorics.antidiagonalTupleGrid b (j + k)) from by
          ring]
        rw [show dLaTGridCount j = ∑ n ∈ Finset.range (j + 1),
            ((Finset.Nat.antidiagonalTuple n j).card : ℝ) from rfl]
        rw [Finset.sum_mul]

private def dLaPairCount (m1 m2 : ℕ) : ℝ :=
  ∑ k1 ∈ Finset.range m1, ∑ k2 ∈ Finset.range m2, dLaTGridCount k1 * dLaTGridCount k2

private lemma dLaPairCount_nonneg (m1 m2 : ℕ) : 0 ≤ dLaPairCount m1 m2 :=
  Finset.sum_nonneg fun k1 _ => Finset.sum_nonneg fun k2 _ =>
    mul_nonneg (dLaTGridCount_nonneg k1) (dLaTGridCount_nonneg k2)

private lemma dLaGridWin_mul_le (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (m1 m2 m3 : ℕ)
    (h3 : m1 + m2 ≤ m3 + 1) :
    dLaGridWin b m1 * dLaGridWin b m2 ≤ dLaPairCount m1 m2 * dLaGridWin b m3 := by
  classical
  have hG_nn : ∀ k, 0 ≤ Combinatorics.antidiagonalTupleGrid b k :=
    fun k => Combinatorics.antidiagonalTupleGrid_nonneg b hb k
  rw [dLaGridWin, dLaGridWin, Finset.sum_mul]
  rw [dLaPairCount, Finset.sum_mul]
  refine Finset.sum_le_sum fun k1 hk1 => ?_
  calc Combinatorics.antidiagonalTupleGrid b k1 *
        ∑ k ∈ Finset.range m2, Combinatorics.antidiagonalTupleGrid b k
      = ∑ k2 ∈ Finset.range m2, Combinatorics.antidiagonalTupleGrid b k1 *
          Combinatorics.antidiagonalTupleGrid b k2 := by rw [Finset.mul_sum]
    _ ≤ ∑ k2 ∈ Finset.range m2, (dLaTGridCount k1 * dLaTGridCount k2) *
          dLaGridWin b m3 := by
        refine Finset.sum_le_sum fun k2 hk2 => ?_
        refine le_trans (antidiagonalTupleGrid_mul_le_dla b hb k1 k2) ?_
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (dLaTGridCount_nonneg k1) (dLaTGridCount_nonneg k2))
        refine grid_le_dLaGridWin b hb ?_
        rw [Finset.mem_range] at hk1 hk2
        omega
    _ = (∑ k2 ∈ Finset.range m2, dLaTGridCount k1 * dLaTGridCount k2) *
          dLaGridWin b m3 := by
        rw [Finset.sum_mul]

set_option linter.unusedSectionVars false in
private lemma rfns_neg_dla (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (-v) =
      riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (-v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_neg]
  rw [← neg_one_smul ℝ (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := r) (s := s) (x := x) v),
    tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

set_option linter.unusedSectionVars false in
private lemma rfns_smul_dla (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (c : ℝ) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

set_option linter.unusedSectionVars false in
private lemma rfns_iCG_sub_le_dla (g : SmoothRiemannianMetric I M) (r s : ℕ) (j : ℕ)
    (A B : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
        ((iteratedCovGrad (I := I) g r s j (A - B)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
          ((iteratedCovGrad (I := I) g r s j A).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
          ((iteratedCovGrad (I := I) g r s j B).toSection x) := by
  have hsec : (iteratedCovGrad (I := I) g r s j (A - B)).toSection x =
      (iteratedCovGrad (I := I) g r s j A).toSection x +
        (-(iteratedCovGrad (I := I) g r s j B).toSection x) := by
    rw [sub_eq_add_neg, iteratedCovGrad_add, iteratedCovGrad_neg, SmoothCcTensor.toSection_add]
    rw [show ((iteratedCovGrad (I := I) g r s j A).toSection +
        (-iteratedCovGrad (I := I) g r s j B).toSection) x =
        (iteratedCovGrad (I := I) g r s j A).toSection x +
          (-iteratedCovGrad (I := I) g r s j B).toSection x from rfl]
    rw [SmoothCcTensor.toSection_neg]
    rfl
  rw [hsec]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g r (s + j) x _ _) ?_
  rw [rfns_neg_dla (I := I) (M := M) g r (s + j) x]

set_option linter.unusedSectionVars false in
private lemma rfns_iCG_add_le_dla (g : SmoothRiemannianMetric I M) (r s : ℕ) (j : ℕ)
    (A B : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
        ((iteratedCovGrad (I := I) g r s j (A + B)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
          ((iteratedCovGrad (I := I) g r s j A).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
          ((iteratedCovGrad (I := I) g r s j B).toSection x) := by
  have hsec : (iteratedCovGrad (I := I) g r s j (A + B)).toSection x =
      (iteratedCovGrad (I := I) g r s j A).toSection x +
        (iteratedCovGrad (I := I) g r s j B).toSection x := by
    rw [iteratedCovGrad_add, SmoothCcTensor.toSection_add]
    rfl
  rw [hsec]
  exact riemannianFiberNormSq_add_le (I := I) (M := M) g r (s + j) x _ _

set_option linter.unusedSectionVars false in
private theorem exists_fixedField_rfns_jet_dla (g₀ : SmoothRiemannianMetric I M)
    (r s : ℕ) (F : SmoothCcTensor g₀ r s) :
    ∃ c : ℕ → ℝ, (∀ j, 0 ≤ c j) ∧ ∀ (j : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + j) x
        ((iteratedCovGrad (I := I) g₀ r s j F).toSection x) ≤ c j := by
  have hex : ∀ j : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + j) x
        ((iteratedCovGrad (I := I) g₀ r s j F).toSection x) ≤ c :=
    fun j => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ r (s + j)
      (iteratedCovGrad (I := I) g₀ r s j F)
  choose c hc_nn hc using hex
  exact ⟨c, hc_nn, fun j x => hc j x⟩

set_option linter.unusedSectionVars false in
private lemma g1_inner_gInvRaisedEndo_left_dla (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g₁.inner x (gInvRaisedEndo (I := I) g₀ g₁ x v) w = g₀.inner x v w := by
  rw [gInvRaisedEndo_apply]
  rw [inverseMetricSharpFib_inner (I := I) g₁ x (g0FlatCLM (I := I) g₀ x v) w]
  rw [show cotangentToDualLinear (I := I) (x := x) (g0FlatCLM (I := I) g₀ x v) w =
      cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₀ x v) w from rfl]
  rw [cotangentToDual_g0FlatCLM]

set_option linter.unusedSectionVars false in
private lemma g0_inner_inverseMetricSharp_mixed_dla (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (v : TangentSpace I x) :
    g₀.inner x (inverseMetricSharpFib (I := I) g₁ x om) v =
      cotangentToDual (I := I) (x := x) om (gInvRaisedEndo (I := I) g₀ g₁ x v) := by
  rw [show cotangentToDual (I := I) (x := x) om (gInvRaisedEndo (I := I) g₀ g₁ x v) =
      cotangentToDualLinear (I := I) (x := x) om (gInvRaisedEndo (I := I) g₀ g₁ x v) from rfl]
  rw [← inverseMetricSharpFib_inner (I := I) g₁ x om (gInvRaisedEndo (I := I) g₀ g₁ x v)]
  rw [g₁.symm x (inverseMetricSharpFib (I := I) g₁ x om) (gInvRaisedEndo (I := I) g₀ g₁ x v)]
  rw [g1_inner_gInvRaisedEndo_left_dla (I := I) (M := M) g₀ g₁ x v
    (inverseMetricSharpFib (I := I) g₁ x om)]
  rw [g₀.symm x v (inverseMetricSharpFib (I := I) g₁ x om)]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma sharpFlatEndoCc_eq_slotInsert_fullRaised_dla (g₀ g₁ : SmoothRiemannianMetric I M) :
    sharpFlatEndoCc (I := I) g₀ g₁ =
      slotInsertEndoCc (I := I) (M := M) g₀ 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro om
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g₀ g₁).toSection x) om) =
      (g0FlatCLM (I := I) g₀ x) (inverseMetricSharpFib (I := I) g₁ x om) from rfl]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁)).toSection x) om) =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x) om from rfl]
  rw [slotInsertEndoFib_apply_eval]
  rw [toModel_om_single_eq_cotangentToDual_dla (I := I) (M := M) x om
    (Function.update m 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x (m 0)))]
  rw [Function.update_self]
  rw [toModel_om_single_eq_cotangentToDual_dla (I := I) (M := M) x
    ((g0FlatCLM (I := I) g₀ x) (inverseMetricSharpFib (I := I) g₁ x om)) m]
  rw [cotangentToDual_g0FlatCLM]
  rw [g0_inner_inverseMetricSharp_mixed_dla (I := I) (M := M) g₀ g₁ x om (m 0)]
  rw [fullRaisedEndoField_apply]

set_option linter.unusedSectionVars false in
private lemma fullRaisedEndoField_diff_split_dla (g₀ g₁ : SmoothRiemannianMetric I M) :
    fullRaisedEndoField (I := I) (M := M) g₀ g₁ =
      gInvDiffRaisedEndoField (I := I) g₀ g₁ +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ := by
  apply ContMDiffSection.ext
  intro x
  rw [show ((gInvDiffRaisedEndoField (I := I) g₀ g₁ +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀) x) =
      gInvDiffRaisedEndoField (I := I) g₀ g₁ x +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ x from by
    rw [ContMDiffSection.coe_add]; rfl]
  apply ContinuousLinearMap.ext
  intro v
  rw [fullRaisedEndoField_apply, ContinuousLinearMap.add_apply]
  rw [show (gInvDiffRaisedEndoField (I := I) g₀ g₁ x) = gInvDiffRaisedEndo (I := I) g₀ g₁ x
    from rfl]
  rw [fullRaisedEndoField_apply]
  rw [gInvRaisedEndo_eq_diff_add_id (I := I) g₀ g₁ x v]
  rw [show gInvRaisedEndo (I := I) g₀ g₀ x v = v from by
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma slotInsertEndoCc_add_endo_dla (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    slotInsertEndoCc (I := I) (M := M) g₀ s (A + B) =
      slotInsertEndoCc (I := I) (M := M) g₀ s A +
        slotInsertEndoCc (I := I) (M := M) g₀ s B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((slotInsertEndoCc (I := I) (M := M) g₀ s A +
        slotInsertEndoCc (I := I) (M := M) g₀ s B).toSection x) =
      (slotInsertEndoCc (I := I) (M := M) g₀ s A).toSection x +
        (slotInsertEndoCc (I := I) (M := M) g₀ s B).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [ContinuousLinearMap.add_apply]
  simp only [slotInsertEndoCc_toSection]
  rw [show ((A + B) x) = A x + B x from by rw [ContMDiffSection.coe_add]; rfl]
  rw [slotInsertEndoFib_add_left, ContinuousLinearMap.add_apply]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma endoCovariantDerivative_fullRaised_id_eq_zero_dla (g₀ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    ((endoCovariantDerivative (I := I) (M := M) g₀)
        (fullRaisedEndoField (I := I) (M := M) g₀ g₀) x v) (Y x) = 0 := by
  have hLeib := endoCovariantDerivative_apply (I := I) (M := M) g₀
    (fullRaisedEndoField (I := I) (M := M) g₀ g₀) Y x v
  have hΛapp : (fun y : M => (fullRaisedEndoField (I := I) (M := M) g₀ g₀ y) (Y y)) =
      (fun y : M => Y y) := by
    funext y
    rw [fullRaisedEndoField_apply]
    rw [show gInvRaisedEndo (I := I) g₀ g₀ y (Y y) = Y y from by
      rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]
  rw [hLeib, hΛapp]
  rw [fullRaisedEndoField_apply]
  rw [show gInvRaisedEndo (I := I) g₀ g₀ x
      ((LeviCivita (I := I) g₀).toFun (fun y : M => Y y) x v) =
      (LeviCivita (I := I) g₀).toFun (fun y : M => Y y) x v from by
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]
  rw [sub_self]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma covGrad_slotInsert_fullRaised_id_eq_zero_dla (g₀ : SmoothRiemannianMetric I M) :
    covGrad (I := I) (M := M) g₀ 1 1
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀)) = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g₀ 1 1
    (slotInsertEndoCc (I := I) (M := M) g₀ 0
      (fullRaisedEndoField (I := I) (M := M) g₀ g₀)) x D m]
  rw [tensorCovDerivAt_slotInsertEndoCc_eq (I := I) (M := M) g₀ 0
    (fullRaisedEndoField (I := I) (M := M) g₀ g₀) x (m 0)]
  rw [show ((endoCovariantDerivative (I := I) (M := M) g₀)
        (fullRaisedEndoField (I := I) (M := M) g₀ g₀) x (m 0)) =
      (0 : TangentSpace I x →L[ℝ] TangentSpace I x) from by
    apply ContinuousLinearMap.ext
    intro w
    rw [ContinuousLinearMap.zero_apply]
    obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I)
      (F := E) (V := fun y : M => TangentSpace I y) (n := (⊤ : ℕ∞)) x w
    rw [← hY]
    exact endoCovariantDerivative_fullRaised_id_eq_zero_dla (I := I) (M := M) g₀ Y x (m 0)]
  rw [show slotInsertEndoFib (I := I) (M := M) (0 + 1) 0 x
        (0 : TangentSpace I x →L[ℝ] TangentSpace I x) = 0 from by
    rw [show (0 : TangentSpace I x →L[ℝ] TangentSpace I x) =
        (0 : ℝ) • (0 : TangentSpace I x →L[ℝ] TangentSpace I x) from (zero_smul ℝ _).symm,
      slotInsertEndoFib_smul_left, zero_smul]]
  simp [SmoothCcTensor.toSection_zero]

set_option linter.unusedSectionVars false in
private lemma iteratedCovGrad_slotInsert_fullRaised_id_succ_eq_zero_dla
    (g₀ : SmoothRiemannianMetric I M) (m : ℕ) :
    iteratedCovGrad (I := I) g₀ 1 1 (m + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀)) = 0 := by
  induction m with
  | zero =>
      rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
      exact covGrad_slotInsert_fullRaised_id_eq_zero_dla (I := I) (M := M) g₀
  | succ m' ih =>
      rw [iteratedCovGrad_succ, ih, covGrad_zero]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private theorem exists_rfns_iteratedCovGrad_sharpFlatEndoCc_tgrid_dla
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ S : ℕ → ℝ, (∀ l, 0 ≤ S l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
          S l * Combinatorics.antidiagonalTupleGrid
            (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) l := by
  classical
  obtain ⟨CD, hCD_nn, hCD⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cid, hcid_nn, hcid⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 1 1
    (slotInsertEndoCc (I := I) (M := M) g₀ 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₀))
  refine ⟨fun l => 2 * CD l + 2 * cid,
    fun l => by have := hCD_nn l; linarith, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound l x
  set b : ℕ → ℝ := fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) with hb_def
  have hb : ∀ j, 0 ≤ b j :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hgrid_nn : 0 ≤ Combinatorics.antidiagonalTupleGrid b l :=
    Combinatorics.antidiagonalTupleGrid_nonneg b hb l
  have hsplit : sharpFlatEndoCc (I := I) g₀ g₁ =
      slotInsertEndoCc (I := I) (M := M) g₀ 0 (gInvDiffRaisedEndoField (I := I) g₀ g₁) +
        slotInsertEndoCc (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀) := by
    rw [sharpFlatEndoCc_eq_slotInsert_fullRaised_dla (I := I) (M := M) g₀ g₁,
      fullRaisedEndoField_diff_split_dla (I := I) (M := M) g₀ g₁,
      slotInsertEndoCc_add_endo_dla (I := I) (M := M) g₀ 0]
  have hsec : (iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x =
      (iteratedCovGrad (I := I) g₀ 1 1 l
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x +
      (iteratedCovGrad (I := I) g₀ 1 1 l
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀))).toSection x := by
    rw [hsplit, iteratedCovGrad_add, SmoothCcTensor.toSection_add]
    rfl
  rw [hsec]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (1 + l) x _ _) ?_
  have hA : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
      ((iteratedCovGrad (I := I) g₀ 1 1 l
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) ≤
      CD l * Combinatorics.antidiagonalTupleGrid b l :=
    hCD g₁ T htie hδ_le hδ0 hbound l x
  have hB : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
      ((iteratedCovGrad (I := I) g₀ 1 1 l
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀))).toSection x) ≤
      cid * Combinatorics.antidiagonalTupleGrid b l := by
    match l with
    | 0 =>
        rw [iteratedCovGrad_zero]
        rw [Combinatorics.antidiagonalTupleGrid_zero, mul_one]
        exact hcid x
    | (m + 1) =>
        rw [iteratedCovGrad_slotInsert_fullRaised_id_succ_eq_zero_dla (I := I) (M := M) g₀ m]
        rw [show ((0 : SmoothCcTensor g₀ 1 (1 + (m + 1))).toSection x) =
            (0 : TensorRSSpace 1 (1 + (m + 1)) I x) from by
          rw [SmoothCcTensor.toSection_zero]; rfl]
        rw [riemannianFiberNormSq_zero (I := I) (M := M) g₀ 1 (1 + (m + 1)) x]
        exact mul_nonneg hcid_nn
          (Combinatorics.antidiagonalTupleGrid_nonneg b hb (m + 1))
  calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (fullRaisedEndoField (I := I) (M := M) g₀ g₀))).toSection x)
      ≤ 2 * (CD l * Combinatorics.antidiagonalTupleGrid b l) +
          2 * (cid * Combinatorics.antidiagonalTupleGrid b l) := by
        have h1 := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x)
        linarith
    _ = (2 * CD l + 2 * cid) * Combinatorics.antidiagonalTupleGrid b l := by ring

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private theorem exists_rfns_iteratedCovGrad_connDiffSection_tgrid_dla
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ CA : ℕ → ℝ, (∀ j, 0 ≤ CA j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 1 2 j
              (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
          CA j * dLaGridWin
            (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
              ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x)) (j + 2) := by
  classical
  obtain ⟨S, hS_nn, hS⟩ := exists_rfns_iteratedCovGrad_sharpFlatEndoCc_tgrid_dla
    (I := I) (M := M) g₀ hδ₀
  refine ⟨fun j => appCcGdiag (E := E) j *
      ∑ i ∈ Finset.range (j + 1), 10 * ∑ l ∈ Finset.range (j + 1 - i), S l,
    fun j => mul_nonneg (appCcGdiag_nonneg (E := E) j)
      (Finset.sum_nonneg fun i _ => mul_nonneg (by norm_num)
        (Finset.sum_nonneg fun l _ => hS_nn l)), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound j x
  set b : ℕ → ℝ := fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
    ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x) with hb_def
  have hb : ∀ j', 0 ≤ b j' :=
    fun j' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j') x _
  set G : ℝ := dLaGridWin b (j + 2) with hG_def
  have hG_nn : 0 ≤ G := dLaGridWin_nonneg b hb (j + 2)
  have hcell : ∀ i ∈ Finset.range (j + 1), ∀ l ∈ Finset.range (j + 1 - i),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
      (10 * S l) * G := by
    intro i hi l hl
    have h1 := rfns_iteratedCovGrad_raisedKoszul_pointwise_le (I := I) (M := M) g₀ g₁ T htie i x
    have h2 := hS g₁ T htie hδ_le hδ0 hbound l x
    have h1_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x)
    have h2_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + l) x
      ((iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x)
    have hb_le_grid : b (i + 1) * Combinatorics.antidiagonalTupleGrid b l ≤
        Combinatorics.antidiagonalTupleGrid b (l + (i + 1)) :=
      Combinatorics.single_factor_mul_antidiagonalTupleGrid_le b hb l (i + 1) (by omega)
    have hgrid_le_G : Combinatorics.antidiagonalTupleGrid b (l + (i + 1)) ≤ G := by
      rw [hG_def]
      refine grid_le_dLaGridWin b hb ?_
      rw [Finset.mem_range] at hi hl
      omega
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x)
        ≤ (10 * b (i + 1)) * (S l * Combinatorics.antidiagonalTupleGrid b l) :=
          mul_le_mul h1 h2 h2_nn (by
            have := hb (i + 1)
            positivity)
      _ = (10 * S l) * (b (i + 1) * Combinatorics.antidiagonalTupleGrid b l) := by ring
      _ ≤ (10 * S l) * Combinatorics.antidiagonalTupleGrid b (l + (i + 1)) := by
          refine mul_le_mul_of_nonneg_left hb_le_grid ?_
          have := hS_nn l
          positivity
      _ ≤ (10 * S l) * G := by
          refine mul_le_mul_of_nonneg_left hgrid_le_G ?_
          have := hS_nn l
          positivity
  refine le_trans (rfns_iteratedCovGrad_connDiffSection_diagonalProductGrid_le
    (I := I) (M := M) g₀ g₁ j x) ?_
  have hsum : ∑ i ∈ Finset.range (j + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) *
        ∑ l ∈ Finset.range (j + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 1 l
              (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
      ∑ i ∈ Finset.range (j + 1), (10 * ∑ l ∈ Finset.range (j + 1 - i), S l) * G := by
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mul_sum]
    have hrw : (10 * ∑ l ∈ Finset.range (j + 1 - i), S l) * G =
        ∑ l ∈ Finset.range (j + 1 - i), (10 * S l) * G := by
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [hrw]
    exact Finset.sum_le_sum fun l hl => hcell i hi l hl
  refine le_trans (mul_le_mul_of_nonneg_left hsum (appCcGdiag_nonneg (E := E) j)) ?_
  rw [← Finset.sum_mul, ← mul_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma connDiffSection_eq_armSlotEndoCc_zero_dla (g₀ gc : SmoothRiemannianMetric I M) :
    connDiffSection (I := I) gc g₀ =
      armSlotEndoCc (I := I) (M := M) g₀ 0 (dLaConnArmPt (I := I) (M := M) g₀ gc) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro om
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (armSlotEndoCc (I := I) (M := M) g₀ 0
          (dLaConnArmPt (I := I) (M := M) g₀ gc)).toSection x) om) =
      armSlotFib (I := I) (M := M) 0 x (dLaConnArmPt (I := I) (M := M) g₀ gc x) om
      from rfl]
  rw [armSlotFib_apply_eval (I := I) (M := M) 0 x
    (dLaConnArmPt (I := I) (M := M) g₀ gc x) om v]
  rw [slotInsertEndoFib_apply_eval]
  rw [show (Function.update (Matrix.vecTail (fun k : Fin 2 => (v k : E))) 0
        (dLaConnArmPt (I := I) (M := M) g₀ gc x (v 0)
          (Matrix.vecTail (fun k : Fin 2 => (v k : E)) 0))) =
      (fun _ : Fin 1 => (show E from
        PDE.DeTurck.connDiff (I := I) gc g₀ x (v 0) (v 1))) from by
    funext k
    rw [show k = (0 : Fin 1) from Subsingleton.elim k 0]
    rw [Function.update_self]
    rfl]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (connDiffSection (I := I) gc g₀).toSection x) om) =
      connDiffPairing (I := I) gc g₀ x om from rfl]
  change connDiffPairing (I := I) gc g₀ x om v = _
  rw [connDiffPairing_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma armSlotEndoCc_one_eq_reindex_slotExtend_dla (g₀ : SmoothRiemannianMetric I M)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    armSlotEndoCc (I := I) (M := M) g₀ 1 Arm =
      reindexCoeffGen (I := I) (M := M) g₀ 2 3
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 3 (finRotate 3).symm
          (slotExtend (I := I) (M := M) g₀ 1 2 (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)))
        (Equiv.swap (0 : Fin 2) 1) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  have hτ0 : (finRotate 3).symm (0 : Fin 3) = (2 : Fin 3) := by decide
  have hτ1 : (finRotate 3).symm (1 : Fin 3) = (0 : Fin 3) := by decide
  have hτ2 : (finRotate 3).symm (2 : Fin 3) = (1 : Fin 3) := by decide
  set D' : Tensor0SSpace 2 I x := Tensor0SSpace.ofModel
    (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
      (Tensor0SSpace.toModel D)) with hD'_def
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (armSlotEndoCc (I := I) (M := M) g₀ 1 Arm).toSection x) D) w =
      Tensor0SSpace.toModel D
        (Function.update (Matrix.vecTail w) 0 (Arm x (w 0) (Matrix.vecTail w 0))) := by
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          (armSlotEndoCc (I := I) (M := M) g₀ 1 Arm).toSection x) D) =
        armSlotFib (I := I) (M := M) 1 x (Arm x) D from rfl]
    rw [armSlotFib_apply_eval (I := I) (M := M) 1 x (Arm x) D w]
    rw [slotInsertEndoFib_apply_eval]
  have e1 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 3
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 3 (finRotate 3).symm
            (slotExtend (I := I) (M := M) g₀ 1 2 (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)))
          (Equiv.swap (0 : Fin 2) 1)).toSection x) D) w =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          rsDomDomCongr (finRotate 3).symm
            ((slotExtend (I := I) (M := M) g₀ 1 2
              (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x)) D') w := by
    have h1 : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 3
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 3 (finRotate 3).symm
            (slotExtend (I := I) (M := M) g₀ 1 2 (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)))
          (Equiv.swap (0 : Fin 2) 1)).toSection x) D) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          rsDomDomCongr (finRotate 3).symm
            ((slotExtend (I := I) (M := M) g₀ 1 2
              (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x)) D') := by
      rw [reindexCoeffGen_toSection]
      rw [reindexCoeffFibGen_apply (I := I) 2 3 (Equiv.swap (0 : Fin 2) 1) x
        (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 3 (finRotate 3).symm
            (slotExtend (I := I) (M := M) g₀ 1 2
              (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm))).toSection x) D]
      rw [← hD'_def]
      rw [rsDomDomCongrSection_toSection]
    exact congrArg (fun t : Tensor0SSpace 3 I x => Tensor0SSpace.toModel t w) h1
  have e2 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        rsDomDomCongr (finRotate 3).symm
          ((slotExtend (I := I) (M := M) g₀ 1 2
            (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x)) D') w =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          (slotExtend (I := I) (M := M) g₀ 1 2
            (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x) D')
        (fun i => w ((finRotate 3).symm i)) := by
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) (finRotate 3).symm
      ((slotExtend (I := I) (M := M) g₀ 1 2
        (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x) D']
    rw [ContinuousMultilinearMap.domDomCongr_apply]
  have e3 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (slotExtend (I := I) (M := M) g₀ 1 2
          (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x) D')
      (fun i => w ((finRotate 3).symm i)) =
      Tensor0SSpace.toModel
        (armSlotFib (I := I) (M := M) 0 x (Arm x)
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D' (w ((finRotate 3).symm 0))))
        (Matrix.vecTail (fun i => w ((finRotate 3).symm i))) := by
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          (slotExtend (I := I) (M := M) g₀ 1 2
            (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x) D') =
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x).symm
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
              (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm).toSection x).comp
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D')) from rfl]
    rw [show (fun i => w ((finRotate 3).symm i)) =
        Fin.cons (w ((finRotate 3).symm 0))
          (Matrix.vecTail (fun i => w ((finRotate 3).symm i))) from by
      funext k
      refine Fin.cases rfl (fun j => rfl) k]
    have hkey := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 2)
      (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x).symm
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
            (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm).toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D')))
      (v0 := w ((finRotate 3).symm 0))
      (vs := Matrix.vecTail (fun i => w ((finRotate 3).symm i)))
    rw [ContinuousLinearEquiv.apply_symm_apply] at hkey
    rw [← hkey]
    rfl
  have e4 : Tensor0SSpace.toModel
      (armSlotFib (I := I) (M := M) 0 x (Arm x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D' (w ((finRotate 3).symm 0))))
      (Matrix.vecTail (fun i => w ((finRotate 3).symm i))) =
      Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D' (w ((finRotate 3).symm 0)))
        (fun _ : Fin 1 => (show E from
          Arm x (w ((finRotate 3).symm 1)) (w ((finRotate 3).symm 2)))) := by
    rw [armSlotFib_apply_eval (I := I) (M := M) 0 x (Arm x)
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D' (w ((finRotate 3).symm 0)))
      (Matrix.vecTail (fun i => w ((finRotate 3).symm i)))]
    rw [slotInsertEndoFib_apply_eval]
    congr 1
    funext k
    refine Fin.cases ?_ (fun j => j.elim0) k
    rw [Function.update_self]
    rfl
  have e5 : Tensor0SSpace.toModel
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D' (w ((finRotate 3).symm 0)))
      (fun _ : Fin 1 => (show E from
        Arm x (w ((finRotate 3).symm 1)) (w ((finRotate 3).symm 2)))) =
      Tensor0SSpace.toModel D'
        (Fin.cons (w ((finRotate 3).symm 0))
          (fun _ : Fin 1 => (show E from
            Arm x (w ((finRotate 3).symm 1)) (w ((finRotate 3).symm 2))))) :=
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 1)
      (T := D') (v0 := w ((finRotate 3).symm 0))
      (vs := fun _ : Fin 1 => (show E from
        Arm x (w ((finRotate 3).symm 1)) (w ((finRotate 3).symm 2))))
  have e6 : Tensor0SSpace.toModel D'
      (Fin.cons (w ((finRotate 3).symm 0))
        (fun _ : Fin 1 => (show E from
          Arm x (w ((finRotate 3).symm 1)) (w ((finRotate 3).symm 2))))) =
      Tensor0SSpace.toModel D
        (Function.update (Matrix.vecTail w) 0 (Arm x (w 0) (Matrix.vecTail w 0))) := by
    rw [hD'_def, Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
    rw [hτ0, hτ1, hτ2]
    congr 1
    funext k
    refine Fin.cases ?_ ?_ k
    · rw [show (Function.update (Matrix.vecTail w) 0
            (Arm x (w 0) (Matrix.vecTail w 0)) (0 : Fin 2)) =
          Arm x (w 0) (Matrix.vecTail w 0) from Function.update_self _ _ _]
      rfl
    · intro j
      refine Fin.cases ?_ (fun j2 => j2.elim0) j
      rw [show (Fin.succ (0 : Fin 1)) = (1 : Fin 2) from rfl]
      rw [Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
      rfl
  rw [hLHS, e1, e2, e3, e4, e5, e6]

set_option linter.unusedSectionVars false in
private lemma rfns_iteratedCovGrad_armSlotPass_connArm_le_dla
    (g₀ gc : SmoothRiemannianMetric I M) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + j) x
        ((iteratedCovGrad (I := I) g₀ 2 3 j
          (armSlotEndoPassZeroCc (I := I) (M := M) g₀
            (dLaConnArmPt (I := I) (M := M) g₀ gc))).toSection x) ≤
      (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) gc g₀)).toSection x) := by
  rw [riemannianFiberNormSq_iteratedCovGrad_armSlotEndoPassZeroCc_eq (I := I) (M := M) g₀
    (dLaConnArmPt (I := I) (M := M) g₀ gc) j x]
  rw [armSlotEndoCc_one_eq_reindex_slotExtend_dla (I := I) (M := M) g₀
    (dLaConnArmPt (I := I) (M := M) g₀ gc)]
  rw [rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ 2 3
    (Equiv.swap (0 : Fin 2) 1) (finRotate 3).symm
    (slotExtend (I := I) (M := M) g₀ 1 2
      (armSlotEndoCc (I := I) (M := M) g₀ 0 (dLaConnArmPt (I := I) (M := M) g₀ gc))) j x]
  refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 2
    (armSlotEndoCc (I := I) (M := M) g₀ 0 (dLaConnArmPt (I := I) (M := M) g₀ gc)) j x) ?_
  rw [← connDiffSection_eq_armSlotEndoCc_zero_dla (I := I) (M := M) g₀ gc]

set_option linter.unusedSectionVars false in
private lemma dLaQuad_tower_of_factors (g₀ ga gb : SmoothRiemannianMetric I M)
    (j : ℕ) (x : M) (b : ℕ → ℝ) (hb : ∀ l, 0 ≤ b l)
    (Ba Bb : ℕ → ℝ) (hBa_nn : ∀ i, 0 ≤ Ba i) (hBb_nn : ∀ l, 0 ≤ Bb l)
    (harm : ∀ i, i ≤ j →
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 2 i (connDiffSection (I := I) ga g₀)).toSection x) ≤
      Ba i * dLaGridWin b (i + 2))
    (hin : ∀ l, l ≤ j →
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 1 2 l (connDiffSection (I := I) gb g₀)).toSection x) ≤
      Bb l * dLaGridWin b (l + 2)) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + j) x
        ((iteratedCovGrad (I := I) g₀ 1 3 j
          (dLaQuadCc (I := I) (M := M) g₀ ga gb)).toSection x) ≤
      (appCcGdiag (E := E) j * ∑ i ∈ Finset.range (j + 1),
        (Module.finrank ℝ E : ℝ) * Ba i *
          ∑ l ∈ Finset.range (j + 1 - i), Bb l * dLaPairCount (i + 2) (l + 2)) *
        dLaGridWin b (j + 3) := by
  have hWnn : 0 ≤ dLaGridWin b (j + 3) := dLaGridWin_nonneg b hb (j + 3)
  have hfr_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
    (I := I) (M := M) g₀ j 1 2 3
    (armSlotEndoPassZeroCc (I := I) (M := M) g₀ (dLaConnArmPt (I := I) (M := M) g₀ ga))
    (connDiffSection (I := I) gb g₀) x) ?_
  have hcell : ∀ i ∈ Finset.range (j + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 3 i
            (armSlotEndoPassZeroCc (I := I) (M := M) g₀
              (dLaConnArmPt (I := I) (M := M) g₀ ga))).toSection x) *
        ∑ l ∈ Finset.range (j + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 2 l
              (connDiffSection (I := I) gb g₀)).toSection x) ≤
      ((Module.finrank ℝ E : ℝ) * Ba i *
        ∑ l ∈ Finset.range (j + 1 - i), Bb l * dLaPairCount (i + 2) (l + 2)) *
        dLaGridWin b (j + 3) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hi_le : i ≤ j := by omega
    have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 3 i
          (armSlotEndoPassZeroCc (I := I) (M := M) g₀
            (dLaConnArmPt (I := I) (M := M) g₀ ga))).toSection x) ≤
        (Module.finrank ℝ E : ℝ) * (Ba i * dLaGridWin b (i + 2)) := by
      refine le_trans (rfns_iteratedCovGrad_armSlotPass_connArm_le_dla
        (I := I) (M := M) g₀ ga i x) ?_
      exact mul_le_mul_of_nonneg_left (harm i hi_le) hfr_nn
    have hA2 : (∑ l ∈ Finset.range (j + 1 - i),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 2 l
            (connDiffSection (I := I) gb g₀)).toSection x)) ≤
        ∑ l ∈ Finset.range (j + 1 - i), Bb l * dLaGridWin b (l + 2) := by
      refine Finset.sum_le_sum fun l hl => ?_
      rw [Finset.mem_range] at hl
      exact hin l (by omega)
    have hsum_nn : 0 ≤ ∑ l ∈ Finset.range (j + 1 - i),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 2 l
            (connDiffSection (I := I) gb g₀)).toSection x) :=
      Finset.sum_nonneg fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + l) x _
    have hA1_rhs_nn : 0 ≤ (Module.finrank ℝ E : ℝ) * (Ba i * dLaGridWin b (i + 2)) :=
      mul_nonneg hfr_nn (mul_nonneg (hBa_nn i) (dLaGridWin_nonneg b hb (i + 2)))
    refine le_trans (mul_le_mul hA1 hA2 hsum_nn hA1_rhs_nn) ?_
    rw [Finset.mul_sum]
    rw [show ((Module.finrank ℝ E : ℝ) * Ba i *
        ∑ l ∈ Finset.range (j + 1 - i), Bb l * dLaPairCount (i + 2) (l + 2)) *
        dLaGridWin b (j + 3) =
        ∑ l ∈ Finset.range (j + 1 - i),
          ((Module.finrank ℝ E : ℝ) * Ba i * (Bb l * dLaPairCount (i + 2) (l + 2))) *
            dLaGridWin b (j + 3) from by
      rw [Finset.mul_sum, Finset.sum_mul]]
    refine Finset.sum_le_sum fun l hl => ?_
    rw [Finset.mem_range] at hl
    have hpair : dLaGridWin b (i + 2) * dLaGridWin b (l + 2) ≤
        dLaPairCount (i + 2) (l + 2) * dLaGridWin b (j + 3) :=
      dLaGridWin_mul_le b hb (i + 2) (l + 2) (j + 3) (by omega)
    calc (Module.finrank ℝ E : ℝ) * (Ba i * dLaGridWin b (i + 2)) *
          (Bb l * dLaGridWin b (l + 2))
        = ((Module.finrank ℝ E : ℝ) * Ba i * Bb l) *
            (dLaGridWin b (i + 2) * dLaGridWin b (l + 2)) := by ring
      _ ≤ ((Module.finrank ℝ E : ℝ) * Ba i * Bb l) *
            (dLaPairCount (i + 2) (l + 2) * dLaGridWin b (j + 3)) := by
          refine mul_le_mul_of_nonneg_left hpair ?_
          exact mul_nonneg (mul_nonneg hfr_nn (hBa_nn i)) (hBb_nn l)
      _ = (Module.finrank ℝ E : ℝ) * Ba i * (Bb l * dLaPairCount (i + 2) (l + 2)) *
            dLaGridWin b (j + 3) := by ring
  calc appCcGdiag (E := E) j *
        ∑ i ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + i) x
              ((iteratedCovGrad (I := I) g₀ 2 3 i
                (armSlotEndoPassZeroCc (I := I) (M := M) g₀
                  (dLaConnArmPt (I := I) (M := M) g₀ ga))).toSection x) *
            ∑ l ∈ Finset.range (j + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 1 2 l
                  (connDiffSection (I := I) gb g₀)).toSection x)
      ≤ appCcGdiag (E := E) j *
          ∑ i ∈ Finset.range (j + 1),
            ((Module.finrank ℝ E : ℝ) * Ba i *
              ∑ l ∈ Finset.range (j + 1 - i), Bb l * dLaPairCount (i + 2) (l + 2)) *
              dLaGridWin b (j + 3) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell) (appCcGdiag_nonneg (E := E) j)
    _ = (appCcGdiag (E := E) j * ∑ i ∈ Finset.range (j + 1),
          (Module.finrank ℝ E : ℝ) * Ba i *
            ∑ l ∈ Finset.range (j + 1 - i), Bb l * dLaPairCount (i + 2) (l + 2)) *
          dLaGridWin b (j + 3) := by
        rw [← Finset.sum_mul, ← mul_assoc]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private theorem exists_rfns_dLaKernelRaised_tgrid (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 3 i
              (dLaKernelRaisedCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          C i * dLaGridWin
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 3) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ := exists_rfns_iteratedCovGrad_connDiffSection_tgrid_dla
    (I := I) (M := M) g₀ hδ₀
  obtain ⟨cbg, hcbg_nn, hcbg⟩ := exists_fixedField_rfns_jet_dla (I := I) (M := M) g₀ 1 3
    (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g_bg g₀))
  obtain ⟨cc, hcc_nn, hcc⟩ := exists_fixedField_rfns_jet_dla (I := I) (M := M) g₀ 1 2
    (connDiffSection (I := I) g_bg g₀)
  set CQ1 : ℕ → ℝ := fun j => appCcGdiag (E := E) j * ∑ i' ∈ Finset.range (j + 1),
    (Module.finrank ℝ E : ℝ) * CA i' *
      ∑ l ∈ Finset.range (j + 1 - i'), CA l * dLaPairCount (i' + 2) (l + 2) with hCQ1_def
  set CQ2 : ℕ → ℝ := fun j => appCcGdiag (E := E) j * ∑ i' ∈ Finset.range (j + 1),
    (Module.finrank ℝ E : ℝ) * cc i' *
      ∑ l ∈ Finset.range (j + 1 - i'), CA l * dLaPairCount (i' + 2) (l + 2) with hCQ2_def
  set CQ3 : ℕ → ℝ := fun j => appCcGdiag (E := E) j * ∑ i' ∈ Finset.range (j + 1),
    (Module.finrank ℝ E : ℝ) * CA i' *
      ∑ l ∈ Finset.range (j + 1 - i'), cc l * dLaPairCount (i' + 2) (l + 2) with hCQ3_def
  have hCQ1_nn : ∀ j, 0 ≤ CQ1 j := by
    intro j
    refine mul_nonneg (appCcGdiag_nonneg (E := E) j) (Finset.sum_nonneg fun i' _ => ?_)
    refine mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCA_nn i'))
      (Finset.sum_nonneg fun l _ => mul_nonneg (hCA_nn l) (dLaPairCount_nonneg _ _))
  have hCQ2_nn : ∀ j, 0 ≤ CQ2 j := by
    intro j
    refine mul_nonneg (appCcGdiag_nonneg (E := E) j) (Finset.sum_nonneg fun i' _ => ?_)
    refine mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hcc_nn i'))
      (Finset.sum_nonneg fun l _ => mul_nonneg (hCA_nn l) (dLaPairCount_nonneg _ _))
  have hCQ3_nn : ∀ j, 0 ≤ CQ3 j := by
    intro j
    refine mul_nonneg (appCcGdiag_nonneg (E := E) j) (Finset.sum_nonneg fun i' _ => ?_)
    refine mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCA_nn i'))
      (Finset.sum_nonneg fun l _ => mul_nonneg (hcc_nn l) (dLaPairCount_nonneg _ _))
  refine ⟨fun i => 2 * (2 * (2 * (2 * (2 * (2 * (2 * CA (i + 1) + 2 * cbg i) + 2 * CQ1 i)
      + 2 * CQ2 i) + 2 * CQ1 i) + 2 * CQ3 i) + 2 * CQ1 i) + 2 * CQ3 i,
    fun i => by
      have h1 := hCA_nn (i + 1)
      have h2 := hcbg_nn i
      have h3 := hCQ1_nn i
      have h4 := hCQ2_nn i
      have h5 := hCQ3_nn i
      positivity, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set W : ℝ := dLaGridWin b (i + 3) with hW_def
  have hW_nn : 0 ≤ W := dLaGridWin_nonneg b hb (i + 3)
  have hW_ge1 : 1 ≤ W := one_le_dLaGridWin b hb (by omega)
  have harm : ∀ i', i' ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i') x
        ((iteratedCovGrad (I := I) g₀ 1 2 i' (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
      CA i' * dLaGridWin b (i' + 2) :=
    fun i' _ => hCA g₁ T htie hδ_le hδ0 hbound i' x
  have hfix : ∀ i', i' ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i') x
        ((iteratedCovGrad (I := I) g₀ 1 2 i' (connDiffSection (I := I) g_bg g₀)).toSection x) ≤
      cc i' * dLaGridWin b (i' + 2) := by
    intro i' _
    refine le_trans (hcc i' x) ?_
    have h1 : (1 : ℝ) ≤ dLaGridWin b (i' + 2) := one_le_dLaGridWin b hb (by omega)
    nlinarith [hcc_nn i']
  have hQ1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (dLaQuadCc (I := I) (M := M) g₀ g₁ g₁)).toSection x) ≤ CQ1 i * W :=
    dLaQuad_tower_of_factors (I := I) (M := M) g₀ g₁ g₁ i x b hb CA CA hCA_nn hCA_nn harm harm
  have hQ2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (dLaQuadCc (I := I) (M := M) g₀ g_bg g₁)).toSection x) ≤ CQ2 i * W :=
    dLaQuad_tower_of_factors (I := I) (M := M) g₀ g_bg g₁ i x b hb cc CA hcc_nn hCA_nn hfix harm
  have hQ3 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (dLaQuadCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤ CQ3 i * W :=
    dLaQuad_tower_of_factors (I := I) (M := M) g₀ g₁ g_bg i x b hb CA cc hCA_nn hcc_nn harm hfix
  have hrs_eq : ∀ (σ : Equiv.Perm (Fin 3)) (F : SmoothCcTensor g₀ 1 3),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 σ F)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i F).toSection x) := by
    intro σ F
    exact rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 1 3 σ F
      (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 σ F)
      (fun y d => by
        rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) i x
  have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))).toSection x) ≤
      CA (i + 1) * W := by
    rw [rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 1 2 i
      (connDiffSection (I := I) g₁ g₀) x]
    exact hCA g₁ T htie hδ_le hδ0 hbound (i + 1) x
  have hA2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g_bg g₀))).toSection x) ≤
      cbg i * W := by
    refine le_trans (hcbg i x) ?_
    nlinarith [hcbg_nn i]
  set A1 := covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) with hA1_def
  set A2 := covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g_bg g₀) with hA2_def
  set Q11 := dLaQuadCc (I := I) (M := M) g₀ g₁ g₁ with hQ11_def
  set Qbg1 := dLaQuadCc (I := I) (M := M) g₀ g_bg g₁ with hQbg1_def
  set Q1bg := dLaQuadCc (I := I) (M := M) g₀ g₁ g_bg with hQ1bg_def
  set P1 := rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (0 : Fin 3) 2) Q11
    with hP1_def
  set P2 := rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (0 : Fin 3) 2) Q1bg
    with hP2_def
  set P3 := rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) Q11 with hP3_def
  set P4 := rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) Q1bg with hP4_def
  have hP1_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i P1).toSection x) ≤ CQ1 i * W :=
    le_of_eq_of_le (hrs_eq (Equiv.swap (0 : Fin 3) 2) Q11) hQ1
  have hP2_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i P2).toSection x) ≤ CQ3 i * W :=
    le_of_eq_of_le (hrs_eq (Equiv.swap (0 : Fin 3) 2) Q1bg) hQ3
  have hP3_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i P3).toSection x) ≤ CQ1 i * W :=
    le_of_eq_of_le (hrs_eq (finRotate 3) Q11) hQ1
  have hP4_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i P4).toSection x) ≤ CQ3 i * W :=
    le_of_eq_of_le (hrs_eq (finRotate 3) Q1bg) hQ3
  have t1 := rfns_iCG_sub_le_dla (I := I) (M := M) g₀ 1 3 i A1 A2 x
  have t2 := rfns_iCG_add_le_dla (I := I) (M := M) g₀ 1 3 i (A1 - A2) Q11 x
  have t3 := rfns_iCG_sub_le_dla (I := I) (M := M) g₀ 1 3 i (A1 - A2 + Q11) Qbg1 x
  have t4 := rfns_iCG_sub_le_dla (I := I) (M := M) g₀ 1 3 i (A1 - A2 + Q11 - Qbg1) P1 x
  have t5 := rfns_iCG_add_le_dla (I := I) (M := M) g₀ 1 3 i (A1 - A2 + Q11 - Qbg1 - P1) P2 x
  have t6 := rfns_iCG_sub_le_dla (I := I) (M := M) g₀ 1 3 i
    (A1 - A2 + Q11 - Qbg1 - P1 + P2) P3 x
  have t7 := rfns_iCG_add_le_dla (I := I) (M := M) g₀ 1 3 i
    (A1 - A2 + Q11 - Qbg1 - P1 + P2 - P3) P4 x
  have hKK : dLaKernelRaisedCc (I := I) (M := M) g₀ g₁ g_bg =
      A1 - A2 + Q11 - Qbg1 - P1 + P2 - P3 + P4 := rfl
  rw [hKK]
  linarith [t1, t2, t3, t4, t5, t6, t7, hA1, hA2, hQ1, hQ2, hQ3,
    hP1_le, hP2_le, hP3_le, hP4_le]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private theorem exists_rfns_dLaLowered_tgrid (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          C i * dLaGridWin
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 3) := by
  obtain ⟨C, hC_nn, hC⟩ := exists_rfns_dLaKernelRaised_tgrid (I := I) (M := M) g₀ g_bg hδ₀
  refine ⟨C, hC_nn, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  have hbridge : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i
        (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i
          (dLaKernelRaisedCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) := by
    have h := rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 2
      (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg) i x
    rw [dLaLoweredCc_raise_repr (I := I) (M := M) g₀ g₁ g_bg] at h
    exact h.symm
  rw [hbridge]
  exact hC g₁ T htie hδ_le hδ0 hbound i x

set_option linter.unusedSectionVars false in
private lemma rfns_iCG_symmS_le_dla (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) := by
  have hsec : (iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)).toSection x =
      (1 / 2 : ℝ) • (iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x +
        (1 / 2 : ℝ) • (iteratedCovGrad (I := I) g₀ 0 2 j
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)).toSection x := by
    rw [iteratedCovGrad_symmS_eq (I := I) (M := M) g₀ T j, SmoothCcTensor.toSection_add]
    rw [show (((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 j T).toSection +
        ((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 j
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)).toSection) x =
        ((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x +
          ((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 j
            (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)).toSection x from rfl]
    rw [SmoothCcTensor.toSection_smul, SmoothCcTensor.toSection_smul]
    rfl
  rw [hsec]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (2 + j) x _ _) ?_
  rw [rfns_smul_dla (I := I) (M := M) g₀ 0 (2 + j) x, rfns_smul_dla (I := I) (M := M) g₀ 0 (2 + j) x]
  have hperm := riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 2) 1) T j x
  rw [hperm]
  ring_nf
  nlinarith [riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)]

set_option linter.unusedSectionVars false in
private lemma rfns_symmS_zero_le_dla (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((symmS (I := I) (M := M) g₀ T).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * δ ^ 2 := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, _hpars, _hrepr, _hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 0 2 x
    ((symmS (I := I) (M := M) g₀ T).toSection x) e bse hnE hbse horth]
  have hcof : coframeS (I := I) (M := M) g₀ x 0 e = fun _ : Fin 0 → Fin n =>
      unitTensor (I := I) (M := M) x := by
    funext K
    apply Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro v
    rw [show Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 0 e K) v =
        coframeS (I := I) (M := M) g₀ x 0 e K v from rfl]
    rw [coframeS_apply (I := I) (M := M) g₀ x 0 e K v]
    rw [show Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x) v =
        unitTensor (I := I) (M := M) x v from rfl]
    rw [Fin.prod_univ_zero]
    rw [unitTensor, Tensor0SSpace.ofModel]
    rfl
  have hcomp : ∀ (K : Fin 0 → Fin n) (J : Fin 2 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
        ((symmS (I := I) (M := M) g₀ T).toSection x) n e K J) ^ 2 ≤ δ ^ 2 := by
    intro K J
    have hval : fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
        ((symmS (I := I) (M := M) g₀ T).toSection x) n e K J =
        ccTensorBilinSymm (I := I) g₀ T x (e (J 0)) (e (J 1)) := by
      rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
          ((symmS (I := I) (M := M) g₀ T).toSection x) n e K J =
          Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
              (symmS (I := I) (M := M) g₀ T).toSection x)
              (coframeS (I := I) (M := M) g₀ x 0 e K))
            (fun i : Fin 2 => (e (J i) : E)) from rfl]
      rw [hcof]
      rw [show Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (symmS (I := I) (M := M) g₀ T).toSection x)
            (unitTensor (I := I) (M := M) x))
          (fun i : Fin 2 => (e (J i) : E)) =
          unitModel (I := I) (M := M) g₀ 2 (symmS (I := I) (M := M) g₀ T) x
            ![e (J 0), e (J 1)] from by
        rw [unitModel]
        refine congrArg _ ?_
        funext k
        fin_cases k <;> rfl]
      rw [unitModel_eq_ccTensorBilin_dla (I := I) (M := M) g₀
        (symmS (I := I) (M := M) g₀ T) x (e (J 0)) (e (J 1))]
      rw [ccTensorBilin_symmS (I := I) (M := M) g₀ T x (e (J 0)) (e (J 1))]
    rw [hval]
    have habs := hbound x (e (J 0)) (e (J 1))
    have h00 : g₀.inner x (e (J 0)) (e (J 0)) = 1 := by
      rw [horth (J 0) (J 0), if_pos rfl]
    have h11 : g₀.inner x (e (J 1)) (e (J 1)) = 1 := by
      rw [horth (J 1) (J 1), if_pos rfl]
    rw [h00, h11, Real.sqrt_one, mul_one, mul_one] at habs
    have := abs_nonneg (ccTensorBilinSymm (I := I) g₀ T x (e (J 0)) (e (J 1)))
    nlinarith [habs, sq_abs (ccTensorBilinSymm (I := I) g₀ T x (e (J 0)) (e (J 1)))]
  calc (∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
          ((symmS (I := I) (M := M) g₀ T).toSection x) n e K J) ^ 2)
      ≤ ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n, δ ^ 2 :=
        Finset.sum_le_sum fun K _ => Finset.sum_le_sum fun J _ => hcomp K J
    _ = (Fintype.card (Fin 0 → Fin n) : ℝ) * ((Fintype.card (Fin 2 → Fin n) : ℝ) * δ ^ 2) := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_univ, nsmul_eq_mul]
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 * δ ^ 2 := by
        have hc0 : (Fintype.card (Fin 0 → Fin n) : ℝ) = 1 := by
          simp
        have hc2 : (Fintype.card (Fin 2 → Fin n) : ℝ) = (n : ℝ) ^ 2 := by
          simp only [Fintype.card_fun, Fintype.card_fin]
          push_cast
          ring
        rw [hc0, hc2, one_mul, hnE]

theorem symmC0_rfns_le (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hbound : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((symmS (I := I) (M := M) g₀ T).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * δ ^ 2 :=
  rfns_symmS_zero_le_dla (I := I) (M := M) g₀ T hδ0 hbound x

set_option linter.unusedSectionVars false in
private lemma rfns_iCG_slotInsert3_dLaPerturb_le (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + j) x
        ((iteratedCovGrad (I := I) g₀ 4 4 j
          (slotInsertEndoCc (I := I) (M := M) g₀ 3
            (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T))).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 3 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)).toSection x) := by
  refine le_trans (rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ 3
    (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T) j x) ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [dLaSlotInsert_perturbSharp_eq_raise_symmS (I := I) (M := M) g₀ T]
  rw [rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 0
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
      (symmS (I := I) (M := M) g₀ T)) j x]
  rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 2) 1) (symmS (I := I) (M := M) g₀ T) j x]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private theorem exists_rfns_dLaSym_tgrid (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
                  (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg) +
                dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) ≤
          C i * dLaGridWin
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 3) := by
  classical
  obtain ⟨CL, hCL_nn, hCL⟩ := exists_rfns_dLaLowered_tgrid (I := I) (M := M) g₀ g_bg hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  set CP : ℕ → ℝ := fun i' => fr ^ 3 * (fr ^ 2 * δ₀ ^ 2 + 1) with hCP_def
  have hCP_nn : ∀ i', 0 ≤ CP i' := fun i' => by rw [hCP_def]; positivity
  set CLT : ℕ → ℝ := fun i => appCcGdiag (E := E) i * ∑ i' ∈ Finset.range (i + 1),
    CP i' * ∑ l ∈ Finset.range (i + 1 - i'), CL l * dLaPairCount (i' + 1) (l + 3) with hCLT_def
  have hCLT_nn : ∀ i, 0 ≤ CLT i := by
    intro i
    refine mul_nonneg (appCcGdiag_nonneg (E := E) i) (Finset.sum_nonneg fun i' _ => ?_)
    exact mul_nonneg (hCP_nn i') (Finset.sum_nonneg fun l _ =>
      mul_nonneg (hCL_nn l) (dLaPairCount_nonneg _ _))
  refine ⟨fun i => 4 * (2 * CL i + 2 * CLT i),
    fun i => by have := hCL_nn i; have := hCLT_nn i; positivity, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set W : ℝ := dLaGridWin b (i + 3) with hW_def
  have hW_nn : 0 ≤ W := dLaGridWin_nonneg b hb (i + 3)
  have hδ₀_nn : 0 ≤ δ₀ := le_trans hδ0 hδ_le
  have hPfac : ∀ i', i' ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + i') x
        ((iteratedCovGrad (I := I) g₀ 4 4 i'
          (slotInsertEndoCc (I := I) (M := M) g₀ 3
            (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T))).toSection x) ≤
      CP i' * dLaGridWin b (i' + 1) := by
    intro i' _
    refine le_trans (rfns_iCG_slotInsert3_dLaPerturb_le (I := I) (M := M) g₀ T i' x) ?_
    have hfr3_nn : (0 : ℝ) ≤ fr ^ 3 := by positivity
    match i' with
    | 0 =>
        have h0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
            ((iteratedCovGrad (I := I) g₀ 0 2 0
              (symmS (I := I) (M := M) g₀ T)).toSection x) ≤ fr ^ 2 * δ ^ 2 := by
          rw [iteratedCovGrad_zero]
          exact rfns_symmS_zero_le_dla (I := I) (M := M) g₀ T hδ0 hbound x
        have hδsq : δ ^ 2 ≤ δ₀ ^ 2 := by nlinarith [hδ0, hδ_le]
        have hwin1 : (1 : ℝ) ≤ dLaGridWin b (0 + 1) := one_le_dLaGridWin b hb (by omega)
        have hle1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
            ((iteratedCovGrad (I := I) g₀ 0 2 0
              (symmS (I := I) (M := M) g₀ T)).toSection x) ≤ fr ^ 2 * δ₀ ^ 2 := by
          refine le_trans h0 (mul_le_mul_of_nonneg_left hδsq (by positivity))
        calc fr ^ 3 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
              ((iteratedCovGrad (I := I) g₀ 0 2 0
                (symmS (I := I) (M := M) g₀ T)).toSection x)
            ≤ fr ^ 3 * (fr ^ 2 * δ₀ ^ 2) := mul_le_mul_of_nonneg_left hle1 hfr3_nn
          _ ≤ fr ^ 3 * (fr ^ 2 * δ₀ ^ 2 + 1) := by
              refine mul_le_mul_of_nonneg_left ?_ hfr3_nn
              linarith
          _ ≤ (fr ^ 3 * (fr ^ 2 * δ₀ ^ 2 + 1)) * dLaGridWin b (0 + 1) := by
              refine le_mul_of_one_le_right ?_ hwin1
              positivity
          _ = CP 0 * dLaGridWin b (0 + 1) := by rw [hCP_def]
    | (m + 1) =>
        have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (m + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (m + 1)
              (symmS (I := I) (M := M) g₀ T)).toSection x) ≤ b (m + 1) :=
          rfns_iCG_symmS_le_dla (I := I) (M := M) g₀ T (m + 1) x
        have h2 : b (m + 1) ≤ Combinatorics.antidiagonalTupleGrid b (m + 1) :=
          single_le_grid_dla b hb (m + 1) (by omega)
        have h3 : Combinatorics.antidiagonalTupleGrid b (m + 1) ≤
            dLaGridWin b ((m + 1) + 1) := grid_le_dLaGridWin b hb (by omega)
        have hfac1 : (1 : ℝ) ≤ fr ^ 2 * δ₀ ^ 2 + 1 :=
          le_add_of_nonneg_left (by positivity)
        have hwin_nn : 0 ≤ dLaGridWin b ((m + 1) + 1) := dLaGridWin_nonneg b hb _
        calc fr ^ 3 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (m + 1)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (m + 1)
                (symmS (I := I) (M := M) g₀ T)).toSection x)
            ≤ fr ^ 3 * dLaGridWin b ((m + 1) + 1) := by
              refine mul_le_mul_of_nonneg_left ?_ hfr3_nn
              exact le_trans h1 (le_trans h2 h3)
          _ ≤ CP (m + 1) * dLaGridWin b ((m + 1) + 1) := by
              rw [hCP_def]
              refine mul_le_mul_of_nonneg_right ?_ hwin_nn
              calc fr ^ 3 = fr ^ 3 * 1 := by ring
                _ ≤ fr ^ 3 * (fr ^ 2 * δ₀ ^ 2 + 1) :=
                    mul_le_mul_of_nonneg_left hfac1 hfr3_nn
  have hLT : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i
        (dLaLoweredPerturbCc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) ≤
      CLT i * W := by
    refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
      (I := I) (M := M) g₀ i 0 4 4
      (slotInsertEndoCc (I := I) (M := M) g₀ 3
        (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T))
      (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg) x) ?_
    have hcell : ∀ i' ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + i') x
            ((iteratedCovGrad (I := I) g₀ 4 4 i'
              (slotInsertEndoCc (I := I) (M := M) g₀ 3
                (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T))).toSection x) *
          ∑ l ∈ Finset.range (i + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 4 l
                (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
        (CP i' * ∑ l ∈ Finset.range (i + 1 - i'), CL l * dLaPairCount (i' + 1) (l + 3)) * W := by
      intro i' hi'
      rw [Finset.mem_range] at hi'
      have hi'_le : i' ≤ i := by omega
      have hA1 := hPfac i' hi'_le
      have hA2 : (∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x)) ≤
          ∑ l ∈ Finset.range (i + 1 - i'), CL l * dLaGridWin b (l + 3) :=
        Finset.sum_le_sum fun l _ => hCL g₁ T htie hδ_le hδ0 hbound l x
      have hsum_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) :=
        Finset.sum_nonneg fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x _
      have hA1_rhs_nn : 0 ≤ CP i' * dLaGridWin b (i' + 1) :=
        mul_nonneg (hCP_nn i') (dLaGridWin_nonneg b hb (i' + 1))
      refine le_trans (mul_le_mul hA1 hA2 hsum_nn hA1_rhs_nn) ?_
      rw [Finset.mul_sum]
      rw [show (CP i' * ∑ l ∈ Finset.range (i + 1 - i'),
          CL l * dLaPairCount (i' + 1) (l + 3)) * W =
          ∑ l ∈ Finset.range (i + 1 - i'),
            (CP i' * (CL l * dLaPairCount (i' + 1) (l + 3))) * W from by
        rw [Finset.mul_sum, Finset.sum_mul]]
      refine Finset.sum_le_sum fun l hl => ?_
      rw [Finset.mem_range] at hl
      have hpair : dLaGridWin b (i' + 1) * dLaGridWin b (l + 3) ≤
          dLaPairCount (i' + 1) (l + 3) * dLaGridWin b (i + 3) :=
        dLaGridWin_mul_le b hb (i' + 1) (l + 3) (i + 3) (by omega)
      calc CP i' * dLaGridWin b (i' + 1) * (CL l * dLaGridWin b (l + 3))
          = (CP i' * CL l) * (dLaGridWin b (i' + 1) * dLaGridWin b (l + 3)) := by ring
        _ ≤ (CP i' * CL l) * (dLaPairCount (i' + 1) (l + 3) * dLaGridWin b (i + 3)) := by
            refine mul_le_mul_of_nonneg_left hpair ?_
            exact mul_nonneg (hCP_nn i') (hCL_nn l)
        _ = (CP i' * (CL l * dLaPairCount (i' + 1) (l + 3))) * W := by
            rw [hW_def]
            ring
    calc appCcGdiag (E := E) i *
          ∑ i' ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + i') x
                ((iteratedCovGrad (I := I) g₀ 4 4 i'
                  (slotInsertEndoCc (I := I) (M := M) g₀ 3
                    (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T))).toSection x) *
              ∑ l ∈ Finset.range (i + 1 - i'),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 4 l
                    (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
        ≤ appCcGdiag (E := E) i *
            ∑ i' ∈ Finset.range (i + 1),
              (CP i' * ∑ l ∈ Finset.range (i + 1 - i'),
                CL l * dLaPairCount (i' + 1) (l + 3)) * W :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell) (appCcGdiag_nonneg (E := E) i)
      _ = CLT i * W := by
          rw [hCLT_def, ← Finset.sum_mul, ← mul_assoc]
  have hL0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i
        (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤ CL i * W :=
    hCL g₁ T htie hδ_le hδ0 hbound i x
  have hLG1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i
        (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) ≤
      2 * (CL i * W) + 2 * (CLT i * W) := by
    refine le_trans (rfns_iCG_add_le_dla (I := I) (M := M) g₀ 0 4 i
      (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)
      (dLaLoweredPerturbCc (I := I) (M := M) g₀ T g₁ g_bg) x) ?_
    linarith [hL0, hLT]
  have hperm : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
          (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg))).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 4 i
          (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) :=
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 4) 1) (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg) i x
  refine le_trans (rfns_iCG_add_le_dla (I := I) (M := M) g₀ 0 4 i
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
      (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg))
    (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg) x) ?_
  rw [hperm]
  linarith [hLG1]

private theorem iteratedCovGrad_smul_dla (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]

private def sigmaE0dla : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![1, 3, 4, 5, 0, 2] : Fin 6 → Fin 6) i,
   fun i => (![4, 0, 5, 1, 2, 3] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

set_option linter.unusedSectionVars false in
private lemma tensor0S_zero_rank_decomp_dla (x : M) (t : Tensor0SSpace 0 I x) :
    t = (Tensor0SSpace.toModel t (fun i : Fin 0 => i.elim0)) • unitTensor (I := I) (M := M) x := by
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  beta_reduce
  rw [show m = (fun i : Fin 0 => i.elim0 : Fin 0 → E) from by
    funext k
    exact k.elim0]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply]
  rw [show Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x)
      (fun i : Fin 0 => i.elim0) = 1 from by
    rw [unitTensor, Tensor0SSpace.toModel_ofModel]
    rfl]
  rw [smul_eq_mul, mul_one]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma slotExtendIter_two_toModel_dla (g₀ : SmoothRiemannianMetric I M)
    (X : SmoothCcTensor g₀ 0 4) (x : M) (D : Tensor0SSpace 2 I x)
    (u : Fin 6 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x) D) u =
      Tensor0SSpace.toModel D ![u 0, u 1] *
        unitModel (I := I) (M := M) g₀ 4 X x (fun k : Fin 4 => u (Fin.natAdd 2 k)) := by
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x) D) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 5 x).symm
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 5 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 4 1 X).toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D)) from rfl]
  have hkey1 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 5)
    (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 5 x).symm
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 4 1 X).toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D)))
    (v0 := u 0) (vs := Matrix.vecTail u)
  rw [ContinuousLinearEquiv.apply_symm_apply] at hkey1
  rw [show (Fin.cons (u 0) (Matrix.vecTail u) : Fin 6 → TangentSpace I x) = u from by
    funext k
    refine Fin.cases rfl (fun i => rfl) k] at hkey1
  rw [← hkey1]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 4 1 X).toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D) (u 0)) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 4 x).symm
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from X.toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)))) from rfl]
  rw [show (Matrix.vecTail u : Fin 5 → TangentSpace I x) =
      Fin.cons (u 1) (fun k : Fin 4 => u (Fin.natAdd 2 k)) from by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · rfl
    · change u (Fin.succ (Fin.succ i)) = u (Fin.natAdd 2 i)
      congr 1
      exact Fin.ext (by simp [Fin.succ, Fin.natAdd]; omega)]
  have hkey2 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 4)
    (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 4 x).symm
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from X.toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)))))
    (v0 := u 1) (vs := fun k : Fin 4 => u (Fin.natAdd 2 k))
  rw [ContinuousLinearEquiv.apply_symm_apply] at hkey2
  rw [← hkey2]
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from X.toSection x).comp
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0))) (u 1)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from X.toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)) (u 1)) from rfl]
  set t : Tensor0SSpace 0 I x :=
    tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)) (u 1) with ht_def
  have htval : Tensor0SSpace.toModel t (fun i : Fin 0 => i.elim0) =
      Tensor0SSpace.toModel D ![u 0, u 1] := by
    rw [ht_def]
    have h1 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 0)
      (T := tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)) (v0 := u 1)
      (vs := fun i : Fin 0 => i.elim0)
    rw [h1]
    have h2 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 1)
      (T := D) (v0 := u 0) (vs := Fin.cons (u 1) (fun i : Fin 0 => i.elim0))
    rw [h2]
    refine congrArg _ ?_
    funext k
    refine Fin.cases rfl (fun i => ?_) k
    refine Fin.cases rfl (fun i2 => i2.elim0) i
  have hdecomp := tensor0S_zero_rank_decomp_dla (I := I) (M := M) x t
  rw [htval] at hdecomp
  rw [hdecomp, map_smul]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rfl

private def pureDTdla (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) :
    SmoothCcTensor g₀ (s + 2) s where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace (s + 2) s I x from cometricDoubleTraceFib (I := I) g₁ s x)
      contMDiff_toFun := cometricDoubleTraceFib_contMDiff (I := I) g₁ s }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private lemma toModel_cons_sum_smul_dla (x : M) {n : ℕ}
    (Zm : Tensor0SModel (n + 1) ℝ E) (d : ℕ) (t : Fin d → ℝ)
    (u : Fin d → E) (rest : Fin n → E) :
    Zm (Fin.cons (∑ c, t c • u c) rest) =
      ∑ c, t c * Zm (Fin.cons (u c) rest) := by
  classical
  have h1 : ∀ v : E, (Fin.cons v rest : Fin (n + 1) → E) =
      Function.update (Fin.cons (0 : E) rest) 0 v := by
    intro v
    rw [Fin.update_cons_zero]
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update (Fin.cons (0 : E) rest) 0 (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c * Zm (Function.update (Fin.cons (0 : E) rest) 0 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : ℝ) • (0 : E)) from (zero_smul ℝ (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a ss ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [ContinuousMultilinearMap.map_update_add]
        rw [ih]
        congr 1
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [smul_eq_mul]
  have h2 := hgen Finset.univ
  rw [h1, h2]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← h1 (u c)]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private lemma toModel_cons_cons_sum_smul_dla (x : M) {n : ℕ}
    (Zm : Tensor0SModel (n + 2) ℝ E) (aa : E) (d : ℕ) (t : Fin d → ℝ)
    (u : Fin d → E) (rest : Fin n → E) :
    Zm (Fin.cons aa (Fin.cons (∑ c, t c • u c) rest)) =
      ∑ c, t c * Zm (Fin.cons aa (Fin.cons (u c) rest)) := by
  classical
  have h1 : ∀ v : E, (Fin.cons aa (Fin.cons v rest) : Fin (n + 2) → E) =
      Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1 v := by
    intro v
    rw [show (1 : Fin (n + 2)) = Fin.succ 0 from rfl]
    rw [← Fin.cons_update]
    rw [Fin.update_cons_zero]
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1 (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c * Zm (Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : ℝ) • (0 : E)) from (zero_smul ℝ (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a ss ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [ContinuousMultilinearMap.map_update_add]
        rw [ih]
        congr 1
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [smul_eq_mul]
  have h2 := hgen Finset.univ
  rw [h1, h2]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← h1 (u c)]

set_option linter.unusedSectionVars false in
private lemma orthoFrame_center_repr_dla (g : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    v = ∑ i : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x i x) v • smoothOrthoFrame (I := I) g x i x := by
  classical
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  haveI : Nonempty (Fin (Module.finrank ℝ E)) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  set B : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x with hB_def
  have horth : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have hlin : LinearIndependent ℝ B := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hpair : g.inner x (∑ i, c i • B i) (B j) = 0 := by
      rw [hc]
      simp
    rw [map_sum, ContinuousLinearMap.sum_apply] at hpair
    have hsimp : ∀ i, g.inner x (c i • B i) (B j) = c i * (if i = j then (1 : ℝ) else 0) := by
      intro i
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, horth i j]
    rw [Finset.sum_congr rfl (fun i _ => hsimp i)] at hpair
    have hcol : (∑ i, c i * (if i = j then (1 : ℝ) else 0)) = c j := by simp
    rw [hcol] at hpair
    exact hpair
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) =
      Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]
    rfl
  set bB : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank hlin hcard with hbB_def
  have hbB_coe : ∀ i, bB i = B i := by
    intro i
    rw [hbB_def]
    change (basisOfLinearIndependentOfCardEqFinrank hlin hcard :
        Fin (Module.finrank ℝ E) → TangentSpace I x) i = B i
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  have hrepr : ∀ (w : TangentSpace I x) (j : Fin (Module.finrank ℝ E)),
      bB.repr w j = g.inner x (B j) w := by
    intro w j
    conv_rhs => rw [← bB.sum_repr w]
    rw [map_sum]
    have hsimp : ∀ i, g.inner x (B j) (bB.repr w i • bB i) =
        bB.repr w i * (if j = i then (1 : ℝ) else 0) := by
      intro i
      rw [map_smul, smul_eq_mul, hbB_coe i, horth j i]
    rw [Finset.sum_congr rfl (fun i _ => hsimp i)]
    simp
  conv_lhs => rw [← bB.sum_repr v]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hrepr v i, hbB_coe i]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
private lemma pureDTdla_eq_trace_fullRaised (g₀ g₁ : SmoothRiemannianMetric I M)
    (s : ℕ) :
    pureDTdla (I := I) (M := M) g₀ g₁ s =
      appCcRS (I := I) (M := M) g₀ (s + 2) (s + 2) s
        (cometricDoubleTraceField (I := I) g₀ s)
        (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁)) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro Z
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro mm
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (pureDTdla (I := I) (M := M) g₀ g₁ s).toSection x) Z) mm =
      ∑ c : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E) mm)) := by
    rw [show ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (pureDTdla (I := I) (M := M) g₀ g₁ s).toSection x) Z) =
        cometricDoubleTraceFib (I := I) g₁ s x Z from rfl]
    rw [cometricDoubleTraceFib_toModel (I := I) g₁ s x Z]
    rw [modelDoubleTrace_apply (E := E) s (cometricLmodel (I := I) g₁ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₁ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x) (Tensor0SSpace.toModel Z) mm]
  rw [hLHS]
  have hRHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (appCcRS (I := I) (M := M) g₀ (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g₀ s)
          (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) Z) mm =
      ∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons (show E from gInvRaisedEndo (I := I) g₀ g₁ x
              (smoothOrthoFrame (I := I) g₀ x a x))
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)) := by
    rw [show ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (appCcRS (I := I) (M := M) g₀ (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g₀ s)
          (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) Z) =
        cometricDoubleTraceFib (I := I) g₀ s x
          (slotInsertEndoFib (I := I) (M := M) (s + 2) 0 x
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x) Z) from by
      rw [appCcRS_toSection]
      rfl]
    rw [cometricDoubleTraceFib_toModel (I := I) g₀ s x]
    rw [modelDoubleTrace_apply (E := E) s (cometricLmodel (I := I) g₀ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      (Tensor0SSpace.toModel
        (slotInsertEndoFib (I := I) (M := M) (s + 2) 0 x
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x) Z)) mm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [slotInsertEndoFib_apply_eval]
    rw [Fin.update_cons_zero]
    rfl
  rw [hRHS]
  have hGrep : ∀ a : Fin (Module.finrank ℝ E),
      (show E from gInvRaisedEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x)) =
        ∑ c : Fin (Module.finrank ℝ E),
          (g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x) (smoothOrthoFrame (I := I) g₁ x c x)) •
            (smoothOrthoFrame (I := I) g₁ x c x : E) := by
    intro a
    have h1 := orthoFrame_center_repr_dla (I := I) (M := M) g₁ x
      (gInvRaisedEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x))
    rw [show (show E from gInvRaisedEndo (I := I) g₀ g₁ x
        (smoothOrthoFrame (I := I) g₀ x a x)) =
        gInvRaisedEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x) from rfl]
    conv_lhs => rw [h1]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    rw [g₁.symm x (smoothOrthoFrame (I := I) g₁ x c x)
      (gInvRaisedEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x))]
    rw [g1_inner_gInvRaisedEndo_left_dla (I := I) (M := M) g₀ g₁ x
      (smoothOrthoFrame (I := I) g₀ x a x) (smoothOrthoFrame (I := I) g₁ x c x)]
  symm
  calc (∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons (show E from gInvRaisedEndo (I := I) g₀ g₁ x
              (smoothOrthoFrame (I := I) g₀ x a x))
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)))
      = ∑ a : Fin (Module.finrank ℝ E), ∑ c : Fin (Module.finrank ℝ E),
          (g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x)) *
          Tensor0SSpace.toModel Z
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hGrep a]
        exact toModel_cons_sum_smul_dla (E := E) x (Tensor0SSpace.toModel Z)
          (Module.finrank ℝ E)
          (fun c => g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x))
          (fun c => (smoothOrthoFrame (I := I) g₁ x c x : E))
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)
    _ = ∑ c : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
          (g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x)) *
          Tensor0SSpace.toModel Z
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)) :=
        Finset.sum_comm
    _ = ∑ c : Fin (Module.finrank ℝ E),
          Tensor0SSpace.toModel Z
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E) mm)) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        have hsum := toModel_cons_cons_sum_smul_dla (E := E) x (Tensor0SSpace.toModel Z)
          ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
          (Module.finrank ℝ E)
          (fun a => g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x))
          (fun a => (smoothOrthoFrame (I := I) g₀ x a x : E)) mm
        rw [← hsum]
        congr 2
        have hrep0 := orthoFrame_center_repr_dla (I := I) (M := M) g₀ x
          (smoothOrthoFrame (I := I) g₁ x c x)
        rw [show (∑ a : Fin (Module.finrank ℝ E),
            g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
              (smoothOrthoFrame (I := I) g₁ x c x) •
              (smoothOrthoFrame (I := I) g₀ x a x : E)) =
            ((∑ a : Fin (Module.finrank ℝ E),
              g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
                (smoothOrthoFrame (I := I) g₁ x c x) •
                smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) from rfl]
        rw [← hrep0]

private def pairTraceOpDla (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 6 2 :=
  appCcRS (I := I) (M := M) g₀ 6 4 2
    (pureDTdla (I := I) (M := M) g₀ g₁ 2)
    (pureDTdla (I := I) (M := M) g₀ g₁ 4)

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
private lemma pairTraceOpDla_apply_toModel (g₀ gm : SmoothRiemannianMetric I M)
    (X : SmoothCcTensor g₀ 0 4) (x : M) (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (appCcRS (I := I) (M := M) g₀ 2 6 2 (pairTraceOpDla (I := I) (M := M) g₀ gm)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) D) v =
      ∑ b : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![(smoothOrthoFrame (I := I) gm x a x : E),
              (smoothOrthoFrame (I := I) gm x b x : E)] *
          unitModel (I := I) (M := M) g₀ 4 X x
            ![v 0, v 1, (smoothOrthoFrame (I := I) gm x a x : E),
              (smoothOrthoFrame (I := I) gm x b x : E)] := by
  classical
  set Y : Tensor0SSpace 6 I x :=
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x) D with hY_def
  have hYval : ∀ w : Fin 6 → TangentSpace I x,
      Tensor0SSpace.toModel Y w =
        Tensor0SSpace.toModel D ![w 1, w 3] *
          unitModel (I := I) (M := M) g₀ 4 X x ![w 4, w 5, w 0, w 2] := by
    intro w
    rw [hY_def]
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x) D) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          rsDomDomCongr sigmaE0dla
            ((slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x)) D) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) sigmaE0dla
      ((slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x) D]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [slotExtendIter_two_toModel_dla (I := I) (M := M) g₀ X x D
      (fun i => w (sigmaE0dla i))]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (appCcRS (I := I) (M := M) g₀ 2 6 2 (pairTraceOpDla (I := I) (M := M) g₀ gm)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) D) =
      cometricDoubleTraceFib (I := I) gm 2 x
        (cometricDoubleTraceFib (I := I) gm 4 x Y) from by
    rw [hY_def]
    rw [appCcRS_toSection]
    rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) gm 2 x]
  rw [modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) gm x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) gm x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) gm 4 x Y))
    (fun j => (v j : E))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [cometricDoubleTraceFib_toModel (I := I) gm 4 x Y]
  rw [modelDoubleTrace_apply (E := E) 4 (cometricLmodel (I := I) gm x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) gm x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel Y)
    (Fin.cons ((smoothOrthoFrame (I := I) gm x b x : TangentSpace I x) : E)
      (Fin.cons ((smoothOrthoFrame (I := I) gm x b x : TangentSpace I x) : E)
        (fun j => (v j : E))))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hYval]
  rfl

private def dLaSymCc (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 4 :=
  domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
      (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg) +
    dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma dLaLoweredG1Cc_unitModel_apply (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (g₁ g_bg : SmoothRiemannianMetric I M)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (x : M) (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4
        (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg) x m =
      g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x (m 1) (m 2) (m 3)) (m 0) := by
  rw [dLaLoweredG1Cc, unitModel_add_dla (I := I) (M := M) g₀ 4]
  rw [dLaLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x m]
  rw [dLaLoweredPerturbCc_unitModel_apply (I := I) (M := M) g₀ T g₁ g_bg x m]
  rw [htie x (dLaCovKernel (I := I) g₁ g_bg x (m 1) (m 2) (m 3)) (m 0)]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma dLaSymCc_unitModel_apply (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (g₁ g_bg : SmoothRiemannianMetric I M)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (x : M) (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4
        (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg) x m =
      g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x (m 0) (m 2) (m 3)) (m 1) +
        g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x (m 1) (m 2) (m 3)) (m 0) := by
  rw [dLaSymCc, unitModel_add_dla (I := I) (M := M) g₀ 4]
  rw [domDomCongrSection_unitModel (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
    (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg) x]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [dLaLoweredG1Cc_unitModel_apply (I := I) (M := M) g₀ T g₁ g_bg htie x
    (fun i => m ((Equiv.swap (0 : Fin 4) 1) i))]
  rw [dLaLoweredG1Cc_unitModel_apply (I := I) (M := M) g₀ T g₁ g_bg htie x m]
  rw [show (Equiv.swap (0 : Fin 4) 1) 0 = 1 from Equiv.swap_apply_left 0 1,
    show (Equiv.swap (0 : Fin 4) 1) 1 = 0 from Equiv.swap_apply_right 0 1,
    show (Equiv.swap (0 : Fin 4) 1) 2 = 2 from by decide,
    show (Equiv.swap (0 : Fin 4) 1) 3 = 3 from by decide]

set_option linter.unusedSectionVars false in
private lemma iCG_succ_cometricDT_zero_dla (g₀ : SmoothRiemannianMetric I M) (s m : ℕ) :
    iteratedCovGrad (I := I) g₀ (s + 2) s (m + 1)
      (cometricDoubleTraceField (I := I) g₀ s) = 0 := by
  induction m with
  | zero =>
      rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
      exact cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ s
  | succ m' ih =>
      rw [iteratedCovGrad_succ, ih, covGrad_zero]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private theorem exists_rfns_pureDT_tgrid (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + j) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) s j
              (pureDTdla (I := I) (M := M) g₀ g₁ s)).toSection x) ≤
          C j * dLaGridWin
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (j + 1) := by
  classical
  obtain ⟨S, hS_nn, hS⟩ := exists_rfns_iteratedCovGrad_sharpFlatEndoCc_tgrid_dla
    (I := I) (M := M) g₀ hδ₀
  obtain ⟨c0, hc0_nn, hc0⟩ := exists_fixedField_rfns_jet_dla (I := I) (M := M) g₀ (s + 2) s
    (cometricDoubleTraceField (I := I) g₀ s)
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun j => appCcGdiag (E := E) j *
      (c0 0 * ∑ l ∈ Finset.range (j + 1), fr ^ (s + 1) * S l),
    fun j => mul_nonneg (appCcGdiag_nonneg (E := E) j)
      (mul_nonneg (hc0_nn 0) (Finset.sum_nonneg fun l _ =>
        mul_nonneg (by positivity) (hS_nn l))), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound j x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  have hsFlat : ∀ l : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
        ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l
          (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) ≤
      (fr ^ (s + 1) * S l) * Combinatorics.antidiagonalTupleGrid b l := by
    intro l
    refine le_trans (rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ (s + 1)
      (fullRaisedEndoField (I := I) (M := M) g₀ g₁) l x) ?_
    rw [← hfr_def]
    have hins : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
        ((iteratedCovGrad (I := I) g₀ 1 1 l
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) ≤
        S l * Combinatorics.antidiagonalTupleGrid b l := by
      rw [← sharpFlatEndoCc_eq_slotInsert_fullRaised_dla (I := I) (M := M) g₀ g₁]
      exact hS g₁ T htie hδ_le hδ0 hbound l x
    calc fr ^ (s + 1) * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x)
        ≤ fr ^ (s + 1) * (S l * Combinatorics.antidiagonalTupleGrid b l) :=
          mul_le_mul_of_nonneg_left hins (by positivity)
      _ = (fr ^ (s + 1) * S l) * Combinatorics.antidiagonalTupleGrid b l := by ring
  rw [pureDTdla_eq_trace_fullRaised (I := I) (M := M) g₀ g₁ s]
  refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
    (I := I) (M := M) g₀ j (s + 2) (s + 2) s
    (cometricDoubleTraceField (I := I) g₀ s)
    (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
      (fullRaisedEndoField (I := I) (M := M) g₀ g₁)) x) ?_
  have hzero : ∀ i' ∈ Finset.range (j + 1), i' ≠ 0 →
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + i') x
          ((iteratedCovGrad (I := I) g₀ (s + 2) s i'
            (cometricDoubleTraceField (I := I) g₀ s)).toSection x) *
        ∑ l ∈ Finset.range (j + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l
              (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
                (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) = 0 := by
    intro i' _ hi'0
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi'0
    rw [iCG_succ_cometricDT_zero_dla (I := I) (M := M) g₀ s m]
    rw [show ((0 : SmoothCcTensor g₀ (s + 2) (s + (m + 1))).toSection x) =
        (0 : TensorRSSpace (s + 2) (s + (m + 1)) I x) from by
      rw [SmoothCcTensor.toSection_zero]; rfl]
    rw [riemannianFiberNormSq_zero (I := I) (M := M) g₀ (s + 2) (s + (m + 1)) x]
    rw [zero_mul]
  have hsum_eq : (∑ i' ∈ Finset.range (j + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + i') x
          ((iteratedCovGrad (I := I) g₀ (s + 2) s i'
            (cometricDoubleTraceField (I := I) g₀ s)).toSection x) *
        ∑ l ∈ Finset.range (j + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l
              (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
                (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x)) =
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + 0) x
          ((iteratedCovGrad (I := I) g₀ (s + 2) s 0
            (cometricDoubleTraceField (I := I) g₀ s)).toSection x) *
        ∑ l ∈ Finset.range (j + 1 - 0),
          riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l
              (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
                (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) := by
    refine Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega)) ?_
    intro i' hi' hi'0
    exact hzero i' hi' hi'0
  rw [hsum_eq]
  have hc0' : riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + 0) x
      ((iteratedCovGrad (I := I) g₀ (s + 2) s 0
        (cometricDoubleTraceField (I := I) g₀ s)).toSection x) ≤ c0 0 := hc0 0 x
  have hsumS : (∑ l ∈ Finset.range (j + 1 - 0),
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
        ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l
          (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x)) ≤
      (∑ l ∈ Finset.range (j + 1), fr ^ (s + 1) * S l) *
        dLaGridWin b (j + 1) := by
    rw [show j + 1 - 0 = j + 1 from rfl]
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun l hl => ?_
    rw [Finset.mem_range] at hl
    refine le_trans (hsFlat l) ?_
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by positivity) (hS_nn l))
    exact grid_le_dLaGridWin b hb (by omega)
  have hrfns_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + 0) x
      ((iteratedCovGrad (I := I) g₀ (s + 2) s 0
        (cometricDoubleTraceField (I := I) g₀ s)).toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ (s + 2) (s + 0) x _
  have hsum_nn : 0 ≤ ∑ l ∈ Finset.range (j + 1 - 0),
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
        ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l
          (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) :=
    Finset.sum_nonneg fun l _ =>
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x _
  refine le_trans (mul_le_mul_of_nonneg_left
    (mul_le_mul hc0' hsumS hsum_nn (hc0_nn 0)) (appCcGdiag_nonneg (E := E) j)) ?_
  rw [← mul_assoc, ← mul_assoc]
  rw [mul_assoc (appCcGdiag (E := E) j) (c0 0)]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private theorem exists_rfns_pairTraceOpDla_tgrid (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 6 2 j
              (pairTraceOpDla (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C j * dLaGridWin
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (j + 1) := by
  classical
  obtain ⟨C2, hC2_nn, hC2⟩ := exists_rfns_pureDT_tgrid (I := I) (M := M) g₀ 2 hδ₀
  obtain ⟨C4, hC4_nn, hC4⟩ := exists_rfns_pureDT_tgrid (I := I) (M := M) g₀ 4 hδ₀
  refine ⟨fun j => appCcGdiag (E := E) j * ∑ i' ∈ Finset.range (j + 1),
      C2 i' * ∑ l ∈ Finset.range (j + 1 - i'), C4 l * dLaPairCount (i' + 1) (l + 1),
    fun j => mul_nonneg (appCcGdiag_nonneg (E := E) j)
      (Finset.sum_nonneg fun i' _ => mul_nonneg (hC2_nn i')
        (Finset.sum_nonneg fun l _ => mul_nonneg (hC4_nn l) (dLaPairCount_nonneg _ _))), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound j x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set W : ℝ := dLaGridWin b (j + 1) with hW_def
  have hW_nn : 0 ≤ W := dLaGridWin_nonneg b hb (j + 1)
  refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
    (I := I) (M := M) g₀ j 6 4 2
    (pureDTdla (I := I) (M := M) g₀ g₁ 2)
    (pureDTdla (I := I) (M := M) g₀ g₁ 4) x) ?_
  have hcell : ∀ i' ∈ Finset.range (j + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i') x
          ((iteratedCovGrad (I := I) g₀ 4 2 i'
            (pureDTdla (I := I) (M := M) g₀ g₁ 2)).toSection x) *
        ∑ l ∈ Finset.range (j + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 6 4 l
              (pureDTdla (I := I) (M := M) g₀ g₁ 4)).toSection x) ≤
      (C2 i' * ∑ l ∈ Finset.range (j + 1 - i'), C4 l * dLaPairCount (i' + 1) (l + 1)) * W := by
    intro i' hi'
    rw [Finset.mem_range] at hi'
    have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i') x
        ((iteratedCovGrad (I := I) g₀ 4 2 i'
          (pureDTdla (I := I) (M := M) g₀ g₁ 2)).toSection x) ≤
        C2 i' * dLaGridWin b (i' + 1) :=
      hC2 g₁ T htie hδ_le hδ0 hbound i' x
    have hA2 : (∑ l ∈ Finset.range (j + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 6 4 l
            (pureDTdla (I := I) (M := M) g₀ g₁ 4)).toSection x)) ≤
        ∑ l ∈ Finset.range (j + 1 - i'), C4 l * dLaGridWin b (l + 1) :=
      Finset.sum_le_sum fun l _ => hC4 g₁ T htie hδ_le hδ0 hbound l x
    have hsum_nn : 0 ≤ ∑ l ∈ Finset.range (j + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 6 4 l
            (pureDTdla (I := I) (M := M) g₀ g₁ 4)).toSection x) :=
      Finset.sum_nonneg fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 6 (4 + l) x _
    have hA1_rhs_nn : 0 ≤ C2 i' * dLaGridWin b (i' + 1) :=
      mul_nonneg (hC2_nn i') (dLaGridWin_nonneg b hb (i' + 1))
    refine le_trans (mul_le_mul hA1 hA2 hsum_nn hA1_rhs_nn) ?_
    rw [Finset.mul_sum]
    rw [show (C2 i' * ∑ l ∈ Finset.range (j + 1 - i'),
        C4 l * dLaPairCount (i' + 1) (l + 1)) * W =
        ∑ l ∈ Finset.range (j + 1 - i'),
          (C2 i' * (C4 l * dLaPairCount (i' + 1) (l + 1))) * W from by
      rw [Finset.mul_sum, Finset.sum_mul]]
    refine Finset.sum_le_sum fun l hl => ?_
    rw [Finset.mem_range] at hl
    have hpair : dLaGridWin b (i' + 1) * dLaGridWin b (l + 1) ≤
        dLaPairCount (i' + 1) (l + 1) * dLaGridWin b (j + 1) :=
      dLaGridWin_mul_le b hb (i' + 1) (l + 1) (j + 1) (by omega)
    calc C2 i' * dLaGridWin b (i' + 1) * (C4 l * dLaGridWin b (l + 1))
        = (C2 i' * C4 l) * (dLaGridWin b (i' + 1) * dLaGridWin b (l + 1)) := by ring
      _ ≤ (C2 i' * C4 l) * (dLaPairCount (i' + 1) (l + 1) * dLaGridWin b (j + 1)) := by
          refine mul_le_mul_of_nonneg_left hpair ?_
          exact mul_nonneg (hC2_nn i') (hC4_nn l)
      _ = (C2 i' * (C4 l * dLaPairCount (i' + 1) (l + 1))) * W := by
          rw [hW_def]
          ring
  calc appCcGdiag (E := E) j *
        ∑ i' ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i') x
              ((iteratedCovGrad (I := I) g₀ 4 2 i'
                (pureDTdla (I := I) (M := M) g₀ g₁ 2)).toSection x) *
            ∑ l ∈ Finset.range (j + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
                ((iteratedCovGrad (I := I) g₀ 6 4 l
                  (pureDTdla (I := I) (M := M) g₀ g₁ 4)).toSection x)
      ≤ appCcGdiag (E := E) j *
          ∑ i' ∈ Finset.range (j + 1),
            (C2 i' * ∑ l ∈ Finset.range (j + 1 - i'),
              C4 l * dLaPairCount (i' + 1) (l + 1)) * W :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell) (appCcGdiag_nonneg (E := E) j)
    _ = _ := by
        rw [← Finset.sum_mul, ← mul_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
private theorem deTurckLieDLaCoeffField_eq_pairTrace
    (g₀ g_bg g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w) :
    deTurckLieDLaCoeffField (I := I) (M := M) g₀ g₁ g_bg =
      (-1 : ℝ) • appCcRS (I := I) (M := M) g₀ 2 6 2 (pairTraceOpDla (I := I) (M := M) g₀ g₁)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  have hsmul : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (((-1 : ℝ) • appCcRS (I := I) (M := M) g₀ 2 6 2 (pairTraceOpDla (I := I) (M := M) g₀ g₁)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x)) D) =
      (-1 : ℝ) • ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        ((appCcRS (I := I) (M := M) g₀ 2 6 2 (pairTraceOpDla (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x)) D) := by
    rw [show ((((-1 : ℝ) • appCcRS (I := I) (M := M) g₀ 2 6 2
        (pairTraceOpDla (I := I) (M := M) g₀ g₁)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x)) =
        (-1 : ℝ) • ((appCcRS (I := I) (M := M) g₀ 2 6 2
          (pairTraceOpDla (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]
      rfl]
    rfl
  rw [hsmul]
  beta_reduce
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [pairTraceOpDla_apply_toModel (I := I) (M := M) g₀ g₁
    (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg) x D v]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (deTurckLieDLaCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x) D) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        dLaBiContrFib (I := I) g₁ g_bg x) D from rfl]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      dLaBiContrFib (I := I) g₁ g_bg x) =
      dLaBiContrFibFixedFrame (I := I) g₁ g_bg (smoothOrthoFrame (I := I) g₁ x) x from rfl]
  rw [dLaBiContrFibFixedFrame_toModel (I := I) g₁ g_bg (smoothOrthoFrame (I := I) g₁ x) x D v]
  have hXval : ∀ a b : Fin (Module.finrank ℝ E),
      unitModel (I := I) (M := M) g₀ 4 (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg) x
        ![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
          (smoothOrthoFrame (I := I) g₁ x b x : E)] =
      g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x (v 0)
          (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)) (v 1) +
        g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x (v 1)
          (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)) (v 0) := by
    intro a b
    rw [dLaSymCc_unitModel_apply (I := I) (M := M) g₀ T g₁ g_bg htie x
      (![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
        (smoothOrthoFrame (I := I) g₁ x b x : E)] : Fin 4 → TangentSpace I x)]
    rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
        (smoothOrthoFrame (I := I) g₁ x b x : E)] : Fin 4 → TangentSpace I x) 0 = v 0 from rfl]
    rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
        (smoothOrthoFrame (I := I) g₁ x b x : E)] : Fin 4 → TangentSpace I x) 1 = v 1 from rfl]
    rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
        (smoothOrthoFrame (I := I) g₁ x b x : E)] : Fin 4 → TangentSpace I x) 2 =
      smoothOrthoFrame (I := I) g₁ x a x from rfl]
    rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
        (smoothOrthoFrame (I := I) g₁ x b x : E)] : Fin 4 → TangentSpace I x) 3 =
      smoothOrthoFrame (I := I) g₁ x b x from rfl]
  rw [show (∑ b : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)] *
        unitModel (I := I) (M := M) g₀ 4 (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg) x
          ![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)]) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          unitModel (I := I) (M := M) g₀ 4 (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg) x
            ![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] from Finset.sum_comm]
  rw [neg_one_mul, neg_one_mul]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hXval a b]
  ring

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
theorem rfns_iteratedCovGrad_deTurckLieDLaCoeffField_diagonalProductGrid_le
    (g₀ g_bg : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieDLaCoeffField (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  classical
  obtain ⟨CPT, hCPT_nn, hCPT⟩ := exists_rfns_pairTraceOpDla_tgrid (I := I) (M := M) g₀ hδ₀
  obtain ⟨CX, hCX_nn, hCX⟩ := exists_rfns_dLaSym_tgrid (I := I) (M := M) g₀ g_bg hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun i => appCcGdiag (E := E) i * ∑ i' ∈ Finset.range (i + 1),
      CPT i' * ∑ l ∈ Finset.range (i + 1 - i'),
        (fr * (fr * CX l)) * dLaPairCount (i' + 1) (l + 3),
    fun i => mul_nonneg (appCcGdiag_nonneg (E := E) i)
      (Finset.sum_nonneg fun i' _ => mul_nonneg (hCPT_nn i')
        (Finset.sum_nonneg fun l _ => mul_nonneg
          (mul_nonneg hfr_nn (mul_nonneg hfr_nn (hCX_nn l))) (dLaPairCount_nonneg _ _))), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set W : ℝ := dLaGridWin b (i + 3) with hW_def
  have hW_nn : 0 ≤ W := dLaGridWin_nonneg b hb (i + 3)
  have hXtower : ∀ l, l ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) ≤
      CX l * dLaGridWin b (l + 3) := by
    intro l _
    exact hCX g₁ T htie hδ_le hδ0 hbound l x
  have hWtower : ∀ l, l ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 6 l
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x) ≤
      (fr * (fr * CX l)) * dLaGridWin b (l + 3) := by
    intro l hl
    have hperm : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 6 l
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))).toSection x) :=
      rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 2 6 sigmaE0dla
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))
        (fun y d => by
          rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) l x
    rw [hperm]
    have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 6 l
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))).toSection x) ≤
        fr * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 5 l
            (slotExtendIter (I := I) (M := M) g₀ 0 4 1
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))).toSection x) :=
      rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5
        (slotExtendIter (I := I) (M := M) g₀ 0 4 1
          (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)) l x
    have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + l) x
        ((iteratedCovGrad (I := I) g₀ 1 5 l
          (slotExtendIter (I := I) (M := M) g₀ 0 4 1
            (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))).toSection x) ≤
        fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l
            (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) :=
      rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4
        (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg) l x
    have h3 := hXtower l hl
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))).toSection x)
        ≤ fr * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 5 l
              (slotExtendIter (I := I) (M := M) g₀ 0 4 1
                (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))).toSection x) := h1
      _ ≤ fr * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x)) :=
          mul_le_mul_of_nonneg_left h2 hfr_nn
      _ ≤ fr * (fr * (CX l * dLaGridWin b (l + 3))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hfr_nn) hfr_nn
      _ = (fr * (fr * CX l)) * dLaGridWin b (l + 3) := by ring
  have hlift : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (deTurckLieDLaCoeffField (I := I) (M := M) g₀ g₁ g_bg)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (appCcRS (I := I) (M := M) g₀ 2 6 2 (pairTraceOpDla (I := I) (M := M) g₀ g₁)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))))).toSection x) := by
    rw [deTurckLieDLaCoeffField_eq_pairTrace (I := I) (M := M) g₀ g_bg g₁ T htie]
    rw [iteratedCovGrad_smul_dla]
    rw [show (((-1 : ℝ) • iteratedCovGrad (I := I) g₀ 2 2 i
        (appCcRS (I := I) (M := M) g₀ 2 6 2 (pairTraceOpDla (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))))).toSection x) =
        (-1 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
          (appCcRS (I := I) (M := M) g₀ 2 6 2 (pairTraceOpDla (I := I) (M := M) g₀ g₁)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))))).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]
      rfl]
    rw [rfns_smul_dla (I := I) (M := M) g₀ 2 (2 + i) x]
    ring
  rw [hlift]
  refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
    (I := I) (M := M) g₀ i 2 6 2
    (pairTraceOpDla (I := I) (M := M) g₀ g₁)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))) x) ?_
  have hcell : ∀ i' ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + i') x
          ((iteratedCovGrad (I := I) g₀ 6 2 i'
            (pairTraceOpDla (I := I) (M := M) g₀ g₁)).toSection x) *
        ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 6 l
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x) ≤
      (CPT i' * ∑ l ∈ Finset.range (i + 1 - i'),
        (fr * (fr * CX l)) * dLaPairCount (i' + 1) (l + 3)) * W := by
    intro i' hi'
    rw [Finset.mem_range] at hi'
    have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + i') x
        ((iteratedCovGrad (I := I) g₀ 6 2 i'
          (pairTraceOpDla (I := I) (M := M) g₀ g₁)).toSection x) ≤
        CPT i' * dLaGridWin b (i' + 1) :=
      hCPT g₁ T htie hδ_le hδ0 hbound i' x
    have hA2 : (∑ l ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x)) ≤
        ∑ l ∈ Finset.range (i + 1 - i'), (fr * (fr * CX l)) * dLaGridWin b (l + 3) := by
      refine Finset.sum_le_sum fun l hl => ?_
      rw [Finset.mem_range] at hl
      exact hWtower l (by omega)
    have hsum_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x) :=
      Finset.sum_nonneg fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + l) x _
    have hA1_rhs_nn : 0 ≤ CPT i' * dLaGridWin b (i' + 1) :=
      mul_nonneg (hCPT_nn i') (dLaGridWin_nonneg b hb (i' + 1))
    refine le_trans (mul_le_mul hA1 hA2 hsum_nn hA1_rhs_nn) ?_
    rw [Finset.mul_sum]
    rw [show (CPT i' * ∑ l ∈ Finset.range (i + 1 - i'),
        (fr * (fr * CX l)) * dLaPairCount (i' + 1) (l + 3)) * W =
        ∑ l ∈ Finset.range (i + 1 - i'),
          (CPT i' * ((fr * (fr * CX l)) * dLaPairCount (i' + 1) (l + 3))) * W from by
      rw [Finset.mul_sum, Finset.sum_mul]]
    refine Finset.sum_le_sum fun l hl => ?_
    rw [Finset.mem_range] at hl
    have hpair : dLaGridWin b (i' + 1) * dLaGridWin b (l + 3) ≤
        dLaPairCount (i' + 1) (l + 3) * dLaGridWin b (i + 3) :=
      dLaGridWin_mul_le b hb (i' + 1) (l + 3) (i + 3) (by omega)
    calc CPT i' * dLaGridWin b (i' + 1) * ((fr * (fr * CX l)) * dLaGridWin b (l + 3))
        = (CPT i' * (fr * (fr * CX l))) *
            (dLaGridWin b (i' + 1) * dLaGridWin b (l + 3)) := by ring
      _ ≤ (CPT i' * (fr * (fr * CX l))) *
            (dLaPairCount (i' + 1) (l + 3) * dLaGridWin b (i + 3)) := by
          refine mul_le_mul_of_nonneg_left hpair ?_
          exact mul_nonneg (hCPT_nn i')
            (mul_nonneg hfr_nn (mul_nonneg hfr_nn (hCX_nn l)))
      _ = (CPT i' * ((fr * (fr * CX l)) * dLaPairCount (i' + 1) (l + 3))) * W := by
          rw [hW_def]
          ring
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell)
    (appCcGdiag_nonneg (E := E) i)) ?_
  rw [← Finset.sum_mul, ← mul_assoc]
  beta_reduce
  rw [hW_def]
  rfl

set_option linter.unusedVariables false in
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (Icc_subset_realizedSmallSet) in
theorem deTurckLieDLaCoeffField_realizedFam_jetL2_perOrder_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieDLaCoeffField (I := I) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤ P i := by
  classical
  set δ₁ : ℝ := max δ₀ 0 with hδ₁_def
  have hδ₁_nn : 0 ≤ δ₁ := le_max_right _ _
  have hδ₁_lt : δ₁ < 1 := max_lt hδ₀ one_pos
  obtain ⟨C, hC_nn, hC⟩ :=
    rfns_iteratedCovGrad_deTurckLieDLaCoeffField_diagonalProductGrid_le
      (I := I) (M := M) g₀ g_bg hδ₁_lt
  obtain ⟨K, hK_nn, hK⟩ :=
    antidiagonalTupleGrid_integral_ballUniform_tameWindow (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => C i * ∑ k ∈ Finset.range (i + 3),
      K k * (1 + ((a + 3 : ℕ) : ℝ) * R ^ 2),
    fun i => mul_nonneg (hC_nn i) (Finset.sum_nonneg fun k _ =>
      mul_nonneg (hK_nn k) (by positivity)), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  set g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hg₁_def
  set Pc : SmoothCcTensor g₀ 0 2 := convexPerturbation (I := I) g₀ T T' s with hPc_def
  have hδs_raw : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ Pc)
      (|1 - s| * δ' + |s| * δ) := by
    rw [hPc_def]
    exact convexPerturbation_gFibreOpBound_abs (I := I) g₀ T T' hδ hδ' s
  set δP : ℝ := max (|1 - s| * δ' + |s| * δ) 0 with hδP_def
  have hδP_nn : 0 ≤ δP := le_max_right _ _
  have hδP_bound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ Pc) δP :=
    gFibreOpBound_mono_of_le (I := I) (M := M) g₀ _ (le_max_left _ _) hδs_raw
  have hδP_le : δP ≤ δ₁ := by
    refine max_le ?_ hδ₁_nn
    rw [abs_of_nonneg h1ms, abs_of_nonneg hs0]
    have h1 : δ' ≤ δ₁ := le_trans hδ'_le (le_max_left _ _)
    have h2 : δ ≤ δ₁ := le_trans hδ_le (le_max_left _ _)
    nlinarith [h1, h2]
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ Pc y v w := by
    intro y v w
    rw [hg₁_def, hPc_def]
    exact realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ'
      (Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs) y v w
  have hPball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j Pc‖ ≤ R := by
    intro j hj
    have heq : iteratedCovGrad (I := I) g₀ 0 2 j Pc
        = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
          + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
      rw [hPc_def]
      rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
        iteratedCovGrad_add, iteratedCovGrad_smul_dla, iteratedCovGrad_smul_dla]
    rw [heq]
    calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
            + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
        ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
      _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg h1ms, abs_of_nonneg hs0]
      _ ≤ (1 - s) * R + s * R :=
          add_le_add (mul_le_mul_of_nonneg_left (hT'ball j hj) h1ms)
            (mul_le_mul_of_nonneg_left (hTball j hj) hs0)
      _ = R := by ring
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieDLaCoeffField (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
        C i * ∑ k ∈ Finset.range (i + 3),
          ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) Pc).toSection x) :=
    fun x => hC g₁ Pc htie hδP_le hδP_nn hδP_bound i x
  have hint_k : ∀ k ∈ Finset.range (i + 3), MeasureTheory.Integrable
      (fun x => ∑ n ∈ Finset.range (k + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
          ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) Pc).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    fun k _ => (hK Pc hPball k).1
  have hint : MeasureTheory.Integrable
      (fun x => C i * ∑ k ∈ Finset.range (i + 3),
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) Pc).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (MeasureTheory.integrable_finset_sum (Finset.range (i + 3)) hint_k).const_mul (C i)
  have hnorm := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
    (iteratedCovGrad (I := I) g₀ 2 2 i
      (deTurckLieDLaCoeffField (I := I) (M := M) g₀ g₁ g_bg))
    (fun x => C i * ∑ k ∈ Finset.range (i + 3),
      ∑ n ∈ Finset.range (k + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
          ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) Pc).toSection x))
    hint hpt
  refine le_trans hnorm ?_
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_finset_sum (Finset.range (i + 3)) hint_k]
  refine mul_le_mul_of_nonneg_left ?_ (hC_nn i)
  refine Finset.sum_le_sum fun k hk => ?_
  rw [Finset.mem_range] at hk
  refine le_trans (hK Pc hPball k).2 ?_
  refine mul_le_mul_of_nonneg_left ?_ (hK_nn k)
  have hsum_le : (∑ j ∈ Finset.range (k + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j Pc‖ ^ 2) ≤ ((a + 3 : ℕ) : ℝ) * R ^ 2 := by
    calc (∑ j ∈ Finset.range (k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j Pc‖ ^ 2)
        ≤ ∑ j ∈ Finset.range (k + 1), R ^ 2 := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [Finset.mem_range] at hj
          have hjle : j ≤ a + 2 := by omega
          have h := hPball j hjle
          nlinarith [norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 j Pc), h, hR]
      _ = ((k + 1 : ℕ) : ℝ) * R ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ((a + 3 : ℕ) : ℝ) * R ^ 2 := by
          have hcast : ((k + 1 : ℕ) : ℝ) ≤ ((a + 3 : ℕ) : ℝ) := by
            exact_mod_cast (by omega : k + 1 ≤ a + 3)
          nlinarith [sq_nonneg R]
  linarith [hsum_le]

/-! ### DLa top-separated tower (keeps the `A1 = covGrad (connDiffSection g₁ g₀)` head separate). -/

/-- Reshape the `connDiffSection` top-separated engine remainder
`∑_{k<j} b(j-k)·antidiagonalTupleGrid b (k+1)` into `dLaGridWin` currency (`R`-independent
combinatorial count times `dLaGridWin b (j+2)`).  Pure combinatorial. -/
private lemma engineRem_le_dLaGridWin (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (j : ℕ) :
    ∑ k ∈ Finset.range j,
        b (j - k) * Combinatorics.antidiagonalTupleGrid b (k + 1) ≤
      (∑ k ∈ Finset.range j, dLaTGridCount (j - k) * dLaTGridCount (k + 1)) *
        dLaGridWin b (j + 2) := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun k hk => ?_)
  rw [Finset.mem_range] at hk
  have hg_nn : 0 ≤ Combinatorics.antidiagonalTupleGrid b (k + 1) :=
    Combinatorics.antidiagonalTupleGrid_nonneg b hb (k + 1)
  have h1 : b (j - k) ≤ Combinatorics.antidiagonalTupleGrid b (j - k) :=
    single_le_grid_dla b hb (j - k) (by omega)
  have h2 : Combinatorics.antidiagonalTupleGrid b (j - k) *
      Combinatorics.antidiagonalTupleGrid b (k + 1) ≤
      (dLaTGridCount (j - k) * dLaTGridCount (k + 1)) *
        Combinatorics.antidiagonalTupleGrid b ((j - k) + (k + 1)) :=
    antidiagonalTupleGrid_mul_le_dla b hb (j - k) (k + 1)
  have h3 : Combinatorics.antidiagonalTupleGrid b ((j - k) + (k + 1)) ≤ dLaGridWin b (j + 2) :=
    grid_le_dLaGridWin b hb (by omega)
  calc b (j - k) * Combinatorics.antidiagonalTupleGrid b (k + 1)
      ≤ Combinatorics.antidiagonalTupleGrid b (j - k) *
          Combinatorics.antidiagonalTupleGrid b (k + 1) :=
        mul_le_mul_of_nonneg_right h1 hg_nn
    _ ≤ (dLaTGridCount (j - k) * dLaTGridCount (k + 1)) *
          Combinatorics.antidiagonalTupleGrid b ((j - k) + (k + 1)) := h2
    _ ≤ (dLaTGridCount (j - k) * dLaTGridCount (k + 1)) * dLaGridWin b (j + 2) :=
        mul_le_mul_of_nonneg_left h3
          (mul_nonneg (dLaTGridCount_nonneg _) (dLaTGridCount_nonneg _))

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **connDiffSection top-separated jet bound in `dLaGridWin` currency.**  The top coefficient
`Ktop = 2·Kt0` (`Kt0` = engine head `10·S 0`) is `R`-independent; the remainder is `dLaGridWin`
(house `R`-pattern).  This is the `dLaGridWin`-currency sibling of the head cell
`covGradConnDiffSection_perOrder_rfns_topSeparated`, in the shape the DLa 8-summand kernel triangle's
`A1` slot consumes. -/
private theorem exists_rfns_connDiffSection_topsep_dla
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ j, 0 ≤ Kc j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
          Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (j + 1)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (j + 1) T).toSection x) +
          Kc j * dLaGridWin
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (j + 2) := by
  classical
  obtain ⟨Kt0, hKt0_nn, Kc0, hKc0_nn, hbot⟩ :=
    rfns_iteratedCovGrad_connDiffSection_topSeparated_le (I := I) (M := M) g₀ hδ₀
  refine ⟨2 * Kt0, mul_nonneg (by norm_num) hKt0_nn,
    fun j => 2 * Kc0 j * (∑ k ∈ Finset.range j, dLaTGridCount (j - k) * dLaTGridCount (k + 1)),
    fun j => mul_nonneg (mul_nonneg (by norm_num) (hKc0_nn j))
      (Finset.sum_nonneg fun k _ =>
        mul_nonneg (dLaTGridCount_nonneg _) (dLaTGridCount_nonneg _)), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound j x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  have heng := hbot g₁ T htie hδ_le hδ0 hbound j x
  set Hd : SmoothCcTensor g₀ 1 (2 + j) :=
    appCcRS (I := I) (M := M) g₀ 1 1 (2 + j)
      (iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁))
      (sharpFlatEndoCc (I := I) g₀ g₁) with hHd_def
  have hhead : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x (Hd.toSection x) ≤
      Kt0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (j + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (j + 1) T).toSection x) := heng.1
  have hrem := heng.2
  have hsplit : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x (Hd.toSection x) +
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) -
          Hd).toSection x) := by
    have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (2 + j) x
      (Hd.toSection x)
      ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) - Hd).toSection x)
    have key :
        (iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection x =
          Hd.toSection x +
            (iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) -
              Hd).toSection x := by
      simp only [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
      abel
    rw [key]
    exact hadd
  have hrem2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) - Hd).toSection x) ≤
      Kc0 j * ((∑ k ∈ Finset.range j, dLaTGridCount (j - k) * dLaTGridCount (k + 1)) *
        dLaGridWin b (j + 2)) :=
    le_trans hrem (mul_le_mul_of_nonneg_left (engineRem_le_dLaGridWin b hb j) (hKc0_nn j))
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection x)
      ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x (Hd.toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) -
            Hd).toSection x) := hsplit
    _ ≤ 2 * (Kt0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (j + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (j + 1) T).toSection x)) +
        2 * (Kc0 j * ((∑ k ∈ Finset.range j,
          dLaTGridCount (j - k) * dLaTGridCount (k + 1)) * dLaGridWin b (j + 2))) := by
          linarith [hhead, hrem2]
    _ = (2 * Kt0) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (j + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (j + 1) T).toSection x) +
        (2 * Kc0 j * (∑ k ∈ Finset.range j,
          dLaTGridCount (j - k) * dLaTGridCount (k + 1))) * dLaGridWin b (j + 2) := by ring

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **Kernel top-separated bound.**  Top-separated twin of `exists_rfns_dLaKernelRaised_tgrid`:
the isolated `A1 = covGrad (connDiffSection g₁ g₀)` head is kept separate via the top-separated
connDiffSection bound (`R`-independent top coefficient `Ktop = 128·KtopA`), while the 7 lower
summands (`A2 = covGrad (connDiffSection g_bg g₀)` and the 6 quad terms) go entirely into the
`dLaGridWin` remainder. -/
private theorem exists_rfns_dLaKernelRaised_topsep (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 3 i
              (dLaKernelRaisedCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
          Kc i * dLaGridWin
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 3) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ := exists_rfns_iteratedCovGrad_connDiffSection_tgrid_dla
    (I := I) (M := M) g₀ hδ₀
  obtain ⟨KtopA, hKtopA_nn, KcA, hKcA_nn, hCAts⟩ :=
    exists_rfns_connDiffSection_topsep_dla (I := I) (M := M) g₀ hδ₀
  obtain ⟨cbg, hcbg_nn, hcbg⟩ := exists_fixedField_rfns_jet_dla (I := I) (M := M) g₀ 1 3
    (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g_bg g₀))
  obtain ⟨cc, hcc_nn, hcc⟩ := exists_fixedField_rfns_jet_dla (I := I) (M := M) g₀ 1 2
    (connDiffSection (I := I) g_bg g₀)
  set CQ1 : ℕ → ℝ := fun j => appCcGdiag (E := E) j * ∑ i' ∈ Finset.range (j + 1),
    (Module.finrank ℝ E : ℝ) * CA i' *
      ∑ l ∈ Finset.range (j + 1 - i'), CA l * dLaPairCount (i' + 2) (l + 2) with hCQ1_def
  set CQ2 : ℕ → ℝ := fun j => appCcGdiag (E := E) j * ∑ i' ∈ Finset.range (j + 1),
    (Module.finrank ℝ E : ℝ) * cc i' *
      ∑ l ∈ Finset.range (j + 1 - i'), CA l * dLaPairCount (i' + 2) (l + 2) with hCQ2_def
  set CQ3 : ℕ → ℝ := fun j => appCcGdiag (E := E) j * ∑ i' ∈ Finset.range (j + 1),
    (Module.finrank ℝ E : ℝ) * CA i' *
      ∑ l ∈ Finset.range (j + 1 - i'), cc l * dLaPairCount (i' + 2) (l + 2) with hCQ3_def
  have hCQ1_nn : ∀ j, 0 ≤ CQ1 j := by
    intro j
    refine mul_nonneg (appCcGdiag_nonneg (E := E) j) (Finset.sum_nonneg fun i' _ => ?_)
    refine mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCA_nn i'))
      (Finset.sum_nonneg fun l _ => mul_nonneg (hCA_nn l) (dLaPairCount_nonneg _ _))
  have hCQ2_nn : ∀ j, 0 ≤ CQ2 j := by
    intro j
    refine mul_nonneg (appCcGdiag_nonneg (E := E) j) (Finset.sum_nonneg fun i' _ => ?_)
    refine mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hcc_nn i'))
      (Finset.sum_nonneg fun l _ => mul_nonneg (hCA_nn l) (dLaPairCount_nonneg _ _))
  have hCQ3_nn : ∀ j, 0 ≤ CQ3 j := by
    intro j
    refine mul_nonneg (appCcGdiag_nonneg (E := E) j) (Finset.sum_nonneg fun i' _ => ?_)
    refine mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCA_nn i'))
      (Finset.sum_nonneg fun l _ => mul_nonneg (hcc_nn l) (dLaPairCount_nonneg _ _))
  refine ⟨128 * KtopA, by positivity,
    fun i => 2 * (2 * (2 * (2 * (2 * (2 * (2 * KcA (i + 1) + 2 * cbg i) + 2 * CQ1 i)
      + 2 * CQ2 i) + 2 * CQ1 i) + 2 * CQ3 i) + 2 * CQ1 i) + 2 * CQ3 i,
    fun i => by
      have h1 := hKcA_nn (i + 1)
      have h2 := hcbg_nn i
      have h3 := hCQ1_nn i
      have h4 := hCQ2_nn i
      have h5 := hCQ3_nn i
      positivity, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set W : ℝ := dLaGridWin b (i + 3) with hW_def
  have hW_nn : 0 ≤ W := dLaGridWin_nonneg b hb (i + 3)
  have hW_ge1 : 1 ≤ W := one_le_dLaGridWin b hb (by omega)
  have harm : ∀ i', i' ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i') x
        ((iteratedCovGrad (I := I) g₀ 1 2 i' (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
      CA i' * dLaGridWin b (i' + 2) :=
    fun i' _ => hCA g₁ T htie hδ_le hδ0 hbound i' x
  have hfix : ∀ i', i' ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i') x
        ((iteratedCovGrad (I := I) g₀ 1 2 i' (connDiffSection (I := I) g_bg g₀)).toSection x) ≤
      cc i' * dLaGridWin b (i' + 2) := by
    intro i' _
    refine le_trans (hcc i' x) ?_
    have h1 : (1 : ℝ) ≤ dLaGridWin b (i' + 2) := one_le_dLaGridWin b hb (by omega)
    nlinarith [hcc_nn i']
  have hQ1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (dLaQuadCc (I := I) (M := M) g₀ g₁ g₁)).toSection x) ≤ CQ1 i * W :=
    dLaQuad_tower_of_factors (I := I) (M := M) g₀ g₁ g₁ i x b hb CA CA hCA_nn hCA_nn harm harm
  have hQ2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (dLaQuadCc (I := I) (M := M) g₀ g_bg g₁)).toSection x) ≤ CQ2 i * W :=
    dLaQuad_tower_of_factors (I := I) (M := M) g₀ g_bg g₁ i x b hb cc CA hcc_nn hCA_nn hfix harm
  have hQ3 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (dLaQuadCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤ CQ3 i * W :=
    dLaQuad_tower_of_factors (I := I) (M := M) g₀ g₁ g_bg i x b hb CA cc hCA_nn hcc_nn harm hfix
  have hrs_eq : ∀ (σ : Equiv.Perm (Fin 3)) (F : SmoothCcTensor g₀ 1 3),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 σ F)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i F).toSection x) := by
    intro σ F
    exact rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 1 3 σ F
      (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 σ F)
      (fun y d => by
        rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) i x
  have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))).toSection x) ≤
      KtopA * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
      KcA (i + 1) * W := by
    rw [rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 1 2 i
      (connDiffSection (I := I) g₁ g₀) x]
    exact hCAts g₁ T htie hδ_le hδ0 hbound (i + 1) x
  have hA2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g_bg g₀))).toSection x) ≤
      cbg i * W := by
    refine le_trans (hcbg i x) ?_
    nlinarith [hcbg_nn i]
  set A1 := covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) with hA1_def
  set A2 := covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g_bg g₀) with hA2_def
  set Q11 := dLaQuadCc (I := I) (M := M) g₀ g₁ g₁ with hQ11_def
  set Qbg1 := dLaQuadCc (I := I) (M := M) g₀ g_bg g₁ with hQbg1_def
  set Q1bg := dLaQuadCc (I := I) (M := M) g₀ g₁ g_bg with hQ1bg_def
  set P1 := rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (0 : Fin 3) 2) Q11
    with hP1_def
  set P2 := rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (0 : Fin 3) 2) Q1bg
    with hP2_def
  set P3 := rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) Q11 with hP3_def
  set P4 := rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) Q1bg with hP4_def
  have hP1_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i P1).toSection x) ≤ CQ1 i * W :=
    le_of_eq_of_le (hrs_eq (Equiv.swap (0 : Fin 3) 2) Q11) hQ1
  have hP2_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i P2).toSection x) ≤ CQ3 i * W :=
    le_of_eq_of_le (hrs_eq (Equiv.swap (0 : Fin 3) 2) Q1bg) hQ3
  have hP3_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i P3).toSection x) ≤ CQ1 i * W :=
    le_of_eq_of_le (hrs_eq (finRotate 3) Q11) hQ1
  have hP4_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i P4).toSection x) ≤ CQ3 i * W :=
    le_of_eq_of_le (hrs_eq (finRotate 3) Q1bg) hQ3
  have t1 := rfns_iCG_sub_le_dla (I := I) (M := M) g₀ 1 3 i A1 A2 x
  have t2 := rfns_iCG_add_le_dla (I := I) (M := M) g₀ 1 3 i (A1 - A2) Q11 x
  have t3 := rfns_iCG_sub_le_dla (I := I) (M := M) g₀ 1 3 i (A1 - A2 + Q11) Qbg1 x
  have t4 := rfns_iCG_sub_le_dla (I := I) (M := M) g₀ 1 3 i (A1 - A2 + Q11 - Qbg1) P1 x
  have t5 := rfns_iCG_add_le_dla (I := I) (M := M) g₀ 1 3 i (A1 - A2 + Q11 - Qbg1 - P1) P2 x
  have t6 := rfns_iCG_sub_le_dla (I := I) (M := M) g₀ 1 3 i
    (A1 - A2 + Q11 - Qbg1 - P1 + P2) P3 x
  have t7 := rfns_iCG_add_le_dla (I := I) (M := M) g₀ 1 3 i
    (A1 - A2 + Q11 - Qbg1 - P1 + P2 - P3) P4 x
  have hKK : dLaKernelRaisedCc (I := I) (M := M) g₀ g₁ g_bg =
      A1 - A2 + Q11 - Qbg1 - P1 + P2 - P3 + P4 := rfl
  rw [hKK]
  linarith [t1, t2, t3, t4, t5, t6, t7, hA1, hA2, hQ1, hQ2, hQ3,
    hP1_le, hP2_le, hP3_le, hP4_le,
    mul_assoc (128 : ℝ) KtopA (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
      ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))]

/-! ### Piece 4 — field-level lift of the DLa top-separated bound. -/


set_option linter.unusedSectionVars false in
/-- Pure-real grid split: pull the `(i'=0, l=i)` top cell out of the appCcRS product grid. -/
private lemma gridSplit_dla (G cΦ0 τ Wtop Wrem gridB : ℝ) (i : ℕ) (pΦ qW : ℕ → ℝ)
    (hG_nn : 0 ≤ G) (hcΦ0 : 0 ≤ cΦ0) (hpΦ_nn : ∀ i', 0 ≤ pΦ i') (hqW_nn : ∀ l, 0 ≤ qW l)
    (hΦ0 : pΦ 0 ≤ cΦ0) (hWi : qW i ≤ Wtop * τ + Wrem)
    (hfull : G * ∑ i' ∈ Finset.range (i + 1),
        pΦ i' * ∑ l ∈ Finset.range (i + 1 - i'), qW l ≤ gridB) :
    G * ∑ i' ∈ Finset.range (i + 1),
        pΦ i' * ∑ l ∈ Finset.range (i + 1 - i'), qW l ≤
      G * cΦ0 * Wtop * τ + (G * cΦ0 * Wrem + gridB) := by
  classical
  have hqi_le_S0 : qW i ≤ ∑ l ∈ Finset.range (i + 1 - 0), qW l :=
    Finset.single_le_sum (f := qW) (fun l _ => hqW_nn l) (by rw [Finset.mem_range]; omega)
  have hpq_le : pΦ 0 * qW i ≤
      ∑ i' ∈ Finset.range (i + 1), pΦ i' * ∑ l ∈ Finset.range (i + 1 - i'), qW l := by
    calc pΦ 0 * qW i
        ≤ pΦ 0 * ∑ l ∈ Finset.range (i + 1 - 0), qW l :=
          mul_le_mul_of_nonneg_left hqi_le_S0 (hpΦ_nn 0)
      _ ≤ ∑ i' ∈ Finset.range (i + 1), pΦ i' * ∑ l ∈ Finset.range (i + 1 - i'), qW l :=
          Finset.single_le_sum
            (f := fun i' => pΦ i' * ∑ l ∈ Finset.range (i + 1 - i'), qW l)
            (fun i' _ => mul_nonneg (hpΦ_nn i') (Finset.sum_nonneg fun l _ => hqW_nn l))
            (by rw [Finset.mem_range]; omega)
  have hcell : G * (pΦ 0 * qW i) ≤ G * (cΦ0 * (Wtop * τ + Wrem)) := by
    refine mul_le_mul_of_nonneg_left ?_ hG_nn
    calc pΦ 0 * qW i
        ≤ cΦ0 * qW i := mul_le_mul_of_nonneg_right hΦ0 (hqW_nn i)
      _ ≤ cΦ0 * (Wtop * τ + Wrem) := mul_le_mul_of_nonneg_left hWi hcΦ0
  have hrest : G * ((∑ i' ∈ Finset.range (i + 1),
      pΦ i' * ∑ l ∈ Finset.range (i + 1 - i'), qW l) - pΦ 0 * qW i) ≤ gridB :=
    le_trans (mul_le_mul_of_nonneg_left
      (by linarith [mul_nonneg (hpΦ_nn 0) (hqW_nn i)]) hG_nn) hfull
  calc G * ∑ i' ∈ Finset.range (i + 1), pΦ i' * ∑ l ∈ Finset.range (i + 1 - i'), qW l
      = G * (pΦ 0 * qW i) +
          G * ((∑ i' ∈ Finset.range (i + 1),
            pΦ i' * ∑ l ∈ Finset.range (i + 1 - i'), qW l) - pΦ 0 * qW i) := by ring
    _ ≤ G * (cΦ0 * (Wtop * τ + Wrem)) + gridB := add_le_add hcell hrest
    _ = G * cΦ0 * Wtop * τ + (G * cΦ0 * Wrem + gridB) := by ring

set_option linter.unusedSectionVars false in
/-- Shared appCcRS full-grid bound (`hfull` producer for both DLa extractions;
both use window shape `(i'+1)(l+3) → (i+3)`). -/
private lemma appCcGrid_le_dla (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (i : ℕ)
    (pΦ cΦ qW cW : ℕ → ℝ)
    (hqW_nn : ∀ l, 0 ≤ qW l) (hcΦ_nn : ∀ i', 0 ≤ cΦ i') (hcW_nn : ∀ l, 0 ≤ cW l)
    (hΦ : ∀ i', i' ≤ i → pΦ i' ≤ cΦ i' * dLaGridWin b (i' + 1))
    (hW : ∀ l, l ≤ i → qW l ≤ cW l * dLaGridWin b (l + 3)) :
    appCcGdiag (E := E) i * ∑ i' ∈ Finset.range (i + 1),
        pΦ i' * ∑ l ∈ Finset.range (i + 1 - i'), qW l ≤
      (appCcGdiag (E := E) i * ∑ i' ∈ Finset.range (i + 1),
        cΦ i' * ∑ l ∈ Finset.range (i + 1 - i'), cW l * dLaPairCount (i' + 1) (l + 3)) *
        dLaGridWin b (i + 3) := by
  classical
  have hcell : ∀ i' ∈ Finset.range (i + 1),
      pΦ i' * ∑ l ∈ Finset.range (i + 1 - i'), qW l ≤
      (cΦ i' * ∑ l ∈ Finset.range (i + 1 - i'), cW l * dLaPairCount (i' + 1) (l + 3)) *
        dLaGridWin b (i + 3) := by
    intro i' hi'
    rw [Finset.mem_range] at hi'
    have hi'_le : i' ≤ i := by omega
    have hA1 : pΦ i' ≤ cΦ i' * dLaGridWin b (i' + 1) := hΦ i' hi'_le
    have hA2 : (∑ l ∈ Finset.range (i + 1 - i'), qW l) ≤
        ∑ l ∈ Finset.range (i + 1 - i'), cW l * dLaGridWin b (l + 3) :=
      Finset.sum_le_sum fun l hl => hW l (by rw [Finset.mem_range] at hl; omega)
    have hsum_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'), qW l :=
      Finset.sum_nonneg fun l _ => hqW_nn l
    have hA1_rhs_nn : 0 ≤ cΦ i' * dLaGridWin b (i' + 1) :=
      mul_nonneg (hcΦ_nn i') (dLaGridWin_nonneg b hb (i' + 1))
    refine le_trans (mul_le_mul hA1 hA2 hsum_nn hA1_rhs_nn) ?_
    rw [Finset.mul_sum]
    rw [show (cΦ i' * ∑ l ∈ Finset.range (i + 1 - i'),
        cW l * dLaPairCount (i' + 1) (l + 3)) * dLaGridWin b (i + 3) =
        ∑ l ∈ Finset.range (i + 1 - i'),
          (cΦ i' * (cW l * dLaPairCount (i' + 1) (l + 3))) * dLaGridWin b (i + 3) from by
      rw [Finset.mul_sum, Finset.sum_mul]]
    refine Finset.sum_le_sum fun l hl => ?_
    rw [Finset.mem_range] at hl
    have hpair : dLaGridWin b (i' + 1) * dLaGridWin b (l + 3) ≤
        dLaPairCount (i' + 1) (l + 3) * dLaGridWin b (i + 3) :=
      dLaGridWin_mul_le b hb (i' + 1) (l + 3) (i + 3) (by omega)
    calc cΦ i' * dLaGridWin b (i' + 1) * (cW l * dLaGridWin b (l + 3))
        = (cΦ i' * cW l) * (dLaGridWin b (i' + 1) * dLaGridWin b (l + 3)) := by ring
      _ ≤ (cΦ i' * cW l) * (dLaPairCount (i' + 1) (l + 3) * dLaGridWin b (i + 3)) :=
          mul_le_mul_of_nonneg_left hpair (mul_nonneg (hcΦ_nn i') (hcW_nn l))
      _ = (cΦ i' * (cW l * dLaPairCount (i' + 1) (l + 3))) * dLaGridWin b (i + 3) := by ring
  calc appCcGdiag (E := E) i * ∑ i' ∈ Finset.range (i + 1),
        pΦ i' * ∑ l ∈ Finset.range (i + 1 - i'), qW l
      ≤ appCcGdiag (E := E) i * ∑ i' ∈ Finset.range (i + 1),
          (cΦ i' * ∑ l ∈ Finset.range (i + 1 - i'), cW l * dLaPairCount (i' + 1) (l + 3)) *
            dLaGridWin b (i + 3) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell) (appCcGdiag_nonneg (E := E) i)
    _ = (appCcGdiag (E := E) i * ∑ i' ∈ Finset.range (i + 1),
          cΦ i' * ∑ l ∈ Finset.range (i + 1 - i'), cW l * dLaPairCount (i' + 1) (l + 3)) *
          dLaGridWin b (i + 3) := by
        rw [← Finset.sum_mul, ← mul_assoc]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **dLaLoweredCc top-separated.**  Raise-eq bridge into the kernel top-separation (piece 3).
`R`-independent top coefficient (`= 256·Kt0`). -/
private theorem exists_rfns_dLaLowered_topsep (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
          Kc i * dLaGridWin
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 3) := by
  obtain ⟨Ktop, hKtop_nn, Kc, hKc_nn, hker⟩ :=
    exists_rfns_dLaKernelRaised_topsep (I := I) (M := M) g₀ g_bg hδ₀
  refine ⟨Ktop, hKtop_nn, Kc, hKc_nn, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  have hbridge : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i
        (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i
          (dLaKernelRaisedCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) := by
    have h := rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 2
      (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg) i x
    rw [dLaLoweredCc_raise_repr (I := I) (M := M) g₀ g₁ g_bg] at h
    exact h.symm
  rw [hbridge]
  exact hker g₁ T htie hδ_le hδ0 hbound i x

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 3200000 in
/-- **dLaSymCc top-separated.**  Exported top coefficient `Ktop_sym` is a FIXED `R`-free real;
the `appCcGdiag i` power is explicit so the summed layer fixes one constant via
`appCcGdiag i ≤ appCcGdiag a`. -/
private theorem exists_rfns_dLaSym_topsep (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) ≤
          Ktop * appCcGdiag (E := E) i *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
          Kc i * dLaGridWin
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 3) := by
  classical
  obtain ⟨KtopL, hKtopL_nn, KcL, hKcL_nn, hL⟩ :=
    exists_rfns_dLaLowered_topsep (I := I) (M := M) g₀ g_bg hδ₀
  obtain ⟨CL, hCL_nn, hCL⟩ := exists_rfns_dLaLowered_tgrid (I := I) (M := M) g₀ g_bg hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  set cPer : ℝ := fr ^ 5 * δ₀ ^ 2 with hcPer_def
  have hcPer_nn : 0 ≤ cPer := by rw [hcPer_def]; positivity
  set CP : ℕ → ℝ := fun _ => fr ^ 3 * (fr ^ 2 * δ₀ ^ 2 + 1) with hCP_def
  have hCP_nn : ∀ i', 0 ≤ CP i' := fun i' => by rw [hCP_def]; positivity
  set CLT : ℕ → ℝ := fun i => appCcGdiag (E := E) i * ∑ i' ∈ Finset.range (i + 1),
    CP i' * ∑ l ∈ Finset.range (i + 1 - i'), CL l * dLaPairCount (i' + 1) (l + 3) with hCLT_def
  have hCLT_nn : ∀ i, 0 ≤ CLT i := by
    intro i
    refine mul_nonneg (appCcGdiag_nonneg (E := E) i) (Finset.sum_nonneg fun i' _ => ?_)
    exact mul_nonneg (hCP_nn i') (Finset.sum_nonneg fun l _ =>
      mul_nonneg (hCL_nn l) (dLaPairCount_nonneg _ _))
  refine ⟨8 * KtopL * (1 + cPer),
      mul_nonneg (mul_nonneg (by norm_num) hKtopL_nn) (by positivity),
    fun i => 8 * KcL i + 8 * appCcGdiag (E := E) i * cPer * KcL i + 8 * CLT i,
    fun i => by
      have h1 := hKcL_nn i; have h2 := hCLT_nn i; have h3 := appCcGdiag_nonneg (E := E) i
      positivity, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set W : ℝ := dLaGridWin b (i + 3) with hW_def
  have hW_nn : 0 ≤ W := dLaGridWin_nonneg b hb (i + 3)
  have hτ_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
      ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (i + 2)) x _
  have happ_nn : 0 ≤ appCcGdiag (E := E) i := appCcGdiag_nonneg (E := E) i
  have happ_ge1 : (1 : ℝ) ≤ appCcGdiag (E := E) i := by
    rw [appCcGdiag]
    exact one_le_pow₀ (by
      have : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
      linarith)
  -- perturb slotInsert Φ-per-order (`CP i'` constant, R-free), for `hfull`.
  have hPfac : ∀ i', i' ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + i') x
        ((iteratedCovGrad (I := I) g₀ 4 4 i'
          (slotInsertEndoCc (I := I) (M := M) g₀ 3
            (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T))).toSection x) ≤
      CP i' * dLaGridWin b (i' + 1) := by
    intro i' _
    refine le_trans (rfns_iCG_slotInsert3_dLaPerturb_le (I := I) (M := M) g₀ T i' x) ?_
    have hfr3_nn : (0 : ℝ) ≤ fr ^ 3 := by positivity
    match i' with
    | 0 =>
        have h0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
            ((iteratedCovGrad (I := I) g₀ 0 2 0
              (symmS (I := I) (M := M) g₀ T)).toSection x) ≤ fr ^ 2 * δ ^ 2 := by
          rw [iteratedCovGrad_zero]
          exact rfns_symmS_zero_le_dla (I := I) (M := M) g₀ T hδ0 hbound x
        have hδsq : δ ^ 2 ≤ δ₀ ^ 2 := by nlinarith [hδ0, hδ_le]
        have hwin1 : (1 : ℝ) ≤ dLaGridWin b (0 + 1) := one_le_dLaGridWin b hb (by omega)
        have hle1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
            ((iteratedCovGrad (I := I) g₀ 0 2 0
              (symmS (I := I) (M := M) g₀ T)).toSection x) ≤ fr ^ 2 * δ₀ ^ 2 :=
          le_trans h0 (mul_le_mul_of_nonneg_left hδsq (by positivity))
        calc fr ^ 3 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
              ((iteratedCovGrad (I := I) g₀ 0 2 0
                (symmS (I := I) (M := M) g₀ T)).toSection x)
            ≤ fr ^ 3 * (fr ^ 2 * δ₀ ^ 2) := mul_le_mul_of_nonneg_left hle1 hfr3_nn
          _ ≤ fr ^ 3 * (fr ^ 2 * δ₀ ^ 2 + 1) := by
              refine mul_le_mul_of_nonneg_left ?_ hfr3_nn; linarith
          _ ≤ (fr ^ 3 * (fr ^ 2 * δ₀ ^ 2 + 1)) * dLaGridWin b (0 + 1) :=
              le_mul_of_one_le_right (by positivity) hwin1
          _ = CP 0 * dLaGridWin b (0 + 1) := by rw [hCP_def]
    | (m + 1) =>
        have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (m + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (m + 1)
              (symmS (I := I) (M := M) g₀ T)).toSection x) ≤ b (m + 1) :=
          rfns_iCG_symmS_le_dla (I := I) (M := M) g₀ T (m + 1) x
        have h2 : b (m + 1) ≤ Combinatorics.antidiagonalTupleGrid b (m + 1) :=
          single_le_grid_dla b hb (m + 1) (by omega)
        have h3 : Combinatorics.antidiagonalTupleGrid b (m + 1) ≤
            dLaGridWin b ((m + 1) + 1) := grid_le_dLaGridWin b hb (by omega)
        have hfac1 : (1 : ℝ) ≤ fr ^ 2 * δ₀ ^ 2 + 1 := le_add_of_nonneg_left (by positivity)
        have hwin_nn : 0 ≤ dLaGridWin b ((m + 1) + 1) := dLaGridWin_nonneg b hb _
        calc fr ^ 3 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (m + 1)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (m + 1)
                (symmS (I := I) (M := M) g₀ T)).toSection x)
            ≤ fr ^ 3 * dLaGridWin b ((m + 1) + 1) :=
              mul_le_mul_of_nonneg_left (le_trans h1 (le_trans h2 h3)) hfr3_nn
          _ ≤ CP (m + 1) * dLaGridWin b ((m + 1) + 1) := by
              rw [hCP_def]
              refine mul_le_mul_of_nonneg_right ?_ hwin_nn
              calc fr ^ 3 = fr ^ 3 * 1 := by ring
                _ ≤ fr ^ 3 * (fr ^ 2 * δ₀ ^ 2 + 1) := mul_le_mul_of_nonneg_left hfac1 hfr3_nn
  -- perturb order-0 (`cPer`), for the top cell.
  have hPer0 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + 0) x
      ((iteratedCovGrad (I := I) g₀ 4 4 0
        (slotInsertEndoCc (I := I) (M := M) g₀ 3
          (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T))).toSection x) ≤ cPer := by
    refine le_trans (rfns_iCG_slotInsert3_dLaPerturb_le (I := I) (M := M) g₀ T 0 x) ?_
    have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
        ((iteratedCovGrad (I := I) g₀ 0 2 0 (symmS (I := I) (M := M) g₀ T)).toSection x) ≤
        fr ^ 2 * δ ^ 2 := by
      rw [iteratedCovGrad_zero]
      exact rfns_symmS_zero_le_dla (I := I) (M := M) g₀ T hδ0 hbound x
    have hδsq : δ ^ 2 ≤ δ₀ ^ 2 := by nlinarith [hδ0, hδ_le]
    rw [hcPer_def]
    calc fr ^ 3 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
          ((iteratedCovGrad (I := I) g₀ 0 2 0 (symmS (I := I) (M := M) g₀ T)).toSection x)
        ≤ fr ^ 3 * (fr ^ 2 * δ ^ 2) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ fr ^ 3 * (fr ^ 2 * δ₀ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hδsq (by positivity))
            (by positivity)
      _ = fr ^ 5 * δ₀ ^ 2 := by ring
  -- perturb top-separated.
  have hPer : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i
        (dLaLoweredPerturbCc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) ≤
      appCcGdiag (E := E) i * cPer * KtopL *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
        (appCcGdiag (E := E) i * cPer * (KcL i * W) + CLT i * W) := by
    refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
      (I := I) (M := M) g₀ i 0 4 4
      (slotInsertEndoCc (I := I) (M := M) g₀ 3 (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T))
      (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg) x) ?_
    exact gridSplit_dla (appCcGdiag (E := E) i) cPer
      (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))
      KtopL (KcL i * W) (CLT i * W) i
      (fun i' => riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + i') x
        ((iteratedCovGrad (I := I) g₀ 4 4 i'
          (slotInsertEndoCc (I := I) (M := M) g₀ 3
            (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T))).toSection x))
      (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x))
      happ_nn hcPer_nn
      (fun i' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 4 (4 + i') x _)
      (fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x _)
      hPer0 (hL g₁ T htie hδ_le hδ0 hbound i x)
      (le_trans (appCcGrid_le_dla b hb i
        (fun i' => riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + i') x
          ((iteratedCovGrad (I := I) g₀ 4 4 i'
            (slotInsertEndoCc (I := I) (M := M) g₀ 3
              (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T))).toSection x))
        CP
        (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l
            (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x))
        CL
        (fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x _)
        hCP_nn hCL_nn hPfac (fun l _ => hCL g₁ T htie hδ_le hδ0 hbound l x))
        (le_of_eq (by rw [hCLT_def, hW_def])))
  -- G1 = dLaLoweredCc + dLaLoweredPerturbCc.
  have hG1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i
        (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) ≤
      (2 * KtopL * (1 + cPer)) * appCcGdiag (E := E) i *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
        (2 * KcL i + 2 * appCcGdiag (E := E) i * cPer * KcL i + 2 * CLT i) * W := by
    refine le_trans (rfns_iCG_add_le_dla (I := I) (M := M) g₀ 0 4 i
      (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)
      (dLaLoweredPerturbCc (I := I) (M := M) g₀ T g₁ g_bg) x) ?_
    have hL0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 4 i
          (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
        KtopL * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) + KcL i * W :=
      hL g₁ T htie hδ_le hδ0 hbound i x
    have htoplift : 2 * KtopL + 2 * appCcGdiag (E := E) i * cPer * KtopL ≤
        (2 * KtopL * (1 + cPer)) * appCcGdiag (E := E) i := by
      have hkey : (0 : ℝ) ≤ KtopL * (appCcGdiag (E := E) i - 1) :=
        mul_nonneg hKtopL_nn (by linarith [happ_ge1])
      nlinarith [hkey, hcPer_nn, hKtopL_nn]
    calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (dLaLoweredPerturbCc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x)
        ≤ 2 * (KtopL * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) + KcL i * W) +
            2 * (appCcGdiag (E := E) i * cPer * KtopL *
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
                (appCcGdiag (E := E) i * cPer * (KcL i * W) + CLT i * W)) := by
          linarith [hL0, hPer]
      _ = (2 * KtopL + 2 * appCcGdiag (E := E) i * cPer * KtopL) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
          (2 * KcL i + 2 * appCcGdiag (E := E) i * cPer * KcL i + 2 * CLT i) * W := by ring
      _ ≤ (2 * KtopL * (1 + cPer)) * appCcGdiag (E := E) i *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
          (2 * KcL i + 2 * appCcGdiag (E := E) i * cPer * KcL i + 2 * CLT i) * W :=
          add_le_add (mul_le_mul_of_nonneg_right htoplift hτ_nn) (le_refl _)
  -- sym = domDomCongr(swap 0 1)(G1) + G1.
  have hperm : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
          (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg))).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 4 i
          (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) :=
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 4) 1) (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg) i x
  refine le_trans (rfns_iCG_add_le_dla (I := I) (M := M) g₀ 0 4 i
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
      (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg))
    (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg) x) ?_
  rw [hperm]
  calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 4 i
            (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 4 i
            (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x)
      ≤ 2 * ((2 * KtopL * (1 + cPer)) * appCcGdiag (E := E) i *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
          (2 * KcL i + 2 * appCcGdiag (E := E) i * cPer * KcL i + 2 * CLT i) * W) +
        2 * ((2 * KtopL * (1 + cPer)) * appCcGdiag (E := E) i *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
          (2 * KcL i + 2 * appCcGdiag (E := E) i * cPer * KcL i + 2 * CLT i) * W) := by
        linarith [hG1]
    _ = (8 * KtopL * (1 + cPer)) * appCcGdiag (E := E) i *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
        (8 * KcL i + 8 * appCcGdiag (E := E) i * cPer * KcL i + 8 * CLT i) * W := by ring


set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 3200000 in
/-- **Field pointwise top-separated bound** for `deTurckLieDLaCoeffField`.  Exported base top
coefficient `Ktop` is `R`-free; the `appCcGdiag i` powers are explicit (the field carries TWO
nested appCcRS extractions, so `(appCcGdiag i)²`). -/
private theorem rfns_iCG_dLaField_topsep (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieDLaCoeffField (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          Ktop * appCcGdiag (E := E) i * appCcGdiag (E := E) i *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
          Kc i * dLaGridWin
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 3) := by
  classical
  obtain ⟨CPT, hCPT_nn, hCPT⟩ := exists_rfns_pairTraceOpDla_tgrid (I := I) (M := M) g₀ hδ₀
  obtain ⟨KtopS, hKtopS_nn, KcS, hKcS_nn, hSym⟩ :=
    exists_rfns_dLaSym_topsep (I := I) (M := M) g₀ g_bg hδ₀
  obtain ⟨CX, hCX_nn, hCX⟩ := exists_rfns_dLaSym_tgrid (I := I) (M := M) g₀ g_bg hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  set Cfield : ℕ → ℝ := fun i => appCcGdiag (E := E) i * ∑ i' ∈ Finset.range (i + 1),
    CPT i' * ∑ l ∈ Finset.range (i + 1 - i'), (fr * (fr * CX l)) * dLaPairCount (i' + 1) (l + 3)
    with hCfield_def
  have hCfield_nn : ∀ i, 0 ≤ Cfield i := by
    intro i
    refine mul_nonneg (appCcGdiag_nonneg (E := E) i) (Finset.sum_nonneg fun i' _ => ?_)
    exact mul_nonneg (hCPT_nn i') (Finset.sum_nonneg fun l _ =>
      mul_nonneg (mul_nonneg hfr_nn (mul_nonneg hfr_nn (hCX_nn l))) (dLaPairCount_nonneg _ _))
  refine ⟨CPT 0 * fr ^ 2 * KtopS,
      mul_nonneg (mul_nonneg (hCPT_nn 0) (by positivity)) hKtopS_nn,
    fun i => appCcGdiag (E := E) i * CPT 0 * fr ^ 2 * KcS i + Cfield i,
    fun i => by
      have h1 := hKcS_nn i; have h2 := hCfield_nn i; have h3 := appCcGdiag_nonneg (E := E) i
      have h4 := hCPT_nn 0
      positivity, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set W : ℝ := dLaGridWin b (i + 3) with hW_def
  have hW_nn : 0 ≤ W := dLaGridWin_nonneg b hb (i + 3)
  have happ_nn : 0 ≤ appCcGdiag (E := E) i := appCcGdiag_nonneg (E := E) i
  -- X-tower reduction `rfns(∇^l X) ≤ fr²·rfns(∇^l dLaSymCc)`.
  have hXfr : ∀ l, riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 6 l
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x) ≤
      fr ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) := by
    intro l
    have hperm : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 6 l
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))).toSection x) :=
      rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 2 6 sigmaE0dla
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))
        (fun y d => by rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) l x
    rw [hperm]
    have h1 := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5
      (slotExtendIter (I := I) (M := M) g₀ 0 4 1 (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)) l x
    have h2 := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4
      (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg) l x
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))).toSection x)
        ≤ fr * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 5 l
              (slotExtendIter (I := I) (M := M) g₀ 0 4 1
                (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))).toSection x) := h1
      _ ≤ fr * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x)) :=
          mul_le_mul_of_nonneg_left h2 hfr_nn
      _ = fr ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) := by ring
  -- pairTrace order-0 for the top cell.
  have hPT0 : riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + 0) x
      ((iteratedCovGrad (I := I) g₀ 6 2 0 (pairTraceOpDla (I := I) (M := M) g₀ g₁)).toSection x) ≤
      CPT 0 := by
    have h := hCPT g₁ T htie hδ_le hδ0 hbound 0 x
    rwa [show dLaGridWin b (0 + 1) = 1 from by
          rw [dLaGridWin, Finset.sum_range_one, Combinatorics.antidiagonalTupleGrid_zero],
        mul_one] at h
  -- top cell (via X-tower at `l = i` + dLaSym top-sep).
  have hWi : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 6 i
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x) ≤
      (fr ^ 2 * KtopS * appCcGdiag (E := E) i) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
        fr ^ 2 * KcS i * W := by
    refine le_trans (hXfr i) ?_
    have hs := hSym g₁ T htie hδ_le hδ0 hbound i x
    calc fr ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 4 i
            (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x)
        ≤ fr ^ 2 * (KtopS * appCcGdiag (E := E) i *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) + KcS i * W) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = (fr ^ 2 * KtopS * appCcGdiag (E := E) i) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) + fr ^ 2 * KcS i * W := by
          ring
  -- field ↔ appCcRS lift.
  have hlift : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (deTurckLieDLaCoeffField (I := I) (M := M) g₀ g₁ g_bg)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (appCcRS (I := I) (M := M) g₀ 2 6 2 (pairTraceOpDla (I := I) (M := M) g₀ g₁)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))))).toSection x) := by
    rw [deTurckLieDLaCoeffField_eq_pairTrace (I := I) (M := M) g₀ g_bg g₁ T htie]
    rw [iteratedCovGrad_smul_dla]
    rw [show (((-1 : ℝ) • iteratedCovGrad (I := I) g₀ 2 2 i
        (appCcRS (I := I) (M := M) g₀ 2 6 2 (pairTraceOpDla (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))))).toSection x) =
        (-1 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
          (appCcRS (I := I) (M := M) g₀ 2 6 2 (pairTraceOpDla (I := I) (M := M) g₀ g₁)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))))).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rw [rfns_smul_dla (I := I) (M := M) g₀ 2 (2 + i) x]
    ring
  rw [hlift]
  refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
    (I := I) (M := M) g₀ i 2 6 2 (pairTraceOpDla (I := I) (M := M) g₀ g₁)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))) x) ?_
  refine le_trans (gridSplit_dla (appCcGdiag (E := E) i) (CPT 0)
    (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
      ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))
    (fr ^ 2 * KtopS * appCcGdiag (E := E) i) (fr ^ 2 * KcS i * W) (Cfield i * W) i
    (fun i' => riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + i') x
      ((iteratedCovGrad (I := I) g₀ 6 2 i' (pairTraceOpDla (I := I) (M := M) g₀ g₁)).toSection x))
    (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
      ((iteratedCovGrad (I := I) g₀ 2 6 l
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x))
    happ_nn (hCPT_nn 0)
    (fun i' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 6 (2 + i') x _)
    (fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + l) x _)
    hPT0 hWi
    (le_trans (appCcGrid_le_dla b hb i
      (fun i' => riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + i') x
        ((iteratedCovGrad (I := I) g₀ 6 2 i' (pairTraceOpDla (I := I) (M := M) g₀ g₁)).toSection x))
      CPT
      (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 6 l
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x))
      (fun l => fr * (fr * CX l))
      (fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + l) x _)
      hCPT_nn (fun l => mul_nonneg hfr_nn (mul_nonneg hfr_nn (hCX_nn l)))
      (fun i' _ => hCPT g₁ T htie hδ_le hδ0 hbound i' x)
      (fun l _ => le_trans (hXfr l)
        (by
          have := hCX g₁ T htie hδ_le hδ0 hbound l x
          calc fr ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 4 l
                  (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x)
              ≤ fr ^ 2 * (CX l * dLaGridWin b (l + 3)) :=
                mul_le_mul_of_nonneg_left this (by positivity)
            _ = (fr * (fr * CX l)) * dLaGridWin b (l + 3) := by ring)))
      (le_of_eq (by rw [hCfield_def, hW_def])))) ?_
  exact le_of_eq (by ring)

/-! ### Summation helpers (copied verbatim from `DLaTopSeparated`). -/

private lemma sum_shift_le (g : ℕ → ℝ) (hg : ∀ j, 0 ≤ g j) (m c : ℕ) :
    ∑ i ∈ Finset.range m, g (i + c) ≤ ∑ j ∈ Finset.range (m + c), g j := by
  classical
  have hsub :
      (Finset.range m).map ⟨fun i => i + c, fun a b h => by simpa using h⟩ ⊆
        Finset.range (m + c) := by
    intro j hj
    rw [Finset.mem_map] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    rw [Finset.mem_range] at hi ⊢
    simp only [Function.Embedding.coeFn_mk]
    omega
  calc ∑ i ∈ Finset.range m, g (i + c)
      = ∑ j ∈ (Finset.range m).map ⟨fun i => i + c, fun a b h => by simpa using h⟩, g j := by
        rw [Finset.sum_map]; rfl
    _ ≤ ∑ j ∈ Finset.range (m + c), g j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hg j)

private lemma jetL2_sum_lowShift
    (a p q : ℕ) (Ktop : ℝ) (hKtop : 0 ≤ Ktop) (Kc : ℕ → ℝ) (hKc : ∀ i, 0 ≤ Kc i)
    (f w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hper : ∀ i, i ≤ a →
        f i ≤ Ktop * w (i + p) + Kc i * (1 + ∑ j ∈ Finset.range (i + q), w j)) :
    ∑ i ∈ Finset.range (a + 1), f i ≤
      Ktop * (∑ j ∈ Finset.range (a + 1 + p), w j) +
      (∑ i ∈ Finset.range (a + 1), Kc i) * (1 + ∑ j ∈ Finset.range (a + q), w j) := by
  refine le_trans (Finset.sum_le_sum (fun i hi =>
    hper i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))) ?_
  rw [Finset.sum_add_distrib]
  have hB : (∑ i ∈ Finset.range (a + 1), Ktop * w (i + p)) ≤
      Ktop * ∑ j ∈ Finset.range (a + 1 + p), w j := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_shift_le w hw (a + 1) p) hKtop
  have hA : (∑ i ∈ Finset.range (a + 1), Kc i * (1 + ∑ j ∈ Finset.range (i + q), w j)) ≤
      (∑ i ∈ Finset.range (a + 1), Kc i) * (1 + ∑ j ∈ Finset.range (a + q), w j) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hi' : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    refine mul_le_mul_of_nonneg_left ?_ (hKc i)
    have hsub : Finset.range (i + q) ⊆ Finset.range (a + q) := by
      intro y hy; rw [Finset.mem_range] at hy ⊢; omega
    have hss : ∑ j ∈ Finset.range (i + q), w j ≤ ∑ j ∈ Finset.range (a + q), w j :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hw j)
    linarith
  linarith [hA, hB]


set_option linter.unusedVariables false in
set_option maxHeartbeats 3200000 in
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (Icc_subset_realizedSmallSet) in
/-- **`realizedFam` per-order top-separated jet-L2 bound** for the DLa coefficient field.  Fixes
the single top constant `Ktop = Ktop_field·(appCcGdiag a)²` (`R`-free) by
`appCcGdiag i ≤ appCcGdiag a`; the remainder uses the ball-uniform tame-window integrator. -/
theorem deTurckLieDLaCoeffField_realizedFam_jetL2_perOrder_topSeparated
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieDLaCoeffField (I := I) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤
            Ktop * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) +
            Kc i * (1 + ∑ j ∈ Finset.range (i + 3),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  classical
  set δ₁ : ℝ := max δ₀ 0 with hδ₁_def
  have hδ₁_nn : 0 ≤ δ₁ := le_max_right _ _
  have hδ₁_lt : δ₁ < 1 := max_lt hδ₀ one_pos
  obtain ⟨Ktop_field, hKtop_field_nn, Kc_field, hKc_field_nn, hfield⟩ :=
    rfns_iCG_dLaField_topsep (I := I) (M := M) g₀ g_bg hδ₁_lt
  obtain ⟨K, hK_nn, hK⟩ :=
    antidiagonalTupleGrid_integral_ballUniform_tameWindow (I := I) (M := M) g₀ a ha_super hR
  refine ⟨Ktop_field * appCcGdiag (E := E) a * appCcGdiag (E := E) a,
      mul_nonneg (mul_nonneg hKtop_field_nn (appCcGdiag_nonneg (E := E) a))
        (appCcGdiag_nonneg (E := E) a),
    fun i => Kc_field i * ∑ k ∈ Finset.range (i + 3), K k,
    fun i => mul_nonneg (hKc_field_nn i) (Finset.sum_nonneg fun k _ => hK_nn k), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs i hi
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  set g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hg₁_def
  set Pc : SmoothCcTensor g₀ 0 2 := convexPerturbation (I := I) g₀ T T' s with hPc_def
  have hδs_raw : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ Pc)
      (|1 - s| * δ' + |s| * δ) := by
    rw [hPc_def]; exact convexPerturbation_gFibreOpBound_abs (I := I) g₀ T T' hδ hδ' s
  set δP : ℝ := max (|1 - s| * δ' + |s| * δ) 0 with hδP_def
  have hδP_nn : 0 ≤ δP := le_max_right _ _
  have hδP_bound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ Pc) δP :=
    gFibreOpBound_mono_of_le (I := I) (M := M) g₀ _ (le_max_left _ _) hδs_raw
  have hδP_le : δP ≤ δ₁ := by
    refine max_le ?_ hδ₁_nn
    rw [abs_of_nonneg h1ms, abs_of_nonneg hs0]
    have h1 : δ' ≤ δ₁ := le_trans hδ'_le (le_max_left _ _)
    have h2 : δ ≤ δ₁ := le_trans hδ_le (le_max_left _ _)
    nlinarith [h1, h2]
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ Pc y v w := by
    intro y v w
    rw [hg₁_def, hPc_def]
    exact realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ'
      (Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs) y v w
  have hPball : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j Pc‖ ≤ R := by
    intro j hj
    have heq : iteratedCovGrad (I := I) g₀ 0 2 j Pc
        = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
          + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
      rw [hPc_def, show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
        iteratedCovGrad_add, iteratedCovGrad_smul_dla, iteratedCovGrad_smul_dla]
    rw [heq]
    calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
            + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
        ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
      _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg h1ms, abs_of_nonneg hs0]
      _ ≤ (1 - s) * R + s * R :=
          add_le_add (mul_le_mul_of_nonneg_left (hT'ball j hj) h1ms)
            (mul_le_mul_of_nonneg_left (hTball j hj) hs0)
      _ = R := by ring
  have hwin : ∀ j : ℕ,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j Pc‖ ^ 2 ≤
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2 := by
    intro j
    have heq : iteratedCovGrad (I := I) g₀ 0 2 j Pc
        = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
          + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
      rw [hPc_def, show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
        iteratedCovGrad_add, iteratedCovGrad_smul_dla, iteratedCovGrad_smul_dla]
    have hy_nn : 0 ≤ (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
        + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ :=
      add_nonneg (mul_nonneg h1ms (norm_nonneg _)) (mul_nonneg hs0 (norm_nonneg _))
    have hnorm_le : ‖iteratedCovGrad (I := I) g₀ 0 2 j Pc‖ ≤
        (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
          + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
      rw [heq]
      calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
              + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
          ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
              + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
        _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
              + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg h1ms, abs_of_nonneg hs0]
    nlinarith [mul_le_mul hnorm_le hnorm_le (norm_nonneg
        (iteratedCovGrad (I := I) g₀ 0 2 j Pc)) hy_nn,
      mul_nonneg (mul_nonneg hs0 h1ms)
        (sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ -
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖)),
      mul_nonneg h1ms (sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖),
      mul_nonneg hs0 (sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖)]
  -- pointwise field top-sep bound (with the grid remainder in explicit `∑∑∑∏` form).
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieDLaCoeffField (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
        (Ktop_field * appCcGdiag (E := E) i * appCcGdiag (E := E) i *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) Pc).toSection x)) +
          Kc_field i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) Pc).toSection x) := by
    intro x
    refine (hfield g₁ Pc htie hδP_le hδP_nn hδP_bound i x).trans_eq ?_
    have hgw : dLaGridWin (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l Pc).toSection x)) (i + 3) =
        ∑ k ∈ Finset.range (i + 3), ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) Pc).toSection x) := by
      rw [dLaGridWin]; rfl
    rw [hgw]
  have hint_k : ∀ k ∈ Finset.range (i + 3), MeasureTheory.Integrable
      (fun x => ∑ n ∈ Finset.range (k + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
          ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) Pc).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    fun k _ => (hK Pc hPball k).1
  have hutop_int : MeasureTheory.Integrable
      (fun x => Ktop_field * appCcGdiag (E := E) i * appCcGdiag (E := E) i *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) Pc).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + (i + 2))
      (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) Pc)).const_mul _
  have hvrem_int : MeasureTheory.Integrable
      (fun x => Kc_field i * ∑ k ∈ Finset.range (i + 3),
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) Pc).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (MeasureTheory.integrable_finset_sum (Finset.range (i + 3)) hint_k).const_mul _
  have hnorm := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
    (iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieDLaCoeffField (I := I) (M := M) g₀ g₁ g_bg))
    (fun x => (Ktop_field * appCcGdiag (E := E) i * appCcGdiag (E := E) i *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) Pc).toSection x)) +
      Kc_field i * ∑ k ∈ Finset.range (i + 3),
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) Pc).toSection x))
    (hutop_int.add hvrem_int) hpt
  refine le_trans hnorm ?_
  rw [MeasureTheory.integral_add hutop_int hvrem_int]
  -- top integral
  have htop_eval : (∫ x, Ktop_field * appCcGdiag (E := E) i * appCcGdiag (E := E) i *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) Pc).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
      Ktop_field * appCcGdiag (E := E) i * appCcGdiag (E := E) i *
        ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) Pc‖ ^ 2 := by
    rw [MeasureTheory.integral_const_mul,
      SmoothCcTensor.norm_def (I := I) (M := M) (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) Pc),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 0
        (2 + (i + 2)) (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) Pc)]
  rw [htop_eval]
  -- remainder integral
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_finset_sum (Finset.range (i + 3)) hint_k]
  -- top: bound `appCcGdiag i·appCcGdiag i ≤ appCcGdiag a·appCcGdiag a` and `Pc → (T,T')`.
  have happ_mono : appCcGdiag (E := E) i ≤ appCcGdiag (E := E) a := by
    rw [appCcGdiag, appCcGdiag]
    exact pow_le_pow_right₀ (by
      have : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
      linarith) hi
  have happ_nn : 0 ≤ appCcGdiag (E := E) i := appCcGdiag_nonneg (E := E) i
  have happa_nn : 0 ≤ appCcGdiag (E := E) a := appCcGdiag_nonneg (E := E) a
  have htop_le : Ktop_field * appCcGdiag (E := E) i * appCcGdiag (E := E) i *
        ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) Pc‖ ^ 2 ≤
      (Ktop_field * appCcGdiag (E := E) a * appCcGdiag (E := E) a) *
        (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) := by
    have hc_le : Ktop_field * appCcGdiag (E := E) i * appCcGdiag (E := E) i ≤
        Ktop_field * appCcGdiag (E := E) a * appCcGdiag (E := E) a := by
      have h1 : Ktop_field * appCcGdiag (E := E) i ≤ Ktop_field * appCcGdiag (E := E) a :=
        mul_le_mul_of_nonneg_left happ_mono hKtop_field_nn
      have h2 : 0 ≤ Ktop_field * appCcGdiag (E := E) i :=
        mul_nonneg hKtop_field_nn happ_nn
      calc Ktop_field * appCcGdiag (E := E) i * appCcGdiag (E := E) i
          ≤ Ktop_field * appCcGdiag (E := E) a * appCcGdiag (E := E) i :=
            mul_le_mul_of_nonneg_right h1 happ_nn
        _ ≤ Ktop_field * appCcGdiag (E := E) a * appCcGdiag (E := E) a :=
            mul_le_mul_of_nonneg_left happ_mono (mul_nonneg hKtop_field_nn happa_nn)
    have hc_nn : 0 ≤ Ktop_field * appCcGdiag (E := E) a * appCcGdiag (E := E) a :=
      mul_nonneg (mul_nonneg hKtop_field_nn happa_nn) happa_nn
    calc Ktop_field * appCcGdiag (E := E) i * appCcGdiag (E := E) i *
          ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) Pc‖ ^ 2
        ≤ (Ktop_field * appCcGdiag (E := E) a * appCcGdiag (E := E) a) *
            ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) Pc‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hc_le (sq_nonneg _)
      _ ≤ (Ktop_field * appCcGdiag (E := E) a * appCcGdiag (E := E) a) *
            (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hwin (i + 2)) hc_nn
  -- remainder: bound each `∫ grid_k ≤ K k·(1+∑_{j<k+1}‖∇^jPc‖²)`, then Pc→(T,T').
  have hrem_le : Kc_field i * ∑ k ∈ Finset.range (i + 3),
        (∫ x, ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) Pc).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
      (Kc_field i * ∑ k ∈ Finset.range (i + 3), K k) *
        (1 + ∑ j ∈ Finset.range (i + 3),
          (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
    have hstep : (∑ k ∈ Finset.range (i + 3),
          (∫ x, ∑ n ∈ Finset.range (k + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) Pc).toSection x)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))) ≤
        (∑ k ∈ Finset.range (i + 3), K k) *
          (1 + ∑ j ∈ Finset.range (i + 3),
            (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun k hk => ?_
      rw [Finset.mem_range] at hk
      refine le_trans (hK Pc hPball k).2 ?_
      refine mul_le_mul_of_nonneg_left ?_ (hK_nn k)
      have hjwin : (∑ j ∈ Finset.range (k + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j Pc‖ ^ 2) ≤
          ∑ j ∈ Finset.range (i + 3),
            (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) := by
        calc (∑ j ∈ Finset.range (k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j Pc‖ ^ 2)
            ≤ ∑ j ∈ Finset.range (k + 1),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
              Finset.sum_le_sum fun j _ => hwin j
          _ ≤ ∑ j ∈ Finset.range (i + 3),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (by intro y hy; rw [Finset.mem_range] at hy ⊢; omega)
                (fun j _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
      linarith
    calc Kc_field i * ∑ k ∈ Finset.range (i + 3), (∫ x, _ ∂_)
        ≤ Kc_field i * ((∑ k ∈ Finset.range (i + 3), K k) *
            (1 + ∑ j ∈ Finset.range (i + 3),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left hstep (hKc_field_nn i)
      _ = (Kc_field i * ∑ k ∈ Finset.range (i + 3), K k) *
            (1 + ∑ j ∈ Finset.range (i + 3),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by ring
  linarith [htop_le, hrem_le]

set_option linter.unusedVariables false in
/-- **Summed** `realizedFam` top-separated jet-L2 bound for the DLa coefficient field.  Top window
`a+3` (matching the deTurckLie window), `Ktop` `R`-free, `Kc = ∑_{i≤a} Kc_perOrder i`. -/
theorem deTurckLieDLaCoeffField_realizedFam_jetL2_summed_topSeparated
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℝ, 0 ≤ Kc ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ∑ i ∈ Finset.range (a + 1),
              ‖iteratedCovGrad (I := I) g₀ 2 2 i
                (deTurckLieDLaCoeffField (I := I) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤
            Ktop * (∑ j ∈ Finset.range (a + 3),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) +
            Kc * (1 + ∑ j ∈ Finset.range (a + 3),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  obtain ⟨Ktop, hKtop_nn, Kc, hKc_nn, hper⟩ :=
    deTurckLieDLaCoeffField_realizedFam_jetL2_perOrder_topSeparated
      (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  refine ⟨Ktop, hKtop_nn, ∑ i ∈ Finset.range (a + 1), Kc i,
    Finset.sum_nonneg (fun i _ => hKc_nn i), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs
  exact jetL2_sum_lowShift a 2 3 Ktop hKtop_nn Kc hKc_nn
    (fun i => ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (deTurckLieDLaCoeffField (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2)
    (fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)
    (fun j => add_nonneg (sq_nonneg _) (sq_nonneg _))
    (fun i hi => hper T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs i hi)

end DLaGridBrick

end DifferentialGeometry.Integral.Connection

end

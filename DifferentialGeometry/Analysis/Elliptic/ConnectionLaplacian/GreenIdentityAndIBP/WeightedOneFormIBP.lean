import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OneFormRealization
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradCrossBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.EigenvectorChartCrossRightLimit
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorConnLapGreenIntertwiner
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.CovariantIntegrationByParts
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorConnLapLoweredIBP
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Integrability
import DifferentialGeometry.Analysis.Integration.L2.Basic
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorLoweringParallel
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.RankZeroInner
import DifferentialGeometry.Geometry.Hodge.Codifferential
import DifferentialGeometry.Geometry.Curvature.Metric
import DifferentialGeometry.Geometry.Operator.RoughLaplacian
import DifferentialGeometry.Tensor.RicciIdentity.OneForm
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetric
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SInnerLeibniz
import DifferentialGeometry.Tensor.RSTensor.Coordinates.Field
import DifferentialGeometry.Tensor.RSTensor.Defs

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

noncomputable section

namespace DifferentialGeometry
namespace Integral
namespace Connection

open MeasureTheory
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Riemannian.Forms
open DifferentialGeometry.Analysis.Parabolic
open Bundle Tensor0SBundle
open Tensor0SNabla
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators Matrix

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [I.Boundaryless] [BoundarylessManifold I M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem oneForm_weighted_roughLap_ibp
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → Real} (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (alpha : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (nabla2Alpha : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hRealizes : ∀ x : M,
      Nabla2OneFormRealizesAt (I := I) (metricCov (I := I) (M := M) g)
        alpha nablaAlpha x (nabla2Alpha x)) :
    (2 : Real) * (∫ x, f x * inner0S (I := I) g x 1 (alpha x)
            (roughLap0STensor (I := I) g (s := 1) (nabla2Alpha x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      + (∫ x, formLaplacianScalar (I := I) g hf x * normSq0S (I := I) g x 1 (alpha x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      = -2 * ∫ x, f x * normSq0S (I := I) g x 2 (nablaAlpha x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set W : SmoothCcTensor g 0 1 :=
    { toSection := alpha.toTensorRSField (∞ : WithTop ℕ∞)
      hasCompactSupport := HasCompactSupport.of_compactSpace _ } with hW_def
  have hW : ∀ y : M, W.toSection y = Tensor0SSpace.toRS0 (alpha y) := fun y =>
    Tensor0SField.toRS0_eq (I := I) (M := M) (∞ : WithTop ℕ∞) alpha y
  set ζ : C^∞⟮I, M; ℝ⟯ := ⟨f, hf⟩ with hζ_def
  set GW : SmoothCcTensor g 0 (1 + 1) := TensorSpectral.covGrad (I := I) (M := M) g 0 1 W
    with hGW_def
  set LW : SmoothCcTensor g 0 1 := rawTensorConnLapSmooth (I := I) g 0 1 W with hLW_def
  set KW : SmoothCcTensor g 0 1 := TensorSpectral.scalarSmul (I := I) (M := M) g 0 1 ζ W
    with hKW_def
  set SGW : SmoothCcTensor g 0 (1 + 1) :=
    TensorSpectral.scalarSmul (I := I) (M := M) g 0 (1 + 1) ζ GW with hSGW_def
  set PP : SmoothCcTensor g 0 (1 + 1) :=
    TensorSpectral.prependCovGradSlot (I := I) (M := M) g 0 1 ζ W with hPP_def
  have hbridge := fun x : M =>
    DifferentialGeometry.Analysis.Spectral.OneFormRealization.wrapped_covGrad_rawConnLap_realizes
      (I := I) (M := M) g alpha nablaAlpha nabla2Alpha W hW x (hRealizes x)
  have hB1 : ∀ x : M, GW.toFun x =
      TensorRSSpace.toModel (Tensor0SSpace.toRS0 (nablaAlpha x)) :=
    fun x => (hbridge x).1
  have hB2 : ∀ x : M, LW.toFun x =
      TensorRSSpace.toModel
        (Tensor0SSpace.toRS0
          (roughLap0STensor (I := I) g (s := 1) (nabla2Alpha x))) :=
    fun x => (hbridge x).2
  have hKWs : ∀ x : M, TensorRSSpace.toModel (KW.toSection x)
      = f x • TensorRSSpace.toModel (Tensor0SSpace.toRS0 (alpha x)) := by
    intro x
    rw [hKW_def, TensorSpectral.scalarSmul_toSection_apply, TensorRSSpace.toModel_smul, hW x]
    rfl
  have hSGWs : ∀ x : M, TensorRSSpace.toModel (SGW.toSection x) = f x • GW.toFun x := by
    intro x
    rw [hSGW_def, TensorSpectral.scalarSmul_toSection_apply, TensorRSSpace.toModel_smul]
    rfl
  have hcovKW : ∀ x : M, (TensorSpectral.covGrad (I := I) (M := M) g 0 1 KW).toFun x
      = SGW.toFun x + PP.toFun x := by
    intro x
    have h0 := TensorSpectral.prependCovGradSlot_toSection (I := I) (M := M) g 0 1 ζ W
    have h1 : PP.toSection x
        = (TensorSpectral.covGrad (I := I) (M := M) g 0 1 KW).toSection x
          - SGW.toSection x := by
      rw [hPP_def]
      rw [show (TensorSpectral.prependCovGradSlot (I := I) (M := M) g 0 1 ζ W).toSection
          = (TensorSpectral.covGrad (I := I) (M := M) g 0 1
              (TensorSpectral.scalarSmul (I := I) (M := M) g 0 1 ζ W)).toSection
            - (TensorSpectral.scalarSmul (I := I) (M := M) g 0 (1 + 1) ζ
              (TensorSpectral.covGrad (I := I) (M := M) g 0 1 W)).toSection from h0]
      rfl
    have h2 : (TensorSpectral.covGrad (I := I) (M := M) g 0 1 KW).toSection x
        = SGW.toSection x + PP.toSection x := by
      rw [h1]
      abel
    rw [SmoothCcTensor.toFun_apply, SmoothCcTensor.toFun_apply, SmoothCcTensor.toFun_apply,
      h2, TensorRSSpace.toModel_add]
  have hf1 : ∀ x : M, tensorInnerPointwise (I := I) (M := M) g 0 (1 + 1) x
        (GW.toFun x) (SGW.toFun x)
      = f x * normSq0S (I := I) g x 2 (nablaAlpha x) := by
    intro x
    rw [show SGW.toFun x = TensorRSSpace.toModel (SGW.toSection x) from rfl, hSGWs x,
      tensorInnerPointwise_smul_right]
    congr 1
    rw [hB1 x, ← normSq0S_eq_tensorInnerPointwise_toRS0]
  have hf3 : ∀ x : M, tensorInnerPointwise (I := I) (M := M) g 0 1 x
        (LW.toFun x) (KW.toFun x)
      = f x * inner0S (I := I) g x 1
          (roughLap0STensor (I := I) g (s := 1) (nabla2Alpha x)) (alpha x) := by
    intro x
    rw [show KW.toFun x = TensorRSSpace.toModel (KW.toSection x) from rfl, hKWs x,
      tensorInnerPointwise_smul_right]
    congr 1
    rw [hB2 x, inner_toRS0, ← inner0S_eq_covariantTensorInnerPointwise]
  have hcross1 : ∀ x : M,
      tensorInnerPointwise (I := I) (M := M) g 0 (1 + 1) x (GW.toFun x) (PP.toFun x)
        = TensorSpectral.tensorCovDerivCrossLeft (I := I) (M := M) g 0 1 ζ W W x :=
    fun x => (TensorSpectral.tensorCovDerivCrossLeft_eq_tensorInnerPointwise_grad
      (I := I) (M := M) g 0 1 ζ W W x).symm
  have hcross2 : ∀ x : M,
      TensorSpectral.tensorCovDerivCrossLeft (I := I) (M := M) g 0 1 ζ W W x
        = tensorInnerPointwise (I := I) (M := M) g 0 1 x (W.toFun x)
            ((TensorSpectral.covDerivAlongGrad (I := I) (M := M) g 0 1 W ζ).toFun x) := by
    intro x
    rw [← TensorSpectral.tensorCovDerivCrossRight_eq_crossLeft (I := I) (M := M) g 0 1 ζ W W x]
    exact TensorSpectral.tensorCovDerivCrossRight_eq_tensorInnerPointwise_grad
      (I := I) (M := M) g 0 1 ζ W W x
  have hlift2 : ∀ x : M,
      Tensor0SSpace.toModel
          (liftedTensorSection (I := I) (M := M) g 0 1
            (TensorSpectral.covDerivAlongGrad (I := I) (M := M) g 0 1 W ζ).toSection x)
        = Tensor0SSpace.toModel
            (loweredCovDerivAt (I := I) (M := M) g 0 1 W.toSection x
              ((grad_g (I := I) g hf) x)) := by
    intro x
    rw [toModel_liftedTensorSection]
    rw [loweredCovDerivAt_eq_lower_tensorCovDerivAt_rs (I := I) (M := M) g 0 1
      W.toSection x ((grad_g (I := I) g hf) x)]
    congr 1
  have hBval : ∀ x : M,
      tensorInnerPointwise (I := I) (M := M) g 0 (1 + 1) x (GW.toFun x) (PP.toFun x)
        = covariantTensorInnerPointwise (I := I) (M := M) (0 + 1) g x
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g 0 1 W.toSection x))
            (Tensor0SSpace.toModel
              (loweredCovDerivAt (I := I) (M := M) g 0 1 W.toSection x
                ((grad_g (I := I) g hf) x))) := by
    intro x
    rw [hcross1 x, hcross2 x]
    rw [show tensorInnerPointwise (I := I) (M := M) g 0 1 x (W.toFun x)
          ((TensorSpectral.covDerivAlongGrad (I := I) (M := M) g 0 1 W ζ).toFun x)
        = tensorInnerPointwise (I := I) (M := M) g 0 1 x
            (TensorRSSpace.toModel (W.toSection x))
            (TensorRSSpace.toModel
              ((TensorSpectral.covDerivAlongGrad (I := I) (M := M) g 0 1 W ζ).toSection x))
        from rfl]
    rw [tensorInnerPointwise_eq_liftedTensorSection_inner (I := I) (M := M) g 0 1
      W.toSection (TensorSpectral.covDerivAlongGrad (I := I) (M := M) g 0 1 W ζ).toSection x]
    rw [hlift2 x]
  have hAeqB : ∀ x : M,
      covariantTensorInnerPointwise (I := I) (M := M) (0 + 1) g x
          (Tensor0SSpace.toModel
            (loweredCovDerivAt (I := I) (M := M) g 0 1 W.toSection x
              ((grad_g (I := I) g hf) x)))
          (Tensor0SSpace.toModel
            (liftedTensorSection (I := I) (M := M) g 0 1 W.toSection x))
        = covariantTensorInnerPointwise (I := I) (M := M) (0 + 1) g x
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g 0 1 W.toSection x))
            (Tensor0SSpace.toModel
              (loweredCovDerivAt (I := I) (M := M) g 0 1 W.toSection x
                ((grad_g (I := I) g hf) x))) :=
    fun x => tensorInnerPointwise_0s_symm (I := I) (M := M) g x (0 + 1) _ _
  have int_cross : Integrable (fun x : M =>
      tensorInnerPointwise (I := I) (M := M) g 0 (1 + 1) x (GW.toFun x) (PP.toFun x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    SmoothCcTensor.integrable_inner_cross (I := I) (M := M) GW PP
  have int_B : Integrable (fun x : M =>
      covariantTensorInnerPointwise (I := I) (M := M) (0 + 1) g x
        (Tensor0SSpace.toModel
          (liftedTensorSection (I := I) (M := M) g 0 1 W.toSection x))
        (Tensor0SSpace.toModel
          (loweredCovDerivAt (I := I) (M := M) g 0 1 W.toSection x
            ((grad_g (I := I) g hf) x))))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    int_cross.congr (Filter.Eventually.of_forall hBval)
  have int_A : Integrable (fun x : M =>
      covariantTensorInnerPointwise (I := I) (M := M) (0 + 1) g x
        (Tensor0SSpace.toModel
          (loweredCovDerivAt (I := I) (M := M) g 0 1 W.toSection x
            ((grad_g (I := I) g hf) x)))
        (Tensor0SSpace.toModel
          (liftedTensorSection (I := I) (M := M) g 0 1 W.toSection x)))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    int_B.congr (Filter.Eventually.of_forall (fun x => (hAeqB x).symm))
  have hWS := tensorInnerScalar_contMDiff (I := I) (M := M) g 0 1 W.toSection W.toSection
  have hIBP := integral_tensorInner_covDeriv_integrationByParts (I := I) (M := M) g 0 1
    W.toSection W.toSection (grad_g (I := I) g hf) hWS int_A int_B
  have hnsq : ∀ x : M,
      tensorInnerScalar (I := I) (M := M) g 0 1 W.toSection W.toSection x
        = normSq0S (I := I) g x 1 (alpha x) := by
    intro x
    rw [tensorInnerScalar_apply]
    rw [show TensorRSSpace.toModel (W.toSection x)
        = TensorRSSpace.toModel (Tensor0SSpace.toRS0 (alpha x)) from
      congrArg TensorRSSpace.toModel (hW x)]
    rw [← normSq0S_eq_tensorInnerPointwise_toRS0]
  have hdivV : ∀ x : M,
      divergence_g (I := I) g (grad_g (I := I) g hf) x
        = - formLaplacianScalar (I := I) g hf x := by
    intro x
    rw [show formLaplacianScalar (I := I) g hf x
        = - divergence_g (I := I) g (grad_g (I := I) g hf) x from rfl]
    ring
  have hdivint : (∫ x, tensorInnerScalar (I := I) (M := M) g 0 1 W.toSection W.toSection x
        * divergence_g (I := I) g (grad_g (I := I) g hf) x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      = - ∫ x, formLaplacianScalar (I := I) g hf x * normSq0S (I := I) g x 1 (alpha x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [← MeasureTheory.integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    beta_reduce
    rw [hnsq x, hdivV x]
    ring
  have hABint : (∫ x, covariantTensorInnerPointwise (I := I) (M := M) (0 + 1) g x
          (Tensor0SSpace.toModel
            (loweredCovDerivAt (I := I) (M := M) g 0 1 W.toSection x
              ((grad_g (I := I) g hf) x)))
          (Tensor0SSpace.toModel
            (liftedTensorSection (I := I) (M := M) g 0 1 W.toSection x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      = ∫ x, covariantTensorInnerPointwise (I := I) (M := M) (0 + 1) g x
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g 0 1 W.toSection x))
            (Tensor0SSpace.toModel
              (loweredCovDerivAt (I := I) (M := M) g 0 1 W.toSection x
                ((grad_g (I := I) g hf) x)))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall hAeqB)
  have hHalf : (2 : Real) * (∫ x, covariantTensorInnerPointwise (I := I) (M := M) (0 + 1) g x
          (Tensor0SSpace.toModel
            (liftedTensorSection (I := I) (M := M) g 0 1 W.toSection x))
          (Tensor0SSpace.toModel
            (loweredCovDerivAt (I := I) (M := M) g 0 1 W.toSection x
              ((grad_g (I := I) g hf) x)))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      = ∫ x, formLaplacianScalar (I := I) g hf x * normSq0S (I := I) g x 1 (alpha x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [hdivint, hABint] at hIBP
    linarith [hIBP]
  have int_f1 : Integrable (fun x : M => tensorInnerPointwise (I := I) (M := M) g 0 (1 + 1) x
      (GW.toFun x) (SGW.toFun x)) (riemannianVolumeMeasure (I := I) (M := M) g) :=
    SmoothCcTensor.integrable_inner_cross (I := I) (M := M) GW SGW
  have hI1 : (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 (1 + 1) x
        (GW.toFun x) (SGW.toFun x) ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      + (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 (1 + 1) x
        (GW.toFun x) (PP.toFun x) ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      = - ∫ x, tensorInnerPointwise (I := I) (M := M) g 0 1 x
          (LW.toFun x) (KW.toFun x) ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hGreen := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_gen
      (I := I) (M := M) g 1 W KW
    have hLHS : tensorL2Inner (I := I) (M := M) g 0 (1 + 1)
        (TensorSpectral.covGrad (I := I) (M := M) g 0 1 W).toFun
        (TensorSpectral.covGrad (I := I) (M := M) g 0 1 KW).toFun
        = (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 (1 + 1) x
            (GW.toFun x) (SGW.toFun x) ∂(riemannianVolumeMeasure (I := I) (M := M) g))
          + (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 (1 + 1) x
            (GW.toFun x) (PP.toFun x) ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
      change (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 (1 + 1) x
          ((TensorSpectral.covGrad (I := I) (M := M) g 0 1 W).toFun x)
          ((TensorSpectral.covGrad (I := I) (M := M) g 0 1 KW).toFun x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = _
      rw [integral_congr_ae (Filter.Eventually.of_forall (fun x => by
        rw [show (TensorSpectral.covGrad (I := I) (M := M) g 0 1 W).toFun x
            = GW.toFun x from rfl, hcovKW x, tensorInnerPointwise_add_right]))]
      exact MeasureTheory.integral_add int_f1 int_cross
    have hRHS : tensorL2Inner (I := I) (M := M) g 0 1
        (rawTensorConnLapSmooth (I := I) g 0 1 W).toFun KW.toFun
        = ∫ x, tensorInnerPointwise (I := I) (M := M) g 0 1 x
            (LW.toFun x) (KW.toFun x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := rfl
    rw [← hLHS, ← hRHS]
    exact hGreen
  have hflip : (∫ x, f x * inner0S (I := I) g x 1
        (roughLap0STensor (I := I) g (s := 1) (nabla2Alpha x)) (alpha x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      = ∫ x, f x * inner0S (I := I) g x 1 (alpha x)
          (roughLap0STensor (I := I) g (s := 1) (nabla2Alpha x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    beta_reduce
    rw [Tensor0SBundle.inner0S_symm (I := I) g x
      (roughLap0STensor (I := I) g (s := 1) (nabla2Alpha x)) (alpha x)]
  have e1 := integral_congr_ae (μ := riemannianVolumeMeasure (I := I) (M := M) g)
    (Filter.Eventually.of_forall hf1)
  have e2 := integral_congr_ae (μ := riemannianVolumeMeasure (I := I) (M := M) g)
    (Filter.Eventually.of_forall hBval)
  have e3 := integral_congr_ae (μ := riemannianVolumeMeasure (I := I) (M := M) g)
    (Filter.Eventually.of_forall hf3)
  linarith [hI1, e1, e2, e3, hHalf, hflip]

end Connection
end Integral
end DifferentialGeometry

end

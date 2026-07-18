import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OneFormRealization
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorConnLapGreenIntertwiner
import DifferentialGeometry.Analysis.Integration.L2.Pairing.Defs
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.RankZeroInner
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetric
import DifferentialGeometry.Geometry.Operator.RoughLaplacian
import DifferentialGeometry.Tensor.RicciIdentity.OneForm
import DifferentialGeometry.Geometry.Curvature.Metric
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs
import DifferentialGeometry.Tensor.RSTensor.Coordinates.Field
import DifferentialGeometry.Tensor.RSTensor.Defs

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

namespace DifferentialGeometry
namespace Integral
namespace Connection

open MeasureTheory
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
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

theorem oneForm_gradNormSq_integral_eq_neg_eigen
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (κ : Real)
    (alpha : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (nabla2Alpha : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hRealizes : ∀ x : M,
      Nabla2OneFormRealizesAt (I := I) (metricCov g) alpha nablaAlpha x (nabla2Alpha x))
    (hEigen : ∀ (x : M) (X : TangentSpace I x),
      roughLap0STensor (I := I) g (s := 1) (nabla2Alpha x) (fun _ : Fin 1 => X)
        = κ * alpha x (fun _ : Fin 1 => X)) :
    ∫ x, normSq0S (I := I) g x 2 (nablaAlpha x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      = -κ * ∫ x, normSq0S (I := I) g x 1 (alpha x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set ν := riemannianVolumeMeasure (I := I) (M := M) g with hν_def
  set W : SmoothCcTensor g 0 1 :=
    { toSection := alpha.toTensorRSField
      hasCompactSupport := HasCompactSupport.of_compactSpace _ } with hW_def
  have hW : ∀ y : M, W.toSection y = Tensor0SSpace.toRS0 (alpha y) := by
    intro y
    rw [hW_def]
    exact Tensor0SField.toRS0_eq (I := I) (M := M) ∞ alpha y
  have hbridge := fun x : M =>
    DifferentialGeometry.Analysis.Spectral.OneFormRealization.wrapped_covGrad_rawConnLap_realizes
      (I := I) (M := M) g alpha nablaAlpha nabla2Alpha W hW x (hRealizes x)
  have hB1 : ∀ x : M,
      (TensorSpectral.covGrad (I := I) (M := M) g 0 1 W).toFun x =
        TensorRSSpace.toModel (Tensor0SSpace.toRS0 (nablaAlpha x)) :=
    fun x => (hbridge x).1
  have hB2 : ∀ x : M,
      (rawTensorConnLapSmooth (I := I) g 0 1 W).toFun x =
        TensorRSSpace.toModel
          (Tensor0SSpace.toRS0
            (roughLap0STensor (I := I) g (s := 1) (nabla2Alpha x))) :=
    fun x => (hbridge x).2
  have hEigenTensor : ∀ x : M,
      roughLap0STensor (I := I) g (s := 1) (nabla2Alpha x) = κ • alpha x := by
    intro x
    refine tensor0SSpace_ext 1 x (fun v => ?_)
    have hval : roughLap0STensor (I := I) g (s := 1) (nabla2Alpha x) v
        = κ * alpha x v := by
      have hkey := hEigen x (v 0)
      have h0 : (fun _ : Fin 1 => v 0) = v := by funext i; fin_cases i; rfl
      rw [h0] at hkey
      exact hkey
    rw [Tensor0SSpace.smul_apply, smul_eq_mul]
    exact hval
  have hEigenInner : ∀ x : M,
      inner0S (I := I) g x 1
          (roughLap0STensor (I := I) g (s := 1) (nabla2Alpha x)) (alpha x)
        = κ * normSq0S (I := I) g x 1 (alpha x) := by
    intro x
    rw [hEigenTensor x, inner0S_smul_left (I := I) g x 1 κ (alpha x) (alpha x),
      ← normSq0S_eq_inner (I := I) g x 1 (alpha x)]
  have hInnerB : ∀ x : M,
      inner0S (I := I) g x 1
          (roughLap0STensor (I := I) g (s := 1) (nabla2Alpha x)) (alpha x)
        = tensorInnerPointwise (I := I) (M := M) g 0 1 x
            ((rawTensorConnLapSmooth (I := I) g 0 1 W).toFun x) (W.toFun x) := by
    intro x
    rw [hB2 x, SmoothCcTensor.toFun_apply, hW x,
      inner_toRS0 (I := I) (M := M) g 1 x
        (roughLap0STensor (I := I) g (s := 1) (nabla2Alpha x)) (alpha x),
      inner0S_eq_covariantTensorInnerPointwise (I := I) g x 1
        (roughLap0STensor (I := I) g (s := 1) (nabla2Alpha x)) (alpha x)]
  have hInnerNq : ∀ x : M,
      tensorInnerPointwise (I := I) (M := M) g 0 2 x
          ((TensorSpectral.covGrad (I := I) (M := M) g 0 1 W).toFun x)
          ((TensorSpectral.covGrad (I := I) (M := M) g 0 1 W).toFun x)
        = normSq0S (I := I) g x 2 (nablaAlpha x) := by
    intro x
    rw [hB1 x, ← normSq0S_eq_tensorInnerPointwise_toRS0 (I := I) g x 2 (nablaAlpha x)]
  have htL2_1 :
      tensorL2Inner (I := I) (M := M) g 0 1
          (rawTensorConnLapSmooth (I := I) g 0 1 W).toFun W.toFun
        = ∫ x, inner0S (I := I) g x 1
            (roughLap0STensor (I := I) g (s := 1) (nabla2Alpha x)) (alpha x) ∂ν := by
    change (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 1 x
        ((rawTensorConnLapSmooth (I := I) g 0 1 W).toFun x) (W.toFun x) ∂ν) = _
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => (hInnerB x).symm))
  have htL2_2 :
      tensorL2Inner (I := I) (M := M) g 0 2
          (TensorSpectral.covGrad (I := I) (M := M) g 0 1 W).toFun
          (TensorSpectral.covGrad (I := I) (M := M) g 0 1 W).toFun
        = ∫ x, normSq0S (I := I) g x 2 (nablaAlpha x) ∂ν := by
    change (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 2 x
        ((TensorSpectral.covGrad (I := I) (M := M) g 0 1 W).toFun x)
        ((TensorSpectral.covGrad (I := I) (M := M) g 0 1 W).toFun x) ∂ν) = _
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => hInnerNq x))
  have hGreenId :
      tensorL2Inner (I := I) (M := M) g 0 2
          (TensorSpectral.covGrad (I := I) (M := M) g 0 1 W).toFun
          (TensorSpectral.covGrad (I := I) (M := M) g 0 1 W).toFun
        = - tensorL2Inner (I := I) (M := M) g 0 1
            (rawTensorConnLapSmooth (I := I) g 0 1 W).toFun W.toFun :=
    tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_gen (I := I) (M := M) g 1 W W
  have hInnerInt :
      (∫ x, inner0S (I := I) g x 1
          (roughLap0STensor (I := I) g (s := 1) (nabla2Alpha x)) (alpha x) ∂ν)
        = - ∫ x, normSq0S (I := I) g x 2 (nablaAlpha x) ∂ν := by
    rw [← htL2_1, ← htL2_2]
    linarith [hGreenId]
  have hEigenInt :
      (∫ x, inner0S (I := I) g x 1
          (roughLap0STensor (I := I) g (s := 1) (nabla2Alpha x)) (alpha x) ∂ν)
        = κ * ∫ x, normSq0S (I := I) g x 1 (alpha x) ∂ν := by
    rw [← MeasureTheory.integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => hEigenInner x))
  have hfinal :
      (∫ x, normSq0S (I := I) g x 2 (nablaAlpha x) ∂ν)
        = - (κ * ∫ x, normSq0S (I := I) g x 1 (alpha x) ∂ν) := by
    rw [← hEigenInt]
    linarith [hInnerInt]
  rw [hfinal]
  ring

end Connection
end Integral
end DifferentialGeometry

end

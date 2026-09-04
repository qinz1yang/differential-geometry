import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.SectionDifference.ConnectionBicontraction
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.Iterates
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.TensorCommutator
import DifferentialGeometry.Geometry.Curvature.RoughLaplacian.Commutator.GradientField
import DifferentialGeometry.Geometry.Connection.ChartFrame.RicciIdentitySmoothFrame
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection


noncomputable section


open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitModel_eq_toModel_unitEval
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (W : SmoothCcTensor g₀ 0 s) (x : M)
    (v : Fin s → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ s W x
        (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (v i)) =
      Tensor0SSpace.eval
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)
          (unitZeroSec (I := I) (M := M) x)) v := rfl


omit [CompactSpace M] [SigmaCompactSpace M] in
private lemma secondCovDeriv_frame_unitEval_eq_iteratedCovGrad
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M)
    (v : Fin 2 → TangentSpace I x) (i : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.eval
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorSecondCovDeriv (I := I) g₀ 0 2
            (smoothOrthoFrame (I := I) g₀ x i) (smoothOrthoFrame (I := I) g₀ x i)
            (fun z : M => S.toSection z) x)
          (unitZeroSec (I := I) (M := M) x)) v =
      unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
        (fun j => tangentSpaceModelContinuousLinearEquiv (I := I) x
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x))
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x)) v) :
              Fin 4 → TangentSpace I x) j)) := by
  have hiter : iteratedCovGrad (I := I) g₀ 0 2 2 S =
      covGrad (I := I) (M := M) g₀ 0 3 (covGrad (I := I) (M := M) g₀ 0 2 S) := by
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, iteratedCovGrad_zero]
  have hbridge := tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval_genVal
    (I := I) (M := M) g₀ 2 S
    (X := smoothOrthoFrame (I := I) g₀ x i)
    (Y := smoothOrthoFrame (I := I) g₀ x i)
    (smoothOrthoFrame_smooth (I := I) g₀ x i) (smoothOrthoFrame_smooth (I := I) g₀ x i) x v
  rw [unitModel_eq_toModel_unitEval, hiter]
  exact hbridge.symm


omit [CompactSpace M] [SigmaCompactSpace M] in
private lemma unitModel_rawTensorConnLapSmooth_eq_frame_sum
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 (rawTensorConnLapSmooth (I := I) g₀ 0 2 S) x
        (fun j => tangentSpaceModelContinuousLinearEquiv (I := I) x (v j)) =
      ∑ i : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
          (fun j => tangentSpaceModelContinuousLinearEquiv (I := I) x
            ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x))
              (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x)) v) :
                Fin 4 → TangentSpace I x) j)) := by
  classical
  rw [unitModel_eq_toModel_unitEval]
  have hsec : (rawTensorConnLapSmooth (I := I) g₀ 0 2 S).toSection x =
      ∑ i : Fin (Module.finrank ℝ E),
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorSecondCovDeriv (I := I) g₀ 0 2
            (smoothOrthoFrame (I := I) g₀ x i) (smoothOrthoFrame (I := I) g₀ x i)
            (fun z : M => S.toSection z) x) := by
    rw [rawTensorConnLapSmooth_toSection_apply (I := I) g₀ 0 2 S x,
      rawTensorConnLap_eq_frame_trace_secondCovDeriv (I := I) g₀ 0 2
        (fun z : M => S.toSection z) x]
  rw [show
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 S).toSection x)
        (unitZeroSec (I := I) (M := M) x) =
      ∑ i : Fin (Module.finrank ℝ E),
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorSecondCovDeriv (I := I) g₀ 0 2
            (smoothOrthoFrame (I := I) g₀ x i) (smoothOrthoFrame (I := I) g₀ x i)
            (fun z : M => S.toSection z) x)
          (unitZeroSec (I := I) (M := M) x) from by
    rw [hsec, sum_apply]]
  rw [Tensor0SSpace.eval_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact secondCovDeriv_frame_unitEval_eq_iteratedCovGrad (I := I) g₀ S x v i


omit [SigmaCompactSpace M] in
theorem rawTensorConnLapSmooth_eq_operatorFieldApplication_cometricDoubleTrace
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 (rawTensorConnLapSmooth (I := I) g₀ 0 2 S) x
        (fun j => tangentSpaceModelContinuousLinearEquiv (I := I) x (v j)) =
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2
          (cometricDoubleTraceCoefficient (I := I) (M := M) g₀ g₀)
          (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x
        (fun j => tangentSpaceModelContinuousLinearEquiv (I := I) x (v j)) := by
  classical
  rw [cometricDoubleTraceCoefficient_operatorFieldApplication_eq_roughLaplacian (I := I) (M := M) g₀ g₀
    (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
    (fun j => tangentSpaceModelContinuousLinearEquiv (I := I) x (v j))]
  rw [unitModel_rawTensorConnLapSmooth_eq_frame_sum (I := I) g₀ S x v]
  exact
    (DifferentialGeometry.Analysis.Spectral.DeTurck.cometric_dualTrace_eq_orthoFrame_diag
    (I := I) g₀ (s := 2) x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x) v).symm

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end

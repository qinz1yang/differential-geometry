import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.SlotCorrectionComponent
import DifferentialGeometry.Tensor.RSTensor.RankZero
open DifferentialGeometry.Geometry.Curvature

noncomputable section


open Bundle Manifold Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem scalar0_raw_eq
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 0)
    (α : M) {x : M} (hx : x ∈ (chartAt H α).source) :
    tensorChartComponentRaw (I := I) (M := M) g 0 0 S α
        Fin.elim0 Fin.elim0 x =
      TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection x := by
  classical
  rw [tensorChartComponentRaw_eq_chartFrame (I := I) (M := M)
    g 0 0 S α hx Fin.elim0 Fin.elim0]
  have hunit :
      chartFrameBasisModel (I := I) (M := M) α x 0 Fin.elim0 =
        (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 0 x).symm
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) := by
    apply (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 0 x).injective
    apply ContinuousMultilinearMap.ext
    intro v
    rw [tensor0SSpaceFiberContinuousLinearEquiv_apply_apply,
      ContinuousLinearEquiv.apply_symm_apply, chartFrameBasisModel_apply, Fin.prod_univ_zero,
      ContinuousMultilinearMap.constOfIsEmpty_apply]
  rw [hunit]
  have hone :
      Tensor0SField.one0 (𝕜 := ℝ) (E := E) (H := H)
          (I := I) (M := M) (∞ : WithTop ℕ∞) x =
        (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 0 x).symm
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) := by
    apply (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 0 x).injective
    apply ContinuousMultilinearMap.ext
    intro v
    rw [tensor0SSpaceFiberContinuousLinearEquiv_apply_apply,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousMultilinearMap.constOfIsEmpty_apply]
    exact Tensor0SField.one0_apply (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (∞ : WithTop ℕ∞) x v
  rw [TensorRSField.scalar0, Tensor0SField.toScalarField,
    TensorRSField.rs0_apply, hone, Tensor0SSpace.toModel,
    tensor0SSpace_continuousLinearEquiv_apply]
  exact congrArg
    (S.toSection x
      ((tensor0SSpaceFiberContinuousLinearEquiv (I := I) 0 x).symm
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))))
    (Subsingleton.elim _ _)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

import DifferentialGeometry.Geometry.Curvature.Order2Defect.GradientSlotLeibniz
open DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Geometry.Connection

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Tensor0SNabla
open DifferentialGeometry.TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [I.Boundaryless] in
theorem metricTrace2_covDeriv_comm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (x : M) (w : TangentSpace I x) :
    (tensorCov (I := I) g r s).toFun
        (fun y : M => metricTrace2 (I := I) g r s (tensorSecondCovDeriv (I := I) g r s)
          (fun z : M => T.toSection z) y) x w =
      ∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g r s).toFun
          (fun y : M => tensorSecondCovDeriv (I := I) g r s
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (fun z : M => T.toSection z) y) x w := by
  have hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T.toSection y)) :=
    T.toSection.contMDiff
  rw [show (fun y : M => metricTrace2 (I := I) g r s (tensorSecondCovDeriv (I := I) g r s)
        (fun z : M => T.toSection z) y) =
      (fun y : M => rawTensorConnLap (I := I) g r s (fun z : M => T.toSection z) y) from by
    funext y
    exact (rawTensorConnLap_eq_metricTrace2 (I := I) g r s
      (fun z : M => T.toSection z) y).symm]
  exact covDeriv_rawConnLap_eq_frozenFrameTrace_sum (I := I) g r s hT x w

omit [I.Boundaryless] in
theorem metricTrace2_covDeriv_comm_map
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (x : M) :
    (tensorCov (I := I) g r s).toFun
        (fun y : M => metricTrace2 (I := I) g r s (tensorSecondCovDeriv (I := I) g r s)
          (fun z : M => T.toSection z) y) x =
      ∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g r s).toFun
          (fun y : M => tensorSecondCovDeriv (I := I) g r s
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (fun z : M => T.toSection z) y) x := by
  refine ContinuousLinearMap.ext (fun w => ?_)
  rw [ContinuousLinearMap.sum_apply]
  exact metricTrace2_covDeriv_comm (I := I) g r s T x w

end Curvature
end Geometry
end DifferentialGeometry

end

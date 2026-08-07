import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower








noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.TensorMultilinear (contMDiffAt_section_apply contMDiff_section_apply)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance sharpFlatTensorRSModelNormedAddCommGroup (r s : ℕ) :
    NormedAddCommGroup (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModel_normedAddCommGroup r s

private local instance sharpFlatTensorRSModelNormedSpace (r s : ℕ) :
    NormedSpace ℝ (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModel_normedSpace r s

private local instance sharpFlatTensorRSTotalSpaceTopology (r s : ℕ) :
    TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E) (fun x : M => TensorRSSpace r s I x)) :=
  Tensor0SBundle.tensorRSBundle_topology r s

private local instance sharpFlatTensorRSFiberBundle (r s : ℕ) :
    FiberBundle (TensorRSModel r s ℝ E) (fun x : M => TensorRSSpace r s I x) :=
  Tensor0SBundle.tensorRSBundle_fiber r s


omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem sharpFlatEndo_eval (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (w : TangentSpace I x) :
    cotangentToDual (I := I)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (sharpFlatEndoCc (I := I) g₀ g₁).toSection x) om) w =
      cotangentToDual (I := I) om (metricComparisonEndo (I := I) g₀ g₁ x w) := by
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g₀ g₁).toSection x) om =
      g0FlatCLM (I := I) g₀ x (inverseMetricSharpFib (I := I) g₁ x om) from rfl]
  rw [cotangentToDual_g0FlatCLM]
  have h₁ : ∀ v : TangentSpace I x,
      g₁.inner x (metricComparisonEndo (I := I) g₀ g₁ x w) v =
        g₀.inner x w v := by
    intro v
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_inner,
      cotangentToDualLinear_apply, cotangentToDual_g0FlatCLM]
  rw [show cotangentToDual (I := I) (x := x) om
        (metricComparisonEndo (I := I) g₀ g₁ x w) =
      g₁.inner x (inverseMetricSharpFib (I := I) g₁ x om)
        (metricComparisonEndo (I := I) g₀ g₁ x w) by
      rw [inverseMetricSharpFib_inner]
      rfl]
  rw [g₁.symm, h₁]
  exact g₀.symm x _ _

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

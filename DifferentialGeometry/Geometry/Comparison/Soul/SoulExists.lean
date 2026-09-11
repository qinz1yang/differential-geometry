import DifferentialGeometry.Geometry.Comparison.Nonnegative.BoundaryShiftTangent
import DifferentialGeometry.Geometry.Comparison.SliceParallelTransport

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Geometry.Riemannian.Variation

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

theorem shavingConcavity_of_sec_nonneg'
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ z : M, metricRm04At (I := I) g z ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) :
    ShavingConcavity (I := I) g :=
  shavingConcavity_of_sec_nonneg (I := I) g hEnorm hsec
    (fun _ hC hCclosed => hasSliceParallelTransport_of_totallyConvex (I := I) hEnorm hC hCclosed)

theorem exists_soul_set_of_sec_nonneg' [NoncompactSpace M]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ z : M, metricRm04At (I := I) (M := M) g z ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) (p : M) :
    ∃ S : Set M, S.Nonempty ∧ IsCompact S ∧ IsTotallyConvex (I := I) g S ∧
      relBoundary I S = ∅ ∧ maxSliceDim I S < Module.finrank ℝ E :=
  exists_soul_set_of_sec_nonneg (I := I) g hEnorm hsec
    (fun _ hC hCclosed => hasSliceParallelTransport_of_totallyConvex (I := I) hEnorm hC hCclosed) p

end DifferentialGeometry.Geometry.Topology

end

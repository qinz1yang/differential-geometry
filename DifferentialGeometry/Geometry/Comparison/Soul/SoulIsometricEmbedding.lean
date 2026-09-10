import DifferentialGeometry.Geometry.Comparison.Soul.InducedSliceMetric
import DifferentialGeometry.Geometry.Comparison.Soul.EmbeddedSliceEmbedding
import DifferentialGeometry.Geometry.Comparison.Soul.PositiveIsometricImmersion

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

theorem embeddedSlice_inclusion_isRiemannianIsometricImmersion
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {S : Set M} (hconv : IsTotallyConvex (I := I) g S)
    (hB : relBoundary I S = ∅) :
    let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
    let _ := embeddedSliceChartedSpace hS
    let _ := embeddedSlice_isManifold hS
    DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion
      (inducedSliceMetric g hS) g (Subtype.val : S → M) := by
  let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  apply DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.of_is_smooth_embedding
    (embeddedSlice_inclusion_isSmoothEmbedding g hEnorm hconv hB)
  intro p u v
  exact (inducedSliceMetric_inner g hS p u v).symm

end DifferentialGeometry.Geometry.Topology

end

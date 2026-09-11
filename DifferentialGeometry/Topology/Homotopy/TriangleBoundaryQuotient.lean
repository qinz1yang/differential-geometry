import DifferentialGeometry.Topology.Homotopy.TriangleEdges
import Mathlib.Topology.ContinuousMap.Compact



noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology


def triangleBoundaryProjection : C(Fin 3 × unitInterval, frontier planeTriangle) :=
  (⟨planeTriangleEdge, continuous_of_discreteTopology⟩ : C(Fin 3, C(unitInterval, frontier planeTriangle))).uncurry


theorem triangleBoundaryProjection_apply (i : Fin 3) (s : unitInterval) :
    (triangleBoundaryProjection (i, s)).val = planeTriangleEdgeValue i s := rfl


theorem triangleBoundaryProjection_surjective : Surjective triangleBoundaryProjection := by
  intro z
  have hz := isClosed_planeTriangle.frontier_subset z.property
  have him : z.val.im ≤ 1 := by linarith [hz.1, hz.2.2]
  have hre : z.val.re ≤ 1 := by linarith [hz.2.1, hz.2.2]
  rcases planeTriangle_frontier_edges z.property with hr | hi | hs
  · refine ⟨(1, ⟨z.val.im, hz.2.1, him⟩), ?_⟩
    apply Subtype.ext
    change planeTriangleEdgeValue 1 _ = z.val
    apply Complex.ext
    · simpa [planeTriangleEdgeValue] using hr.symm
    · simp [planeTriangleEdgeValue]
  · refine ⟨(2, ⟨z.val.re, hz.1, hre⟩), ?_⟩
    apply Subtype.ext
    change planeTriangleEdgeValue 2 _ = z.val
    apply Complex.ext
    · simp [planeTriangleEdgeValue]
    · simpa [planeTriangleEdgeValue] using hi.symm
  · refine ⟨(0, ⟨z.val.im, hz.2.1, him⟩), ?_⟩
    apply Subtype.ext
    change planeTriangleEdgeValue 0 _ = z.val
    apply Complex.ext
    · simpa [planeTriangleEdgeValue] using (show 1 - z.val.im = z.val.re by linarith)
    · simp [planeTriangleEdgeValue]


theorem triangleBoundaryProjection_isQuotientMap :
    _root_.Topology.IsQuotientMap triangleBoundaryProjection :=
  .of_surjective_continuous triangleBoundaryProjection_surjective triangleBoundaryProjection.continuous

end DifferentialGeometry.Topology

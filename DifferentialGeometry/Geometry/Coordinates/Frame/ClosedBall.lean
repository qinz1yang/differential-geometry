import DifferentialGeometry.Topology.Manifold.ClosedBall.Coordinates
import DifferentialGeometry.Geometry.Coordinates.Frame.Chart

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Tensor.Coordinates

open DifferentialGeometry.Topology DifferentialGeometry.Topology.Handle

variable {m : ℕ}
local notation "EuN" => EuclideanSpace ℝ (Fin (m + 1))
local instance : ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
  closedCellChartedSpaceSucc m
local instance : IsManifold (𝓡∂ (m + 1)) ∞ (ClosedCell (m + 1)) := closedCellIsManifold m

private theorem closedCell_chart_eq {x y : ClosedCell (m + 1)}
    (hx : ‖x.val‖ < 1) (hy : ‖y.val‖ < 1) :
    chartAt (EuclideanHalfSpace (m + 1)) x = chartAt (EuclideanHalfSpace (m + 1)) y := by
  change closedCellChartAt x = closedCellChartAt y
  rw [closedCellChartAt, dite_eq_left hx, closedCellChartAt, dite_eq_left hy]

theorem chartBasisVecFiber_closedCell_of_norm_lt_one
    {α x : ClosedCell (m + 1)} (hα : ‖α.val‖ < 1) (hx : ‖x.val‖ < 1)
    (i : Fin (Module.finrank ℝ EuN)) :
    chartBasisVecFiber (I := 𝓡∂ (m + 1)) α i x =
      chartModelBasis EuN i := by
  have ha : achart (EuclideanHalfSpace (m + 1)) α = achart (EuclideanHalfSpace (m + 1)) x :=
    Subtype.ext (closedCell_chart_eq hα hx)
  have hm : x ∈ (chartAt (EuclideanHalfSpace (m + 1)) α).source := by
    rw [closedCell_chart_eq hα hx]
    exact mem_chart_source _ x
  rw [chartBasisVecFiber,
    TangentBundle.symmL_trivializationAt_eq_core hm, ha]
  exact (tangentBundleCore (𝓡∂ (m + 1)) (ClosedCell (m + 1))).coordChange_self
    (achart (EuclideanHalfSpace (m + 1)) x) x
    (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source _ x) _

end DifferentialGeometry.Tensor.Coordinates

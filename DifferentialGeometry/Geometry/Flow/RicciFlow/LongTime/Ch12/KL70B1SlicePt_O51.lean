import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KL70B12Slice_O47

/-!
# CH12-O51, group 1a: B1 step 1 — slice points as centres of the slice-slab escape limit

`[FROZEN] CH12-O51 G1a`.  Every point of a regular slice lies in the terminal regular open set of
its slice slab `sliceSlabR_O3 F s` (closed slab ⇒ terminal regular region = univ), the slab scalar
at the slice time is the slice scalar, and the endpoint terminal metric is the slice metric
restricted to that open set.  These identify O38's sequence data `(s n, y n)` with the centre
`x n` of `slice_b12_of_escape_limit_O47` / the O23 escape theorem.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)

/-- Slice points are terminal-regular for the slice slab. -/
theorem mem_slice_terminalRegularOpen_O51 (s : RegularSlice F.observation) (y : s.stage.Carrier) :
    y ∈ ((sliceSlabR_O3 F s).restrictIncoming le_rfl (sliceSlabR_O3 F s).lt le_rfl).terminalRegularOpen := by
  change y ∈ ((sliceSlabR_O3 F s).restrictIncoming le_rfl (sliceSlabR_O3 F s).lt le_rfl).terminalRegularRegion
  rw [(sliceSlabR_O3 F s).terminalRegularRegion_eq_univ _]
  exact mem_univ _

/-- The slab scalar at the slice time is the slice scalar. -/
theorem slice_flow_scalar_O51 (s : RegularSlice F.observation) (y : s.stage.Carrier) :
    (sliceSlabR_O3 F s).flow.scalar s.time y = metricScalarAt s.metric y := by
  change metricScalarAt ((sliceSlabR_O3 F s).flow.base.metric s.time) y = _
  rw [sliceSlabR_metric_time_O3 F s]
  rfl

/-- The endpoint terminal metric of the slice slab is the slice metric on the terminal open set. -/
theorem slice_endpoint_metric_O51 (s : RegularSlice F.observation) :
    ((sliceSlabR_O3 F s).endpointTerminalLimitMetric
        ((sliceHistoryR_O3 F s).stage (Fin.last (sliceHistoryR_O3 F s).eventCount))).metric =
      s.metric.restrictOpen
        ((sliceSlabR_O3 F s).restrictIncoming le_rfl (sliceSlabR_O3 F s).lt le_rfl).terminalRegularOpen := by
  change ((sliceSlabR_O3 F s).flow.base.metric s.time).restrictOpen _ = _
  rw [sliceSlabR_metric_time_O3 F s]
  rfl

end GC.LongTime.Ch12

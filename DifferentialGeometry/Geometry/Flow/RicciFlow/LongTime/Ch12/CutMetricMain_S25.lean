import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.LateCutGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CutMetricPullback_S25

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.Endpoint GC.Topology Set
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12
universe u

/-- C2b for one slice: every torus decomposition of every slice component has induced cut
metrics, obtained as pullbacks of `s.componentMetric C` along `cutPieceMap`. This is exactly the
`hmetric` input of `exists_late_cut_family_assembly_S24`. -/
theorem exists_inducedCutMetrics_slice_S25 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} (s : RegularSlice F.observation)
    (C : ConnectedComponents s.stage.Carrier)
    (D : TorusDecomposition (s.stage.toClosedOrientedManifold.component C)) :
    ∃ met : ∀ i : Fin D.components.count,
        SmoothRiemannianMetric (D.component i).model (D.component i).Carrier,
      ∀ i, isInducedCutMetric (s.componentMetric C) D i (met i) :=
  ⟨fun i => cutMetric_S25 (s.componentMetric C) D i,
    fun i => isInducedCutMetric_cutMetric_S25 (s.componentMetric C) D i⟩

/-- Family form, binder-for-binder the `hmetric` hypothesis of
`exists_late_cut_family_assembly_S24`. -/
theorem hmetric_S25 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} (slices : ℕ → RegularSlice F.observation) :
    ∀ j (C : ConnectedComponents (slices j).stage.Carrier)
      (D : TorusDecomposition ((slices j).stage.toClosedOrientedManifold.component C)),
      ∃ met : ∀ i : Fin D.components.count,
          SmoothRiemannianMetric (D.component i).model (D.component i).Carrier,
        ∀ i, isInducedCutMetric ((slices j).componentMetric C) D i (met i) :=
  fun j C D => exists_inducedCutMetrics_slice_S25 (slices j) C D

end GC.LongTime.Ch12

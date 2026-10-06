import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.EdgeCircleProductECM
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialEdgeRegistry

/-!
# Consumer of E4c: the radial solid torus (X135) with its circle product PRODUCED

The tree's radial inhabitant `radialEdgeComponentModels` gives the circle product `radialCircleTriv`
by hand. Here the same registry is built from `EdgeComponentModels.ofCircleProducts_ECM`: every
`circleTriv_*` clause is produced by `edge_circle_product_ECM` from the fields of the actual
`radialEdgeBundle` (a solid torus with boundary, base the circle, one circle component, no interval
components). This is a compiled non-trivial inhabitant of the hypotheses of the E4c theorem.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

local instance carrierCharts_ProductX135ECM :
    ChartedSpace (EuclideanHalfSpace 3) carrier.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

/-- The radial edge registry with its circle product produced by `edge_circle_product_ECM`. -/
def radialEdgeComponentModelsECM : EdgeComponentModels radialEdgeBundle :=
  EdgeComponentModels.ofCircleProducts_ECM radialEdgeBundle 0 1 radialComponentEquiv
    (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0) (fun _ => id)
    (fun _ => (Diffeomorph.refl (𝓡 1) Circle ∞).isSmoothEmbedding)
    (fun _ => by rw [radialBaseComponent_univ]; exact range_id)
    radialEndpointEquiv (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
    (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)

theorem radialEdgeComponentModelsECM_counts :
    radialEdgeComponentModelsECM.intervalCount = 0 ∧
      radialEdgeComponentModelsECM.circleCount = 1 :=
  ⟨rfl, rfl⟩

/-- The produced circle product of the radial registry parametrizes the whole component: its
image is the whole solid torus below the level. -/
theorem radialEdgeComponentModelsECM_range :
    range (radialEdgeComponentModelsECM.circleTriv (0 : Fin 1)) =
      radialEdgeBundle.wholeComponent
        (radialEdgeComponentModelsECM.componentEquiv (.inr (0 : Fin 1))) :=
  radialEdgeComponentModelsECM.circleTriv_range (0 : Fin 1)

end GC.GraphManifold.Assembly.FC39P0.X135Radial

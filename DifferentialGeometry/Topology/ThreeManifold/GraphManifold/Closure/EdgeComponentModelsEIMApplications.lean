import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.EdgeComponentModelsEIM
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereEdge
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialEdgeRegistry

/-!
# Consumer of E2 + E3: the actual S³ edge bundle and the radial solid torus (lane S-EDGE-INT2)

* `sphereEdge_interval_product_EIM`: the E3 theorem applied to the two actual interval components
  of the S³ edge bundle (`sphereEdgeModels`): a compiled non-trivial inhabitant of its hypotheses
  (a smooth embedding of `[0, 1]` onto an actual component of the edge base of the sphere bundle),
  producing a whole `D² × [0, 1]` with the four clauses;
* `sphereEdgeBundle_models_EIM` / `radialEdgeBundle_models_EIM`: the assembled registry
  `exists_edgeComponentModels_EIM` on the actual S³ and radial bundles.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

/-- The E3 product over each interval component of the S³ edge bundle. -/
theorem sphereEdge_interval_product_EIM (i : Fin sphereEdgeModels.intervalCount) :
    ∃ H : EdgeHandle sphereW, range H.map =
        sphereEdgeBundle.wholeComponent (sphereEdgeModels.componentEquiv (.inl i)) ∧
      (∀ w t, ∃ hx : H.map (w, t) ∈ sphereEdgeBundle.source,
        sphereEdgeBundle.proj ⟨H.map (w, t), hx⟩ = sphereEdgeModels.intervalBase i t) ∧
      (∀ t, range (fun w => H.map (w, t)) =
        sphereEdgeBundle.disk (sphereEdgeModels.intervalBase i t)) ∧
      (∀ t, (fun w => H.map (w, t)) '' diskRim =
        sphereEdgeBundle.rim (sphereEdgeModels.intervalBase i t)) :=
  sphereEdgeBundle.edge_interval_product_EIM (sphereEdgeModels.intervalBase i)
    (sphereEdgeModels.intervalBase_embedding i) (sphereEdgeModels.componentEquiv (.inl i))
    (sphereEdgeModels.intervalBase_range i)

/-- The assembled edge component registry of the S³ edge bundle. -/
theorem sphereEdgeBundle_models_EIM : Nonempty (EdgeComponentModels sphereEdgeBundle) :=
  sphereEdgeBundle.exists_edgeComponentModels_EIM

/-- The assembled edge component registry of the radial solid torus. -/
theorem radialEdgeBundle_models_EIM :
    Nonempty (EdgeComponentModels X135Radial.radialEdgeBundle) :=
  X135Radial.radialEdgeBundle.exists_edgeComponentModels_EIM

end GC.GraphManifold.Assembly.FC39P0

import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.EdgeBaseComponentsEIM
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.EdgeCircleProductECM
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.EdgeIntervalProductEIM

/-!
# The edge component registry of every edge bundle (lane S-EDGE-INT2, draft 74 E2 + E3 + E4c)

`EdgeBundle.exists_edgeComponentModels_EIM`: every edge bundle `P` over a compact edge base has an
`EdgeComponentModels P`, assembled from

* E2 (`EdgeBundle.finite_interval_circle_components_EIM`): the finite interval / circle
  components of the compact smooth one-domain `C₂`, their smooth parametrizations with exact
  ranges, and the endpoint bijection;
* E3 (`EdgeBundle.edge_interval_product_EIM`): the whole boundary-preserving `D² × [0, 1]` over
  each interval component;
* E4c (`EdgeComponentModels.ofCircleProducts_ECM`): the whole `D² × S¹` over each circle
  component.

No hypothesis beyond the fields of `EdgeBundle` is used.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}}

/-- **The edge component registry exists for every edge bundle** (E2 + E3 + E4c). -/
theorem EdgeBundle.exists_edgeComponentModels_EIM (P : EdgeBundle W) :
    Nonempty (EdgeComponentModels P) := by
  obtain ⟨m, l, e, a, c, ε, ha, har, hc, hcr, hε⟩ := P.finite_interval_circle_components_EIM
  choose H hHr hHp hHd hHm using
    fun i => P.edge_interval_product_EIM (a i) (ha i) (e (Sum.inl i)) (har i)
  exact ⟨EdgeComponentModels.ofCircleProducts_ECM P m l e a ha har c hc hcr ε hε H hHr hHp hHd
    hHm⟩

end GC.GraphManifold.Assembly.FC39P0

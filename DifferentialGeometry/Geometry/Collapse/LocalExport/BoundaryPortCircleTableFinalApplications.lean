import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortCircleTableFinal
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryProducerDPCircleOfPort

/-!
# Transfer check of the circle port table (lane O-PORT-A)

`port_circle_interior_table_BAUGP` discharges the explicit premise `hport` of BAUG-C's conditional
circle stage table `exists_boundaryCircleTable_of_port_BAUGC` (ProducerDP v3.1, group G6a; inside
it the port is called at the transfer point `(Γ, 5Σ/4, eg/2)` and fed to the stage transfer
`BoundarySupply.exists_boundaryCircleSpec_of_port_BAUGC`). The `example` below is that application
with ProducerDP v3.1's circle header; it is the unconditional circle table (BAUG-C's G6b names it).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **Transfer check**: the circle port theorem is the premise `hport` of BAUG-C's conditional
circle stage table, so the circle stage table of the actual slot v2 with its spec V3 holds under
ProducerDP v3.1's circle header alone. -/
example {ν Γ sg eg : ℝ} (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg) (hsgΓ : sg < Γ / 250)
    (hsgC : sg < Γ ^ 3 / (125 * (tcpGraphConst + 2 * bmConst_BAUGC)))
    (heg : 0 < eg) (heg1 : eg < 1 / 100) (hegΓ : eg < Γ * sg / 100) (hν : 0 < ν)
    (hν1 : ν < 1) :=
  exists_boundaryCircleTable_of_port_BAUGC
    (by
      intro ν' Γ' sg' eg' hΓ' _ hsg' hsgΓ' _ heg' heg1' _ hν' hν1'
      exact port_circle_interior_table_BAUGP hΓ' hsg' hsgΓ' heg' heg1' hν' hν1')
    hΓ hΓ1 hsg hsgΓ hsgC heg heg1 hegΓ hν hν1

end DifferentialGeometry.Geometry.Collapse

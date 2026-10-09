import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainTransport74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierTransportEmpty74

/-!
# D74-6 on the closed route: the `cusp` field and the ports from `M.ψ`

Lane C14-REG-CHAIN (by S-REG-CHAIN), G26 (closed consumer). Draft 74 D74-6: `cusp.ports`
(`∂W = ∅`) comes from the boundary transport of `M.ψ`, never from `BoundaryTori.empty W`:

* `ClosedModel.boundary_empty_R74 M : ∂W = ∅` (the model carrier `X` is boundaryless and
  `M.ψ` carries boundaries, `Diffeomorph.image_boundary`);
* **`ClosedModel.cusp_R74 M : CuspCores W (BoundaryTori.empty W)`**: the closed-route cusp field
  of `FC39RowsV2` (`n = 0`), through `CuspCores.ofBoundaryEmpty74`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **`∂W = ∅` from the model** (D74-6): `M.ψ` is a diffeomorphism from the boundaryless carrier
`X`, so it carries the empty boundary of `X` onto the model boundary of `W`. -/
theorem ClosedModel.boundary_empty_R74 {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} (M : ClosedModel W g) :
    W.model.boundary W.Carrier = ∅ := by
  rw [← M.ψ.image_boundary (by simp), ModelWithCorners.Boundaryless.boundary_eq_empty,
    image_empty]

/-- **The closed-route `cusp` field** (`n = 0`): the cusp cores of the empty port family, with
`ports` from the boundary transport of `M.ψ`. -/
def ClosedModel.cusp_R74 {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier}
    (M : ClosedModel W g) : CuspCores W (BoundaryTori.empty W) :=
  CuspCores.ofBoundaryEmpty74 M.boundary_empty_R74

/-- **Consumer**: a closed member has the closed-route cusp field, from either source of `∂W = ∅`
(its standing facts or its normalized model). -/
theorem closedMember_cusp_R74 {W : CompactCarrier.{u}}
    (g : SmoothRiemannianMetric W.model W.Carrier) (h : ClosedMemberFacts W) :
    Nonempty (CuspCores W (BoundaryTori.empty W)) ∧
      ∀ M : ClosedModel W g,
        M.cusp_R74.ports = (CuspCores.ofBoundaryEmpty74 h.boundary_empty).ports :=
  ⟨⟨CuspCores.ofBoundaryEmpty74 h.boundary_empty⟩, fun _ => rfl⟩

end DifferentialGeometry.Geometry.Collapse

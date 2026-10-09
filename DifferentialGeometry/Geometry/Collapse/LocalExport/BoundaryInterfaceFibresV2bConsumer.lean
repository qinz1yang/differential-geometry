import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceFibresV2b

/-!
# Consumer of the whole-fibre layer v2b (lane O-WF, G0)

`BoundaryWholeFiberSpecV2b.fibre_types_OWF`: the three derived fibre exits of a v2b layer in one
statement (circle `S¹`, slim `S²` OR `T²`, edge disk with the rim at `T = 4Δ`), and the source
buffer `{D > 5}`; `BoundaryWholeFiberSpecV2b.toV2_toV2b_OWF`: v2b → v2 → v2b under `{D > 10}`
recovers the same source buffer.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

attribute [local instance] DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ} {Kj : ℕ}
  {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}

namespace BoundaryWholeFiberSpecV2b

variable {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02BasesV2 C}

/-- **The fibre types of a v2b layer** (one statement) and its source buffer `{D > 5}`. -/
theorem fibre_types_OWF (WF : BoundaryWholeFiberSpecV2b C Bs) :
    (∀ y ∈ Bs.base 0, Nonempty (Bs.fibre 0 y ≃ₜ Circle)) ∧
      (∀ y ∈ Bs.base 2, Nonempty (Bs.fibre 2 y ≃ₜ Metric.sphere (0 : E3) 1) ∨
        Nonempty (Bs.fibre 2 y ≃ₜ Circle × Circle)) ∧
      (∀ y ∈ Bs.base 1, ∃ ed : Bs.fibre 1 y ≃ₜ ClosedCell 2,
        Subtype.val '' (ed ⁻¹' {x : ClosedCell 2 | ‖x.1‖ = 1}) =
          Bs.fibre 1 y ∩ {p | C.heightRatio p = 4 * Δ}) ∧
      ∀ st, Bs.source st ⊆ {p | ENNReal.ofReal 5 < distanceToBoundary W g p} :=
  ⟨WF.circle_fibre_OWF, WF.slim_fibre_OWF, WF.edge_fibre_OWF, WF.source_buffered⟩

/-- **Round trip** v2b → v2 → v2b under `{D > 10}`: the v2 exits hold and the buffer `{D > 5}` is
recovered. -/
theorem toV2_toV2b_OWF (WF : BoundaryWholeFiberSpecV2b C Bs)
    (h10 : ∀ st, Bs.source st ⊆ {p | ENNReal.ofReal 10 < distanceToBoundary W g p}) :
    (∀ y ∈ Bs.base 0, Nonempty (Bs.fibre 0 y ≃ₜ Circle)) ∧
      ∀ st, Bs.source st ⊆ {p | ENNReal.ofReal 5 < distanceToBoundary W g p} :=
  ⟨(WF.toV2_OWF h10).circle_fibre_BIFc, (WF.toV2_OWF h10).toV2b_OWF.source_buffered⟩

end BoundaryWholeFiberSpecV2b

end DifferentialGeometry.Geometry.Collapse

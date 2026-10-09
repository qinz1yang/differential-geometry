import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceFibresV2

/-!
# Boundary whole-fibre layer v2b: the buffered sources in `{D > 5}` (lane O-WF)

Named revision for text v3.2 (`source_buffered`: `D > 5`), lead decision 2026-10-05 20:4x. The
v2 field `BoundaryWholeFiberSpecV2.source_buffered` asks the WHOLE source domains to lie in
`{D > 10}`; the chart CENTRES lie in `{D > 10}` (the region `U₁` of the family) and a source point
lies up to `200ρ_j` (circle), `100Δρ_j` (edge), `10⁶Δρ_j` (slim) away from its centre, so only
`D > 10 − O(ρ)` holds: the `10` of v2 is the centre condition written on the sources. v2b is v2
with the buffer `{D > 5}` (the rank region `U₀ = {D > 5}` of the packet's transport clauses).

* `BoundaryWholeFiberSpecV2b C Bs`: the fields of `BoundaryWholeFiberSpecV2` (same names, same
  charts) with `source_buffered : ∀ st, Bs.source st ⊆ {p | ENNReal.ofReal 5 < D(p)}`;
* projections: `BoundaryWholeFiberSpecV2.toV2b_OWF` (always) and
  `BoundaryWholeFiberSpecV2b.toV2_OWF` (given `Bs.source st ⊆ {D > 10}`);
* derived exits on v2b (as on v2): `circle_fibre_OWF`, `slim_fibre_OWF`, `edge_fibre_OWF`;
* inhabitant: `BoundaryGaf02Chain.emptyWholeFiberSpecV2b_OWF` (the empty v2 bases).
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

/-- **The whole-fibre layer v2b** (named revision for text v3.2): `BoundaryWholeFiberSpecV2` with
the buffered sources in `{D > 5}` instead of `{D > 10}`. -/
structure BoundaryWholeFiberSpecV2b (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)
    (Bs : BoundaryGaf02BasesV2 C) : Prop where
  /-- Circle stage: smooth `ℝ² × S¹` charts of `f₁` over `B₁`. -/
  circle_chart : ∀ y ∈ Bs.base 0, SmoothProductChartAt_BIFc W.model (𝓡 1) (F := Circle) 2
    (C.stageMap 0) (Bs.source 0) (Bs.base 0) y
  /-- Slim stage: smooth `ℝ × S²` OR `ℝ × T²` charts of `f₃` over `B₃`. -/
  slim_chart : ∀ y ∈ Bs.base 2,
    SmoothProductChartAt_BIFc W.model (𝓡 2) (F := GC.GraphManifold.ClosureSphere.{0}) 1
        (C.stageMap 2) (Bs.source 2) (Bs.base 2) y ∨
      SmoothProductChartAt_BIFc W.model ((𝓡 1).prod (𝓡 1)) (F := Circle × Circle) 1
        (C.stageMap 2) (Bs.source 2) (Bs.base 2) y
  /-- Edge stage: smooth `ℝ × D²` charts of `f₂` over `B₂` with the rim at `T = 4Δ`. -/
  edge_chart : ∀ y ∈ Bs.base 1, SmoothDiskChartAt_BIFc W.model 1 (C.stageMap 1) C.heightRatio
    (4 * Δ) (Bs.source 1) (Bs.base 1) y
  /-- The whole source domains lie in the rank region `{D > 5}` (v3.2 revision of v2's `10`). -/
  source_buffered : ∀ st, Bs.source st ⊆ {p | ENNReal.ofReal 5 < distanceToBoundary W g p}

/-- **v2 gives v2b** (`{D > 10} ⊆ {D > 5}`). -/
theorem BoundaryWholeFiberSpecV2.toV2b_OWF {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}
    {Bs : BoundaryGaf02BasesV2 C} (WF : BoundaryWholeFiberSpecV2 C Bs) :
    BoundaryWholeFiberSpecV2b C Bs where
  circle_chart := WF.circle_chart
  slim_chart := WF.slim_chart
  edge_chart := WF.edge_chart
  source_buffered := fun st _ hp =>
    lt_trans (ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨by norm_num, by norm_num⟩)
      (WF.source_buffered st hp)

namespace BoundaryWholeFiberSpecV2b

variable {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02BasesV2 C}
  (WF : BoundaryWholeFiberSpecV2b C Bs)
include WF

/-- **v2b gives v2 when the sources lie in `{D > 10}`**. -/
theorem toV2_OWF
    (h10 : ∀ st, Bs.source st ⊆ {p | ENNReal.ofReal 10 < distanceToBoundary W g p}) :
    BoundaryWholeFiberSpecV2 C Bs where
  circle_chart := WF.circle_chart
  slim_chart := WF.slim_chart
  edge_chart := WF.edge_chart
  source_buffered := h10

/-- **Derived: whole circle fibres** `≃ₜ S¹`. -/
theorem circle_fibre_OWF : ∀ y ∈ Bs.base 0, Nonempty (Bs.fibre 0 y ≃ₜ Circle) :=
  fun y hy => (WF.circle_chart y hy).nonempty_fibre_homeomorph

/-- **Derived: whole slim fibres** `≃ₜ S²` OR `≃ₜ T²`. -/
theorem slim_fibre_OWF : ∀ y ∈ Bs.base 2,
    Nonempty (Bs.fibre 2 y ≃ₜ Metric.sphere (0 : E3) 1) ∨
      Nonempty (Bs.fibre 2 y ≃ₜ Circle × Circle) := by
  intro y hy
  rcases WF.slim_chart y hy with h | h
  · obtain ⟨e⟩ := h.nonempty_fibre_homeomorph
    exact Or.inl ⟨e.trans Homeomorph.ulift⟩
  · exact Or.inr h.nonempty_fibre_homeomorph

/-- **Derived: whole edge disk fibres** `≃ₜ ClosedCell 2` with the unit circle onto
`fibre ∩ {T = 4Δ}`. -/
theorem edge_fibre_OWF : ∀ y ∈ Bs.base 1, ∃ ed : Bs.fibre 1 y ≃ₜ ClosedCell 2,
    Subtype.val '' (ed ⁻¹' {x : ClosedCell 2 | ‖x.1‖ = 1}) =
      Bs.fibre 1 y ∩ {p | C.heightRatio p = 4 * Δ} :=
  fun y hy => (WF.edge_chart y hy).fibre_disk_rim

end BoundaryWholeFiberSpecV2b

namespace BoundaryGaf02Chain

variable {D : BoundaryAugmentedData S S.emptySlots_BIF}
  (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)

/-- **The whole-fibre layer v2b of the empty v2 bases** (from v2's empty inhabitant). -/
theorem emptyWholeFiberSpecV2b_OWF (hc : ∀ st, S.stageCentres_BIF st = ∅)
    (hF : Continuous S.boundaryOriginalMap) :
    BoundaryWholeFiberSpecV2b C (C.emptyBasesV2_BIFc hc hF) :=
  (C.emptyWholeFiberSpecV2_BIFc hc hF).toV2b_OWF

end BoundaryGaf02Chain

end DifferentialGeometry.Geometry.Collapse

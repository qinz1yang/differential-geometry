import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryFc43RowBGR

/-!
# FC43 as ONE row: the A4 output given by existence, then the full row

Lane S-FC-WRAP, group G4 (suffix `_FCW`). Blueprint `master207B.tex`, FC43
(`found:fibration-boundary-assembly`, B:7549–7575). The row on an enhanced boundary chain is
`BoundaryGaf02ChainE.fc43_row_BGR` (lane B-BCG-ROWS): the E-free collar block of the export packet
(`fc43_collar_block_FCF`), the BCG03 exits of the chain with the whole fibre types, BCG04 (E1 / E2)
and BCG06 (the STRONG torus-core exit and the two-branch geometric output), with the A4 output
`(Bs, WF)` as DATA. `fc43_row_FCW` replaces that data by its EXISTENCE: on a given enhanced
boundary chain `C` (a non-empty boundary chain: A2-mk, `exists_boundaryGaf02ChainE_mk_BAUGD`,
produces one on every augmented data, see `fc43_row_of_mk_BGR` for that quantifier structure) an
A4 output exists (`hA4`, the statement of BAUG-D's `exists_boundaryGaf02BasesV2_BAUGD`, to be
delivered), and then the FULL FC43 row holds on that chain for the A4 output and every `r_∂` block
with `θ < 1/100`.

* **`BoundaryGaf02ChainE.fc43_row_FCW`**: `∃ Bs WF`, `∀ rd …`, `type_of% (C.fc43_row_BGR …)`.

Not in the tree (the two producers outside this wrapper): `DP` for every supply
(`exists_boundaryAugmentedDataP_BAUGC`, BAUG-C G7b after the circle port) and `hA4`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **FC43, the full row from the existence of an A4 output** (B:7549–7575): on an enhanced
boundary chain `C` that has an A4 output `(Bs, WF)` (`hA4`), for every `r_∂` block with
`θ < 1/100` the whole FC43 row `C.fc43_row_BGR` holds on it. -/
theorem fc43_row_FCW
    (hA4 : ∃ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2 C.toChain Bs) :
    ∃ Bs : BoundaryGaf02BasesV2 C.toChain, ∃ WF : BoundaryWholeFiberSpecV2 C.toChain Bs,
      ∀ {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
        (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
        (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
        (hθ : θ < 1 / 100),
        type_of% (C.fc43_row_BGR WF hrd hrd4 hrdc hprem hθ) := by
  obtain ⟨Bs, WF⟩ := hA4
  exact ⟨Bs, WF, fun hrd hrd4 hrdc hprem hθ => C.fc43_row_BGR WF hrd hrd4 hrdc hprem hθ⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse

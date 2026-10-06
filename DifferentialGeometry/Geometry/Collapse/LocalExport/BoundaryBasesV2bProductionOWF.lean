import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeChartOWF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeLayerConsumerOWF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesV2bAssembly
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimChart
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySourceBufferedConsumer

/-!
# O-WF G8: A4 WHOLE — the v2 BASES exit with its v2b whole-fibre layer on every enhanced chain

**`BoundaryGaf02ChainE.exists_boundaryGaf02BasesV2b_OWF`**: on every enhanced boundary chain
`C : BoundaryGaf02ChainE DP …` (the production chains of `exists_boundaryGaf02ChainE_v3_BAUGD`),
under register premises only,
`∃ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs`.

It is S-BAUG-D2's parts assembly `exists_boundaryGaf02BasesV2b_of_parts_BAUGD` (G19b) with every
argument instantiated, on S-BASES-PORT2's core `Bc := C.basesCore_BBP …`:
plateau `baseSource_plateau_BBP`, bases `baseSet_eq_later_native_BBP`, no merging
`basesCore_hemb_OWF` (circle O-WF G2, edge G6, slim `later_isEmbedding_two_BBP`), the open edge
parent `C.edgeParentSet_OWF` with `hcut / hsub / hrk` (G6), the whole-fibre charts
`circle_chart_OWF` (G2), `slim_chart_OWF` (G3), `edge_chart_OWF` (G7) and the source buffer
`basesCore_source_buffered_OWF` (G5a).

Register premises: `β₂ ≤ 10⁻⁷`, `γ ≤ 1/2`, `γ + β₂ < 1/10`, `5 ≤ K`, `32·10⁶Δ ≤ n` (S-REG-NUM2
G4b discharges these), and the edge (EDP03/EDP04) premises `μ, τ ≤ 10⁻⁸`, `σc ≤ 10⁻³`,
`b ≤ 1/(1000Δ)`, `c₃ < 10⁻⁵`, N76-9, `0 ≤ ε < 1`, `0 < γc ≤ 1/100`, `βc ≤ 10⁻⁵`.
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

local notation "E3" => EuclideanSpace ℝ (Fin 3)

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

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
/-- **A4 whole (v2b)** on every enhanced boundary chain (see the module docstring). -/
theorem exists_boundaryGaf02BasesV2b_OWF (hβ2 : β 2 ≤ 1 / 10000000) (hγ : γ ≤ 1 / 2)
    (hd : γ + β 2 < 1 / 10) (hK : 5 ≤ K) (hn : 32 * (1000000 * Δ) ≤ (n : ℝ))
    (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000)
    (hb : b ≤ 1 / (1000 * Δ)) (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000) :
    ∃ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs := by
  have hσ : σc ≤ 1 / 4 := by linarith
  have hc' : c 2 < 1 / 1000 := by linarith
  obtain ⟨hU, hcut, hsub, hrk⟩ :=
    C.basesCore_edgeParent_OWF hβ2 hγ hμ hτ hσc hb hc hC hε0 hε hγc hγc1 hβc1
  exact C.exists_boundaryGaf02BasesV2b_of_parts_BAUGD hc hC hε0 hε hγc hγc1 hβc1
    (C.basesCore_BBP hβ2 hγ hσ hb) (fun st _ hp => C.baseSource_plateau_BBP st hp)
    C.baseSet_eq_later_native_BBP
    (C.basesCore_hemb_OWF hβ2 hγ hd hμ hτ hσc hb hc hC hε0 hε hγc hγc1 hβc1)
    C.edgeParentSet_OWF hU hcut hsub hrk
    (fun _ hy => C.circle_chart_OWF hc' hβ2 hγ hd hy)
    (fun _ hy => C.slim_chart_OWF hc' hK hy)
    (fun _ hy => C.edge_chart_OWF hμ hτ hσc hb hc hC hε0 hε hγc hγc1 hβc1 hy)
    (C.basesCore_source_buffered_OWF hβ2 hγ hσ hb hn)

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse

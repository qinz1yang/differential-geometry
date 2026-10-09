import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesV2bProductionOWF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRowsFinalApplicationsBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryV2bConsumersBGR

/-!
# O-WF G9: FC43 without the A4 hypothesis

The FC43 rows of lanes S-BCG-ROWS (`fc43_rowAll_V2b_BGR`, chain form) and
`fc43_row_of_chain_V2b_BGR` (non-empty chain form) took A4's output as the hypothesis `hA4`; here
`hA4` is A4 WHOLE (`exists_boundaryGaf02BasesV2b_OWF`, O-WF G8), so only register premises remain.
Two separate declarations (S-FC-WRAP2's design: the statement is read off by `type_of%`, the
production chain enters only through the non-emptiness hypothesis of the second form):

* **`BoundaryGaf02ChainE.fc43_row_OWF`**: on every enhanced boundary chain, `∃ Bs WF, FC43 block ∧
  BCG03 ∧ BCG04 ∧ BCG06` (the conclusion of `fc43_rowAll_V2b_BGR`);
* **`fc43_row_of_nonempty_OWF`**: the same on a non-empty type of enhanced chains (the conclusion
  of the production A2 v3 `exists_boundaryGaf02ChainE_v3_BAUGD`), the conclusion of
  `fc43_row_of_chain_V2b_BGR`.

Premises: A4's register premises (`β₂ ≤ 10⁻⁷`, `γ ≤ 1/2`, `γ + β₂ < 1/10`, `5 ≤ K`,
`32·10⁶Δ ≤ n`, `μ, τ ≤ 10⁻⁸`, `σc ≤ 10⁻³`, `b ≤ 1/(1000Δ)`, `c₃ < 10⁻⁵`, N76-9, `0 ≤ ε < 1`,
`0 < γc ≤ 1/100`, `βc ≤ 10⁻⁵`) and FC43's own `r_∂` block with `θ < 1/100`.
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
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **FC43 on every enhanced boundary chain, without `hA4`** (see the module docstring). -/
theorem fc43_row_OWF (hβ2 : β 2 ≤ 1 / 10000000) (hγ : γ ≤ 1 / 2)
    (hd : γ + β 2 < 1 / 10) (hK : 5 ≤ K) (hn : 32 * (1000000 * Δ) ≤ (n : ℝ))
    (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000)
    (hb : b ≤ 1 / (1000 * Δ)) (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    type_of% (C.fc43_rowAll_V2b_BGR (C.exists_boundaryGaf02BasesV2b_OWF hβ2 hγ hd hK hn hμ hτ
      hσc hb hc hC hε0 hε hγc hγc1 hβc1) hrd hrd4 hrdc hprem hθ) :=
  C.fc43_rowAll_V2b_BGR (C.exists_boundaryGaf02BasesV2b_OWF hβ2 hγ hd hK hn hμ hτ hσc hb hc hC
    hε0 hε hγc hγc1 hβc1) hrd hrd4 hrdc hprem hθ

end BoundaryGaf02ChainE

/-- **FC43 on a non-empty type of enhanced chains, without `hA4`** (see the module docstring). -/
theorem fc43_row_of_nonempty_OWF
    (h : Nonempty (BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj))
    (hβ2 : β 2 ≤ 1 / 10000000) (hγ : γ ≤ 1 / 2)
    (hd : γ + β 2 < 1 / 10) (hK : 5 ≤ K) (hn : 32 * (1000000 * Δ) ≤ (n : ℝ))
    (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000)
    (hb : b ≤ 1 / (1000 * Δ)) (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    type_of% (fc43_row_of_chain_V2b_BGR h (fun C => C.exists_boundaryGaf02BasesV2b_OWF hβ2 hγ hd
      hK hn hμ hτ hσc hb hc hC hε0 hε hγc hγc1 hβc1) hrd hrd4 hrdc hprem hθ) :=
  fc43_row_of_chain_V2b_BGR h (fun C => C.exists_boundaryGaf02BasesV2b_OWF hβ2 hγ hd hK hn hμ hτ
    hσc hb hc hC hε0 hε hγc hγc1 hβc1) hrd hrd4 hrdc hprem hθ

end DifferentialGeometry.Geometry.Collapse

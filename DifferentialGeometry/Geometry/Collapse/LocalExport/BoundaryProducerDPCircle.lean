import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortCircleTableFinal
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryProducerDPCircleOfPort

/-!
# ProducerDP v3.1, the CIRCLE stage table (lane BAUG-C, group G6b)

`exists_boundaryCircleTable_BAUGC` (ProducerDP v3.1 circle statement,
`docs/geometrization/chapter14/evidence/boundary/ProducerDP-v3.1.lean.txt`): the circle stage table
of the actual slot v2 with its spec V3, unconditionally — `exists_boundaryCircleTable_of_port_BAUGC`
(G6a) applied to the delivered circle port theorem `port_circle_interior_table_BAUGP`
(PortTargets v3.1).
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
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **The CIRCLE stage table of the actual slot v2 with its spec V3** (ProducerDP v3.1, N76-7
`0 ≤ θ`, (R2) dropped as unused): the boundary `exists_firstStagePlanes_PLN`. -/
theorem exists_boundaryCircleTable_BAUGC {ν Γ sg eg : ℝ} (hΓ : 0 < Γ) (hΓ1 : Γ < 1)
    (hsg : 0 < sg) (hsgΓ : sg < Γ / 250)
    (hsgC : sg < Γ ^ 3 / (125 * (tcpGraphConst + 2 * bmConst_BAUGC)))
    (heg : 0 < eg) (heg1 : eg < 1 / 100) (hegΓ : eg < Γ * sg / 100) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ γ₀ ηc θt : ℝ, 0 < η₂ ∧ 0 < γ₀ ∧
    0 < ηc ∧ 0 < θt ∧ θt < 1 ∧ ∀ Δ : ℝ, 1200 ≤ Δ → ∃ η₁ : ℝ, 0 < η₁ ∧
    ∀ {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
      {βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
      {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
      {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {n : ℕ}
      {B : NearlyCuspidalBoundary W g K δn}
      {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
      (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
        θ W g δn n B oM),
      -- circle port block (PortTargets v3.1, port_circle_interior_table_BAUGP), eg ↦ eg / 2
      0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 10 ^ 6 * Δ * Λ < 1 / 10 ^ 5 →
      4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      0 ≤ ε → ε ≤ 1 → 0 ≤ σc → σc ≤ θt ^ 2 / 1000 → μ * Δ ≤ θt / 100 →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → γ ≤ γ₀ → 0 < γc → γc ≤ γ₀ → βc ≤ ηc →
      b ≤ η₁ → β 1 ≤ η₁ → 0 < σs → σs ≤ θt ^ 2 / 1000 → vs ≤ θt / 100 → 0 < ζ →
      ζ ≤ θt ^ 2 / 1000 → εr ≤ θt / 100 → 20 * Λz ≤ T → σ⁻¹ ≤ Lmax →
      1000 * tcpGraphConst * Δ * Λ < eg / 2 →
      0 < Δ → 100 * Δ * Λ ≤ 1 / 100 → 0 ≤ V → 0 < β 1 → 0 < b → e ≤ 1 / 10 →
      -- transfer budget: N76-7 `0 ≤ θ` and (R1)
      0 ≤ θ → 16 * bmConst_BAUGC * θ ≤ eg →
      S.SeparatedCollarZero_BIF →
      ∃ R : BoundaryStageReferences_BIF (actualSlotsV2_BAUGD S) 0 ℝ² S.circleEta_BIF
        S.circleRow_BIF, BoundaryEnhancedPlaneSpecV3 R Γ sg eg :=
  exists_boundaryCircleTable_of_port_BAUGC
    (by
      intro ν' Γ' sg' eg' hΓ' _ hsg' hsgΓ' _ heg' heg1' _ hν' hν1'
      exact port_circle_interior_table_BAUGP hΓ' hsg' hsgΓ' heg' heg1' hν' hν1')
    hΓ hΓ1 hsg hsgΓ hsgC
    heg heg1 hegΓ hν hν1

end DifferentialGeometry.Geometry.Collapse

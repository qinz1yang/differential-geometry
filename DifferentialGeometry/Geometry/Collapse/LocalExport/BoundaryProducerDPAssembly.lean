import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortCircleTableFinal
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryProducerDPAssemblyOfPort

/-!
# ProducerDP v3.1, the assembly (lane BAUG-C, group G7b)

`exists_boundaryAugmentedDataP_BAUGC`: the three stage tables with their specs V3 on ONE actual
slot v2 as `BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg` (A2's DP input),
unconditionally: `exists_boundaryAugmentedDataP_of_circlePort_BAUGC` (G7a) applied to the delivered
circle port theorem `port_circle_interior_table_BAUGP`. Strengthened against the frozen v3.1
statement by dropping the unused `eg 1 < Σ₁/1000`; the verbatim v3.1 form is the `example`.
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

/-- **The assembly of ProducerDP v3.1** (N76-7 `0 ≤ θ`, (R2) and `eg 1 < Σ₁/1000` dropped as
unused): the three stage tables with their specs V3 as `BoundaryAugmentedDataPV3`. -/
theorem exists_boundaryAugmentedDataP_BAUGC
    {ν : ℝ} {Γ Sg eg : Fin 3 → ℝ} (hΓ : ∀ j, 0 < Γ j) (hΓ1 : ∀ j, Γ j < 1)
    (hsg : ∀ j, 0 < Sg j) (hsgΓ : ∀ j, Sg j < Γ j / 250)
    (hsgC0 : Sg 0 < Γ 0 ^ 3 / (125 * (tcpGraphConst + 2 * bmConst_BAUGC)))
    (hsgC1 : Sg 1 < Γ 1 ^ 3 / (125 * (egpGraphConst + 2 * bmConst_BAUGC)))
    (hsgC2 : Sg 2 < Γ 2 ^ 3 / (125 * (sgpGraphBound + 2 * bmConst_BAUGC)))
    (heg : ∀ j, 0 < eg j) (heg1 : ∀ j, eg j < 1 / 100) (hegΓ : ∀ j, eg j < Γ j * Sg j / 100)
    (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ γ₀ ηc θt : ℝ, 0 < η₂ ∧ 0 < γ₀ ∧
    0 < ηc ∧ 0 < θt ∧ θt < 1 ∧
    ∀ β₂ : ℝ, 0 < β₂ → β₂ < 1 / 1000000 → ∀ Δ : ℝ, 1200 ≤ Δ →
    ∃ η₁ θs Lc η₀ : ℝ, 0 < η₁ ∧ 0 < θs ∧ θs < 1 ∧ 0 < Lc ∧ 0 < η₀ ∧
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
      1000 * tcpGraphConst * Δ * Λ < eg 0 / 2 →
      0 < Δ → 100 * Δ * Λ ≤ 1 / 100 → 0 ≤ V → 0 < β 1 → 0 < b → e ≤ 1 / 10 →
      -- edge port block (PortTargets v3.1, port_edge_interior_table_BAUGP), eg ↦ eg / 2
      b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax →
      σc ≤ (eg 1 / 2 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
      μ * Δ < eg 1 / 2 / (20 * egpGraphConst) / 100 →
      0 < σs → σs ≤ (eg 1 / 2 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
      vs < eg 1 / 2 / (20 * egpGraphConst) / 100 → 0 < ζ →
      ζ ≤ (eg 1 / 2 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 → ζ ≤ 1 / (1000 * (1000000 * Δ)) →
      εr < eg 1 / 2 / (20 * egpGraphConst) / (100 * (1000000 * Δ)) → β 2 = β₂ →
      -- slim port block (PortTargets v3.1, port_slim_interior_table_BAUGP; `0 < σs`, `0 < ζ` above)
      σs < θs ^ 2 / 10 ^ 6 → vs < θs / 100 →
      ζ < θs ^ 2 / 10 ^ 6 → ζ < 1 / (100 * (1000000 * Δ)) →
      εr < θs / (100 * (1000000 * Δ)) → 0 ≤ εr →
      -- transfer budget: N76-7 `0 ≤ θ` and (R1) at every stage
      0 ≤ θ → (∀ j, 16 * bmConst_BAUGC * θ ≤ eg j) →
      S.SeparatedCollarZero_BIF →
      Nonempty (BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg) :=
  exists_boundaryAugmentedDataP_of_circlePort_BAUGC
    (by
      intro ν' Γ' sg' eg' hΓ' _ hsg' hsgΓ' _ heg' heg1' _ hν' hν1'
      exact port_circle_interior_table_BAUGP hΓ' hsg' hsgΓ' heg' heg1' hν' hν1')
    hΓ hΓ1 hsg
    hsgΓ hsgC0 hsgC1 hsgC2 heg heg1 hegΓ hν hν1

/-- The frozen ProducerDP v3.1 form (with `eg 1 < Σ₁/1000`) from the strengthened theorem. -/
example
    {ν : ℝ} {Γ Sg eg : Fin 3 → ℝ} (hΓ : ∀ j, 0 < Γ j) (hΓ1 : ∀ j, Γ j < 1)
    (hsg : ∀ j, 0 < Sg j) (hsgΓ : ∀ j, Sg j < Γ j / 250)
    (hsgC0 : Sg 0 < Γ 0 ^ 3 / (125 * (tcpGraphConst + 2 * bmConst_BAUGC)))
    (hsgC1 : Sg 1 < Γ 1 ^ 3 / (125 * (egpGraphConst + 2 * bmConst_BAUGC)))
    (hsgC2 : Sg 2 < Γ 2 ^ 3 / (125 * (sgpGraphBound + 2 * bmConst_BAUGC)))
    (heg : ∀ j, 0 < eg j) (heg1 : ∀ j, eg j < 1 / 100) (hegΓ : ∀ j, eg j < Γ j * Sg j / 100)
    (hegS1 : eg 1 < Sg 1 / 1000) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ γ₀ ηc θt : ℝ, 0 < η₂ ∧ 0 < γ₀ ∧
    0 < ηc ∧ 0 < θt ∧ θt < 1 ∧
    ∀ β₂ : ℝ, 0 < β₂ → β₂ < 1 / 1000000 → ∀ Δ : ℝ, 1200 ≤ Δ →
    ∃ η₁ θs Lc η₀ : ℝ, 0 < η₁ ∧ 0 < θs ∧ θs < 1 ∧ 0 < Lc ∧ 0 < η₀ ∧
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
      1000 * tcpGraphConst * Δ * Λ < eg 0 / 2 →
      0 < Δ → 100 * Δ * Λ ≤ 1 / 100 → 0 ≤ V → 0 < β 1 → 0 < b → e ≤ 1 / 10 →
      -- edge port block (PortTargets v3.1, port_edge_interior_table_BAUGP), eg ↦ eg / 2
      b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax →
      σc ≤ (eg 1 / 2 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
      μ * Δ < eg 1 / 2 / (20 * egpGraphConst) / 100 →
      0 < σs → σs ≤ (eg 1 / 2 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
      vs < eg 1 / 2 / (20 * egpGraphConst) / 100 → 0 < ζ →
      ζ ≤ (eg 1 / 2 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 → ζ ≤ 1 / (1000 * (1000000 * Δ)) →
      εr < eg 1 / 2 / (20 * egpGraphConst) / (100 * (1000000 * Δ)) → β 2 = β₂ →
      -- slim port block (PortTargets v3.1, port_slim_interior_table_BAUGP; `0 < σs`, `0 < ζ` above)
      σs < θs ^ 2 / 10 ^ 6 → vs < θs / 100 →
      ζ < θs ^ 2 / 10 ^ 6 → ζ < 1 / (100 * (1000000 * Δ)) →
      εr < θs / (100 * (1000000 * Δ)) → 0 ≤ εr →
      -- transfer budget: N76-7 `0 ≤ θ` and (R1) at every stage
      0 ≤ θ → (∀ j, 16 * bmConst_BAUGC * θ ≤ eg j) →
      S.SeparatedCollarZero_BIF →
      Nonempty (BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg) :=
  (fun _ => exists_boundaryAugmentedDataP_BAUGC hΓ hΓ1 hsg hsgΓ hsgC0 hsgC1 hsgC2 heg heg1 hegΓ
    hν hν1) hegS1

end DifferentialGeometry.Geometry.Collapse

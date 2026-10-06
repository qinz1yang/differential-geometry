import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainEProducerOfDP
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryProducerDPAssembly

/-!
# A2 v3 (production): the non-empty enhanced boundary chain (BAUG-D, group G18b; by S-BAUG-C2)

`exists_boundaryGaf02ChainE_v3_BAUGD`: A2 v3 of the A-v3.1 text (with `0 ≤ θ` before (R1), without
(R2); strengthened as `exists_boundaryGaf02ChainE_of_dp_BAUGD`) with ProducerDP v3.1 supplied by
BAUG-C's unconditional assembly `exists_boundaryAugmentedDataP_BAUGC` (G7b): no `hDP`, no `hport`.
It replaces the conditional stand-in `exists_boundaryGaf02ChainE_of_circlePort_BAUGD` (G18,
S-BAUG-D2) by composing `exists_boundaryGaf02ChainE_of_dp_BAUGD` (G15) with G7b; the conclusion
carries the non-emptiness clause `∀ st, ∃ O, C.toChain.slot st = .active O` that the counts
BCG04 / 05 / 06 consume. The verbatim A-v3.1 form with (R2) is the `example`.
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

/-- **A2 v3 (production): the non-empty enhanced boundary chain on BAUG-C's DP assembly**
(`exists_boundaryAugmentedDataP_BAUGC`). -/
theorem exists_boundaryGaf02ChainE_v3_BAUGD (Kj : ℕ) {cadj ν : ℝ} (hcadj : 0 < cadj)
    (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ (Ξ Γ Sg eg c cw : Fin 3 → ℝ),
      BoundaryChainChoiceValidity_BAUGD Ξ Γ Sg eg c cw cadj ∧
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
        (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
          Λz θ W g δn n B oM),
        -- BEGIN premise block
        -- (i)+(ii) the uniform register block (A2-mk's, verbatim)
        0 ≤ Λ → 0 < Δ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 100 * Δ * Λ ≤ 1 / 100 → 0 ≤ V → 0 < β 1 →
        0 < b → e ≤ 1 / 10 → 1 ≤ Δ → 1000000 * Δ * Λ < 1 / 100000 →
        4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
        σs ∈ Icc (0 : ℝ) 1 → σc ∈ Icc (0 : ℝ) 1 → γc ∈ Icc (0 : ℝ) 1 → εr ∈ Icc (0 : ℝ) 1 →
        -- (iii) ProducerDP v3's premise block (verbatim)
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
        -- slim port block (PortTargets v3.1, port_slim_interior_table_BAUGP; 0 < σs, 0 < ζ above)
        σs < θs ^ 2 / 10 ^ 6 → vs < θs / 100 →
        ζ < θs ^ 2 / 10 ^ 6 → ζ < 1 / (100 * (1000000 * Δ)) →
        εr < θs / (100 * (1000000 * Δ)) → 0 ≤ εr →
        -- N76-7 and the transfer budget (R1) at every stage
        0 ≤ θ → (∀ j, 16 * bmConst_BAUGC * θ ≤ eg j) →
        -- END premise block
        S.SeparatedCollarZero_BIF →
        ∃ DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg,
          ∃ C : BoundaryGaf02ChainE DP Kj Ξ c cw boundaryChainCutoffConst_BAUGD
              boundaryDerivBound_BDFB cutoffKappa_BAUGP2 cadj,
            ∀ st, ∃ O, C.toChain.slot st = .active O := by
  exact exists_boundaryGaf02ChainE_of_dp_BAUGD Kj hcadj hν hν1
    (fun {Γ Sg eg} hΓ hΓ1 hsg hsgΓ hsgC0 hsgC1 hsgC2 heg heg1 hegΓ _ hν' hν1' =>
      exists_boundaryAugmentedDataP_BAUGC hΓ hΓ1 hsg hsgΓ hsgC0 hsgC1 hsgC2 heg heg1 hegΓ hν'
        hν1')

/-- The VERBATIM premise block of the A-v3.1 text plus `0 ≤ θ` (with (R2)), from the strengthened
production theorem (R2 unused). -/
example (Kj : ℕ) {cadj ν : ℝ} (hcadj : 0 < cadj)
    (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ (Ξ Γ Sg eg c cw : Fin 3 → ℝ),
      BoundaryChainChoiceValidity_BAUGD Ξ Γ Sg eg c cw cadj ∧
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
        (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
          Λz θ W g δn n B oM),
        -- BEGIN premise block
        -- (i)+(ii) the uniform register block (A2-mk's, verbatim)
        0 ≤ Λ → 0 < Δ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 100 * Δ * Λ ≤ 1 / 100 → 0 ≤ V → 0 < β 1 →
        0 < b → e ≤ 1 / 10 → 1 ≤ Δ → 1000000 * Δ * Λ < 1 / 100000 →
        4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
        σs ∈ Icc (0 : ℝ) 1 → σc ∈ Icc (0 : ℝ) 1 → γc ∈ Icc (0 : ℝ) 1 → εr ∈ Icc (0 : ℝ) 1 →
        -- (iii) ProducerDP v3's premise block (verbatim)
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
        -- slim port block (PortTargets v3.1, port_slim_interior_table_BAUGP; 0 < σs, 0 < ζ above)
        σs < θs ^ 2 / 10 ^ 6 → vs < θs / 100 →
        ζ < θs ^ 2 / 10 ^ 6 → ζ < 1 / (100 * (1000000 * Δ)) →
        εr < θs / (100 * (1000000 * Δ)) → 0 ≤ εr →
        -- N76-7 and the transfer budget (R1) at every stage
        0 ≤ θ → (∀ j, 16 * bmConst_BAUGC * θ ≤ eg j) →
        1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * (1 / 8) ^ 2 →
        -- END premise block
        S.SeparatedCollarZero_BIF →
        ∃ DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg,
          ∃ C : BoundaryGaf02ChainE DP Kj Ξ c cw boundaryChainCutoffConst_BAUGD
              boundaryDerivBound_BDFB cutoffKappa_BAUGP2 cadj,
            ∀ st, ∃ O, C.toChain.slot st = .active O := by
  obtain ⟨Ξ, Γ, Sg, eg, c, cw, hval, σ, hσ, hσ1, η₂, γ₀, ηc, θt, hη₂, hγ₀, hηc, hθt, hθt1, hP⟩ :=
    exists_boundaryGaf02ChainE_v3_BAUGD Kj hcadj hν hν1
  refine ⟨Ξ, Γ, Sg, eg, c, cw, hval, σ, hσ, hσ1, η₂, γ₀, ηc, θt, hη₂, hγ₀, hηc, hθt, hθt1,
    fun β₂ hβ₂ hβ₂' Δ hΔ => ?_⟩
  obtain ⟨η₁, θs, Lc, η₀, hη₁, hθs, hθs1, hLc, hη₀, hP'⟩ := hP β₂ hβ₂ hβ₂' Δ hΔ
  refine ⟨η₁, θs, Lc, η₀, hη₁, hθs, hθs1, hLc, hη₀, ?_⟩
  intro K A β βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W _ g δn n B oM S
    r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
    c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26
    c27 c28 c29 c30 c31 c32 c33 c34 c35 c36
    d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
    f1 f2 f3 f4 f5 f6 hθ h1 _ hsep
  exact hP' S r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
    c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26
    c27 c28 c29 c30 c31 c32 c33 c34 c35 c36
    d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
    f1 f2 f3 f4 f5 f6 hθ h1 hsep

end DifferentialGeometry.Geometry.Collapse

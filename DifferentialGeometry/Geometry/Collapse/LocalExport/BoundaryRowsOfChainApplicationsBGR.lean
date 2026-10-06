import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRowsOfChainBGR

/-!
# Consumer of the row packages on a non-empty chain (S-BCG-ROWS2 G24')

On BAUG-D's enhanced-chain inhabitant (A2-mk v3's numbers, separated supply, EMPTY stage families:
the only non-empty chain available until the production A2 v3, S-BAUG-D2 G18, lands) the three
packages `bcg04_row_of_chain_BGR`, `bcg05_row_of_chain_BGR`, `bcg06_row_of_chain_BGR` apply, and
their headline clauses (isolation; marker exactly `1` on `Safe_b`; `frontier C_b = H_b` for every
component) are read off.
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

/-- **Consumer on the enhanced-chain inhabitant**: on the empty-family chain of A2-mk v3, the
BCG04 isolation clause, the BCG05 exact marker `1` on `Safe_b`, and `frontier C_b = H_b` for every
component (BCG06) hold, each read off its row package. -/
theorem exists_chainE_rows_of_empty_BAUGD_BGR (Kj : ℕ) {cadj : ℝ} (hcadj : 0 < cadj) :
    ∃ (Ξ Γ Sg eg c cw : Fin 3 → ℝ), BoundaryChainChoiceValidity_BAUGD Ξ Γ Sg eg c cw cadj ∧
      ∀ {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
        {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
        {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
        {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {n : ℕ}
        {B : NearlyCuspidalBoundary W g K δn}
        {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
        (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
          Λz θ W g δn n B oM),
        0 ≤ Λ → 0 < Δ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 100 * Δ * Λ ≤ 1 / 100 → 0 ≤ V → 0 < β 1 →
        0 < b → e ≤ 1 / 10 → 1 ≤ Δ → 1000000 * Δ * Λ < 1 / 100000 →
        4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
        σs ∈ Icc (0 : ℝ) 1 → σc ∈ Icc (0 : ℝ) 1 → γc ∈ Icc (0 : ℝ) 1 → εr ∈ Icc (0 : ℝ) 1 →
        S.SeparatedCollarZero_BIF → (∀ st, S.stageCentres_BIF st = ∅) →
        ∀ {rd : ℝ}, 0 < rd → rd < 1 / 10000 → 20 * (c 2 + 1) * rd < 1 / 1000000 →
        1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2 →
        θ < 1 / 100 →
        ∃ DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg,
          (∃ C : BoundaryGaf02ChainE DP Kj Ξ c cw boundaryChainCutoffConst_BAUGD
              boundaryDerivBound_BDFB cutoffKappa_BAUGP2 cadj,
            ∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier), 20 * rd < S.rho p →
              augmentedBoundaryCoord_BC7C i (C.toChain.stage k p) = (0, 0) ∧
                S.packet.toBoundaryCollarPacket.block i p = (0, 0)) ∧
          (∃ C : BoundaryGaf02ChainE DP Kj Ξ c cw boundaryChainCutoffConst_BAUGD
              boundaryDerivBound_BDFB cutoffKappa_BAUGP2 cadj,
            ∀ (k : Fin 4) (i : Fin S.packet.cusp.count),
              ∀ p ∈ S.packet.toBoundaryCollarPacket.safeBand_BAUGA i,
                (augmentedBoundaryCoord_BC7C i (C.toChain.stage k p)).2 = 1) ∧
          (∃ C : BoundaryGaf02ChainE DP Kj Ξ c cw boundaryChainCutoffConst_BAUGD
              boundaryDerivBound_BDFB cutoffKappa_BAUGP2 cadj,
            ∀ i : Fin S.packet.cusp.count,
              frontier (C.toChain.cuspCore_BIF i) = C.toChain.cuspFront_BIF i) := by
  obtain ⟨Ξ, Γ, Sg, eg, c, cw, hval, h⟩ := exists_boundaryGaf02ChainE_of_empty_BAUGD Kj hcadj
  refine ⟨Ξ, Γ, Sg, eg, c, cw, hval, ?_⟩
  intro K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W _ g δn n B oM S
    hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he hΔ1 hLΛ hLmax he40 hT hσs hσc hγc hεr hsep hempty rd hrd hrd4
    hrdc hprem hθ
  obtain ⟨DP, hC⟩ := h S hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he hΔ1 hLΛ hLmax he40 hT hσs hσc hγc hεr
    hsep hempty
  refine ⟨DP, ?_, ?_, ?_⟩
  · obtain ⟨C, h4⟩ := bcg04_row_of_chain_BGR hC hrd hprem
    exact ⟨C, h4.1.1⟩
  · obtain ⟨C, h5⟩ := bcg05_row_of_chain_BGR hC hrd hrd4 hprem hθ
    exact ⟨C, h5.1⟩
  · obtain ⟨C, h6⟩ := bcg06_row_of_chain_BGR hC hrd hrd4 hrdc hprem hθ
    exact ⟨C, fun i => (h6.1.1 i).relative_frontier_eq⟩

end DifferentialGeometry.Geometry.Collapse

import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoresLevelBGR

/-!
# Consumer of BD0 with E4c (level variant) delivered: the empty-family enhanced chain (G30)

On BAUG-D's enhanced-chain inhabitant (A2-mk v3's numbers, separated supply, EMPTY stage families)
the cusp pieces exist: for every `r_∂` block with `θ < 1/100` there are augmented data, a chain on
them, and for each boundary component a `PieceEmbedding` with `range = C_b`, end `0` onto `∂_bW`,
end `1` onto the front `H_b`, and BCG6-K's level affine along the product (the half-collar input).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
  GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **Consumer on the enhanced-chain inhabitant**: the cusp pieces of the same product exist. -/
theorem exists_chainE_cuspPieces_of_empty_BAUGD_BGR (Kj : ℕ) {cadj : ℝ} (hcadj : 0 < cadj) :
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
          ∃ C : BoundaryGaf02ChainE DP Kj Ξ c cw boundaryChainCutoffConst_BAUGD
            boundaryDerivBound_BDFB cutoffKappa_BAUGP2 cadj,
            ∃ (piece : Fin S.packet.cusp.count → PieceEmbedding W)
              (product : ∀ i, (Torus × Icc (0 : ℝ) 1) ≃ₘ⟮torusModel.prod (𝓡∂ 1), 𝓡∂ 3⟯
                (piece i).Piece),
              (∀ i, range (piece i).map = C.toChain.cuspCore_BIF i) ∧
              (∀ i, (range fun t : Torus => (piece i).map (product i (t, iccEnd false))) =
                S.packet.cusp.component i) ∧
              (∀ i, (range fun t : Torus => (piece i).map (product i (t, iccEnd true))) =
                C.toChain.cuspFront_BIF i) ∧
              ∀ i, ∃ a : ℝ, a < 40 ∧ ∀ p, S.packet.toBoundaryCollarPacket.coreLevel_BCG6K i
                (chainBoundaryU_BCG6K C.toChain.E i) ((piece i).map (product i p)) =
                  a + (40 - a) * (p.2 : ℝ) := by
  obtain ⟨Ξ, Γ, Sg, eg, c, cw, hval, h⟩ := exists_boundaryGaf02ChainE_of_empty_BAUGD Kj hcadj
  refine ⟨Ξ, Γ, Sg, eg, c, cw, hval, ?_⟩
  intro K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W _ g δn n B oM S
    hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he hΔ1 hLΛ hLmax he40 hT hσs hσc hγc hεr hsep hempty rd hrd hrd4
    hrdc hprem hθ
  obtain ⟨DP, ⟨C⟩⟩ := h S hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he hΔ1 hLΛ hLmax he40 hT hσs hσc hγc hεr
    hsep hempty
  obtain ⟨piece, product, h1, h2, h3, h4, -⟩ := C.cuspCoresDataLevel_BGR hrd hrd4 hrdc hprem hθ
  exact ⟨DP, C, piece, product, h1, h2, h3, h4⟩

end DifferentialGeometry.Geometry.Collapse

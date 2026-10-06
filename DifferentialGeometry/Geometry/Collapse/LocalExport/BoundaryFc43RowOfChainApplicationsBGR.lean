import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryFc43RowOfChainBGR

/-!
# Consumer of `fc43_row_of_chain_BGR` (S-BCG-ROWS2 G27)

On BAUG-D's enhanced-chain inhabitant (A2-mk v3's numbers, separated supply, EMPTY stage families:
the only non-empty chain available until the production A2 v3 lands) the FC43 package applies as
soon as A4 (`hA4`: v2 bases with the whole-fibre layer on every chain over every augmented data) is
supplied; the headline clauses (whole slim fibres `S²` / `T²`, BCG06's strong exit for every
component) are read off.
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

/-- **Consumer on the enhanced-chain inhabitant**: on the empty-family chain of A2-mk v3, given A4
for every chain over every augmented data, FC43 holds on one chain and one A4 output: its whole slim
fibres are `S²` or `T²` and every boundary component has BCG06's strong exit. -/
theorem exists_chainE_fc43_of_empty_BAUGD_BGR (Kj : ℕ) {cadj : ℝ} (hcadj : 0 < cadj) :
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
        (∀ (DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg)
          (C : BoundaryGaf02ChainE DP Kj Ξ c cw boundaryChainCutoffConst_BAUGD
            boundaryDerivBound_BDFB cutoffKappa_BAUGP2 cadj),
          ∃ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2 C.toChain Bs) →
        ∀ {rd : ℝ}, 0 < rd → rd < 1 / 10000 → 20 * (c 2 + 1) * rd < 1 / 1000000 →
        1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2 →
        θ < 1 / 100 →
        ∃ DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg,
          ∃ C : BoundaryGaf02ChainE DP Kj Ξ c cw boundaryChainCutoffConst_BAUGD
            boundaryDerivBound_BDFB cutoffKappa_BAUGP2 cadj,
            ∃ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2 C.toChain Bs ∧
              (∀ y ∈ Bs.base 2, Nonempty (Bs.fibre 2 y ≃ₜ Metric.sphere (0 : E3) 1) ∨
                Nonempty (Bs.fibre 2 y ≃ₜ Circle × Circle)) ∧
              ∀ i, S.packet.toBoundaryCollarPacket.BoundaryCuspCoreComponent_BCG6K
                (chainBoundaryU_BCG6K C.toChain.E) (chainBoundaryV_BCG6K C.toChain.E) i := by
  obtain ⟨Ξ, Γ, Sg, eg, c, cw, hval, h⟩ := exists_boundaryGaf02ChainE_of_empty_BAUGD Kj hcadj
  refine ⟨Ξ, Γ, Sg, eg, c, cw, hval, ?_⟩
  intro K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W _ g δn n B oM S
    hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he hΔ1 hLΛ hLmax he40 hT hσs hσc hγc hεr hsep hempty hA4 rd hrd hrd4
    hrdc hprem hθ
  obtain ⟨DP, hC⟩ := h S hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he hΔ1 hLΛ hLmax he40 hT hσs hσc hγc hεr
    hsep hempty
  obtain ⟨C, Bs, WF, hrow⟩ := fc43_row_of_chain_BGR hC (hA4 DP) hrd hrd4 hrdc hprem hθ
  exact ⟨DP, C, Bs, WF, hrow.2.1.2.2.2.2.1, hrow.2.2.2.1⟩

end DifferentialGeometry.Geometry.Collapse

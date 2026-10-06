import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreChainEBGR

/-!
# Consumers of the E series on the enhanced boundary chain (lane B-BCG-ROWS)

* the frozen `TargetsBoundary-v3.1` forms of E1 / E1' (with the unused `r_∂ < 10⁻⁴`,
  `20(c₂ + 1)r_∂ < 10⁻⁶`) and of E4 / E4b (with the unused `cadj ≤ 10⁻⁵`: N76-4 puts
  `c 2 < 10⁻⁵` into the CHOICE validity) as `example`s — the delivered theorems are stronger;
* **`exists_chainE_bcg06_strong_of_empty_BAUGD_BGR`**: on BAUG-D's enhanced-chain inhabitant
  (A2-mk v3's numbers, separated supply, empty stage families) the produced chain satisfies the
  STRONG BCG06 exit (every component) and the direct separated spec E4b.
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

section Frozen

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- Frozen E1 (v3.1 verbatim premises). -/
example : ∀ {rd : ℝ}, 0 < rd → rd < 1 / 10000 → 20 * (c 2 + 1) * rd < 1 / 1000000 →
    1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2 →
    (∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier), 20 * rd < S.rho p →
      augmentedBoundaryCoord_BC7C i (C.toChain.stage k p) = (0, 0) ∧
        S.packet.toBoundaryCollarPacket.block i p = (0, 0)) ∧
    (∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier),
      ‖S.boundaryBlockCLM_BAUGC i (C.toChain.stage k p) -
          S.boundaryBlockCLM_BAUGC i (S.boundaryOriginalMap p)‖ < 20 * c 2 * rd) ∧
    ∀ (i : Fin S.packet.cusp.count) (p : W.Carrier),
      ∀ z ∈ segment ℝ (S.boundaryOriginalMap p) (C.toChain.E p),
      ‖S.boundaryBlockCLM_BAUGC i z - S.boundaryBlockCLM_BAUGC i (S.boundaryOriginalMap p)‖ <
        20 * c 2 * rd :=
  fun hrd _ _ hprem => C.bcg04_on_boundary_chain_BGR hrd hprem

/-- Frozen E1' (v3.1 verbatim premises). -/
example : ∀ {rd : ℝ}, 0 < rd → rd < 1 / 10000 → 20 * (c 2 + 1) * rd < 1 / 1000000 →
    1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2 →
    ∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier),
      |(augmentedBoundaryCoord_BC7C i (C.toChain.stage k p)).1 -
          (S.packet.toBoundaryCollarPacket.block i p).1| < 20 * c 2 * rd ∧
      |(augmentedBoundaryCoord_BC7C i (C.toChain.stage k p)).2 -
          (S.packet.toBoundaryCollarPacket.block i p).2| < 20 * c 2 * rd :=
  fun hrd _ _ hprem => C.bcg04_scalar_on_boundary_chain_BGR hrd hprem

/-- Frozen E4 (v3.1 verbatim premises, two-branch output). -/
example : ∀ {rd : ℝ}, 0 < rd → rd < 1 / 10000 → 20 * (c 2 + 1) * rd < 1 / 1000000 →
    1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2 →
    cadj ≤ 1 / 100000 → θ < 1 / 100 →
    BoundaryCollarPacket.BoundaryGeometricOutput_BCG6K S.packet.toBoundaryCollarPacket
      (chainBoundaryU_BCG6K C.toChain.E) (chainBoundaryV_BCG6K C.toChain.E)
      S.toBoundarySupplyCore.zeroBall_BCG6K :=
  fun hrd hrd4 hrdc hprem _ hθ => C.bcg06_on_boundary_chain_BCG6K hrd hrd4 hrdc hprem hθ

/-- Frozen E4b (v3.1 verbatim premises). -/
example : ∀ {rd : ℝ}, 0 < rd → rd < 1 / 10000 → 20 * (c 2 + 1) * rd < 1 / 1000000 →
    1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2 →
    cadj ≤ 1 / 100000 → θ < 1 / 100 →
    BoundaryCollarPacket.BoundaryCuspCoreSpec_BCG6K S.packet.toBoundaryCollarPacket
      (chainBoundaryU_BCG6K C.toChain.E) (chainBoundaryV_BCG6K C.toChain.E)
      S.toBoundarySupplyCore.zeroBall_BCG6K :=
  fun hrd hrd4 hrdc hprem _ hθ => C.bcg06_coreSpec_on_chain_BGR hrd hrd4 hrdc hprem hθ

end Frozen

/-- **Consumer on BAUG-D's enhanced-chain inhabitant**: A2-mk v3's numbers; for every supply with
the uniform register block, the separated branch and empty stage families, and every `r_∂` block
with `θ < 1/100`, there are augmented data and an enhanced chain on them whose final map satisfies
the STRONG BCG06 exit for every component and the direct separated spec E4b. -/
theorem exists_chainE_bcg06_strong_of_empty_BAUGD_BGR (Kj : ℕ) {cadj : ℝ} (hcadj : 0 < cadj) :
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
            (∀ i, S.packet.toBoundaryCollarPacket.BoundaryCuspCoreComponent_BCG6K
              (chainBoundaryU_BCG6K C.toChain.E) (chainBoundaryV_BCG6K C.toChain.E) i) ∧
            BoundaryCollarPacket.BoundaryCuspCoreSpec_BCG6K S.packet.toBoundaryCollarPacket
              (chainBoundaryU_BCG6K C.toChain.E) (chainBoundaryV_BCG6K C.toChain.E)
              S.toBoundarySupplyCore.zeroBall_BCG6K := by
  obtain ⟨Ξ, Γ, Sg, eg, c, cw, hval, h⟩ := exists_boundaryGaf02ChainE_of_empty_BAUGD Kj hcadj
  refine ⟨Ξ, Γ, Sg, eg, c, cw, hval, ?_⟩
  intro K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W _ g δn n B oM S
    hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he hΔ1 hLΛ hLmax he40 hT hσs hσc hγc hεr hsep hempty rd hrd hrd4
    hrdc hprem hθ
  obtain ⟨DP, ⟨C⟩⟩ := h S hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he hΔ1 hLΛ hLmax he40 hT hσs hσc hγc hεr
    hsep hempty
  exact ⟨DP, C, (C.bcg06_on_boundary_chain_BGR hrd hrd4 hrdc hprem hθ).1,
    C.bcg06_coreSpec_on_chain_BGR hrd hrd4 hrdc hprem hθ⟩

end DifferentialGeometry.Geometry.Collapse

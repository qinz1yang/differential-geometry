import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRigidityChainV3BGR

/-!
# BCG05, the whole row on the actual chain (lane B-BCG-ROWS)

Blueprint `master207B.tex`, BCG05 (B:9202–9216): with `r_∂ < 10⁻⁴` and `Σ_j ≤ ε_j/10000` (the
chain's `numbers`), at every source point with `32 ≤ η_b ≤ 78` the boundary scalar marker of EVERY
intermediate map is exactly `1`; in particular each of them is locally constant `1` on the open
band `32 < η_b < 78`.

* **`BoundaryGaf02Chain.bcg05_row_BGR`**: both clauses on every chain over the ACTUAL slot v2 with
  BAUG-C's V3 specs (the type of `BoundaryGaf02ChainE.toChain`, text A-v3), from
  `bcg05_actualSlotsV2_BGR` and the openness of the collar band (`isOpen_collarBand_BAUGA`) and the
  continuity of `η_b`.
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

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

/-- **BCG05, the whole row** (blueprint B:9202–9216) on every chain over the ACTUAL slot v2 with
the V3 specs: on `32 ≤ η_b ≤ 78` the boundary marker of every intermediate map `g_j` (`j = 0..3`,
`g₀ = F_∂`, `g₃ = E`) is exactly `1`, and every `v_b ∘ g_j` is locally constant `1` on the open band
`32 < η_b < 78`. Premises: the register clause `0 ≤ Λ`, `1 ≤ Δ`, `10⁶ΔΛ < 10⁻⁵` and `θ < 1/100`
(`BoundaryGaf02ChainE.std`, `E.theta_BSTD2`), `r_∂ < 10⁻⁴` with its member premise. -/
theorem BoundaryGaf02Chain.bcg05_row_BGR
    {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ
      W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
    {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
    {Ξ c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
    (C : BoundaryGaf02Chain DP.toBoundaryAugmentedData Kj Ξ Sg eg c cw bcut bder κ)
    (hθ : θ < 1 / 100) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) :
    (∀ (k : Fin 4) (i : Fin S.packet.cusp.count),
      ∀ p ∈ S.packet.toBoundaryCollarPacket.safeBand_BAUGA i,
        (augmentedBoundaryCoord_BC7C i (C.stage k p)).2 = 1) ∧
    ∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier),
      p ∈ S.packet.toBoundaryCollarPacket.collarBand_BAUGA i →
      32 < S.packet.toBoundaryCollarPacket.height i p →
      S.packet.toBoundaryCollarPacket.height i p < 78 →
        ∀ᶠ q in 𝓝 p, (augmentedBoundaryCoord_BC7C i (C.stage k q)).2 = 1 := by
  have h := C.bcg05_actualSlotsV2_BGR hθ hrd hrd4 hprem hΛ hΔ hΛΔ
  refine ⟨h, fun k i p hp h1 h2 => ?_⟩
  have hO : IsOpen (S.packet.toBoundaryCollarPacket.collarBand_BAUGA i ∩
      {y | 32 < S.packet.toBoundaryCollarPacket.height i y ∧
        S.packet.toBoundaryCollarPacket.height i y < 78}) :=
    (S.packet.toBoundaryCollarPacket.isOpen_collarBand_BAUGA i).inter
      ((isOpen_lt continuous_const
        (S.packet.toBoundaryCollarPacket.contMDiff_height i).continuous).inter
      (isOpen_lt (S.packet.toBoundaryCollarPacket.contMDiff_height i).continuous continuous_const))
  filter_upwards [hO.mem_nhds ⟨hp, h1, h2⟩] with q hq
  exact h k i q ⟨hq.1, hq.2.1.le, hq.2.2.le⟩

end DifferentialGeometry.Geometry.Collapse

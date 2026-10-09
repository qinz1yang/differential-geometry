import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryGaf02ChainE
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryMarkerRowBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroDomainPlacementBGR

/-!
# BCG04 / BCG05 / ZSP01 / BCG07 F3 placement on the enhanced boundary chain (lane B-BCG-ROWS)

Text A-v3: the enhanced chain `C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj` (BAUG-D G7)
stores the uniform register block `C.std`, so the rows proved on `C.toChain` (B-BCG-ROWS G6, G7,
G9, G14) hold on `C` WITHOUT register premises; only the data of the statements remain
(`r_∂` with its member premise for BCG04 / BCG05, `θ < 1/100` = `E.theta_BSTD2` for BCG05, and
`e ≤ 1/1000` = N76-6 for ZSP02's (ZB) at `.38`).

* **`BoundaryGaf02ChainE.bcg04_row_BGR`** (BCG04 (BI), frozen E1), **`bcg05_row_BGR`** (BCG05, whole
  row with local constancy);
* **`zsp01_ZI_BGR`**, **`zsp01_ZE_BGR`** (ZSP01 on the boundary chain);
* **`actualZeroDomain_subset_ball_BGR`**, **`actualZeroDomain_cover_BGR`**,
  **`isCompact_actualZeroDomain_BGR`**, **`actualZeroDomain_pairwise_disjoint_BGR`** (four fields of
  BIFACEc's `BoundaryActualZeroDomains_BIFc` on `C.toChain`).
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
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **BCG04 (BI) on the enhanced chain** (frozen target E1; the register clause is `C.std`):
exact isolation `ρ(p) > 20r_∂ ⟹ J_b g_j(p) = J_b F_∂(p) = 0`, `|J_b(g_j − F_∂)| < 20c₃r_∂`
componentwise everywhere and on the segment `[F_∂ p, E p]`. -/
theorem bcg04_row_BGR {rd : ℝ} (hrd : 0 < rd)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2) :
    (∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier), 20 * rd < S.rho p →
      augmentedBoundaryCoord_BC7C i (C.toChain.stage k p) = (0, 0) ∧
        S.packet.toBoundaryCollarPacket.block i p = (0, 0)) ∧
    (∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier),
      |(augmentedBoundaryCoord_BC7C i (C.toChain.stage k p)).1 -
          (S.packet.toBoundaryCollarPacket.block i p).1| < 20 * c 2 * rd ∧
      |(augmentedBoundaryCoord_BC7C i (C.toChain.stage k p)).2 -
          (S.packet.toBoundaryCollarPacket.block i p).2| < 20 * c 2 * rd) ∧
    ∀ (i : Fin S.packet.cusp.count) (p : W.Carrier),
      ∀ z ∈ segment ℝ (S.boundaryOriginalMap p) (C.toChain.E p),
      |(augmentedBoundaryCoord_BC7C i z).1 - (S.packet.toBoundaryCollarPacket.block i p).1| <
          20 * c 2 * rd ∧
      |(augmentedBoundaryCoord_BC7C i z).2 - (S.packet.toBoundaryCollarPacket.block i p).2| <
          20 * c 2 * rd := by
  obtain ⟨hΛ, -, -, -, -, -, -, -, -, hΔ, hΛΔ, -⟩ := C.std
  exact C.toChain.bcg04_actualSlotsV2_BGR hrd hprem hΛ hΔ hΛΔ

/-- **BCG05, the whole row on the enhanced chain**: on `32 ≤ η_b ≤ 78` the boundary marker of
every intermediate map is exactly `1`, and locally constant `1` on the open band. -/
theorem bcg05_row_BGR (hθ : θ < 1 / 100) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2) :
    (∀ (k : Fin 4) (i : Fin S.packet.cusp.count),
      ∀ p ∈ S.packet.toBoundaryCollarPacket.safeBand_BAUGA i,
        (augmentedBoundaryCoord_BC7C i (C.toChain.stage k p)).2 = 1) ∧
    ∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier),
      p ∈ S.packet.toBoundaryCollarPacket.collarBand_BAUGA i →
      32 < S.packet.toBoundaryCollarPacket.height i p →
      S.packet.toBoundaryCollarPacket.height i p < 78 →
        ∀ᶠ q in 𝓝 p, (augmentedBoundaryCoord_BC7C i (C.toChain.stage k q)).2 = 1 := by
  obtain ⟨hΛ, -, -, -, -, -, -, -, -, hΔ, hΛΔ, -⟩ := C.std
  exact C.toChain.bcg05_row_BGR hθ hrd hrd4 hprem hΛ hΔ hΛΔ

include C in
/-- `0 < T` from the register (`1 ≤ Δ`, `1600·10⁶Δ ≤ T`). -/
theorem T_pos_BGR : 0 < T := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hΔ, -, -, -, hT, -⟩ := C.std
  nlinarith only [hΔ, hT]

/-- **ZSP01 (ZI) on the enhanced chain**. -/
theorem zsp01_ZI_BGR (k : S.ZeroIdx_BAUGC) {p : W.Carrier}
    (hρ : 200 * S.zeroRadius_BAUGC k / T < S.rho p) :
    S.zeroBlockCLM_BAUGC k (S.boundaryOriginalMap p) = 0 ∧
      S.zeroBlockCLM_BAUGC k (C.toChain.g₁ p) = 0 ∧
      S.zeroBlockCLM_BAUGC k (C.toChain.g₂ p) = 0 ∧
      S.zeroBlockCLM_BAUGC k (C.toChain.E p) = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, he, -⟩ := C.std
  exact C.toChain.zsp01_ZI_actualSlotsV2_BGR C.T_pos_BGR he k hρ

/-- **ZSP01 (ZE) on the enhanced chain** (`δ₀ = 200c₃/T`). -/
theorem zsp01_ZE_BGR (k : S.ZeroIdx_BAUGC) (p : W.Carrier) :
    (∀ j : Fin 4, ‖S.zeroBlockCLM_BAUGC k (C.toChain.stage j p - S.boundaryOriginalMap p)‖ <
      200 * c 2 / T * S.zeroRadius_BAUGC k) ∧
    ∀ z ∈ segment ℝ (S.boundaryOriginalMap p) (C.toChain.E p),
      ‖S.zeroBlockCLM_BAUGC k (z - S.boundaryOriginalMap p)‖ <
        200 * c 2 / T * S.zeroRadius_BAUGC k := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, he, -⟩ := C.std
  exact C.toChain.zsp01_ZE_actualSlotsV2_BGR C.T_pos_BGR he k p

/-- **`domain_subset_ball`** on the enhanced chain. -/
theorem actualZeroDomain_subset_ball_BGR (k : S.ZeroIdx_BAUGC) :
    C.toChain.actualZeroDomain_BIFc k ⊆ riemannianBallOf g k.1.val (S.zeroRadius_BAUGC k) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hΔ, -, -, he, hT, -⟩ := C.std
  exact C.toChain.actualZeroDomain_subset_ball_BGR hΔ hT he k

/-- **`zero_cover`** on the enhanced chain (`e ≤ 1/1000`, N76-6). -/
theorem actualZeroDomain_cover_BGR (he : e ≤ 1 / 1000) (k : S.ZeroIdx_BAUGC)
    (q : W.pieceInterior ⊤)
    (hq : (letI := inducedMetricSpace S.completion.metric; dist q k.1) <
      38 / 100 * S.zeroRadius_BAUGC k) :
    q.val ∈ interior (C.toChain.actualZeroDomain_BIFc k) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hΔ, -, -, -, hT, -⟩ := C.std
  exact C.toChain.actualZeroDomain_cover_BGR hΔ hT he k q hq

/-- **`isCompact_domain`** on the enhanced chain. -/
theorem isCompact_actualZeroDomain_BGR (k : S.ZeroIdx_BAUGC) :
    IsCompact (C.toChain.actualZeroDomain_BIFc k) := by
  obtain ⟨hΛ, -, hμ, hτ, hΔΛ, hV, hβ1, hb, -, hΔ, -, -, he, hT, -⟩ := C.std
  exact C.toChain.isCompact_actualZeroDomain_BGR hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he hT k

/-- **`pairwise_disjoint`** on the enhanced chain. -/
theorem actualZeroDomain_pairwise_disjoint_BGR :
    Pairwise (Disjoint on C.toChain.actualZeroDomain_BIFc) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hΔ, -, -, he, hT, -⟩ := C.std
  exact C.toChain.actualZeroDomain_pairwise_disjoint_BGR hΔ hT he

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse

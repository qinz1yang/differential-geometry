import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreChainEApplicationsBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryFrontierM1BGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreZeroFixBGR

/-!
# BCG04 / BCG05 / BCG06: the final rows on a NON-EMPTY enhanced boundary chain (S-BCG-ROWS2 G24')

The rows BCG04 (global physical boundary-block isolation), BCG05 (exact boundary marker) and BCG06
(the actual adjusted torus collar and its internal frontier) hold on EVERY enhanced chain
`C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj` (B-BCG-ROWS G6–G17; the register block
`C.std` and the CHOICE validity are stored in `C`).  The only missing input of each row is therefore
the existence of such a chain (BAUG-D's production A2 v3, S-BAUG-D2 G18).  This module packages
each row as `Nonempty chain → ∃ C, <row clauses on C>`, so that G18's output instantiates it:
`obtain ⟨DP, C, -⟩ := (production A2 v3 …); exact bcg04_row_of_chain_BGR ⟨C⟩ hrd hprem`.

* **`bcg04_row_of_chain_BGR`**: E1 (isolation `ρ > 20r_∂ ⟹ J_b g_k = J_b F_∂ = 0`, whole-block
  error `< ε_∂ = 20 c₃ r_∂` for every intermediate map and along the segment `[F_∂, E]`), E1' (the
  two scalar components) and E2 (`|d(u_b − η_b)| ≤ c₃|·|_g` on the tight band);
* **`bcg05_row_of_chain_BGR`**: marker exactly `1` on `Safe_b` for EVERY intermediate map, locally
  constant `1` on `32 < η_b < 78`, vanishing marker differential on the interior of `Safe_b`;
* **`bcg06_row_of_chain_BGR`**: the STRONG component exit (every `C_b`: whole inner collar, labelled
  `T² × [0, 1]`, `∂C_b = ∂_bW ⊔ H_b`, `frontier C_b = H_b`, front in `39.99 < η_b < 40.01`,
  `v_b = 1`, `d(u_b − 40) ≠ 0`, strict-marker equivalence) with the two-branch geometric output,
  the direct separated spec E4b (pairwise disjoint cores, disjoint from the selected zero balls)
  the disjointness of every `C_b` from every ACTUAL zero domain of ZSP02, and (review 76 D76-3 M4)
  the jointly smooth all-level collar isotopy of every component, which fixes every original
  selected zero ball pointwise.

NOT in these rows: the ambient smooth embedding E4c (review 76 D76-3; lane O-CROSS).
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


/-- **BCG04 on a non-empty enhanced chain** (E1 ∧ E1' ∧ E2). Premises: the `r_∂` member premise
`hprem` only (the register block and `c₃` are stored in the chain). -/
theorem bcg04_row_of_chain_BGR
    (h : Nonempty (BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)) {rd : ℝ} (hrd : 0 < rd)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2) :
    ∃ C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj,
      ((∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier), 20 * rd < S.rho p →
        augmentedBoundaryCoord_BC7C i (C.toChain.stage k p) = (0, 0) ∧
          S.packet.toBoundaryCollarPacket.block i p = (0, 0)) ∧
      (∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier),
        ‖S.boundaryBlockCLM_BAUGC i (C.toChain.stage k p) -
            S.boundaryBlockCLM_BAUGC i (S.boundaryOriginalMap p)‖ < 20 * c 2 * rd) ∧
      ∀ (i : Fin S.packet.cusp.count) (p : W.Carrier),
        ∀ z ∈ segment ℝ (S.boundaryOriginalMap p) (C.toChain.E p),
        ‖S.boundaryBlockCLM_BAUGC i z - S.boundaryBlockCLM_BAUGC i (S.boundaryOriginalMap p)‖ <
          20 * c 2 * rd) ∧
      (∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier),
        |(augmentedBoundaryCoord_BC7C i (C.toChain.stage k p)).1 -
            (S.packet.toBoundaryCollarPacket.block i p).1| < 20 * c 2 * rd ∧
        |(augmentedBoundaryCoord_BC7C i (C.toChain.stage k p)).2 -
            (S.packet.toBoundaryCollarPacket.block i p).2| < 20 * c 2 * rd) ∧
      (∀ (i : Fin S.packet.cusp.count), ∀ x ∈ S.packet.toBoundaryCollarPacket.collarBand_BAUGA i,
        38 ≤ S.packet.toBoundaryCollarPacket.height i x →
        S.packet.toBoundaryCollarPacket.height i x ≤ 42 →
        ∀ v : TangentSpace W.model x,
          |mvfderiv W.model (fun y => chainBoundaryU_BCG6K C.toChain.E i y -
              S.packet.toBoundaryCollarPacket.height i y) x v| ≤
            c 2 * Real.sqrt (g.inner x v v)) := by
  obtain ⟨C⟩ := h
  exact ⟨C, C.bcg04_on_boundary_chain_BGR hrd hprem, C.bcg04_scalar_on_boundary_chain_BGR hrd hprem,
    C.bcg04_derivative_on_boundary_chain_BGR⟩

/-- **BCG05 on a non-empty enhanced chain**: the boundary marker of every intermediate map is
exactly `1` on `Safe_b`, locally constant `1` on the open band `32 < η_b < 78`, and has vanishing
differential on the interior of `Safe_b`. Premises: the `r_∂` block and `θ < 1/100`. -/
theorem bcg05_row_of_chain_BGR
    (h : Nonempty (BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∃ C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj,
      (∀ (k : Fin 4) (i : Fin S.packet.cusp.count),
        ∀ p ∈ S.packet.toBoundaryCollarPacket.safeBand_BAUGA i,
          (augmentedBoundaryCoord_BC7C i (C.toChain.stage k p)).2 = 1) ∧
      (∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier),
        p ∈ S.packet.toBoundaryCollarPacket.collarBand_BAUGA i →
        32 < S.packet.toBoundaryCollarPacket.height i p →
        S.packet.toBoundaryCollarPacket.height i p < 78 →
          ∀ᶠ q in 𝓝 p, (augmentedBoundaryCoord_BC7C i (C.toChain.stage k q)).2 = 1) ∧
      ∀ (k : Fin 4) (i : Fin S.packet.cusp.count),
        ∀ p ∈ interior (S.packet.toBoundaryCollarPacket.safeBand_BAUGA i),
          mvfderiv W.model (fun y => (augmentedBoundaryCoord_BC7C i (C.toChain.stage k y)).2) p =
            0 := by
  obtain ⟨C⟩ := h
  exact ⟨C, (C.bcg05_row_BGR hθ hrd hrd4 hprem).1, (C.bcg05_row_BGR hθ hrd hrd4 hprem).2,
    (C.bcg05_on_boundary_chain_BGR hrd hrd4 hprem hθ).2⟩

/-- **BCG06 on a non-empty enhanced chain**: the STRONG component exit and the two-branch output,
the direct separated spec E4b, the disjointness of every `C_b` from every actual zero domain of
ZSP02, and (D76-3 M4) a jointly smooth isotopy of `W` (the identity at time `0`, carrying the
inner sublevel `{level ≤ 40}` onto `C_b` at time `1`) fixing every original selected zero ball
pointwise. Premises: the `r_∂` block and `θ < 1/100` (`c₃ = c 2 < 10⁻⁵` is the CHOICE validity
stored in the chain, N76-4). -/
theorem bcg06_row_of_chain_BGR
    (h : Nonempty (BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∃ C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj,
      ((∀ i, S.packet.toBoundaryCollarPacket.BoundaryCuspCoreComponent_BCG6K
          (chainBoundaryU_BCG6K C.toChain.E) (chainBoundaryV_BCG6K C.toChain.E) i) ∧
        BoundaryCollarPacket.BoundaryGeometricOutput_BCG6K S.packet.toBoundaryCollarPacket
          (chainBoundaryU_BCG6K C.toChain.E) (chainBoundaryV_BCG6K C.toChain.E)
          S.toBoundarySupplyCore.zeroBall_BCG6K) ∧
      BoundaryCollarPacket.BoundaryCuspCoreSpec_BCG6K S.packet.toBoundaryCollarPacket
        (chainBoundaryU_BCG6K C.toChain.E) (chainBoundaryV_BCG6K C.toChain.E)
        S.toBoundarySupplyCore.zeroBall_BCG6K ∧
      (∀ (i : Fin S.packet.cusp.count) (k : S.ZeroIdx_BAUGC),
        Disjoint (C.toChain.cuspCore_BIF i) (C.toChain.actualZeroDomain_BIFc k)) ∧
      ∀ i : Fin S.packet.cusp.count,
        ∃ Φ : ℝ → Diffeomorph W.model W.model W.Carrier W.Carrier ∞,
          ContMDiff (𝓘(ℝ, ℝ).prod W.model) W.model ∞ (fun q : ℝ × W.Carrier => Φ q.1 q.2) ∧
          (∀ x, Φ 0 x = x) ∧
          Φ 1 '' {x | S.packet.toBoundaryCollarPacket.level i x ≤ 40} = C.toChain.cuspCore_BIF i ∧
          ∀ (z : S.toBoundarySupplyCore.zeroIndex_BCG6K) (t : ℝ),
            ∀ x ∈ S.toBoundarySupplyCore.zeroBall_BCG6K z, Φ t x = x := by
  obtain ⟨C⟩ := h
  refine ⟨C, C.bcg06_on_boundary_chain_BGR hrd hrd4 hrdc hprem hθ,
    C.bcg06_coreSpec_on_chain_BGR hrd hrd4 hrdc hprem hθ,
    C.cuspCore_disjoint_actualZeroDomain_BGR hrd hrd4 hrdc hprem hθ, fun i => ?_⟩
  obtain ⟨-, Φ, -, -, h3, h4, -, -, -, -, -, h10, -, h12⟩ :=
    S.toBoundarySupplyCore.flow_fixes_zeroBalls_BGR DP.toBoundaryAugmentedData.separated
      ((C.bcg06_on_boundary_chain_BGR hrd hrd4 hrdc hprem hθ).1 i)
  exact ⟨Φ, h3, h4, h10, h12⟩

end DifferentialGeometry.Geometry.Collapse

import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreChainEBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.FoundationBoundaryCollarBlock
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceFibresV2

/-!
# FC43 assembly preparation on the enhanced boundary chain (lane B-BCG-ROWS)

Blueprint `master207B.tex`, FC43 (B:7549–7575): the E-free collar block of the final export
packet (FC-FOUND G2, `fc43_collar_block_FCF`), the boundary chain with its blocks retained through
all three adjustments (BCG03 = A2 / A3 / A4), BCG04 (rigidity of the boundary blocks) and BCG06
(the torus collar cores, STRONG exit). The A2 output is the enhanced chain `C` itself (BAUG-D G7
`exists_boundaryGaf02ChainE_mk_BAUGD`); the A4 output enters as the v2 bases `Bs` with the
whole-fibre layer `WF` (BIFACEc / BAUG-Dd, pending); the BCG03 conjunct consists of the A3 exits
of `C` (A3a / A3b / A3c) and the fibre types DERIVED from `WF`.

* **`BoundaryGaf02ChainE.fc43_row_BGR`**;
* consumer **`fc43_row_of_mk_BGR`**: on A2-mk v3's chains (every slot active) the row holds for
  every A4 output.
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

/-- **FC43, assembly form** on the enhanced chain `C` (A2's output) and an A4 output `(Bs, WF)`:
(FC43 block) the E-free collar block of the export packet for every boundary component;
(BCG03) the A3 exits of `C` (smoothness of every stage, value errors `< c_k ρ`, derivative errors
`< c_k`) and the whole circle / slim (`S²` or `T²`) / edge-disk fibres derived from `WF`;
(BCG04) E1 (isolation, whole-block exit, segment) and E2 (derivative half on the tight band);
(BCG06) the STRONG component exit and the two-branch geometric output. Premises: the `r_∂` block
and `θ < 1/100`. -/
theorem fc43_row_BGR {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2 C.toChain Bs) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    (∀ i : Fin S.packet.cusp.count,
      ContMDiff W.model 𝓘(ℝ, ℝ × ℝ) ∞ (S.packet.block i) ∧
        (∀ x, (S.packet.block i x).1 = S.packet.height i x * (S.packet.block i x).2 ∧
          (S.packet.block i x).2 = S.packet.cutoff i x) ∧
        (∀ p : CuspHalfSpace, 2 < p.2.val 0 → p.2.val 0 < 98 →
          S.packet.cutoff i ((S.packet.cusp.collar i).toFun p) =
            boundaryProfile (S.packet.height i ((S.packet.cusp.collar i).toFun p))) ∧
        (∀ x, S.packet.cutoff i x ∈ Icc (0 : ℝ) 1) ∧
        (∀ x, S.packet.block i x ≠ 0 → 20 < S.packet.height i x ∧ S.packet.height i x < 90) ∧
        (∀ p : CuspHalfSpace, 2 < p.2.val 0 → p.2.val 0 < 98 →
          S.packet.height i ((S.packet.cusp.collar i).toFun p) ∈ Icc (30 : ℝ) 80 →
            S.packet.cutoff i ((S.packet.cusp.collar i).toFun p) = 1) ∧
        tsupport (S.packet.block i) ⊆ (S.packet.cusp.collar i).toFun ''
          {p : CuspHalfSpace | 20 - cuspTolerance_BCUSP1 (β 1) βd εN ≤ p.2.val 0 ∧
            p.2.val 0 ≤ 90 + cuspTolerance_BCUSP1 (β 1) βd εN}) ∧
    ((∀ k : Fin 4, ContMDiff W.model
        𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞ (C.toChain.stage k)) ∧
      (∀ (k : Fin 3) (p : W.Carrier),
        ‖C.toChain.stage k.succ p - S.boundaryOriginalMap p‖ < c k * S.rho p) ∧
      (∀ k : Fin 3, ∃ Hd : ℝ, Hd < c k ∧ ∀ (p : W.Carrier) (v : TangentSpace W.model p),
        ‖mvfderiv W.model (C.toChain.stage k.succ) p v -
            mvfderiv W.model S.boundaryOriginalMap p v‖ ≤ Hd * Real.sqrt (g.inner p v v)) ∧
      (∀ y ∈ Bs.base 0, Nonempty (Bs.fibre 0 y ≃ₜ Circle)) ∧
      (∀ y ∈ Bs.base 2, Nonempty (Bs.fibre 2 y ≃ₜ Metric.sphere (0 : E3) 1) ∨
        Nonempty (Bs.fibre 2 y ≃ₜ Circle × Circle)) ∧
      (∀ y ∈ Bs.base 1, ∃ ed : Bs.fibre 1 y ≃ₜ ClosedCell 2,
        Subtype.val '' (ed ⁻¹' {x : ClosedCell 2 | ‖x.1‖ = 1}) =
          Bs.fibre 1 y ∩ {p | C.toChain.heightRatio p = 4 * Δ})) ∧
    (((∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier), 20 * rd < S.rho p →
      augmentedBoundaryCoord_BC7C i (C.toChain.stage k p) = (0, 0) ∧
        S.packet.toBoundaryCollarPacket.block i p = (0, 0)) ∧
    (∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier),
      ‖S.boundaryBlockCLM_BAUGC i (C.toChain.stage k p) -
          S.boundaryBlockCLM_BAUGC i (S.boundaryOriginalMap p)‖ < 20 * c 2 * rd) ∧
    ∀ (i : Fin S.packet.cusp.count) (p : W.Carrier),
      ∀ z ∈ segment ℝ (S.boundaryOriginalMap p) (C.toChain.E p),
      ‖S.boundaryBlockCLM_BAUGC i z - S.boundaryBlockCLM_BAUGC i (S.boundaryOriginalMap p)‖ <
        20 * c 2 * rd) ∧
    (∀ (i : Fin S.packet.cusp.count), ∀ x ∈ S.packet.toBoundaryCollarPacket.collarBand_BAUGA i,
      38 ≤ S.packet.toBoundaryCollarPacket.height i x →
      S.packet.toBoundaryCollarPacket.height i x ≤ 42 →
      ∀ v : TangentSpace W.model x,
        |mvfderiv W.model (fun y => chainBoundaryU_BCG6K C.toChain.E i y -
            S.packet.toBoundaryCollarPacket.height i y) x v| ≤
          c 2 * Real.sqrt (g.inner x v v))) ∧
    (∀ i, S.packet.toBoundaryCollarPacket.BoundaryCuspCoreComponent_BCG6K
        (chainBoundaryU_BCG6K C.toChain.E) (chainBoundaryV_BCG6K C.toChain.E) i) ∧
      BoundaryCollarPacket.BoundaryGeometricOutput_BCG6K S.packet.toBoundaryCollarPacket
        (chainBoundaryU_BCG6K C.toChain.E) (chainBoundaryV_BCG6K C.toChain.E)
        S.toBoundarySupplyCore.zeroBall_BCG6K :=
  ⟨fun i => fc43_collar_block_FCF S.packet i,
    ⟨C.stage_smooth_BAUGD, C.stage_error_lt_BAUGD, C.stage_derivative_lt_BAUGD,
      WF.circle_fibre_BIFc, WF.slim_fibre_BIFc, WF.edge_fibre_BIFc⟩,
    ⟨C.bcg04_on_boundary_chain_BGR hrd hprem, C.bcg04_derivative_on_boundary_chain_BGR⟩,
    C.bcg06_on_boundary_chain_BGR hrd hrd4 hrdc hprem hθ⟩

end BoundaryGaf02ChainE

/-- **Consumer on A2-mk v3** (BAUG-D G7): A2-mk's numbers; for every supply with the uniform
register block and every augmented data `DP`, the produced enhanced chain has every slot active,
and for every A4 output `(Bs, WF)` on it and every `r_∂` block with `θ < 1/100`, the whole slim
fibres are `S²` or `T²` and every boundary component has BCG06's strong exit. -/
theorem fc43_row_of_mk_BGR (Kj : ℕ) {cadj : ℝ} (hcadj : 0 < cadj) :
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
        ∀ DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg,
          ∃ C : BoundaryGaf02ChainE DP Kj Ξ c cw boundaryChainCutoffConst_BAUGD
              boundaryDerivBound_BDFB cutoffKappa_BAUGP2 cadj,
            (∀ st, ∃ O, C.toChain.slot st = .active O) ∧
            ∀ (Bs : BoundaryGaf02BasesV2 C.toChain), BoundaryWholeFiberSpecV2 C.toChain Bs →
              ∀ {rd : ℝ}, 0 < rd → rd < 1 / 10000 → 20 * (c 2 + 1) * rd < 1 / 1000000 →
              1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2 →
              θ < 1 / 100 →
                (∀ y ∈ Bs.base 2, Nonempty (Bs.fibre 2 y ≃ₜ Metric.sphere (0 : E3) 1) ∨
                  Nonempty (Bs.fibre 2 y ≃ₜ Circle × Circle)) ∧
                ∀ i, S.packet.toBoundaryCollarPacket.BoundaryCuspCoreComponent_BCG6K
                  (chainBoundaryU_BCG6K C.toChain.E) (chainBoundaryV_BCG6K C.toChain.E) i := by
  obtain ⟨Ξ, Γ, Sg, eg, c, cw, hval, -, -, -, h⟩ := exists_boundaryGaf02ChainE_mk_BAUGD Kj hcadj
  refine ⟨Ξ, Γ, Sg, eg, c, cw, hval, ?_⟩
  intro K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W _ g δn n B oM S
    hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he hΔ1 hLΛ hLmax he40 hT hσs hσc hγc hεr DP
  obtain ⟨C, hact⟩ := h S hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he hΔ1 hLΛ hLmax he40 hT hσs hσc hγc hεr DP
  refine ⟨C, hact, fun Bs WF rd hrd hrd4 hrdc hprem hθ => ?_⟩
  have hrow := C.fc43_row_BGR WF hrd hrd4 hrdc hprem hθ
  exact ⟨hrow.2.1.2.2.2.2.1, hrow.2.2.2.1⟩

end DifferentialGeometry.Geometry.Collapse

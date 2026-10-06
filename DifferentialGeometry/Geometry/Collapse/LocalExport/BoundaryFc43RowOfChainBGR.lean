import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRowsOfChainBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryFc43RowBGR

/-!
# FC43 on a non-empty enhanced chain with an A4 output: the rows' conjunction (S-BCG-ROWS2 G27)

Blueprint FC43 (`master207B.tex`, B:7549–7575, foundation "Nearly cuspidal boundary augmentation"):
the boundary blocks are adjoined to every `Q_j` (the E-free collar block `fc43_collar_block_FCF`),
the adjustments are repeated retaining the blocks like zero blocks (BCG03 = the enhanced chain `C`
with the A3 exits and the whole fibres of the A4 output `(Bs, WF)`), BCG04 (isolation of the whole
boundary block), BCG06 (the torus collar cores `N₃₅(∂_iM) ∪ {x'' ≥ .9, ratio ≤ 40}`: `I × T²` with
the original boundary label, strong exit and the two-branch exceptional whole carrier `I × T²`).

* **`fc43_row_of_chain_BGR`**: from the two upstream producer conclusions only — a NON-EMPTY
  enhanced chain (production A2 v3, S-BAUG-D2 G18) and the A4 output `(Bs, WF)` for every chain (A4,
  S-BAUG-D2 G19 / S-BASES-PORT2) — the FC43 conjunction of `fc43_row_BGR` holds on ONE chain and
  ONE A4 output (`∃ C Bs`, `WF ∧ …`);
* consumer **`exists_chainE_fc43_of_empty_BAUGD_BGR`** on BAUG-D's enhanced-chain inhabitant.
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


/-- **FC43 on a non-empty enhanced chain with an A4 output**: `h` is the conclusion of the
production A2 v3 (a chain on `DP`), `hA4` the conclusion of A4 (v2 bases with the whole-fibre layer
on every chain). The conclusion is `fc43_row_BGR`'s conjunction (FC43 collar block ∧ BCG03 (A3
exits, fibre types of `WF`) ∧ BCG04 ∧ BCG06 strong exit) on one chain and one A4 output.
Premises: the `r_∂` block and `θ < 1/100`. -/
theorem fc43_row_of_chain_BGR
    (h : Nonempty (BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj))
    (hA4 : ∀ C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj,
      ∃ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2 C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∃ C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj,
      ∃ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2 C.toChain Bs ∧
    ((∀ i : Fin S.packet.cusp.count,
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
        S.toBoundarySupplyCore.zeroBall_BCG6K ) := by
  obtain ⟨C⟩ := h
  obtain ⟨Bs, WF⟩ := hA4 C
  exact ⟨C, Bs, WF, C.fc43_row_BGR WF hrd hrd4 hrdc hprem hθ⟩

end DifferentialGeometry.Geometry.Collapse

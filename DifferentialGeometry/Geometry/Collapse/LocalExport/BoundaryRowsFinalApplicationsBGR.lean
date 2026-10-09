import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRowsFinalBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryFc43RowOfChainBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryV2bConsumersBGR

/-!
# FC43 on the production chain with A4 as the parameter; headline consumer (S-BCG-ROWS2 G33)

* **`fc43_rowAll_V2b_BGR`**: FC43's conjunction (`fc43_row_V2b_BGR`: FC43 block ∧ BCG03 ∧ BCG04 ∧
  BCG06) on a GIVEN chain from an A4 output of that chain (v2b) as the hypothesis `hA4`. The
  production-prefix form of FC43 (A2 v3's quantifier prefix) was not stated: the statement alone
  exhausts the elaboration heartbeats of a declaration (the conjunction under ~110 binders); the
  instantiation is `obtain ⟨DP, C, hact⟩ := <A2 v3 at the premises>; exact C.fc43_rowAll_V2b_BGR
  (hA4 DP C) hrd hrd4 hrdc hprem hθ`, with A4 (S-BAUG-D2 G19 / S-BASES-PORT2, not yet whole) as the
  parameter.
* **`bcg_rows_final_headline_BGR`** (consumer of `bcg04_05_06_rows_final_BGR`): on the production
  chain, BCG04's isolation, BCG05's exact marker `1` on `Safe_b` and BCG06's `frontier C_b = H_b`
  for every component hold together.
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

/-- FC43's conjunction on a given chain with an A4 output of the chain (v2b). -/
theorem fc43_rowAll_V2b_BGR
    (hA4 : ∃ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∃ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs ∧
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
  obtain ⟨Bs, WF⟩ := hA4
  exact ⟨Bs, WF, C.fc43_row_V2b_BGR WF hrd hrd4 hrdc hprem hθ⟩

end BoundaryGaf02ChainE

/-- **Headline consumer on the production chain**: isolation (BCG04), exact marker `1` on `Safe_b`
(BCG05) and `frontier C_b = H_b` for every component (BCG06), on ONE chain. -/
theorem bcg_rows_final_headline_BGR (Kj : ℕ) {cadj ν : ℝ} (hcadj : 0 < cadj)
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
        ∀ {rd : ℝ}, 0 < rd → rd < 1 / 10000 → 20 * (c 2 + 1) * rd < 1 / 1000000 →
        1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2 →
        θ < 1 / 100 →
        ∃ DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg,
          ∃ C : BoundaryGaf02ChainE DP Kj Ξ c cw boundaryChainCutoffConst_BAUGD
              boundaryDerivBound_BDFB cutoffKappa_BAUGP2 cadj,
            (∀ st, ∃ O, C.toChain.slot st = .active O) ∧
            (∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier), 20 * rd < S.rho p →
              augmentedBoundaryCoord_BC7C i (C.toChain.stage k p) = (0, 0) ∧
                S.packet.toBoundaryCollarPacket.block i p = (0, 0)) ∧
            (∀ (k : Fin 4) (i : Fin S.packet.cusp.count),
              ∀ p ∈ S.packet.toBoundaryCollarPacket.safeBand_BAUGA i,
                (augmentedBoundaryCoord_BC7C i (C.toChain.stage k p)).2 = 1) ∧
            ∀ i : Fin S.packet.cusp.count,
              frontier (C.toChain.cuspCore_BIF i) = C.toChain.cuspFront_BIF i := by
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
    f1 f2 f3 f4 f5 f6 hθ0 h1 hsep rd hrd hrd4 hrdc hprem hθ
  obtain ⟨DP, C, hact⟩ := hP' S r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
    c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26
    c27 c28 c29 c30 c31 c32 c33 c34 c35 c36
    d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
    f1 f2 f3 f4 f5 f6 hθ0 h1 hsep
  exact ⟨DP, C, hact, (C.bcg04_rowAll_BGR hrd hprem).1.1, (C.bcg05_rowAll_BGR hrd hrd4 hprem hθ).1,
    fun i => ((C.bcg06_rowAll_BGR hrd hrd4 hrdc hprem hθ).1.1 i).relative_frontier_eq⟩

end DifferentialGeometry.Geometry.Collapse

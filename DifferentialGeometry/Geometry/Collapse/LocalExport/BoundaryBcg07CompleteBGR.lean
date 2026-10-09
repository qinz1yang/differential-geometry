import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBcg07WithG3BGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryM1ManifoldApplicationsBGR

/-!
# BCG07 COMPLETE on one production chain with A4 whole (lane S-BCF03c, G32)

`bcg07_complete_BGR`: on the SAME `C`, `Bs`, `WF` chosen by the headline `bcg07_row_whole_final_BGR`
(S-BCG-ROWS3 G35; statement and premise block verbatim, via G32's `bcg07_row_with_g3_BGR`):
the conclusion conjoins

1. the row F1 ∧ F2 ∧ F3 ∧ F4a–d ∧ F5 (`bcg07_row_BGR`);
2. the extras `bcg07_row_extras_BGR` (BCF01 complement: `X₃ ∩ f₃⁻¹(D₃) = M₁ ∩ X₃`, `∂D₃ ⊆
   f₃(∂M₁ ∩ X₃)`, F5z, one base point per cusp front, `f₃(∂M₁ ∩ X₃)` finite, `∂M₁ ⊆ {D ≥ 35}`,
   `D_j` relatively closed);
3. 07.b2 STRONG `M₁_isManifold_BGR` (a `𝓡∂ 3`-structure on `↥M₁`, smooth inclusion with bijective
   differential, boundary points = zero faces and cusp fronts, compact);
4. 07.b2 simplified `M₁_manifold_boundary_eq_frontier_BGR` (boundary points = `frontier M₁`);
5. 07.g3 (`bcg07_clause_g3_OBD`) on the SAME `Bs`, `WF` with the zero domains of F3.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
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

/-- **BCG07 complete** (clause table in the module docstring). -/
theorem bcg07_complete_BGR (Kj : ℕ) {cadj ν : ℝ} (hcadj : 0 < cadj)
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
        3 * βc ≤ β 2 → 0 ≤ γ → γ ≤ 1 / 2 → γ + β 2 < 1 / 10 → β 2 ≤ 1 / 10000000 → 5 ≤ K →
        32 * (1000000 * Δ) ≤ (n : ℝ) → μ ≤ 1 / 10 ^ 8 → τ ≤ 1 / 10 ^ 8 → b ≤ 1 / (1000 * Δ) →
        100 * (boundaryDerivBound_BDFB + 1) * (1 + boundaryChainCutoffConst_BAUGD + cw 0 / Sg 0) *
          Λ * Δ < 1 / 1000000 → ε < 1 → γc ≤ 1 / 100 → βc ≤ 1 / 100000 → e ≤ 1 / 1000 →
        ∀ {rd : ℝ}, 0 < rd → rd < 1 / 10000 → 20 * (c 2 + 1) * rd < 1 / 1000000 →
        1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2 →
        θ < 1 / 100 →
        ∃ DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg,
          ∃ C : BoundaryGaf02ChainE DP Kj Ξ c cw boundaryChainCutoffConst_BAUGD
              boundaryDerivBound_BDFB cutoffKappa_BAUGP2 cadj,
            (∀ st, ∃ O, C.toChain.slot st = .active O) ∧
∃ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs ∧
        -- F1
        ((∀ y ∈ Bs.base 1, ∀ p ∈ Bs.fibre 1 y, C.toChain.heightRatio p = 4 * Δ →
          p ∈ Bs.source 0 ∧
            Bs.fibre 1 y ∩ {q | C.toChain.heightRatio q = 4 * Δ} =
              Bs.fibre 0 (C.toChain.stageMap 0 p)) ∧
        -- F2
        (∀ (st : Fin 3) (i : Fin S.packet.cusp.count) (p q : W.Carrier),
          p ∈ C.toChain.cuspFront_BIF i → C.toChain.stageMap st q = C.toChain.stageMap st p →
            q ∈ C.toChain.cuspFront_BIF i) ∧
        -- F3
        Nonempty (BoundaryActualZeroDomains_BIFc C.toChain Bs) ∧
        -- F4a
        IsCompact C.toChain.M₁_BIFc ∧
        -- F4b
        C.toChain.M₁_BIFc ⊆ {p | ENNReal.ofReal 35 ≤ distanceToBoundary W g p} ∧
        -- F4c
        frontier C.toChain.M₁_BIFc =
          (⋃ k, C.toChain.actualZeroFace_BIFc k) ∪ ⋃ i, C.toChain.cuspFront_BIF i ∧
        -- F4d
        (∀ st : Fin 3, st ≠ 1 → C.toChain.M₁_BIFc ∩ Bs.source st =
          Bs.source st ∩ C.toChain.stageMap st ⁻¹' (C.toChain.stageMap st '' (C.toChain.M₁_BIFc ∩
            Bs.source st))) ∧
        -- F5
        (∀ i : Fin S.packet.cusp.count, (C.toChain.cuspFront_BIF i ∩ Bs.source 2).Nonempty →
          ∃ y ∈ Bs.base 2, C.toChain.cuspFront_BIF i = Bs.fibre 2 y)) ∧
        -- extras (BCF01 complement, `bcg07_row_extras_BGR`) on the SAME Bs, WF
        (Bs.source 2 ∩ C.toChain.stageMap 2 ⁻¹' Bs.slimBaseDomain_BIFc =
            C.toChain.M₁_BIFc ∩ Bs.source 2 ∧
          Bs.slimBaseDomain_BIFc \ relInterior_BIF (Bs.base 2) Bs.slimBaseDomain_BIFc ⊆
            C.toChain.stageMap 2 '' (frontier C.toChain.M₁_BIFc ∩ Bs.source 2) ∧
          (∀ k : S.ZeroIdx_BAUGC, (C.toChain.actualZeroFace_BIFc k ∩ Bs.source 2).Nonempty →
            ∃ y ∈ Bs.base 2, C.toChain.actualZeroFace_BIFc k = Bs.fibre 2 y) ∧
          (∀ i : Fin S.packet.cusp.count, (C.toChain.cuspFront_BIF i ∩ Bs.source 2).Nonempty →
            ∃ y ∈ Bs.base 2,
              C.toChain.stageMap 2 '' (C.toChain.cuspFront_BIF i ∩ Bs.source 2) = {y}) ∧
          (C.toChain.stageMap 2 '' (frontier C.toChain.M₁_BIFc ∩ Bs.source 2)).Finite ∧
          frontier C.toChain.M₁_BIFc ⊆ {p | ENNReal.ofReal 35 ≤ distanceToBoundary W g p} ∧
          (∀ st : Fin 3, st ≠ 1 →
            IsClosed (Subtype.val ⁻¹'
              (C.toChain.stageMap st '' (C.toChain.M₁_BIFc ∩ Bs.source st)) : Set (Bs.base st)))) ∧
        -- 07.b2 STRONG (`M₁_isManifold_BGR`): ambient-compatible smooth structure on M₁
        (∃ cs : ChartedSpace (EuclideanHalfSpace 3) ↥C.toChain.M₁_BIFc,
          letI := cs
          IsManifold (𝓡∂ 3) ∞ ↥C.toChain.M₁_BIFc ∧
          ContMDiff (𝓡∂ 3) W.model ∞ (fun x : ↥C.toChain.M₁_BIFc => x.1) ∧
          (∀ x : ↥C.toChain.M₁_BIFc, Function.Bijective
            (mfderiv (𝓡∂ 3) W.model (fun y : ↥C.toChain.M₁_BIFc => y.1) x)) ∧
          (∀ x : ↥C.toChain.M₁_BIFc, (𝓡∂ 3).IsBoundaryPoint x ↔
            x.1 ∈ (⋃ k, C.toChain.actualZeroFace_BIFc k) ∪ ⋃ i, C.toChain.cuspFront_BIF i) ∧
          CompactSpace ↥C.toChain.M₁_BIFc) ∧
        -- 07.b2 simplified (`M₁_manifold_boundary_eq_frontier_BGR`): boundary = frontier
        (∃ cs : ChartedSpace (EuclideanHalfSpace 3) ↥C.toChain.M₁_BIFc,
          letI := cs
          IsManifold (𝓡∂ 3) ∞ ↥C.toChain.M₁_BIFc ∧ CompactSpace ↥C.toChain.M₁_BIFc ∧
          (∀ x : ↥C.toChain.M₁_BIFc, (𝓡∂ 3).IsBoundaryPoint x ↔
            x.1 ∈ frontier C.toChain.M₁_BIFc)) ∧
        -- 07.g3 (D77-6 shape) on the SAME Bs, WF
        ∀ i : Fin S.packet.cusp.count, (C.toChain.cuspFront_BIF i ∩ Bs.source 2).Nonempty →
        ∃ y₀ ∈ Bs.base 2, C.toChain.cuspFront_BIF i = Bs.fibre 2 y₀ ∧
          cuspRatioBase_OBD i y₀ = 0 ∧
          (∃ O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)), IsOpen O ∧
            y₀ ∈ O ∧ ∀ y ∈ Bs.base 2 ∩ O, (y ∈ Bs.slimBaseDomain_BIFc ↔ 0 ≤ cuspBaseCLM_OBD i y)) ∧
          ∃ σ : EuclideanSpace ℝ (Fin 1) →
              BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count),
            σ 0 = y₀ ∧ ContDiff ℝ ∞ σ ∧ (∃ O, IsOpen O ∧ range σ = Bs.base 2 ∩ O) ∧
            fderiv ℝ (cuspRatioBase_OBD i ∘ σ) 0 ≠ 0 := by
  obtain ⟨Ξ, Γ, Sg, eg, c, cw, hval, σ, hσ, hσ1, η₂, γ₀, ηc, θt, hη₂, hγ₀, hηc, hθt, hθt1, hP⟩ :=
    bcg07_row_with_g3_BGR Kj hcadj hν hν1
  refine ⟨Ξ, Γ, Sg, eg, c, cw, hval, σ, hσ, hσ1, η₂, γ₀, ηc, θt, hη₂, hγ₀, hηc, hθt, hθt1,
    fun β₂ hβ₂ hβ₂' Δ hΔ => ?_⟩
  obtain ⟨η₁, θs, Lc, η₀, hη₁, hθs, hθs1, hLc, hη₀, hP'⟩ := hP β₂ hβ₂ hβ₂' Δ hΔ
  refine ⟨η₁, θs, Lc, η₀, hη₁, hθs, hθs1, hLc, hη₀, ?_⟩
  intro K A β βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W _ g δn n B oM S
    r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
    c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26
    c27 c28 c29 c30 c31 c32 c33 c34 c35 c36
    d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
    f1 f2 f3 f4 f5 f6 hθ0 h1 hsep h3βc hγ0 hγ hd hβ2 hK hn hμ hτ hb hC hε hγc1 hβc1 he
    rd hrd hrd4 hrdc hprem hθ
  obtain ⟨DP, C, hact, Bs, WF, hrow⟩ := hP' S
    r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10
    c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33
    c34 c35 c36 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 f1 f2 f3 f4 f5 f6 hθ0 h1 hsep
    h3βc hγ0 hγ hd hβ2 hK hn hμ hτ hb hC hε hγc1 hβc1 he hrd hrd4 hrdc hprem hθ
  have hεr : εr < 1 / 2 := by linarith
  exact ⟨DP, C, hact, Bs, WF, hrow.1, C.bcg07_row_extras_BGR hεr hrd hrd4 hrdc hprem hθ WF,
    C.M₁_isManifold_BGR hεr hrd hrd4 hrdc hprem hθ,
    C.M₁_manifold_boundary_eq_frontier_BGR hεr hrd hrd4 hrdc hprem hθ, hrow.2⟩

end DifferentialGeometry.Geometry.Collapse

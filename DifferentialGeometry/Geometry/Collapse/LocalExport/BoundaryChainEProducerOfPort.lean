import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainEProducerOfDP
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryProducerDPAssemblyOfPort

/-!
# A2 v3 on the DP assembly of BAUG-C (conditional on the circle port theorem), G18 stand-in
(S-BAUG-D2, successor of BAUG-De / S-BAUG-D)

`exists_boundaryGaf02ChainE_of_circlePort_BAUGD`: A2 v3 of the A-v3.1 text (with `0 ≤ θ` before
(R1), without (R2); strengthened as `exists_boundaryGaf02ChainE_of_dp_BAUGD`) with ProducerDP v3.1
supplied by BAUG-C's assembly `exists_boundaryAugmentedDataP_of_circlePort_BAUGC`. The only extra
hypothesis is `hport`, the frozen PortTargets v3.1 circle statement (`port_circle_interior_table_
BAUGP`, O-PORT-A's gate). The production theorem `exists_boundaryGaf02ChainE_v3_BAUGD` is the same
statement without `hport` (compose `exists_boundaryGaf02ChainE_of_dp_BAUGD` with BAUG-C's G7b
`exists_boundaryAugmentedDataP_BAUGC`); it is a new file once G7b is delivered.
The non-emptiness clause `∀ st, ∃ O, C.toChain.slot st = .active O` of the conclusion is the one
the counts BCG04 / 05 / 06 consume.
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

open Classical in
/-- **A2 v3 on BAUG-C's DP assembly, conditional on the circle port theorem** (`hport`). -/
theorem exists_boundaryGaf02ChainE_of_circlePort_BAUGD (Kj : ℕ) {cadj ν : ℝ} (hcadj : 0 < cadj)
    (hν : 0 < ν) (hν1 : ν < 1)
    (hport : ∀ {ν Γ sg eg : ℝ}, 0 < Γ → Γ < 1 → 0 < sg → sg < Γ / 200 →
      sg < Γ ^ 3 / (100 * tcpGraphConst) → 0 < eg → eg < 1 / 100 → eg < Γ * sg / 100 →
      0 < ν → ν < 1 →
      ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ γ₀ ηc θt : ℝ, 0 < η₂ ∧ 0 < γ₀ ∧
      0 < ηc ∧ 0 < θt ∧ θt < 1 ∧ ∀ Δ : ℝ, 1200 ≤ Δ → ∃ η₁ : ℝ, 0 < η₁ ∧
      ∀ {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
        {βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
        {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
        {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {n : ℕ}
        {B : NearlyCuspidalBoundary W g K δn}
        {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
        (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
          θ W g δn n B oM),
        0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 10 ^ 6 * Δ * Λ < 1 / 10 ^ 5 →
        4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
        0 ≤ ε → ε ≤ 1 → 0 ≤ σc → σc ≤ θt ^ 2 / 1000 → μ * Δ ≤ θt / 100 →
        3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → γ ≤ γ₀ → 0 < γc → γc ≤ γ₀ → βc ≤ ηc →
        b ≤ η₁ → β 1 ≤ η₁ → 0 < σs → σs ≤ θt ^ 2 / 1000 → vs ≤ θt / 100 → 0 < ζ →
        ζ ≤ θt ^ 2 / 1000 → εr ≤ θt / 100 → 20 * Λz ≤ T → σ⁻¹ ≤ Lmax →
        1000 * tcpGraphConst * Δ * Λ < eg →
        0 < Δ → 100 * Δ * Λ ≤ 1 / 100 → 0 ≤ V → 0 < β 1 → 0 < b → e ≤ 1 / 10 →
        S.SeparatedCollarZero_BIF →
        letI := inducedMetricSpace S.completion.metric
        ∃ (Ψ : W.pieceInterior ⊤ → ℝ² → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))
          (Kint : W.pieceInterior ⊤ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) →L[ℝ]
            BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))
          (Pc : W.pieceInterior ⊤ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) →L[ℝ] ℝ²)
          (rpre : (actualSlotsV2_BAUGD S).stageCloudEnlarged 0 → W.pieceInterior ⊤)
          (pre : (actualSlotsV2_BAUGD S).stageCloud 0 → W.pieceInterior ⊤)
          (ref : (actualSlotsV2_BAUGD S).stageCloud 0 → W.pieceInterior ⊤),
        -- (M)
        (∀ a ∈ S.stageCentres_BIF 0, ContDiff ℝ 2 (Kint a ∘ Ψ a) ∧ ∀ u,
          ‖fderiv ℝ (Kint a ∘ Ψ a) u‖ ≤ tcpGraphConst ∧ ‖fderiv ℝ (fderiv ℝ (Kint a ∘ Ψ a)) u‖ ≤
            tcpGraphConst) ∧
        -- (OWN)
        (∀ a ∈ S.stageCentres_BIF 0, (∀ z, ‖Pc a z‖ ≤ ‖z‖) ∧ (∀ u, Pc a ((Kint a ∘ Ψ a) u) = u) ∧
          ∀ x : W.pieceInterior ⊤, (dist x a < 200 * S.rho a ∧ ‖S.circleEta_BIF a x‖ ≤ 8) →
            Pc a ((S.rho a)⁻¹ • blockRestrict (S.stageTagsV2_BAUGD 0) (S.interiorMapOn_BAUGA x)) =
              S.circleEta_BIF a x) ∧
        -- (Q)
        -- (stage 0: Q₁ = H, automatic)
        (∀ a ∈ S.stageCentres_BIF 0, ∀ u,
          blockRestrict (S.stageTagsV2_BAUGD 0) ((Kint a ∘ Ψ a) u) = (Kint a ∘ Ψ a) u) ∧
        -- (TG)
        (∀ a ∈ S.stageCentres_BIF 0, ∀ x : W.pieceInterior ⊤, (dist x a < 200 * S.rho a ∧
          ‖S.circleEta_BIF a x‖ ≤ 8) →
          ‖(S.rho a)⁻¹ • blockRestrict (S.stageTagsV2_BAUGD 0) (S.interiorMapOn_BAUGA x) -
              (Kint a ∘ Ψ a) (S.circleEta_BIF a x)‖ < eg ∧
          ∀ w : TangentSpace 𝓘(ℝ, E3) x,
            ‖(S.rho a)⁻¹ • mvfderiv 𝓘(ℝ, E3)
                (fun y => blockRestrict (S.stageTagsV2_BAUGD 0) (S.interiorMapOn_BAUGA y)) x w -
                fderiv ℝ (Kint a ∘ Ψ a) (S.circleEta_BIF a x) (mvfderiv 𝓘(ℝ, E3) (S.circleEta_BIF
                  a) x w)‖ ≤
              eg * Real.sqrt ((S.rho a)⁻¹ ^ 2 * S.completion.metric.inner x w w)) ∧
        -- (SEL)
        -- (the clouds are images of W° sets)
        (∀ x, (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap (rpre x).val) = x.1) ∧
        (∀ x, ref x ∈ S.stageCentres_BIF 0 ∧ (dist (pre x) (ref x) < 200 * S.rho (ref x) ∧
          ‖S.circleEta_BIF (ref x) (pre x)‖ ≤ 7) ∧
          dist (pre x) (ref x) < stageDomain_BIF Δ 0 * S.rho (ref x) ∧
          (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap (pre x).val) = x.1) ∧
        -- (LOC)
        (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 0),
          ∀ y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 0,
            ‖augIntProjCLM_BAUGC (y - x)‖ ≤ sg * S.rho (ref ⟨x, hx⟩) / Γ →
            ∃ q : W.pieceInterior ⊤, (dist q (ref ⟨x, hx⟩) < 200 * S.rho (ref ⟨x, hx⟩) ∧
              ‖S.circleEta_BIF (ref ⟨x, hx⟩) q‖ ≤ 8) ∧
              dist q (ref ⟨x, hx⟩) < stageDomain_BIF Δ 0 * S.rho (ref ⟨x, hx⟩) ∧
              (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val) = y) ∧
        -- (COV)
        (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 0), ∀ u : ℝ²,
          ‖u - S.circleEta_BIF (ref ⟨x, hx⟩) (pre ⟨x, hx⟩)‖ ≤ 2 * sg / Γ →
          ∃ q : W.pieceInterior ⊤, (dist q (ref ⟨x, hx⟩) < 200 * S.rho (ref ⟨x, hx⟩) ∧
            ‖S.circleEta_BIF (ref ⟨x, hx⟩) q‖ ≤ 8) ∧
            dist q (ref ⟨x, hx⟩) < stageDomain_BIF Δ 0 * S.rho (ref ⟨x, hx⟩) ∧
            S.circleEta_BIF (ref ⟨x, hx⟩) q = u ∧
            (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val) ∈
              (actualSlotsV2_BAUGD S).stageCloudEnlarged 0) ∧
        -- (PRE)
        (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 0), ∀ q : W.pieceInterior ⊤,
          (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val) = x →
          (dist q (ref ⟨x, hx⟩) < 200 * S.rho (ref ⟨x, hx⟩) ∧ ‖S.circleEta_BIF (ref ⟨x, hx⟩) q‖ ≤
            8) ∧ dist q (ref ⟨x, hx⟩) < stageDomain_BIF Δ 0 * S.rho (ref ⟨x, hx⟩) ∧
            S.circleEta_BIF (ref ⟨x, hx⟩) q = S.circleEta_BIF (ref ⟨x, hx⟩) (pre ⟨x, hx⟩)) ∧
        -- (PP-int)
        (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 0), ∀ q : W.pieceInterior ⊤,
          (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val) = x →
          ∀ m : S.MarkerIdx_BAUGC, S.rho (S.markerCentre_BAUGC m) < S.rho q / 5 →
            ∀ v : ℝ², ((fderiv ℝ (Kint (ref ⟨x, hx⟩) ∘ Ψ (ref ⟨x, hx⟩))
              (S.circleEta_BIF (ref ⟨x, hx⟩) (pre ⟨x, hx⟩)) v) (S.markerTag_BAUGC m)).snd = 0) ∧
        -- (SB-int)
        (∀ a ∈ S.stageCentres_BIF 0, ∀ m : S.MarkerIdx_BAUGC,
          S.rho (S.markerCentre_BAUGC m) ≤ smallBlockFactor_BAUGC 0 * S.rho a →
          ∀ u, (Kint a ∘ Ψ a) u (S.markerTag_BAUGC m) = 0) ∧
        -- (FM*-int)
        -- (ActualStagePlaneFullMarker.lean)
        -- (edge: t_B = edgeB.smoothing/ρ)
        (∀ εc σ' : ℝ, 0 < εc → 0 ≤ σ' → σ' ≤ εc / 10000 → ∀ (x₀ : W.pieceInterior ⊤)
          (m : S.MarkerIdx_BAUGC), S.markerStage_BAUGC m = 0 → ∀ p ∈ S.markerCore7_BAUGC m,
          ∀ y (hy : y ∈ (actualSlotsV2_BAUGD S).stageCloud 0),
            (closedBall y (80 * εc⁻¹ * (σ' * S.rho (if hyT : y ∈ (actualSlotsV2_BAUGD
              S).stageCloudEnlarged 0
                then rpre ⟨y, hyT⟩ else x₀))) ∩
              ball ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap p.val))
                (8 * εc⁻¹ * (σ' * S.rho (if hpT : (actualSlotsV2_BAUGD S).stageProj 0
                    (S.boundaryOriginalMap p.val) ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 0
                  then rpre ⟨_, hpT⟩ else x₀)))).Nonempty →
            S.markerCLM_BAUGC m y = S.rho (S.markerCentre_BAUGC m) ∧
            ∀ v : ℝ², ((fderiv ℝ (Kint (ref ⟨y, hy⟩) ∘ Ψ (ref ⟨y, hy⟩))
              (S.circleEta_BIF (ref ⟨y, hy⟩) (pre ⟨y, hy⟩)) v) (S.markerTag_BAUGC m)).snd = 0) ∧
        -- (ZB*-int)
        (∀ εc σ' : ℝ, 0 < εc → σ' ≤ εc / 10000 → ∀ (x₀ : W.pieceInterior ⊤)
          (k : S.ZeroIdx_BAUGC) (p : W.pieceInterior ⊤),
          (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap p.val) ∈
            (actualSlotsV2_BAUGD S).stageCloud 0 →
          200 * S.zeroRadius_BAUGC k / T < S.rho p →
          ∀ y (hy : y ∈ (actualSlotsV2_BAUGD S).stageCloud 0),
            (closedBall y (80 * εc⁻¹ * (σ' * S.rho (if hyT : y ∈ (actualSlotsV2_BAUGD
              S).stageCloudEnlarged 0
                then rpre ⟨y, hyT⟩ else x₀))) ∩
              ball ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap p.val))
                (8 * εc⁻¹ * (σ' * S.rho (if hpT : (actualSlotsV2_BAUGD S).stageProj 0
                    (S.boundaryOriginalMap p.val) ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 0
                  then rpre ⟨_, hpT⟩ else x₀)))).Nonempty →
            S.zeroBlockCLM_BAUGC k y = 0 ∧
            ∀ v : ℝ², (fderiv ℝ (Kint (ref ⟨y, hy⟩) ∘ Ψ (ref ⟨y, hy⟩))
              (S.circleEta_BIF (ref ⟨y, hy⟩) (pre ⟨y, hy⟩)) v) (S.zeroTag_BAUGC k) = 0) ∧
        -- (SCL)
        (∀ a ∈ S.stageCentres_BIF 0, ∀ u v : ℝ²,
          ((fderiv ℝ (Kint a ∘ Ψ a) u v) S.scaleTag_BAUGA).snd = 0)) :
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
        ∃ DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg,
          ∃ C : BoundaryGaf02ChainE DP Kj Ξ c cw boundaryChainCutoffConst_BAUGD
              boundaryDerivBound_BDFB cutoffKappa_BAUGP2 cadj,
            ∀ st, ∃ O, C.toChain.slot st = .active O := by
  exact exists_boundaryGaf02ChainE_of_dp_BAUGD Kj hcadj hν hν1
    (fun {Γ Sg eg} hΓ hΓ1 hsg hsgΓ hsgC0 hsgC1 hsgC2 heg heg1 hegΓ _ hν' hν1' =>
      exists_boundaryAugmentedDataP_of_circlePort_BAUGC hport hΓ hΓ1 hsg hsgΓ hsgC0 hsgC1 hsgC2
        heg heg1 hegΓ hν' hν1')


open Classical in
/-- The VERBATIM premise block of the A-v3.1 text plus `0 ≤ θ` (with (R2)), from the
strengthened theorem (R2 unused). -/
example (Kj : ℕ) {cadj ν : ℝ} (hcadj : 0 < cadj)
    (hν : 0 < ν) (hν1 : ν < 1)
    (hport : ∀ {ν Γ sg eg : ℝ}, 0 < Γ → Γ < 1 → 0 < sg → sg < Γ / 200 →
      sg < Γ ^ 3 / (100 * tcpGraphConst) → 0 < eg → eg < 1 / 100 → eg < Γ * sg / 100 →
      0 < ν → ν < 1 →
      ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ γ₀ ηc θt : ℝ, 0 < η₂ ∧ 0 < γ₀ ∧
      0 < ηc ∧ 0 < θt ∧ θt < 1 ∧ ∀ Δ : ℝ, 1200 ≤ Δ → ∃ η₁ : ℝ, 0 < η₁ ∧
      ∀ {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
        {βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
        {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
        {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {n : ℕ}
        {B : NearlyCuspidalBoundary W g K δn}
        {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
        (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
          θ W g δn n B oM),
        0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 10 ^ 6 * Δ * Λ < 1 / 10 ^ 5 →
        4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
        0 ≤ ε → ε ≤ 1 → 0 ≤ σc → σc ≤ θt ^ 2 / 1000 → μ * Δ ≤ θt / 100 →
        3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → γ ≤ γ₀ → 0 < γc → γc ≤ γ₀ → βc ≤ ηc →
        b ≤ η₁ → β 1 ≤ η₁ → 0 < σs → σs ≤ θt ^ 2 / 1000 → vs ≤ θt / 100 → 0 < ζ →
        ζ ≤ θt ^ 2 / 1000 → εr ≤ θt / 100 → 20 * Λz ≤ T → σ⁻¹ ≤ Lmax →
        1000 * tcpGraphConst * Δ * Λ < eg →
        0 < Δ → 100 * Δ * Λ ≤ 1 / 100 → 0 ≤ V → 0 < β 1 → 0 < b → e ≤ 1 / 10 →
        S.SeparatedCollarZero_BIF →
        letI := inducedMetricSpace S.completion.metric
        ∃ (Ψ : W.pieceInterior ⊤ → ℝ² → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))
          (Kint : W.pieceInterior ⊤ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) →L[ℝ]
            BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))
          (Pc : W.pieceInterior ⊤ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) →L[ℝ] ℝ²)
          (rpre : (actualSlotsV2_BAUGD S).stageCloudEnlarged 0 → W.pieceInterior ⊤)
          (pre : (actualSlotsV2_BAUGD S).stageCloud 0 → W.pieceInterior ⊤)
          (ref : (actualSlotsV2_BAUGD S).stageCloud 0 → W.pieceInterior ⊤),
        -- (M)
        (∀ a ∈ S.stageCentres_BIF 0, ContDiff ℝ 2 (Kint a ∘ Ψ a) ∧ ∀ u,
          ‖fderiv ℝ (Kint a ∘ Ψ a) u‖ ≤ tcpGraphConst ∧ ‖fderiv ℝ (fderiv ℝ (Kint a ∘ Ψ a)) u‖ ≤
            tcpGraphConst) ∧
        -- (OWN)
        (∀ a ∈ S.stageCentres_BIF 0, (∀ z, ‖Pc a z‖ ≤ ‖z‖) ∧ (∀ u, Pc a ((Kint a ∘ Ψ a) u) = u) ∧
          ∀ x : W.pieceInterior ⊤, (dist x a < 200 * S.rho a ∧ ‖S.circleEta_BIF a x‖ ≤ 8) →
            Pc a ((S.rho a)⁻¹ • blockRestrict (S.stageTagsV2_BAUGD 0) (S.interiorMapOn_BAUGA x)) =
              S.circleEta_BIF a x) ∧
        -- (Q)
        -- (stage 0: Q₁ = H, automatic)
        (∀ a ∈ S.stageCentres_BIF 0, ∀ u,
          blockRestrict (S.stageTagsV2_BAUGD 0) ((Kint a ∘ Ψ a) u) = (Kint a ∘ Ψ a) u) ∧
        -- (TG)
        (∀ a ∈ S.stageCentres_BIF 0, ∀ x : W.pieceInterior ⊤, (dist x a < 200 * S.rho a ∧
          ‖S.circleEta_BIF a x‖ ≤ 8) →
          ‖(S.rho a)⁻¹ • blockRestrict (S.stageTagsV2_BAUGD 0) (S.interiorMapOn_BAUGA x) -
              (Kint a ∘ Ψ a) (S.circleEta_BIF a x)‖ < eg ∧
          ∀ w : TangentSpace 𝓘(ℝ, E3) x,
            ‖(S.rho a)⁻¹ • mvfderiv 𝓘(ℝ, E3)
                (fun y => blockRestrict (S.stageTagsV2_BAUGD 0) (S.interiorMapOn_BAUGA y)) x w -
                fderiv ℝ (Kint a ∘ Ψ a) (S.circleEta_BIF a x) (mvfderiv 𝓘(ℝ, E3) (S.circleEta_BIF
                  a) x w)‖ ≤
              eg * Real.sqrt ((S.rho a)⁻¹ ^ 2 * S.completion.metric.inner x w w)) ∧
        -- (SEL)
        -- (the clouds are images of W° sets)
        (∀ x, (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap (rpre x).val) = x.1) ∧
        (∀ x, ref x ∈ S.stageCentres_BIF 0 ∧ (dist (pre x) (ref x) < 200 * S.rho (ref x) ∧
          ‖S.circleEta_BIF (ref x) (pre x)‖ ≤ 7) ∧
          dist (pre x) (ref x) < stageDomain_BIF Δ 0 * S.rho (ref x) ∧
          (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap (pre x).val) = x.1) ∧
        -- (LOC)
        (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 0),
          ∀ y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 0,
            ‖augIntProjCLM_BAUGC (y - x)‖ ≤ sg * S.rho (ref ⟨x, hx⟩) / Γ →
            ∃ q : W.pieceInterior ⊤, (dist q (ref ⟨x, hx⟩) < 200 * S.rho (ref ⟨x, hx⟩) ∧
              ‖S.circleEta_BIF (ref ⟨x, hx⟩) q‖ ≤ 8) ∧
              dist q (ref ⟨x, hx⟩) < stageDomain_BIF Δ 0 * S.rho (ref ⟨x, hx⟩) ∧
              (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val) = y) ∧
        -- (COV)
        (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 0), ∀ u : ℝ²,
          ‖u - S.circleEta_BIF (ref ⟨x, hx⟩) (pre ⟨x, hx⟩)‖ ≤ 2 * sg / Γ →
          ∃ q : W.pieceInterior ⊤, (dist q (ref ⟨x, hx⟩) < 200 * S.rho (ref ⟨x, hx⟩) ∧
            ‖S.circleEta_BIF (ref ⟨x, hx⟩) q‖ ≤ 8) ∧
            dist q (ref ⟨x, hx⟩) < stageDomain_BIF Δ 0 * S.rho (ref ⟨x, hx⟩) ∧
            S.circleEta_BIF (ref ⟨x, hx⟩) q = u ∧
            (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val) ∈
              (actualSlotsV2_BAUGD S).stageCloudEnlarged 0) ∧
        -- (PRE)
        (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 0), ∀ q : W.pieceInterior ⊤,
          (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val) = x →
          (dist q (ref ⟨x, hx⟩) < 200 * S.rho (ref ⟨x, hx⟩) ∧ ‖S.circleEta_BIF (ref ⟨x, hx⟩) q‖ ≤
            8) ∧ dist q (ref ⟨x, hx⟩) < stageDomain_BIF Δ 0 * S.rho (ref ⟨x, hx⟩) ∧
            S.circleEta_BIF (ref ⟨x, hx⟩) q = S.circleEta_BIF (ref ⟨x, hx⟩) (pre ⟨x, hx⟩)) ∧
        -- (PP-int)
        (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 0), ∀ q : W.pieceInterior ⊤,
          (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val) = x →
          ∀ m : S.MarkerIdx_BAUGC, S.rho (S.markerCentre_BAUGC m) < S.rho q / 5 →
            ∀ v : ℝ², ((fderiv ℝ (Kint (ref ⟨x, hx⟩) ∘ Ψ (ref ⟨x, hx⟩))
              (S.circleEta_BIF (ref ⟨x, hx⟩) (pre ⟨x, hx⟩)) v) (S.markerTag_BAUGC m)).snd = 0) ∧
        -- (SB-int)
        (∀ a ∈ S.stageCentres_BIF 0, ∀ m : S.MarkerIdx_BAUGC,
          S.rho (S.markerCentre_BAUGC m) ≤ smallBlockFactor_BAUGC 0 * S.rho a →
          ∀ u, (Kint a ∘ Ψ a) u (S.markerTag_BAUGC m) = 0) ∧
        -- (FM*-int)
        -- (ActualStagePlaneFullMarker.lean)
        -- (edge: t_B = edgeB.smoothing/ρ)
        (∀ εc σ' : ℝ, 0 < εc → 0 ≤ σ' → σ' ≤ εc / 10000 → ∀ (x₀ : W.pieceInterior ⊤)
          (m : S.MarkerIdx_BAUGC), S.markerStage_BAUGC m = 0 → ∀ p ∈ S.markerCore7_BAUGC m,
          ∀ y (hy : y ∈ (actualSlotsV2_BAUGD S).stageCloud 0),
            (closedBall y (80 * εc⁻¹ * (σ' * S.rho (if hyT : y ∈ (actualSlotsV2_BAUGD
              S).stageCloudEnlarged 0
                then rpre ⟨y, hyT⟩ else x₀))) ∩
              ball ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap p.val))
                (8 * εc⁻¹ * (σ' * S.rho (if hpT : (actualSlotsV2_BAUGD S).stageProj 0
                    (S.boundaryOriginalMap p.val) ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 0
                  then rpre ⟨_, hpT⟩ else x₀)))).Nonempty →
            S.markerCLM_BAUGC m y = S.rho (S.markerCentre_BAUGC m) ∧
            ∀ v : ℝ², ((fderiv ℝ (Kint (ref ⟨y, hy⟩) ∘ Ψ (ref ⟨y, hy⟩))
              (S.circleEta_BIF (ref ⟨y, hy⟩) (pre ⟨y, hy⟩)) v) (S.markerTag_BAUGC m)).snd = 0) ∧
        -- (ZB*-int)
        (∀ εc σ' : ℝ, 0 < εc → σ' ≤ εc / 10000 → ∀ (x₀ : W.pieceInterior ⊤)
          (k : S.ZeroIdx_BAUGC) (p : W.pieceInterior ⊤),
          (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap p.val) ∈
            (actualSlotsV2_BAUGD S).stageCloud 0 →
          200 * S.zeroRadius_BAUGC k / T < S.rho p →
          ∀ y (hy : y ∈ (actualSlotsV2_BAUGD S).stageCloud 0),
            (closedBall y (80 * εc⁻¹ * (σ' * S.rho (if hyT : y ∈ (actualSlotsV2_BAUGD
              S).stageCloudEnlarged 0
                then rpre ⟨y, hyT⟩ else x₀))) ∩
              ball ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap p.val))
                (8 * εc⁻¹ * (σ' * S.rho (if hpT : (actualSlotsV2_BAUGD S).stageProj 0
                    (S.boundaryOriginalMap p.val) ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 0
                  then rpre ⟨_, hpT⟩ else x₀)))).Nonempty →
            S.zeroBlockCLM_BAUGC k y = 0 ∧
            ∀ v : ℝ², (fderiv ℝ (Kint (ref ⟨y, hy⟩) ∘ Ψ (ref ⟨y, hy⟩))
              (S.circleEta_BIF (ref ⟨y, hy⟩) (pre ⟨y, hy⟩)) v) (S.zeroTag_BAUGC k) = 0) ∧
        -- (SCL)
        (∀ a ∈ S.stageCentres_BIF 0, ∀ u v : ℝ²,
          ((fderiv ℝ (Kint a ∘ Ψ a) u v) S.scaleTag_BAUGA).snd = 0)) :
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
        1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * (1 / 8) ^ 2 →
        -- END premise block
        S.SeparatedCollarZero_BIF →
        ∃ DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg,
          ∃ C : BoundaryGaf02ChainE DP Kj Ξ c cw boundaryChainCutoffConst_BAUGD
              boundaryDerivBound_BDFB cutoffKappa_BAUGP2 cadj,
            ∀ st, ∃ O, C.toChain.slot st = .active O := by
  obtain ⟨Ξ, Γ, Sg, eg, c, cw, hval, σ, hσ, hσ1, η₂, γ₀, ηc, θt, hη₂, hγ₀, hηc, hθt, hθt1, hP⟩ :=
    exists_boundaryGaf02ChainE_of_circlePort_BAUGD Kj hcadj hν hν1 hport
  refine ⟨Ξ, Γ, Sg, eg, c, cw, hval, σ, hσ, hσ1, η₂, γ₀, ηc, θt, hη₂, hγ₀, hηc, hθt, hθt1,
    fun β₂ hβ₂ hβ₂' Δ hΔ => ?_⟩
  obtain ⟨η₁, θs, Lc, η₀, hη₁, hθs, hθs1, hLc, hη₀, hP'⟩ := hP β₂ hβ₂ hβ₂' Δ hΔ
  refine ⟨η₁, θs, Lc, η₀, hη₁, hθs, hθs1, hLc, hη₀, ?_⟩
  intro K A β βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W _ g δn n B oM S
    r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
    c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26
    c27 c28 c29 c30 c31 c32 c33 c34 c35 c36
    d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
    f1 f2 f3 f4 f5 f6 hθ h1 _ hsep
  exact hP' S r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
    c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26
    c27 c28 c29 c30 c31 c32 c33 c34 c35 c36
    d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
    f1 f2 f3 f4 f5 f6 hθ h1 hsep

end DifferentialGeometry.Geometry.Collapse

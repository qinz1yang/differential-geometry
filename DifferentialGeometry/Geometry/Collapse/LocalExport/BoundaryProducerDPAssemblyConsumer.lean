import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainEProducerOfDP
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryProducerDPAssemblyOfPort

/-!
# Consumer of the ProducerDP assembly (lane BAUG-C, group G7a)

A2 v3 modulo ProducerDP (`exists_boundaryGaf02ChainE_of_dp_BAUGD`, BAUG-D G15) takes the assembly
as its hypothesis `hDP` (with the unused premise `eg 1 < Σ₁/1000`); the conditional assembly
`exists_boundaryAugmentedDataP_of_circlePort_BAUGC` supplies it, so A2 v3 follows from the circle
port theorem alone. (An `example` only: it declares no constant.)
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
/-- A2 v3 from the circle port theorem (the composition A2 `_of_dp` ∘ conditional assembly). -/
example
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
          ((fderiv ℝ (Kint a ∘ Ψ a) u v) S.scaleTag_BAUGA).snd = 0))
    (Kj : ℕ) {cadj ν : ℝ} (hcadj : 0 < cadj) (hν : 0 < ν) (hν1 : ν < 1) :=
  exists_boundaryGaf02ChainE_of_dp_BAUGD Kj hcadj hν hν1
    (fun {_ _ _} hΓ hΓ1 hsg hsgΓ hsgC0 hsgC1 hsgC2 heg heg1 hegΓ _ hν' hν1' =>
      exists_boundaryAugmentedDataP_of_circlePort_BAUGC hport hΓ hΓ1 hsg hsgΓ hsgC0 hsgC1 hsgC2
        heg heg1 hegΓ hν' hν1')

end DifferentialGeometry.Geometry.Collapse

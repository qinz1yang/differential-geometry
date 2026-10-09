import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedDataPV3
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryProducerDPCircleOfPort
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryProducerDPEdge
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryProducerDPSlim

/-!
# ProducerDP v3.1, the assembly, conditional on the circle port theorem (lane BAUG-C, group G7a)

`exists_boundaryAugmentedDataP_of_circlePort_BAUGC`: the three stage tables with their specs V3 on
ONE actual slot v2, as `BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg` (the DP input
of A2's `exists_boundaryGaf02ChainE_of_dp_BAUGD`), from the circle table of
`exists_boundaryCircleTable_of_port_BAUGC` (conditional on the circle port theorem `hport`,
`port_circle_interior_table_BAUGP` of PortTargets v3.1), the edge table
`exists_boundaryEdgeTable_BAUGC` (G5) and the slim table `exists_boundarySlimTable_BAUGC` (G4b).
The statement is the v3.1 assembly of
`docs/geometrization/chapter14/evidence/boundary/ProducerDP-v3.1.lean.txt` with `hport` in front
and without the unused premise `hegS1 : eg 1 < Σ₁/1000` (strengthened; the edge table does not
use it: pass any proof of it away, e.g. `fun … _ … => …`, to obtain the `hDP` shape of A2).
The late thresholds are `Lc := max Lc₁ Lc₂`, `η₀ := min η₀₁ η₀₂` (edge / slim) and the circle's
`η₁`; every block premise is routed to the stage that needs it. Once the circle port theorem is
delivered, `exists_boundaryAugmentedDataP_BAUGC` (G7b) is this theorem without `hport`.
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
/-- **The assembly of ProducerDP v3.1, conditional on the circle port theorem** (`hport` = the
frozen PortTargets v3.1 circle statement; conclusion: `Nonempty (BoundaryAugmentedDataPV3 …)`). -/
theorem exists_boundaryAugmentedDataP_of_circlePort_BAUGC
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
    {ν : ℝ} {Γ Sg eg : Fin 3 → ℝ} (hΓ : ∀ j, 0 < Γ j) (hΓ1 : ∀ j, Γ j < 1)
    (hsg : ∀ j, 0 < Sg j) (hsgΓ : ∀ j, Sg j < Γ j / 250)
    (hsgC0 : Sg 0 < Γ 0 ^ 3 / (125 * (tcpGraphConst + 2 * bmConst_BAUGC)))
    (hsgC1 : Sg 1 < Γ 1 ^ 3 / (125 * (egpGraphConst + 2 * bmConst_BAUGC)))
    (hsgC2 : Sg 2 < Γ 2 ^ 3 / (125 * (sgpGraphBound + 2 * bmConst_BAUGC)))
    (heg : ∀ j, 0 < eg j) (heg1 : ∀ j, eg j < 1 / 100) (hegΓ : ∀ j, eg j < Γ j * Sg j / 100)
    (hν : 0 < ν) (hν1 : ν < 1) :
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
      (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
        θ W g δn n B oM),
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
      -- slim port block (PortTargets v3.1, port_slim_interior_table_BAUGP; `0 < σs`, `0 < ζ` above)
      σs < θs ^ 2 / 10 ^ 6 → vs < θs / 100 →
      ζ < θs ^ 2 / 10 ^ 6 → ζ < 1 / (100 * (1000000 * Δ)) →
      εr < θs / (100 * (1000000 * Δ)) → 0 ≤ εr →
      -- transfer budget: N76-7 `0 ≤ θ` and (R1) at every stage
      0 ≤ θ → (∀ j, 16 * bmConst_BAUGC * θ ≤ eg j) →
      S.SeparatedCollarZero_BIF →
      Nonempty (BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg) := by
  obtain ⟨σ, hσ, hσ1, η₂, γ₀, ηc, θt, hη₂, hγ₀, hηc, hθt, hθt1, hC⟩ :=
    exists_boundaryCircleTable_of_port_BAUGC hport (hΓ 0) (hΓ1 0) (hsg 0) (hsgΓ 0) hsgC0 (heg 0)
      (heg1 0) (hegΓ 0) hν hν1
  clear hport
  refine ⟨σ, hσ, hσ1, η₂, γ₀, ηc, θt, hη₂, hγ₀, hηc, hθt, hθt1,
    fun β₂ hβ₂ hβ₂1 Δ hΔ => ?_⟩
  obtain ⟨η₁, hη₁, hCΔ⟩ := hC Δ hΔ
  obtain ⟨Lc₁, η₀₁, hLc₁, hη₀₁, hE⟩ :=
    exists_boundaryEdgeTable_BAUGC (hΓ 1) (hΓ1 1) (hsg 1) (hsgΓ 1) hsgC1 (heg 1) (heg1 1)
      (hegΓ 1) β₂ hβ₂ hβ₂1 Δ hΔ
  obtain ⟨θs, hθs, hθs1, Lc₂, η₀₂, hLc₂, hη₀₂, hS⟩ :=
    exists_boundarySlimTable_BAUGC (hΓ 2) (hΓ1 2) (hsg 2) (hsgΓ 2) hsgC2 (heg 2) (heg1 2)
      (hegΓ 2) β₂ hβ₂ (hβ₂1.trans (by norm_num)) Δ hΔ
  refine ⟨η₁, θs, max Lc₁ Lc₂, min η₀₁ η₀₂, hη₁, hθs, hθs1, lt_max_of_lt_left hLc₁,
    lt_min hη₀₁ hη₀₂, ?_⟩
  intro K A β βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W _ g δn n B oM S
    hΛ hμ hτ hΛΔ hLmax he40 hT hε0 hε1 hσc0 hσcθ hμΔ hβ3 hβ31 hβ2σ hβ2η hγ hγc0 hγc hβc hb1
    hβ1η1 hσs0 hσsθ hvs hζ0 hζθ hεr hΛz hσL hCc hΔ0 hΔΛ hV hβ1 hb he
    hbη₀ hs hβ1η₀ hLcL hσcE hμΔE _ hσsE hvsE _ hζE hζΔE hεrE hβ2
    hσsS hvsS hζθS hζΔS hεrS hεr0 hθ hR hsep
  obtain ⟨R₀, hR₀⟩ := hCΔ S hΛ hμ hτ hΛΔ hLmax he40 hT hε0 hε1 hσc0 hσcθ hμΔ hβ3 hβ31 hβ2σ hβ2η
    hγ hγc0 hγc hβc hb1 hβ1η1 hσs0 hσsθ hvs hζ0 hζθ hεr hΛz hσL hCc hΔ0 hΔΛ hV hβ1 hb he hθ
    (hR 0) hsep
  obtain ⟨R₁, hR₁⟩ := hE S hΛ hμ hτ hΛΔ he40 hT hΛz (hbη₀.trans (min_le_left _ _)) hs
    (hβ1η₀.trans (min_le_left _ _)) ((le_max_left _ _).trans hLcL) hσc0 hσcE hμΔE hσs0 hσsE hvsE
    hζ0 hζE hζΔE hεrE hβ2 hΔ0 hΔΛ hV hβ1 hb he hθ (hR 1) hsep
  obtain ⟨R₂, hR₂⟩ := hS S hΛ hμ hτ hΛΔ he40 hT hΛz hβ2 (hβ1η₀.trans (min_le_right _ _))
    ((le_max_right _ _).trans hLcL) hσs0 hσsS hvsS hζ0 hζθS hζΔS hεrS hεr0 hΔ0 hΔΛ hV hβ1 hb he
    hθ (hR 2) hsep
  exact ⟨{ separated := hsep, circle := R₀, edge := R₁, slim := R₂,
           circle_spec := hR₀, edge_spec := hR₁, slim_spec := hR₂ }⟩

end DifferentialGeometry.Geometry.Collapse

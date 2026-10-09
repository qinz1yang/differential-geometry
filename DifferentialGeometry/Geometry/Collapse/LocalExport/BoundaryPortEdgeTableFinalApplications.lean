import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeTableFinal

/-!
# Consumers of the edge port table (lane S-PORT-EDGE)

* `port_edge_interior_table_transfer_BPE` — `port_edge_interior_table_BAUGP` at BAUG-C's transfer
  point `(Γ, 5Σ/4, eg/2)` from the header of `exists_boundaryEdgeSpec_of_port_BAUGC` (ProducerDP v3:
  `Σ < Γ/250`, `eg < 1/100`);
* `port_edge_cloud_scale_core_BPE` — (PRE~) in both directions on the core cloud `S₁ ⊆ S̃₁`.
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
/-- **The edge table at the transfer point** `(Γ, 5Σ/4, eg/2)`: from `0 < Σ < Γ/250` and
`0 < eg < 1/100` (the edge header of BAUG-C's `exists_boundaryEdgeSpec_of_port_BAUGC`). -/
theorem port_edge_interior_table_transfer_BPE {Γ sg eg : ℝ} (hΓ : 0 < Γ) (hsg : 0 < sg)
    (hsgΓ : sg < Γ / 250) (heg : 0 < eg) (heg1 : eg < 1 / 100) :
    ∀ β₂ : ℝ, 0 < β₂ → β₂ < 1 / 1000000 → ∀ Δ : ℝ, 1200 ≤ Δ →
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
    ∀ {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
      {βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
      {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
      {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {n : ℕ}
      {B : NearlyCuspidalBoundary W g K δn} {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤)
        3}
      (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
        θ W g δn n B oM),
      0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 10 ^ 6 * Δ * Λ < 1 / 10 ^ 5 →
      e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T →
      b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax →
      σc ≤ ((eg / 2) / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 → μ * Δ < (eg / 2) / (20 *
        egpGraphConst) / 100 →
      0 < σs → σs ≤ ((eg / 2) / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
      vs < (eg / 2) / (20 * egpGraphConst) / 100 → 0 < ζ →
      ζ ≤ ((eg / 2) / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 → ζ ≤ 1 / (1000 * (1000000 * Δ)) →
      εr < (eg / 2) / (20 * egpGraphConst) / (100 * (1000000 * Δ)) → β 2 = β₂ →
      0 < Δ → 100 * Δ * Λ ≤ 1 / 100 → 0 ≤ V → 0 < β 1 → 0 < b → e ≤ 1 / 10 →
      S.SeparatedCollarZero_BIF →
      letI := inducedMetricSpace S.completion.metric
      ∃ (Ψ : W.pieceInterior ⊤ → ℝ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))
        (Kint : W.pieceInterior ⊤ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) →L[ℝ]
          BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))
        (Pc : W.pieceInterior ⊤ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) →L[ℝ] ℝ)
        (rpre : (actualSlotsV2_BAUGD S).stageCloudEnlarged 1 → W.pieceInterior ⊤)
        (pre : (actualSlotsV2_BAUGD S).stageCloud 1 → W.pieceInterior ⊤)
        (ref : (actualSlotsV2_BAUGD S).stageCloud 1 → W.pieceInterior ⊤),
      -- (M)
      (∀ a ∈ S.stageCentres_BIF 1, ContDiff ℝ 2 (Kint a ∘ Ψ a) ∧ ∀ u,
        ‖fderiv ℝ (Kint a ∘ Ψ a) u‖ ≤ egpGraphConst ∧ ‖fderiv ℝ (fderiv ℝ (Kint a ∘ Ψ a)) u‖ ≤
          egpGraphConst) ∧
      -- (OWN)
      (∀ a ∈ S.stageCentres_BIF 1, (∀ z, ‖Pc a z‖ ≤ ‖z‖) ∧ (∀ u, Pc a ((Kint a ∘ Ψ a) u) = u) ∧
        ∀ x : W.pieceInterior ⊤, (dist x a < 100 * Δ * S.rho a ∧ |S.edgeEta_BIF a x| ≤ 8 * Δ ∧
          S.edgeHeightRaw x ≤ 8 * Δ) →
          Pc a ((S.rho a)⁻¹ • blockRestrict (S.stageTagsV2_BAUGD 1) (S.interiorMapOn_BAUGA x)) =
            S.edgeEta_BIF a x) ∧
      -- (Q)
      (∀ a ∈ S.stageCentres_BIF 1, ∀ u,
        blockRestrict (S.stageTagsV2_BAUGD 1) ((Kint a ∘ Ψ a) u) = (Kint a ∘ Ψ a) u) ∧
      -- (TG)
      (∀ a ∈ S.stageCentres_BIF 1, ∀ x : W.pieceInterior ⊤, (dist x a < 100 * Δ * S.rho a ∧
        |S.edgeEta_BIF a x| ≤ 8 * Δ ∧ S.edgeHeightRaw x ≤ 8 * Δ) →
        ‖(S.rho a)⁻¹ • blockRestrict (S.stageTagsV2_BAUGD 1) (S.interiorMapOn_BAUGA x) -
            (Kint a ∘ Ψ a) (S.edgeEta_BIF a x)‖ < (eg / 2) ∧
        ∀ w : TangentSpace 𝓘(ℝ, E3) x,
          ‖(S.rho a)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (fun y => blockRestrict (S.stageTagsV2_BAUGD 1) (S.interiorMapOn_BAUGA y)) x w -
              fderiv ℝ (Kint a ∘ Ψ a) (S.edgeEta_BIF a x) (mvfderiv 𝓘(ℝ, E3) (S.edgeEta_BIF a) x
                w)‖ ≤
            (eg / 2) * Real.sqrt ((S.rho a)⁻¹ ^ 2 * S.completion.metric.inner x w w)) ∧
      -- (SEL)
      (∀ x, (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap (rpre x).val) = x.1) ∧
      (∀ x, ref x ∈ S.stageCentres_BIF 1 ∧ (dist (pre x) (ref x) < 100 * Δ * S.rho (ref x) ∧
        |S.edgeEta_BIF (ref x) (pre x)| ≤ 7 * Δ ∧ S.edgeHeightRaw (pre x) ≤ 7 * Δ) ∧
        dist (pre x) (ref x) < stageDomain_BIF Δ 1 * S.rho (ref x) ∧
        (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap (pre x).val) = x.1) ∧
      -- (LOC)
      (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 1),
        ∀ y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 1,
          ‖augIntProjCLM_BAUGC (y - x)‖ ≤ (5 / 4 * sg) * S.rho (ref ⟨x, hx⟩) / Γ →
          ∃ q : W.pieceInterior ⊤, (dist q (ref ⟨x, hx⟩) < 100 * Δ * S.rho (ref ⟨x, hx⟩) ∧
            |S.edgeEta_BIF (ref ⟨x, hx⟩) q| ≤ 8 * Δ ∧ S.edgeHeightRaw q ≤ 8 * Δ) ∧
            dist q (ref ⟨x, hx⟩) < stageDomain_BIF Δ 1 * S.rho (ref ⟨x, hx⟩) ∧
            (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val) = y) ∧
      -- (COV)
      (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 1), ∀ u : ℝ,
        ‖u - S.edgeEta_BIF (ref ⟨x, hx⟩) (pre ⟨x, hx⟩)‖ ≤ 2 * (5 / 4 * sg) / Γ →
        ∃ q : W.pieceInterior ⊤, (dist q (ref ⟨x, hx⟩) < 100 * Δ * S.rho (ref ⟨x, hx⟩) ∧
          |S.edgeEta_BIF (ref ⟨x, hx⟩) q| ≤ 8 * Δ ∧ S.edgeHeightRaw q ≤ 8 * Δ) ∧
          dist q (ref ⟨x, hx⟩) < stageDomain_BIF Δ 1 * S.rho (ref ⟨x, hx⟩) ∧
          S.edgeEta_BIF (ref ⟨x, hx⟩) q = u ∧
          (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val) ∈
            (actualSlotsV2_BAUGD S).stageCloudEnlarged 1) ∧
      -- (PRE)
      (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 1), ∀ q : W.pieceInterior ⊤,
        (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val) = x →
        (dist q (ref ⟨x, hx⟩) < 100 * Δ * S.rho (ref ⟨x, hx⟩) ∧ |S.edgeEta_BIF (ref ⟨x, hx⟩) q| ≤
          8 * Δ ∧ S.edgeHeightRaw q ≤ 8 * Δ) ∧ dist q (ref ⟨x, hx⟩) < stageDomain_BIF Δ 1 * S.rho
          (ref ⟨x, hx⟩) ∧
          S.edgeEta_BIF (ref ⟨x, hx⟩) q = S.edgeEta_BIF (ref ⟨x, hx⟩) (pre ⟨x, hx⟩)) ∧
      -- (MCb)
      (∀ sel : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → W.pieceInterior ⊤,
        (∀ x ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 1,
          (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap (sel x).val) = x) →
        ∀ L' : ℝ, 0 ≤ L' → L' * (5 / 4 * sg) ≤ 1 / 5 →
        ∀ x ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 1,
        ∀ y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 1,
          dist y x ≤ L' * max ((5 / 4 * sg) * S.rho (sel y)) ((5 / 4 * sg) * S.rho (sel x)) →
          (5 / 4 * sg) * S.rho (sel x) / (5 / 3) ≤ (5 / 4 * sg) * S.rho (sel y) ∧
            (5 / 4 * sg) * S.rho (sel y) ≤ 5 / 3 * ((5 / 4 * sg) * S.rho (sel x))) ∧
      -- (PP-int)
      (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 1), ∀ q : W.pieceInterior ⊤,
        (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val) = x →
        ∀ m : S.MarkerIdx_BAUGC, S.rho (S.markerCentre_BAUGC m) < S.rho q / 5 →
          ∀ v : ℝ, ((fderiv ℝ (Kint (ref ⟨x, hx⟩) ∘ Ψ (ref ⟨x, hx⟩))
            (S.edgeEta_BIF (ref ⟨x, hx⟩) (pre ⟨x, hx⟩)) v) (S.markerTag_BAUGC m)).snd = 0) ∧
      -- (SB-int)
      (∀ a ∈ S.stageCentres_BIF 1, ∀ m : S.MarkerIdx_BAUGC,
        S.rho (S.markerCentre_BAUGC m) ≤ smallBlockFactor_BAUGC 1 * S.rho a →
        ∀ u, (Kint a ∘ Ψ a) u (S.markerTag_BAUGC m) = 0) ∧
      -- (FM*-int)
      (∀ εc σ' : ℝ, 0 < εc → 0 ≤ σ' → σ' ≤ εc / 10000 → ∀ (x₀ : W.pieceInterior ⊤)
        (m : S.MarkerIdx_BAUGC), S.markerStage_BAUGC m = 1 → ∀ p ∈ S.markerCore7_BAUGC m,
        ∀ y (hy : y ∈ (actualSlotsV2_BAUGD S).stageCloud 1),
          (closedBall y (80 * εc⁻¹ * (σ' * S.rho (if hyT : y ∈ (actualSlotsV2_BAUGD
            S).stageCloudEnlarged 1
              then rpre ⟨y, hyT⟩ else x₀))) ∩
            ball ((actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap p.val))
              (8 * εc⁻¹ * (σ' * S.rho (if hpT : (actualSlotsV2_BAUGD S).stageProj 1
                  (S.boundaryOriginalMap p.val) ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 1
                then rpre ⟨_, hpT⟩ else x₀)))).Nonempty →
          S.markerCLM_BAUGC m y = S.rho (S.markerCentre_BAUGC m) ∧
          ∀ v : ℝ, ((fderiv ℝ (Kint (ref ⟨y, hy⟩) ∘ Ψ (ref ⟨y, hy⟩))
            (S.edgeEta_BIF (ref ⟨y, hy⟩) (pre ⟨y, hy⟩)) v) (S.markerTag_BAUGC m)).snd = 0) ∧
      -- (ZB*-int)
      (∀ εc σ' : ℝ, 0 < εc → σ' ≤ εc / 10000 → ∀ (x₀ : W.pieceInterior ⊤)
        (k : S.ZeroIdx_BAUGC) (p : W.pieceInterior ⊤),
        (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap p.val) ∈
          (actualSlotsV2_BAUGD S).stageCloud 1 →
        200 * S.zeroRadius_BAUGC k / T < S.rho p →
        ∀ y (hy : y ∈ (actualSlotsV2_BAUGD S).stageCloud 1),
          (closedBall y (80 * εc⁻¹ * (σ' * S.rho (if hyT : y ∈ (actualSlotsV2_BAUGD
            S).stageCloudEnlarged 1
              then rpre ⟨y, hyT⟩ else x₀))) ∩
            ball ((actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap p.val))
              (8 * εc⁻¹ * (σ' * S.rho (if hpT : (actualSlotsV2_BAUGD S).stageProj 1
                  (S.boundaryOriginalMap p.val) ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 1
                then rpre ⟨_, hpT⟩ else x₀)))).Nonempty →
          S.zeroBlockCLM_BAUGC k y = 0 ∧
          ∀ v : ℝ, (fderiv ℝ (Kint (ref ⟨y, hy⟩) ∘ Ψ (ref ⟨y, hy⟩))
            (S.edgeEta_BIF (ref ⟨y, hy⟩) (pre ⟨y, hy⟩)) v) (S.zeroTag_BAUGC k) = 0)
  := port_edge_interior_table_BAUGP (sg := 5 / 4 * sg) (eg := eg / 2) hΓ
    (by linarith only [hsg]) (by linarith only [hsgΓ]) (by linarith only [heg])
    (by linarith only [heg1])

/-- **(PRE~) on the core cloud, both directions**: two preimages in `W°` of one point of `S₁` have
comparable scales, `ρ q₁ ≤ 5/3·ρ q₂` and `ρ q₂ ≤ 5/3·ρ q₁` (`S₁ ⊆ S̃₁`). -/
theorem port_edge_cloud_scale_core_BPE {Δ : ℝ} (hΔ : 1200 ≤ Δ) {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
    {βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
    {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
    {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {n : ℕ}
    {B : NearlyCuspidalBoundary W g K δn}
    {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
    (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
      θ W g δn n B oM)
    (hΛ : 0 ≤ Λ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100) (hΛΔ : 10 ^ 6 * Δ * Λ < 1 / 10 ^ 5)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hΛzT : 20 * Λz ≤ T) (hΔ0 : 0 < Δ)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) (he10 : e ≤ 1 / 10)
    (hsep : S.SeparatedCollarZero_BIF)
    {x : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 1) {q₁ q₂ : W.pieceInterior ⊤}
    (h1 : (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q₁.val) = x)
    (h2 : (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q₂.val) = x) :
    S.rho q₁ ≤ 5 / 3 * S.rho q₂ ∧ S.rho q₂ ≤ 5 / 3 * S.rho q₁ := by
  have hxT := actualSlotsV2_stageCloud_subset_BAUGD S hΔ0.le 1 hx
  exact ⟨port_edge_cloud_scale_BAUGP Δ hΔ S hΛ hμ hτ hΛΔ he hT hΛzT hΔ0 hΔΛ hV hβ1 hb he10 hsep
    x hxT q₁ q₂ h1 h2, port_edge_cloud_scale_BAUGP Δ hΔ S hΛ hμ hτ hΛΔ he hT hΛzT hΔ0 hΔΛ hV hβ1
    hb he10 hsep x hxT q₂ q₁ h2 h1⟩

end DifferentialGeometry.Geometry.Collapse

import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryProducerDPCircleOfPort
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryProducerDPEdge
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryProducerDPSlim
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryProducerPremises

/-!
# The validity certificate of the DP thresholds, modulo the circle port theorem (BAUG-C, G8b)

`exists_validDPThresholds_of_circlePort_BAUGC` (D76-2): for every choice `(Γ, Σ, eg)` with the
numbers of ProducerDP v3.1 and every `ν` with `3ν ≤ thr`, there is a CHI record `χ`
(`BoundaryChainThresholds_BSTD2`: `ν`, `eg / 2`, the first thresholds `σ η₂ γ₀ ηc θt` of the circle
table, the late thresholds `η₁` (circle), `Lc₁ η₀₁` (edge), `θs Lc₂ η₀₂` (slim) skolemized in
`(β₂, Δ)` from the three stage tables, `ϑ₀ = min_j eg j / (16 P_*)`) together with
`ValidDPThresholds_BAUGC Γ Sg eg χ`: χ and the certificate are chosen together, before every
register parameter. The three stage tables are `exists_boundaryCircleTable_of_port_BAUGC` (G6a,
with the circle port theorem `hport` as hypothesis until O-PORT-A delivers it),
`exists_boundaryEdgeTable_BAUGC` (G5) and `exists_boundarySlimTable_BAUGC` (G4b); the per-stage
use of the premises (`Lc₁`, `Lc₂`, `η₀₁`, `η₀₂` kept apart) matches the closed CHI block exactly,
which is why the register's `chi_block_BSTD2` supplies `ProducerPremises_BAUGC` as is.
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
/-- **The validity certificate of the DP thresholds, conditional on the circle port theorem**
(D76-2): `χ` and `ValidDPThresholds_BAUGC Γ Sg eg χ` are produced together from the three stage
tables of ProducerDP v3.1. -/
theorem exists_validDPThresholds_of_circlePort_BAUGC
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
    (hν : 0 < ν) (hν3 : 3 * ν ≤ threeSplittingExclusionThreshold.{0, 0}) :
    ∃ χ : BoundaryChainThresholds_BSTD2, χ.ν = ν ∧ ValidDPThresholds_BAUGC Γ Sg eg χ := by
  have hthr1 := threeSplittingExclusionThreshold_lt.{0, 0}
  have hν1 : ν < 1 := by linarith
  have hP0 : 0 < 16 * bmConst_BAUGC := by linarith [one_le_bmConst_BAUGC]
  obtain ⟨σ, hσ, hσ1, η₂, γ₀, ηc, θt, hη₂, hγ₀, hηc, hθt, hθt1, hC⟩ :=
    exists_boundaryCircleTable_of_port_BAUGC hport (hΓ 0) (hΓ1 0) (hsg 0) (hsgΓ 0) hsgC0 (heg 0)
      (heg1 0) (hegΓ 0) hν hν1
  clear hport
  have hEdge : ∀ β₂ : ℝ, 0 < β₂ → β₂ < 1 / 1000000 → ∀ Δ : ℝ, 1200 ≤ Δ → _ := fun β₂ h1 h2 Δ h3 =>
    exists_boundaryEdgeTable_BAUGC (hΓ 1) (hΓ1 1) (hsg 1) (hsgΓ 1) hsgC1 (heg 1) (heg1 1)
      (hegΓ 1) β₂ h1 h2 Δ h3
  have hSlim : ∀ β₂ : ℝ, 0 < β₂ → β₂ < 1 / 1000000 → ∀ Δ : ℝ, 1200 ≤ Δ → _ := fun β₂ h1 h2 Δ h3 =>
    exists_boundarySlimTable_BAUGC (hΓ 2) (hΓ1 2) (hsg 2) (hsgΓ 2) hsgC2 (heg 2) (heg1 2)
      (hegΓ 2) β₂ h1 (h2.trans (by norm_num)) Δ h3
  choose η₁ hη₁ hCΔ using hC
  choose Lc₁ η₀₁ hLc₁ hη₀₁ hE using hEdge
  choose θs hθs hθs1 Lc₂ η₀₂ hLc₂ hη₀₂ hS using hSlim
  clear hLc₁ hθs1 hLc₂
  let Cβ : ℝ → ℝ → Prop := fun β₂ Δ => 0 < β₂ ∧ β₂ < 1 / 1000000 ∧ 1200 ≤ Δ
  let χ : BoundaryChainThresholds_BSTD2 :=
    { ν := ν
      eg := fun j => eg j / 2
      σ := σ
      η₂ := η₂
      γ₀ := γ₀
      ηc := ηc
      θt := θt
      ϑ₀ := min (eg 0) (min (eg 1) (eg 2)) / (16 * bmConst_BAUGC)
      η₁ := fun β₂ Δ => if h : Cβ β₂ Δ then η₁ Δ h.2.2 else 1
      Lc₁ := fun β₂ Δ => if h : Cβ β₂ Δ then Lc₁ β₂ h.1 h.2.1 Δ h.2.2 else 1
      η₀₁ := fun β₂ Δ => if h : Cβ β₂ Δ then η₀₁ β₂ h.1 h.2.1 Δ h.2.2 else 1
      θs := fun β₂ Δ => if h : Cβ β₂ Δ then θs β₂ h.1 h.2.1 Δ h.2.2 else 1
      Lc₂ := fun β₂ Δ => if h : Cβ β₂ Δ then Lc₂ β₂ h.1 h.2.1 Δ h.2.2 else 1
      η₀₂ := fun β₂ Δ => if h : Cβ β₂ Δ then η₀₂ β₂ h.1 h.2.1 Δ h.2.2 else 1
      ν_pos := hν
      three_ν_le := hν3
      eg_pos := fun j => half_pos (heg j)
      σ_pos := hσ
      η₂_pos := hη₂
      γ₀_pos := hγ₀
      ηc_pos := hηc
      θt_pos := hθt
      ϑ₀_pos := div_pos (lt_min (heg 0) (lt_min (heg 1) (heg 2))) hP0
      η₁_pos := fun β₂ Δ => dite_mem_BSTD1 (fun x => 0 < x) (fun h => hη₁ Δ h.2.2) one_pos
      η₀₁_pos := fun β₂ Δ =>
        dite_mem_BSTD1 (fun x => 0 < x) (fun h => hη₀₁ β₂ h.1 h.2.1 Δ h.2.2) one_pos
      θs_pos := fun β₂ Δ =>
        dite_mem_BSTD1 (fun x => 0 < x) (fun h => hθs β₂ h.1 h.2.1 Δ h.2.2)
          one_pos
      η₀₂_pos := fun β₂ Δ =>
        dite_mem_BSTD1 (fun x => 0 < x)
          (fun h => hη₀₂ β₂ h.1 h.2.1 Δ h.2.2) one_pos }
  refine ⟨χ, rfl, fun j => rfl, ?_⟩
  intro β₂ hβ₂ hβ₂1 Δ hΔ K A β βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W _
    g δn n B oM S hP hsep
  have hCβ : Cβ β₂ Δ := ⟨hβ₂, hβ₂1, hΔ⟩
  have e1 : χ.η₁ β₂ Δ = η₁ Δ hΔ := dite_eq_left hCβ
  have e2 : χ.Lc₁ β₂ Δ = Lc₁ β₂ hβ₂ hβ₂1 Δ hΔ := dite_eq_left hCβ
  have e3 : χ.η₀₁ β₂ Δ = η₀₁ β₂ hβ₂ hβ₂1 Δ hΔ := dite_eq_left hCβ
  have e4 : χ.θs β₂ Δ = θs β₂ hβ₂ hβ₂1 Δ hΔ := dite_eq_left hCβ
  have e5 : χ.Lc₂ β₂ Δ = Lc₂ β₂ hβ₂ hβ₂1 Δ hΔ := dite_eq_left hCβ
  have e6 : χ.η₀₂ β₂ Δ = η₀₂ β₂ hβ₂ hβ₂1 Δ hΔ := dite_eq_left hCβ
  obtain ⟨⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19,
    f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31⟩, ⟨d1, d2, d3, d4, d5, d6, d7, d8,
    d9, d10, d11⟩, ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩, ⟨hΔ0, hΔΛ, hV, hβ1, hb, he⟩, hθ0,
    hθ⟩ := hP
  rw [e1] at f21 f22
  rw [e3] at d1 d3
  rw [e2] at d4
  rw [e6] at m2
  rw [e5] at m3
  rw [e4] at m4 m5 m6 m8
  have f4' : 10 ^ 6 * Δ * Λ < 1 / 10 ^ 5 := by
    have h := f4
    norm_num at h ⊢
    linarith only [h]
  have hθ' : θ ≤ min (eg 0) (min (eg 1) (eg 2)) / (16 * bmConst_BAUGC) := hθ
  have h16 : ∀ j, 16 * bmConst_BAUGC * θ ≤ eg j := by
    intro j
    have h1 : θ * (16 * bmConst_BAUGC) ≤ min (eg 0) (min (eg 1) (eg 2)) :=
      (le_div_iff₀ hP0).mp hθ'
    have hj : min (eg 0) (min (eg 1) (eg 2)) ≤ eg j := by
      fin_cases j
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (min_le_left _ _)
      · exact (min_le_right _ _).trans (min_le_right _ _)
    linarith
  obtain ⟨R₀, hR₀⟩ := hCΔ Δ hΔ S f1 f2 f3 f4' f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 hΔ0 hΔΛ hV hβ1 hb he hθ0 (h16 0) hsep
  obtain ⟨R₁, hR₁⟩ := hE β₂ hβ₂ hβ₂1 Δ hΔ S f1 f2 f3 f4' f6 f7 f29 d1 d2 d3 d4 f10 d5 d6 f23 d7 d8
    f26 d9 d10 d11 m1 hΔ0 hΔΛ hV hβ1 hb he hθ0 (h16 1) hsep
  obtain ⟨R₂, hR₂⟩ := hS β₂ hβ₂ hβ₂1 Δ hΔ S f1 f2 f3 f4' f6 f7 f29 m1 m2 m3
    f23 m4 m5 f26 m6 m7 m8 m9 hΔ0 hΔΛ hV hβ1 hb he hθ0 (h16 2) hsep
  exact ⟨{ separated := hsep, circle := R₀, edge := R₁, slim := R₂,
           circle_spec := hR₀, edge_spec := hR₁, slim_spec := hR₂ }⟩

end DifferentialGeometry.Geometry.Collapse

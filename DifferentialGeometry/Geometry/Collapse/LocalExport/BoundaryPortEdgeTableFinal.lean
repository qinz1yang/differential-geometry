import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeTableB

/-!
# PORT target: the interior edge stage table, final assembly (lane S-PORT-EDGE)

Completes the frozen port targets of the edge stage (PortTargets v3.1,
`docs/geometrization/chapter14/evidence/boundary/PortTargets-v3.1.lean.txt`, and the supplement
`PortTargets-v3-supplement.lean.txt`) on top of the clause layers `BoundaryPortEdgeTableA` and
`BoundaryPortEdgeTableB`:

* `edgeTable_FM_BPE`, `edgeTable_ZB_BPE` — the clauses (FM*-int) and (ZB*-int) in the frozen wording
  (classical windows around the radius selections `rpre`);
* **`port_edge_interior_table_BAUGP`** — the interior half of the stage-`1` table on the actual
  slot, STRENGTHENED: the unused premises `Γ < 1`, `sg < Γ³/(100·egpGraphConst)`,
  `eg < Γ·sg/100` and `eg < sg/1000` of the frozen text are dropped; the verbatim frozen form is
  kept as an `example` right after it. Data: `Ψ a = edgeStageModel_BPE` (EGP06's model
  `edgeModelOf_BPE` of the `edgeB` centre `a`), `Kint a = id`, `Pc a = edgeStageOwn_BPE`, core
  preimages `pre` with references `ref` (threshold-`7` cores), radius preimages `rpre` (any
  preimage). Closed twin `exists_edgeStagePlanes_PLN`. No premise `0 ≤ σc` is needed (N76-8 not
  used);
* **`port_edge_cloud_scale_BAUGP`** — (PRE~), the frozen supplement statement verbatim.
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

namespace BoundarySupply

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
  θ W g δn n B oM) (sgnf cf : S.EdgeIdx_BAUGD → S.IntTag_BAUGA → ℝ)
  (jref : (actualSlotsV2_BAUGD S).stageCloud 1 → S.EdgeIdx_BAUGD)
  (pre : (actualSlotsV2_BAUGD S).stageCloud 1 → W.pieceInterior ⊤)
  (rpre : (actualSlotsV2_BAUGD S).stageCloudEnlarged 1 → W.pieceInterior ⊤)

open Classical in
/-- **(FM*-int)** on the classical contributor windows: a stage-`1` marker with a threshold-`7`
core point `p` is full at every cloud point `y` of the window and annihilates the plane
`DΨ(η(pre y))`. -/
theorem edgeTable_FM_BPE (hΔ1 : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) {eg : ℝ} (heg0 : 0 ≤ eg) (heg : eg < 1 / 100)
    (hTG : ∀ i : S.EdgeIdx_BAUGD, ∀ x : W.pieceInterior ⊤,
      (letI := inducedMetricSpace S.completion.metric
       dist x i.1 < 100 * Δ * S.rho i.1) →
      |S.edgeEta_BIF i.1 x| ≤ 8 * Δ → S.edgeHeightRaw x ≤ 8 * Δ →
      ‖(S.rho i.1)⁻¹ • blockRestrict (S.stageTagsV2_BAUGD 1) (S.interiorMapOn_BAUGA x) -
        S.edgeModelOf_BPE i (sgnf i) (cf i) (S.edgeEta_BIF i.1 x)‖ < eg)
    (hpre : ∀ x, (letI := inducedMetricSpace S.completion.metric
        dist (pre x) (jref x).1 < 100 * Δ * S.rho (jref x).1) ∧
      |S.edgeEta_BIF (jref x).1 (pre x)| ≤ 7 * Δ ∧ S.edgeHeightRaw (pre x) ≤ 7 * Δ ∧
      (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap (pre x).val) = x.1)
    (hrpre : ∀ x, (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap (rpre x).val) = x.1) :
    ∀ εc σ' : ℝ, 0 < εc → 0 ≤ σ' → σ' ≤ εc / 10000 → ∀ (x₀ : W.pieceInterior ⊤)
      (m : S.MarkerIdx_BAUGC), S.markerStage_BAUGC m = 1 → ∀ p ∈ S.markerCore7_BAUGC m,
      ∀ y (hy : y ∈ (actualSlotsV2_BAUGD S).stageCloud 1),
        (closedBall y (80 * εc⁻¹ * (σ' * S.rho (if hyT : y ∈
            (actualSlotsV2_BAUGD S).stageCloudEnlarged 1
            then rpre ⟨y, hyT⟩ else x₀))) ∩
          ball ((actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap p.val))
            (8 * εc⁻¹ * (σ' * S.rho (if hpT : (actualSlotsV2_BAUGD S).stageProj 1
                (S.boundaryOriginalMap p.val) ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 1
              then rpre ⟨_, hpT⟩ else x₀)))).Nonempty →
        S.markerCLM_BAUGC m y = S.rho (S.markerCentre_BAUGC m) ∧
        ∀ v : ℝ, ((fderiv ℝ
            (⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
            S.edgeStageModel_BPE sgnf cf (jref ⟨y, hy⟩).1)
          (S.edgeEta_BIF (jref ⟨y, hy⟩).1 (pre ⟨y, hy⟩)) v) (S.markerTag_BAUGC m)).snd = 0 := by
  intro εc σ' hε hσ hσε x₀ m hm p hp y hy hwin
  rcases m with i | i | i
  · exact absurd hm (by simp [BoundarySupplyCore.markerStage_BAUGC])
  · exact absurd hm (by simp [BoundarySupplyCore.markerStage_BAUGC])
  · have hp' : (letI := inducedMetricSpace S.completion.metric
        dist p i.1 < 100 * Δ * S.rho i.1) ∧ |S.edgeEta_BIF i.1 p| ≤ 7 * Δ ∧
        S.edgeHeightRaw p ≤ 7 * Δ := hp
    have h := hpre ⟨y, hy⟩
    have hΔ0 : 0 < Δ := by linarith only [hΔ1]
    have hyT : y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 1 :=
      actualSlotsV2_stageCloud_subset_BAUGD S hΔ0.le 1 hy
    have hpT := S.stageProj_mem_stageCloudEnlarged_one_BPE i hp'.1
      (by linarith only [hp'.2.1, hΔ0]) (by linarith only [hp'.2.2, hΔ0])
    rw [dite_eq_left hyT, dite_eq_left hpT] at hwin
    have hj := (Set.Finite.mem_toFinset _).mp (jref ⟨y, hy⟩).2
    rw [S.edgeStageModel_comp_BPE sgnf cf hj]
    exact S.edge_full_marker_point_BPE hΔ1 hΛ hΛΔ hV hβ1 hb heg0 heg hε hσ hσε i hp'.1 hp'.2.1
      hp'.2.2 (jref ⟨y, hy⟩) (sgnf _) (cf _) h.1 h.2.1 h.2.2.1 h.2.2.2 (hrpre ⟨y, hyT⟩)
      (hrpre ⟨_, hpT⟩) hwin
      (hTG _ (pre ⟨y, hy⟩) h.1 (by linarith only [h.2.1, hΔ0]) (by linarith only [h.2.2.1, hΔ0]))

open Classical in
/-- **(ZB*-int)** on the classical contributor windows: for a zero centre `k` and a preimage `p`
of a point of `S₁` with `ρ(p) > 200R_k/T`, the zero block of every window cloud point `y` and of
the plane `DΨ(η(pre y))` vanish. -/
theorem edgeTable_ZB_BPE (hΔ1 : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) (hT : 1600 * (1000000 * Δ) ≤ T) (he : e < 1 / 40)
    (hpre : ∀ x, (letI := inducedMetricSpace S.completion.metric
        dist (pre x) (jref x).1 < 100 * Δ * S.rho (jref x).1) ∧
      |S.edgeEta_BIF (jref x).1 (pre x)| ≤ 7 * Δ ∧ S.edgeHeightRaw (pre x) ≤ 7 * Δ ∧
      (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap (pre x).val) = x.1)
    (hrpre : ∀ x, (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap (rpre x).val) = x.1) :
    ∀ εc σ' : ℝ, 0 < εc → σ' ≤ εc / 10000 → ∀ (x₀ : W.pieceInterior ⊤)
      (k : S.ZeroIdx_BAUGC) (p : W.pieceInterior ⊤),
      (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap p.val) ∈
        (actualSlotsV2_BAUGD S).stageCloud 1 →
      200 * S.zeroRadius_BAUGC k / T < S.rho p →
      ∀ y (hy : y ∈ (actualSlotsV2_BAUGD S).stageCloud 1),
        (closedBall y (80 * εc⁻¹ * (σ' * S.rho (if hyT : y ∈
            (actualSlotsV2_BAUGD S).stageCloudEnlarged 1
            then rpre ⟨y, hyT⟩ else x₀))) ∩
          ball ((actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap p.val))
            (8 * εc⁻¹ * (σ' * S.rho (if hpT : (actualSlotsV2_BAUGD S).stageProj 1
                (S.boundaryOriginalMap p.val) ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 1
              then rpre ⟨_, hpT⟩ else x₀)))).Nonempty →
        S.zeroBlockCLM_BAUGC k y = 0 ∧
        ∀ v : ℝ, (fderiv ℝ
            (⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
            S.edgeStageModel_BPE sgnf cf (jref ⟨y, hy⟩).1)
          (S.edgeEta_BIF (jref ⟨y, hy⟩).1 (pre ⟨y, hy⟩)) v) (S.zeroTag_BAUGC k) = 0 := by
  intro εc σ' hε hσε x₀ k p hp hρp y hy hwin
  have h := hpre ⟨y, hy⟩
  have hΔ0 : 0 < Δ := by linarith only [hΔ1]
  have hyT : y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 1 :=
    actualSlotsV2_stageCloud_subset_BAUGD S hΔ0.le 1 hy
  have hpT : (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap p.val) ∈
      (actualSlotsV2_BAUGD S).stageCloudEnlarged 1 :=
    actualSlotsV2_stageCloud_subset_BAUGD S hΔ0.le 1 hp
  rw [dite_eq_left hyT, dite_eq_left hpT] at hwin
  have hj := (Set.Finite.mem_toFinset _).mp (jref ⟨y, hy⟩).2
  rw [S.edgeStageModel_comp_BPE sgnf cf hj]
  exact S.edge_zero_block_point_BPE hΔ1 hΛ hΛΔ hV hβ1 hb hT he hε hσε k hp hρp
    (jref ⟨y, hy⟩) (sgnf _) (cf _) h.1 h.2.1 h.2.2.1 h.2.2.2 (hrpre ⟨y, hyT⟩)
    (hrpre ⟨_, hpT⟩) hwin

end BoundarySupply

open Classical in
/-- **PORT TARGET (EDGE edgeB (EGP02–EGP07), stage `1`)**: the interior stage table of the actual
slot (PortTargets v3.1), STRENGTHENED: the frozen premises `Γ < 1`, `sg < Γ³/(100·egpGraphConst)`,
`eg < Γ·sg/100` and `eg < sg/1000` are not needed and are dropped (the verbatim frozen form is the
`example` below). Data: `Ψ a = edgeStageModel_BPE` (EGP06's model of the `edgeB` centre `a`),
`Kint a = id`, `Pc a = edgeStageOwn_BPE`, core preimages `pre` with references `ref`
(threshold-`7` cores), radius preimages `rpre` (any preimage). Closed twin
`exists_edgeStagePlanes_PLN`. -/
theorem port_edge_interior_table_BAUGP {Γ sg eg : ℝ} (hΓ : 0 < Γ)
    (hsg : 0 < sg) (hsgΓ : sg < Γ / 200)
    (heg : 0 < eg) (heg1 : eg < 1 / 100) :
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
      σc ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 → μ * Δ < eg / (20 * egpGraphConst) / 100 →
      0 < σs → σs ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
      vs < eg / (20 * egpGraphConst) / 100 → 0 < ζ →
      ζ ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 → ζ ≤ 1 / (1000 * (1000000 * Δ)) →
      εr < eg / (20 * egpGraphConst) / (100 * (1000000 * Δ)) → β 2 = β₂ →
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
            (Kint a ∘ Ψ a) (S.edgeEta_BIF a x)‖ < eg ∧
        ∀ w : TangentSpace 𝓘(ℝ, E3) x,
          ‖(S.rho a)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (fun y => blockRestrict (S.stageTagsV2_BAUGD 1) (S.interiorMapOn_BAUGA y)) x w -
              fderiv ℝ (Kint a ∘ Ψ a) (S.edgeEta_BIF a x) (mvfderiv 𝓘(ℝ, E3) (S.edgeEta_BIF a) x
                w)‖ ≤
            eg * Real.sqrt ((S.rho a)⁻¹ ^ 2 * S.completion.metric.inner x w w)) ∧
      -- (SEL)
      (∀ x, (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap (rpre x).val) = x.1) ∧
      (∀ x, ref x ∈ S.stageCentres_BIF 1 ∧ (dist (pre x) (ref x) < 100 * Δ * S.rho (ref x) ∧
        |S.edgeEta_BIF (ref x) (pre x)| ≤ 7 * Δ ∧ S.edgeHeightRaw (pre x) ≤ 7 * Δ) ∧
        dist (pre x) (ref x) < stageDomain_BIF Δ 1 * S.rho (ref x) ∧
        (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap (pre x).val) = x.1) ∧
      -- (LOC)
      (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 1),
        ∀ y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 1,
          ‖augIntProjCLM_BAUGC (y - x)‖ ≤ sg * S.rho (ref ⟨x, hx⟩) / Γ →
          ∃ q : W.pieceInterior ⊤, (dist q (ref ⟨x, hx⟩) < 100 * Δ * S.rho (ref ⟨x, hx⟩) ∧
            |S.edgeEta_BIF (ref ⟨x, hx⟩) q| ≤ 8 * Δ ∧ S.edgeHeightRaw q ≤ 8 * Δ) ∧
            dist q (ref ⟨x, hx⟩) < stageDomain_BIF Δ 1 * S.rho (ref ⟨x, hx⟩) ∧
            (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val) = y) ∧
      -- (COV)
      (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 1), ∀ u : ℝ,
        ‖u - S.edgeEta_BIF (ref ⟨x, hx⟩) (pre ⟨x, hx⟩)‖ ≤ 2 * sg / Γ →
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
        ∀ L' : ℝ, 0 ≤ L' → L' * sg ≤ 1 / 5 →
        ∀ x ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 1,
        ∀ y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 1,
          dist y x ≤ L' * max (sg * S.rho (sel y)) (sg * S.rho (sel x)) →
          sg * S.rho (sel x) / (5 / 3) ≤ sg * S.rho (sel y) ∧
            sg * S.rho (sel y) ≤ 5 / 3 * (sg * S.rho (sel x))) ∧
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
            (S.edgeEta_BIF (ref ⟨y, hy⟩) (pre ⟨y, hy⟩)) v) (S.zeroTag_BAUGC k) = 0) := by
  have hR : sg / Γ < 1 / 100 := by
    rw [div_lt_iff₀ hΓ]
    linarith only [hsgΓ, hΓ]
  have h2sg : 2 * sg / Γ ≤ 1 / 100 := by
    rw [div_le_iff₀ hΓ]
    linarith only [hsgΓ, hΓ]
  intro β₂ hβ₂ hβ₂1 Δ hΔ
  have hΔ1 : 1 ≤ Δ := by linarith only [hΔ]
  refine (edge_row_supply_BPE hΔ1 hβ₂ hβ₂1 heg heg1).elim fun Lc h1 => h1.elim fun η₀ h2 =>
    ⟨Lc, η₀, h2.1, h2.2.1, ?_⟩
  intro K A β βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W _ g δn n B oM S
    hΛ hμ hτ hΛΔ' he hT hTz hb hs hβ1η hLmax hσc hμΔ hσs0 hσs hvs hζ0 hζθ hζL hεr _ hΔ0 hΔΛ hV hβ1
    hb0 _ _
  have h6 : (10 : ℝ) ^ 6 = 1000000 := by norm_num
  have h5 : (10 : ℝ) ^ 5 = 100000 := by norm_num
  rw [h6, h5] at hΛΔ'
  choose sgnf cf hsgn hsm hbd hTG using fun i : S.EdgeIdx_BAUGD =>
    h2.2.2 S hb hs hβ1η hLmax hΛ hΛΔ' hμ hτ hσc hμΔ hσs0 hσs hvs he hT hTz hζ0 hζθ hζL hεr i
  choose jref pre hpre using fun x : (actualSlotsV2_BAUGD S).stageCloud 1 =>
    S.exists_core_of_mem_stageCloud_one_BPE x.2
  have hrp : ∀ x : (actualSlotsV2_BAUGD S).stageCloudEnlarged 1, ∃ r : W.pieceInterior ⊤,
      (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap r.val) = x.1 := by
    intro x
    obtain ⟨r, -, hr⟩ := x.2
    exact ⟨r, hr⟩
  choose rpre hrpre using hrp
  exact ⟨S.edgeStageModel_BPE sgnf cf, fun _ => ContinuousLinearMap.id ℝ _,
    S.edgeStageOwn_BPE, rpre, pre, fun x => (jref x).1,
    S.edgeTable_M_BPE sgnf cf (fun i => ⟨hsm i, hbd i⟩),
    S.edgeTable_OWN_BPE sgnf cf hΔ0, S.edgeTable_Q_BPE sgnf cf,
    S.edgeTable_TG_BPE sgnf cf hTG, hrpre, S.edgeTable_SEL_BPE jref pre hΛ hΔ0 hμ hτ hΔΛ hpre,
    S.edgeTable_LOC_BPE jref pre hΛ hΔ1 hμ hτ hΔΛ hR hpre,
    S.edgeTable_COV_BPE jref pre hΔ1 h2sg hpre,
    S.edgeTable_PRE_BPE jref pre hΛ hΔ0 hμ hτ hΔΛ hpre,
    S.edgeTable_MCb_BPE hsg.le hΔ1 hΛ hΛΔ' hV hβ1 hb0,
    S.edgeTable_PP_BPE sgnf cf jref pre hΔ1 hΛ hΛΔ' hV hβ1 hb0 hpre,
    S.edgeTable_SB_BPE sgnf cf hΔ0 hΛ hΛΔ',
    S.edgeTable_FM_BPE sgnf cf jref pre rpre hΔ1 hΛ hΛΔ' hV hβ1 hb0 heg.le heg1
      (fun i x h1 h2 h3 => (hTG i x h1 h2 h3).1) hpre hrpre,
    S.edgeTable_ZB_BPE sgnf cf jref pre rpre hΔ1 hΛ hΛΔ' hV hβ1 hb0 hT he hpre hrpre⟩

open Classical in
/-- `port_edge_interior_table_BAUGP` in the verbatim frozen form of PortTargets v3.1 (with the four
unused premises `hΓ1`, `hsgC`, `hegΓ`, `hegS`; the long frozen comments are shortened to their
clause labels). -/
example {Γ sg eg : ℝ} (hΓ : 0 < Γ) (hΓ1 : Γ < 1)
    (hsg : 0 < sg) (hsgΓ : sg < Γ / 200) (hsgC : sg < Γ ^ 3 / (100 * egpGraphConst))
    (heg : 0 < eg) (heg1 : eg < 1 / 100) (hegΓ : eg < Γ * sg / 100) (hegS : eg < sg / 1000) :
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
      σc ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 → μ * Δ < eg / (20 * egpGraphConst) / 100 →
      0 < σs → σs ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
      vs < eg / (20 * egpGraphConst) / 100 → 0 < ζ →
      ζ ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 → ζ ≤ 1 / (1000 * (1000000 * Δ)) →
      εr < eg / (20 * egpGraphConst) / (100 * (1000000 * Δ)) → β 2 = β₂ →
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
            (Kint a ∘ Ψ a) (S.edgeEta_BIF a x)‖ < eg ∧
        ∀ w : TangentSpace 𝓘(ℝ, E3) x,
          ‖(S.rho a)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (fun y => blockRestrict (S.stageTagsV2_BAUGD 1) (S.interiorMapOn_BAUGA y)) x w -
              fderiv ℝ (Kint a ∘ Ψ a) (S.edgeEta_BIF a x) (mvfderiv 𝓘(ℝ, E3) (S.edgeEta_BIF a) x
                w)‖ ≤
            eg * Real.sqrt ((S.rho a)⁻¹ ^ 2 * S.completion.metric.inner x w w)) ∧
      -- (SEL)
      (∀ x, (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap (rpre x).val) = x.1) ∧
      (∀ x, ref x ∈ S.stageCentres_BIF 1 ∧ (dist (pre x) (ref x) < 100 * Δ * S.rho (ref x) ∧
        |S.edgeEta_BIF (ref x) (pre x)| ≤ 7 * Δ ∧ S.edgeHeightRaw (pre x) ≤ 7 * Δ) ∧
        dist (pre x) (ref x) < stageDomain_BIF Δ 1 * S.rho (ref x) ∧
        (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap (pre x).val) = x.1) ∧
      -- (LOC)
      (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 1),
        ∀ y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 1,
          ‖augIntProjCLM_BAUGC (y - x)‖ ≤ sg * S.rho (ref ⟨x, hx⟩) / Γ →
          ∃ q : W.pieceInterior ⊤, (dist q (ref ⟨x, hx⟩) < 100 * Δ * S.rho (ref ⟨x, hx⟩) ∧
            |S.edgeEta_BIF (ref ⟨x, hx⟩) q| ≤ 8 * Δ ∧ S.edgeHeightRaw q ≤ 8 * Δ) ∧
            dist q (ref ⟨x, hx⟩) < stageDomain_BIF Δ 1 * S.rho (ref ⟨x, hx⟩) ∧
            (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val) = y) ∧
      -- (COV)
      (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 1), ∀ u : ℝ,
        ‖u - S.edgeEta_BIF (ref ⟨x, hx⟩) (pre ⟨x, hx⟩)‖ ≤ 2 * sg / Γ →
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
        ∀ L' : ℝ, 0 ≤ L' → L' * sg ≤ 1 / 5 →
        ∀ x ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 1,
        ∀ y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 1,
          dist y x ≤ L' * max (sg * S.rho (sel y)) (sg * S.rho (sel x)) →
          sg * S.rho (sel x) / (5 / 3) ≤ sg * S.rho (sel y) ∧
            sg * S.rho (sel y) ≤ 5 / 3 * (sg * S.rho (sel x))) ∧
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
  := (fun _ _ _ _ => port_edge_interior_table_BAUGP hΓ hsg hsgΓ heg heg1) hΓ1 hsgC hegΓ hegS

/-- **PORT TARGET (PRE~), EDGE `edgeB`, stage `1`** (frozen supplement, verbatim): two preimages in
`W°` of the same point of the enlarged edge cloud `S̃₂ = π₁F_∂(Ã₁)` have `ρ q₁ ≤ 5/3·ρ q₂`.
Closed twin: the fourth clause of `fc27_edge_cloud_scale` at distance `0`; here
`edge_scale_ratio_BPE` with `σ = L' = 0`. -/
theorem port_edge_cloud_scale_BAUGP :
    ∀ Δ : ℝ, 1200 ≤ Δ →
    ∀ {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
      {βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
      {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
      {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {n : ℕ}
      {B : NearlyCuspidalBoundary W g K δn}
      {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
      (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
        θ W g δn n B oM),
      0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 10 ^ 6 * Δ * Λ < 1 / 10 ^ 5 →
      e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T →
      0 < Δ → 100 * Δ * Λ ≤ 1 / 100 → 0 ≤ V → 0 < β 1 → 0 < b → e ≤ 1 / 10 →
      S.SeparatedCollarZero_BIF →
      -- (PRE~)
      ∀ x ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 1, ∀ q₁ q₂ : W.pieceInterior ⊤,
        (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q₁.val) = x →
        (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q₂.val) = x →
        S.rho q₁ ≤ 5 / 3 * S.rho q₂ := by
  intro Δ hΔ K A β βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W _ g δn n B oM
    S hΛ _ _ hΛΔ' _ _ _ _ _ hV hβ1 hb _ _ x hx q₁ q₂ h1 h2
  have h6 : (10 : ℝ) ^ 6 = 1000000 := by norm_num
  have h5 : (10 : ℝ) ^ 5 = 100000 := by norm_num
  rw [h6, h5] at hΛΔ'
  have hp : (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q₂.val) ∈
      (actualSlotsV2_BAUGD S).stageCloudEnlarged 1 := by
    rw [h2]
    exact hx
  have hq : (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q₁.val) ∈
      (actualSlotsV2_BAUGD S).stageCloudEnlarged 1 := by
    rw [h1]
    exact hx
  have hd : dist ((actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q₁.val))
      ((actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q₂.val)) ≤
      0 * max (0 * S.rho q₁.val) (0 * S.rho q₂.val) := by
    rw [h1, h2, dist_self, zero_mul]
  exact (S.edge_scale_ratio_BPE hΛ (by linarith only [hΔ]) hΛΔ' hV hβ1 hb le_rfl le_rfl
    (by norm_num) hp hq hd).2

end DifferentialGeometry.Geometry.Collapse

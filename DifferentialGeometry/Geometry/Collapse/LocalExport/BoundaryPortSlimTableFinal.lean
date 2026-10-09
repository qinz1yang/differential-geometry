import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSlimTable

/-!
# PORT target: the interior slim stage table, final assembly (lane B-PORT-SLIMc)

Completes the frozen port targets of the slim stage (PortTargets v3.1,
`docs/geometrization/chapter14/evidence/boundary/PortTargets-v3.1.lean.txt`, and the supplement
`PortTargets-v3-supplement.lean.txt`) on top of the clause layer `BoundaryPortSlimTable`:

* `slimTable_FM_BPS`, `slimTable_ZB_BPS` — the clauses (FM*-int) and (ZB*-int) in the frozen wording
  (classical windows around the radius selections `rpre`);
* **`port_slim_interior_table_BAUGP`** — the interior half of the stage-`2` table on the actual
  slot, STRENGTHENED: the unused premises `Γ < 1`, `sg < Γ³/(100·sgpGraphBound)` and
  `eg < Γ·sg/100` of the frozen text are dropped; the verbatim frozen form is kept as an `example`
  right after it;
* **`port_slim_cloud_scale_BAUGP`** — (PRE~), the frozen supplement statement verbatim.
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
  θ W g δn n B oM) (sgnf cf zsgnf zcf : S.SlimIdx_BAUGD → W.pieceInterior ⊤ → ℝ)
  (jref : (actualSlotsV2_BAUGD S).stageCloud 2 → S.SlimIdx_BAUGD)
  (pre : (actualSlotsV2_BAUGD S).stageCloud 2 → W.pieceInterior ⊤)
  (rpre : (actualSlotsV2_BAUGD S).stageCloudEnlarged 2 → W.pieceInterior ⊤)

open Classical in
/-- **(FM*-int)** on the classical contributor windows: a stage-`2` marker with a threshold-`7`
core point `p` is full at every cloud point `y` of the window and annihilates the plane
`DΨ(η(pre y))`. -/
theorem slimTable_FM_BPS (hΔ1 : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) {eg : ℝ} (heg0 : 0 ≤ eg) (heg : eg < 1 / 100)
    (hTG : ∀ i : S.SlimIdx_BAUGD, ∀ x : W.pieceInterior ⊤,
      (letI := inducedMetricSpace S.completion.metric
       dist x i.1 < 1000000 * Δ * S.rho i.1) →
      |S.slimEta_BIF i.1 x| ≤ 8 * (100000 * Δ) →
      ‖(S.rho i.1)⁻¹ • blockRestrict (S.stageTagsV2_BAUGD 2) (S.interiorMapOn_BAUGA x) -
        S.slimModelOf_BPS i (sgnf i) (cf i) (zsgnf i) (zcf i) (S.slimEta_BIF i.1 x)‖ < eg)
    (hpre : ∀ x, (letI := inducedMetricSpace S.completion.metric
        dist (pre x) (jref x).1 < 1000000 * Δ * S.rho (jref x).1) ∧
      |S.slimEta_BIF (jref x).1 (pre x)| ≤ 7 * (100000 * Δ) ∧
      (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap (pre x).val) = x.1)
    (hrpre : ∀ x, (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap (rpre x).val) = x.1) :
    ∀ εc σ' : ℝ, 0 < εc → 0 ≤ σ' → σ' ≤ εc / 10000 → ∀ (x₀ : W.pieceInterior ⊤)
      (m : S.MarkerIdx_BAUGC), S.markerStage_BAUGC m = 2 → ∀ p ∈ S.markerCore7_BAUGC m,
      ∀ y (hy : y ∈ (actualSlotsV2_BAUGD S).stageCloud 2),
        (closedBall y (80 * εc⁻¹ * (σ' * S.rho (if hyT : y ∈
            (actualSlotsV2_BAUGD S).stageCloudEnlarged 2
            then rpre ⟨y, hyT⟩ else x₀))) ∩
          ball ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap p.val))
            (8 * εc⁻¹ * (σ' * S.rho (if hpT : (actualSlotsV2_BAUGD S).stageProj 2
                (S.boundaryOriginalMap p.val) ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 2
              then rpre ⟨_, hpT⟩ else x₀)))).Nonempty →
        S.markerCLM_BAUGC m y = S.rho (S.markerCentre_BAUGC m) ∧
        ∀ v : ℝ, ((fderiv ℝ
            (⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
            S.slimStageModel_BPS sgnf cf zsgnf zcf (jref ⟨y, hy⟩).1)
          (S.slimEta_BIF (jref ⟨y, hy⟩).1 (pre ⟨y, hy⟩)) v) (S.markerTag_BAUGC m)).snd = 0 := by
  intro εc σ' hε hσ hσε x₀ m hm p hp y hy hwin
  rcases m with i | i | i
  · exact absurd hm (by simp [BoundarySupplyCore.markerStage_BAUGC])
  · have hp' : (letI := inducedMetricSpace S.completion.metric
        dist p i.1 < 1000000 * Δ * S.rho i.1) ∧ |S.slimEta_BIF i.1 p| ≤ 7 * (100000 * Δ) := hp
    have h := hpre ⟨y, hy⟩
    have hΔ0 : 0 < Δ := by linarith only [hΔ1]
    have hyT : y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 2 :=
      actualSlotsV2_stageCloud_subset_BAUGD S hΔ0.le 2 hy
    have hpT := S.stageProj_mem_stageCloudEnlarged_two_BPS i hp'.1 (by linarith only [hp'.2, hΔ0])
    rw [dite_eq_left hyT, dite_eq_left hpT] at hwin
    have hj := (Set.Finite.mem_toFinset _).mp (jref ⟨y, hy⟩).2
    rw [S.slimStageModel_comp_BPS sgnf cf zsgnf zcf hj]
    exact S.slim_full_marker_point_BPS hΔ1 hΛ hΛΔ hV hβ1 hb heg0 heg hε hσ hσε i hp'.1 hp'.2
      (jref ⟨y, hy⟩) (sgnf _) (cf _) (S.slimModelOf_BPS _ _ _ _ _)
      ((S.contDiff_slimModelOf_BPS _ _ _ _ _).differentiable (by simp))
      (fun w => S.slimModelOf_slim_BPS _ _ _ _ _ i w) h.1 h.2.1 h.2.2 (hrpre ⟨y, hyT⟩)
      (hrpre ⟨_, hpT⟩) hwin (hTG _ (pre ⟨y, hy⟩) h.1 (by linarith only [h.2.1, hΔ0]))
  · exact absurd hm (by simp [BoundarySupplyCore.markerStage_BAUGC])

open Classical in
/-- **(ZB*-int)** on the classical contributor windows: for a zero centre `k` and a preimage `p`
of a point of `S₂` with `ρ(p) > 200R_k/T`, the zero block of every window cloud point `y` and of
the plane `DΨ(η(pre y))` vanish. -/
theorem slimTable_ZB_BPS (hΔ1 : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) (hT : 1600 * (1000000 * Δ) ≤ T) (he : e < 1 / 40)
    (hpre : ∀ x, (letI := inducedMetricSpace S.completion.metric
        dist (pre x) (jref x).1 < 1000000 * Δ * S.rho (jref x).1) ∧
      |S.slimEta_BIF (jref x).1 (pre x)| ≤ 7 * (100000 * Δ) ∧
      (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap (pre x).val) = x.1)
    (hrpre : ∀ x, (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap (rpre x).val) = x.1) :
    ∀ εc σ' : ℝ, 0 < εc → σ' ≤ εc / 10000 → ∀ (x₀ : W.pieceInterior ⊤)
      (k : S.ZeroIdx_BAUGC) (p : W.pieceInterior ⊤),
      (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap p.val) ∈
        (actualSlotsV2_BAUGD S).stageCloud 2 →
      200 * S.zeroRadius_BAUGC k / T < S.rho p →
      ∀ y (hy : y ∈ (actualSlotsV2_BAUGD S).stageCloud 2),
        (closedBall y (80 * εc⁻¹ * (σ' * S.rho (if hyT : y ∈
            (actualSlotsV2_BAUGD S).stageCloudEnlarged 2
            then rpre ⟨y, hyT⟩ else x₀))) ∩
          ball ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap p.val))
            (8 * εc⁻¹ * (σ' * S.rho (if hpT : (actualSlotsV2_BAUGD S).stageProj 2
                (S.boundaryOriginalMap p.val) ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 2
              then rpre ⟨_, hpT⟩ else x₀)))).Nonempty →
        S.zeroBlockCLM_BAUGC k y = 0 ∧
        ∀ v : ℝ, (fderiv ℝ
            (⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
            S.slimStageModel_BPS sgnf cf zsgnf zcf (jref ⟨y, hy⟩).1)
          (S.slimEta_BIF (jref ⟨y, hy⟩).1 (pre ⟨y, hy⟩)) v) (S.zeroTag_BAUGC k) = 0 := by
  intro εc σ' hε hσε x₀ k p hp hρp y hy hwin
  have h := hpre ⟨y, hy⟩
  have hΔ0 : 0 < Δ := by linarith only [hΔ1]
  have hyT : y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 2 :=
    actualSlotsV2_stageCloud_subset_BAUGD S hΔ0.le 2 hy
  have hpT : (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap p.val) ∈
      (actualSlotsV2_BAUGD S).stageCloudEnlarged 2 :=
    actualSlotsV2_stageCloud_subset_BAUGD S hΔ0.le 2 hp
  rw [dite_eq_left hyT, dite_eq_left hpT] at hwin
  have hj := (Set.Finite.mem_toFinset _).mp (jref ⟨y, hy⟩).2
  rw [S.slimStageModel_comp_BPS sgnf cf zsgnf zcf hj]
  exact S.slim_zero_block_point_BPS hΔ1 hΛ hΛΔ hV hβ1 hb hT he hε hσε k hp hρp
    (jref ⟨y, hy⟩) (zsgnf _) (zcf _) (S.slimModelOf_BPS _ _ _ _ _)
    (fun w => S.slimModelOf_zero_BPS _ _ _ _ _ k w) h.1 h.2.1 h.2.2 (hrpre ⟨y, hyT⟩)
    (hrpre ⟨_, hpT⟩) hwin

end BoundarySupply

open Classical in
/-- **PORT TARGET (SLIM (SGP02–SGP06), stage `2`)**: the interior stage table of the actual slot
(PortTargets v3.1), STRENGTHENED: the frozen premises `Γ < 1`, `sg < Γ³/(100·sgpGraphBound)` and
`eg < Γ·sg/100` are not needed and are dropped (the verbatim frozen form is the `example` below).
Data: `Ψ a = slimStageModel_BPS` (SGP04's full model of the slim centre `a`), `Kint a = id`,
`Pc a = slimStageOwn_BPS`, core preimages `pre` with references `ref` (threshold-`7` cores),
radius preimages `rpre` (any preimage). Closed twin `exists_slimStagePlanes_PLN`. -/
theorem port_slim_interior_table_BAUGP {Γ sg eg : ℝ} (hΓ : 0 < Γ)
    (hsg : 0 < sg) (hsgΓ : sg < Γ / 200)
    (heg : 0 < eg) (heg1 : eg < 1 / 100) :
    ∀ β₂ : ℝ, 0 < β₂ → β₂ < 1 → ∀ Δ : ℝ, 1200 ≤ Δ →
    ∃ θs : ℝ, 0 < θs ∧ θs < 1 ∧ ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
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
      β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 < σs → σs < θs ^ 2 / 10 ^ 6 → vs < θs / 100 →
      0 < ζ → ζ < θs ^ 2 / 10 ^ 6 → ζ < 1 / (100 * (1000000 * Δ)) →
      εr < θs / (100 * (1000000 * Δ)) → 0 ≤ εr →
      0 < Δ → 100 * Δ * Λ ≤ 1 / 100 → 0 ≤ V → 0 < β 1 → 0 < b → e ≤ 1 / 10 →
      S.SeparatedCollarZero_BIF →
      letI := inducedMetricSpace S.completion.metric
      ∃ (Ψ : W.pieceInterior ⊤ → ℝ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))
        (Kint : W.pieceInterior ⊤ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) →L[ℝ]
          BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))
        (Pc : W.pieceInterior ⊤ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) →L[ℝ] ℝ)
        (rpre : (actualSlotsV2_BAUGD S).stageCloudEnlarged 2 → W.pieceInterior ⊤)
        (pre : (actualSlotsV2_BAUGD S).stageCloud 2 → W.pieceInterior ⊤)
        (ref : (actualSlotsV2_BAUGD S).stageCloud 2 → W.pieceInterior ⊤),
      -- (M)
      (∀ a ∈ S.stageCentres_BIF 2, ContDiff ℝ 2 (Kint a ∘ Ψ a) ∧ ∀ u,
        ‖fderiv ℝ (Kint a ∘ Ψ a) u‖ ≤ sgpGraphBound ∧
            ‖fderiv ℝ (fderiv ℝ (Kint a ∘ Ψ a)) u‖ ≤ sgpGraphBound) ∧
      -- (OWN)
      (∀ a ∈ S.stageCentres_BIF 2, (∀ z, ‖Pc a z‖ ≤ ‖z‖) ∧ (∀ u, Pc a ((Kint a ∘ Ψ a) u) = u) ∧
        ∀ x : W.pieceInterior ⊤, (dist x a < 1000000 * Δ * S.rho a ∧
            |S.slimEta_BIF a x| ≤ 8 * (100000 * Δ)) →
          Pc a ((S.rho a)⁻¹ • blockRestrict (S.stageTagsV2_BAUGD 2) (S.interiorMapOn_BAUGA x)) =
            S.slimEta_BIF a x) ∧
      -- (Q)
      (∀ a ∈ S.stageCentres_BIF 2, ∀ u,
        blockRestrict (S.stageTagsV2_BAUGD 2) ((Kint a ∘ Ψ a) u) = (Kint a ∘ Ψ a) u) ∧
      -- (TG)
      (∀ a ∈ S.stageCentres_BIF 2, ∀ x : W.pieceInterior ⊤, (dist x a < 1000000 * Δ * S.rho a ∧
          |S.slimEta_BIF a x| ≤ 8 * (100000 * Δ)) →
        ‖(S.rho a)⁻¹ • blockRestrict (S.stageTagsV2_BAUGD 2) (S.interiorMapOn_BAUGA x) -
            (Kint a ∘ Ψ a) (S.slimEta_BIF a x)‖ < eg ∧
        ∀ w : TangentSpace 𝓘(ℝ, E3) x,
          ‖(S.rho a)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (fun y => blockRestrict (S.stageTagsV2_BAUGD 2) (S.interiorMapOn_BAUGA y)) x w -
              fderiv ℝ (Kint a ∘ Ψ a) (S.slimEta_BIF a x)
                (mvfderiv 𝓘(ℝ, E3) (S.slimEta_BIF a) x w)‖ ≤
            eg * Real.sqrt ((S.rho a)⁻¹ ^ 2 * S.completion.metric.inner x w w)) ∧
      -- (SEL)
      (∀ x, (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap (rpre x).val) = x.1) ∧
      (∀ x, ref x ∈ S.stageCentres_BIF 2 ∧ (dist (pre x) (ref x) < 1000000 * Δ * S.rho (ref x) ∧
          |S.slimEta_BIF (ref x) (pre x)| ≤ 7 * (100000 * Δ)) ∧
        dist (pre x) (ref x) < stageDomain_BIF Δ 2 * S.rho (ref x) ∧
        (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap (pre x).val) = x.1) ∧
      -- (LOC)
      (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 2),
        ∀ y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 2,
          ‖augIntProjCLM_BAUGC (y - x)‖ ≤ sg * S.rho (ref ⟨x, hx⟩) / Γ →
          ∃ q : W.pieceInterior ⊤, (dist q (ref ⟨x, hx⟩) < 1000000 * Δ * S.rho (ref ⟨x, hx⟩) ∧
              |S.slimEta_BIF (ref ⟨x, hx⟩) q| ≤ 8 * (100000 * Δ)) ∧
            dist q (ref ⟨x, hx⟩) < stageDomain_BIF Δ 2 * S.rho (ref ⟨x, hx⟩) ∧
            (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val) = y) ∧
      -- (COV)
      (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 2), ∀ u : ℝ,
        ‖u - S.slimEta_BIF (ref ⟨x, hx⟩) (pre ⟨x, hx⟩)‖ ≤ 2 * sg / Γ →
        ∃ q : W.pieceInterior ⊤, (dist q (ref ⟨x, hx⟩) < 1000000 * Δ * S.rho (ref ⟨x, hx⟩) ∧
            |S.slimEta_BIF (ref ⟨x, hx⟩) q| ≤ 8 * (100000 * Δ)) ∧
          dist q (ref ⟨x, hx⟩) < stageDomain_BIF Δ 2 * S.rho (ref ⟨x, hx⟩) ∧
          S.slimEta_BIF (ref ⟨x, hx⟩) q = u ∧
          (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val) ∈
            (actualSlotsV2_BAUGD S).stageCloudEnlarged 2) ∧
      -- (PRE)
      (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 2), ∀ q : W.pieceInterior ⊤,
        (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val) = x →
        (dist q (ref ⟨x, hx⟩) < 1000000 * Δ * S.rho (ref ⟨x, hx⟩) ∧
            |S.slimEta_BIF (ref ⟨x, hx⟩) q| ≤ 8 * (100000 * Δ)) ∧
          dist q (ref ⟨x, hx⟩) < stageDomain_BIF Δ 2 * S.rho (ref ⟨x, hx⟩) ∧
          S.slimEta_BIF (ref ⟨x, hx⟩) q = S.slimEta_BIF (ref ⟨x, hx⟩) (pre ⟨x, hx⟩)) ∧
      -- (MCb)
      (∀ sel : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → W.pieceInterior ⊤,
        (∀ x ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 2,
          (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap (sel x).val) = x) →
        ∀ L' : ℝ, 0 ≤ L' → L' * sg ≤ 1 / 5 →
        ∀ x ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 2,
        ∀ y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 2,
          dist y x ≤ L' * max (sg * S.rho (sel y)) (sg * S.rho (sel x)) →
          sg * S.rho (sel x) / (5 / 3) ≤ sg * S.rho (sel y) ∧
            sg * S.rho (sel y) ≤ 5 / 3 * (sg * S.rho (sel x))) ∧
      -- (PP-int)
      (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 2), ∀ q : W.pieceInterior ⊤,
        (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val) = x →
        ∀ m : S.MarkerIdx_BAUGC, S.rho (S.markerCentre_BAUGC m) < S.rho q / 5 →
          ∀ v : ℝ, ((fderiv ℝ (Kint (ref ⟨x, hx⟩) ∘ Ψ (ref ⟨x, hx⟩))
            (S.slimEta_BIF (ref ⟨x, hx⟩) (pre ⟨x, hx⟩)) v) (S.markerTag_BAUGC m)).snd = 0) ∧
      -- (SB-int)
      (∀ a ∈ S.stageCentres_BIF 2, ∀ m : S.MarkerIdx_BAUGC,
        S.rho (S.markerCentre_BAUGC m) ≤ smallBlockFactor_BAUGC 2 * S.rho a →
        ∀ u, (Kint a ∘ Ψ a) u (S.markerTag_BAUGC m) = 0) ∧
      -- (FM*-int)
      (∀ εc σ' : ℝ, 0 < εc → 0 ≤ σ' → σ' ≤ εc / 10000 → ∀ (x₀ : W.pieceInterior ⊤)
        (m : S.MarkerIdx_BAUGC), S.markerStage_BAUGC m = 2 → ∀ p ∈ S.markerCore7_BAUGC m,
        ∀ y (hy : y ∈ (actualSlotsV2_BAUGD S).stageCloud 2),
          (closedBall y (80 * εc⁻¹ * (σ' * S.rho (if hyT : y ∈
              (actualSlotsV2_BAUGD S).stageCloudEnlarged 2
              then rpre ⟨y, hyT⟩ else x₀))) ∩
            ball ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap p.val))
              (8 * εc⁻¹ * (σ' * S.rho (if hpT : (actualSlotsV2_BAUGD S).stageProj 2
                  (S.boundaryOriginalMap p.val) ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 2
                then rpre ⟨_, hpT⟩ else x₀)))).Nonempty →
          S.markerCLM_BAUGC m y = S.rho (S.markerCentre_BAUGC m) ∧
          ∀ v : ℝ, ((fderiv ℝ (Kint (ref ⟨y, hy⟩) ∘ Ψ (ref ⟨y, hy⟩))
            (S.slimEta_BIF (ref ⟨y, hy⟩) (pre ⟨y, hy⟩)) v) (S.markerTag_BAUGC m)).snd = 0) ∧
      -- (ZB*-int)
      (∀ εc σ' : ℝ, 0 < εc → σ' ≤ εc / 10000 → ∀ (x₀ : W.pieceInterior ⊤)
        (k : S.ZeroIdx_BAUGC) (p : W.pieceInterior ⊤),
        (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap p.val) ∈
          (actualSlotsV2_BAUGD S).stageCloud 2 →
        200 * S.zeroRadius_BAUGC k / T < S.rho p →
        ∀ y (hy : y ∈ (actualSlotsV2_BAUGD S).stageCloud 2),
          (closedBall y (80 * εc⁻¹ * (σ' * S.rho (if hyT : y ∈
              (actualSlotsV2_BAUGD S).stageCloudEnlarged 2
              then rpre ⟨y, hyT⟩ else x₀))) ∩
            ball ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap p.val))
              (8 * εc⁻¹ * (σ' * S.rho (if hpT : (actualSlotsV2_BAUGD S).stageProj 2
                  (S.boundaryOriginalMap p.val) ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 2
                then rpre ⟨_, hpT⟩ else x₀)))).Nonempty →
          S.zeroBlockCLM_BAUGC k y = 0 ∧
          ∀ v : ℝ, (fderiv ℝ (Kint (ref ⟨y, hy⟩) ∘ Ψ (ref ⟨y, hy⟩))
            (S.slimEta_BIF (ref ⟨y, hy⟩) (pre ⟨y, hy⟩)) v) (S.zeroTag_BAUGC k) = 0) := by
  have hR : sg / Γ < 1 / 100 := by
    rw [div_lt_iff₀ hΓ]
    linarith only [hsgΓ, hΓ]
  have h2sg : 2 * sg / Γ ≤ 1 / 100 := by
    rw [div_le_iff₀ hΓ]
    linarith only [hsgΓ, hΓ]
  intro β₂ hβ₂ hβ₂1 Δ hΔ
  have hΔ1 : 1 ≤ Δ := by linarith only [hΔ]
  obtain ⟨θs, hθ, hθ1, Lc, η₀, hLc, hη₀, hsup⟩ := slim_row_supply_BPS hΔ1 hβ₂ hβ₂1 heg heg1
  refine ⟨θs, hθ, hθ1, Lc, η₀, hLc, hη₀, ?_⟩
  intro K A β βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W _ g δn n B oM S
    hΛ _ _ hΛΔ' he hT hΛzT hβ2 hβ1η hLc' hσs hσθ hvθ hζ hζθ hζL hεr _ hΔ0 _ hV hβ1 hb _ _
  have h6 : (10 : ℝ) ^ 6 = 1000000 := by norm_num
  have h5 : (10 : ℝ) ^ 5 = 100000 := by norm_num
  rw [h6, h5] at hΛΔ'
  have hθ2 : θs ^ 2 ≤ 1 := pow_le_one₀ hθ.le hθ1.le
  have hσs1 : σs ≤ 1 / 100 := by
    have h : θs ^ 2 / 10 ^ 6 ≤ 1 / 100 := by
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
      linarith only [hθ2]
    linarith only [hσθ, h]
  choose sgnf cf zsgnf zcf hsgn hzsgn hTG using
    hsup S hβ2 hβ1η hLc' hΛ hΛΔ' he hT hΛzT hσs hσθ hvθ hζ hζθ hζL hεr
  choose jref pre hpre using fun x : (actualSlotsV2_BAUGD S).stageCloud 2 =>
    S.exists_core_of_mem_stageCloud_two_BPS x.2
  have hrp : ∀ x : (actualSlotsV2_BAUGD S).stageCloudEnlarged 2, ∃ r : W.pieceInterior ⊤,
      (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap r.val) = x.1 := by
    intro x
    obtain ⟨r, -, hr⟩ := x.2
    exact ⟨r, hr⟩
  choose rpre hrpre using hrp
  exact ⟨S.slimStageModel_BPS sgnf cf zsgnf zcf, fun _ => ContinuousLinearMap.id ℝ _,
    S.slimStageOwn_BPS, rpre, pre, fun x => (jref x).1,
    S.slimTable_M_BPS sgnf cf zsgnf zcf hΔ1 hΛ hΛΔ' he hT hσs.le hσs1 hsgn hzsgn,
    S.slimTable_OWN_BPS sgnf cf zsgnf zcf, S.slimTable_Q_BPS sgnf cf zsgnf zcf,
    S.slimTable_TG_BPS sgnf cf zsgnf zcf hTG, hrpre, S.slimTable_SEL_BPS jref pre hΔ0 hpre,
    S.slimTable_LOC_BPS jref pre hΔ1 hR hpre, S.slimTable_COV_BPS jref pre hΔ1 h2sg hpre,
    S.slimTable_PRE_BPS jref pre hΔ0 hpre, S.slimTable_MCb_BPS hsg.le hΔ1 hΛ hΛΔ' hV hβ1 hb,
    S.slimTable_PP_BPS sgnf cf zsgnf zcf jref pre hΔ1 hΛ hΛΔ' hV hβ1 hb hpre,
    S.slimTable_SB_BPS sgnf cf zsgnf zcf hΔ0 hΛ hΛΔ',
    S.slimTable_FM_BPS sgnf cf zsgnf zcf jref pre rpre hΔ1 hΛ hΛΔ' hV hβ1 hb heg.le heg1
      (fun i x h1 h2 => (hTG i x h1 h2).1) hpre hrpre,
    S.slimTable_ZB_BPS sgnf cf zsgnf zcf jref pre rpre hΔ1 hΛ hΛΔ' hV hβ1 hb hT he hpre hrpre⟩

open Classical in
/-- `port_slim_interior_table_BAUGP` in the verbatim frozen form of PortTargets v3.1 (with the three
unused premises `hΓ1`, `hsgC`, `hegΓ`). -/
example {Γ sg eg : ℝ} (hΓ : 0 < Γ) (hΓ1 : Γ < 1)
    (hsg : 0 < sg) (hsgΓ : sg < Γ / 200) (hsgC : sg < Γ ^ 3 / (100 * sgpGraphBound))
    (heg : 0 < eg) (heg1 : eg < 1 / 100) (hegΓ : eg < Γ * sg / 100) :
    ∀ β₂ : ℝ, 0 < β₂ → β₂ < 1 → ∀ Δ : ℝ, 1200 ≤ Δ →
    ∃ θs : ℝ, 0 < θs ∧ θs < 1 ∧ ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
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
      β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 < σs → σs < θs ^ 2 / 10 ^ 6 → vs < θs / 100 →
      0 < ζ → ζ < θs ^ 2 / 10 ^ 6 → ζ < 1 / (100 * (1000000 * Δ)) →
      εr < θs / (100 * (1000000 * Δ)) → 0 ≤ εr →
      0 < Δ → 100 * Δ * Λ ≤ 1 / 100 → 0 ≤ V → 0 < β 1 → 0 < b → e ≤ 1 / 10 →
      S.SeparatedCollarZero_BIF →
      letI := inducedMetricSpace S.completion.metric
      ∃ (Ψ : W.pieceInterior ⊤ → ℝ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))
        (Kint : W.pieceInterior ⊤ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) →L[ℝ]
          BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))
        (Pc : W.pieceInterior ⊤ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) →L[ℝ] ℝ)
        (rpre : (actualSlotsV2_BAUGD S).stageCloudEnlarged 2 → W.pieceInterior ⊤)
        (pre : (actualSlotsV2_BAUGD S).stageCloud 2 → W.pieceInterior ⊤)
        (ref : (actualSlotsV2_BAUGD S).stageCloud 2 → W.pieceInterior ⊤),
      -- (M)
      (∀ a ∈ S.stageCentres_BIF 2, ContDiff ℝ 2 (Kint a ∘ Ψ a) ∧ ∀ u,
        ‖fderiv ℝ (Kint a ∘ Ψ a) u‖ ≤ sgpGraphBound ∧
            ‖fderiv ℝ (fderiv ℝ (Kint a ∘ Ψ a)) u‖ ≤ sgpGraphBound) ∧
      -- (OWN)
      (∀ a ∈ S.stageCentres_BIF 2, (∀ z, ‖Pc a z‖ ≤ ‖z‖) ∧ (∀ u, Pc a ((Kint a ∘ Ψ a) u) = u) ∧
        ∀ x : W.pieceInterior ⊤, (dist x a < 1000000 * Δ * S.rho a ∧
            |S.slimEta_BIF a x| ≤ 8 * (100000 * Δ)) →
          Pc a ((S.rho a)⁻¹ • blockRestrict (S.stageTagsV2_BAUGD 2) (S.interiorMapOn_BAUGA x)) =
            S.slimEta_BIF a x) ∧
      -- (Q)
      (∀ a ∈ S.stageCentres_BIF 2, ∀ u,
        blockRestrict (S.stageTagsV2_BAUGD 2) ((Kint a ∘ Ψ a) u) = (Kint a ∘ Ψ a) u) ∧
      -- (TG)
      (∀ a ∈ S.stageCentres_BIF 2, ∀ x : W.pieceInterior ⊤, (dist x a < 1000000 * Δ * S.rho a ∧
          |S.slimEta_BIF a x| ≤ 8 * (100000 * Δ)) →
        ‖(S.rho a)⁻¹ • blockRestrict (S.stageTagsV2_BAUGD 2) (S.interiorMapOn_BAUGA x) -
            (Kint a ∘ Ψ a) (S.slimEta_BIF a x)‖ < eg ∧
        ∀ w : TangentSpace 𝓘(ℝ, E3) x,
          ‖(S.rho a)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (fun y => blockRestrict (S.stageTagsV2_BAUGD 2) (S.interiorMapOn_BAUGA y)) x w -
              fderiv ℝ (Kint a ∘ Ψ a) (S.slimEta_BIF a x)
                (mvfderiv 𝓘(ℝ, E3) (S.slimEta_BIF a) x w)‖ ≤
            eg * Real.sqrt ((S.rho a)⁻¹ ^ 2 * S.completion.metric.inner x w w)) ∧
      -- (SEL)
      (∀ x, (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap (rpre x).val) = x.1) ∧
      (∀ x, ref x ∈ S.stageCentres_BIF 2 ∧ (dist (pre x) (ref x) < 1000000 * Δ * S.rho (ref x) ∧
          |S.slimEta_BIF (ref x) (pre x)| ≤ 7 * (100000 * Δ)) ∧
        dist (pre x) (ref x) < stageDomain_BIF Δ 2 * S.rho (ref x) ∧
        (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap (pre x).val) = x.1) ∧
      -- (LOC)
      (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 2),
        ∀ y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 2,
          ‖augIntProjCLM_BAUGC (y - x)‖ ≤ sg * S.rho (ref ⟨x, hx⟩) / Γ →
          ∃ q : W.pieceInterior ⊤, (dist q (ref ⟨x, hx⟩) < 1000000 * Δ * S.rho (ref ⟨x, hx⟩) ∧
              |S.slimEta_BIF (ref ⟨x, hx⟩) q| ≤ 8 * (100000 * Δ)) ∧
            dist q (ref ⟨x, hx⟩) < stageDomain_BIF Δ 2 * S.rho (ref ⟨x, hx⟩) ∧
            (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val) = y) ∧
      -- (COV)
      (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 2), ∀ u : ℝ,
        ‖u - S.slimEta_BIF (ref ⟨x, hx⟩) (pre ⟨x, hx⟩)‖ ≤ 2 * sg / Γ →
        ∃ q : W.pieceInterior ⊤, (dist q (ref ⟨x, hx⟩) < 1000000 * Δ * S.rho (ref ⟨x, hx⟩) ∧
            |S.slimEta_BIF (ref ⟨x, hx⟩) q| ≤ 8 * (100000 * Δ)) ∧
          dist q (ref ⟨x, hx⟩) < stageDomain_BIF Δ 2 * S.rho (ref ⟨x, hx⟩) ∧
          S.slimEta_BIF (ref ⟨x, hx⟩) q = u ∧
          (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val) ∈
            (actualSlotsV2_BAUGD S).stageCloudEnlarged 2) ∧
      -- (PRE)
      (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 2), ∀ q : W.pieceInterior ⊤,
        (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val) = x →
        (dist q (ref ⟨x, hx⟩) < 1000000 * Δ * S.rho (ref ⟨x, hx⟩) ∧
            |S.slimEta_BIF (ref ⟨x, hx⟩) q| ≤ 8 * (100000 * Δ)) ∧
          dist q (ref ⟨x, hx⟩) < stageDomain_BIF Δ 2 * S.rho (ref ⟨x, hx⟩) ∧
          S.slimEta_BIF (ref ⟨x, hx⟩) q = S.slimEta_BIF (ref ⟨x, hx⟩) (pre ⟨x, hx⟩)) ∧
      -- (MCb)
      (∀ sel : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → W.pieceInterior ⊤,
        (∀ x ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 2,
          (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap (sel x).val) = x) →
        ∀ L' : ℝ, 0 ≤ L' → L' * sg ≤ 1 / 5 →
        ∀ x ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 2,
        ∀ y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 2,
          dist y x ≤ L' * max (sg * S.rho (sel y)) (sg * S.rho (sel x)) →
          sg * S.rho (sel x) / (5 / 3) ≤ sg * S.rho (sel y) ∧
            sg * S.rho (sel y) ≤ 5 / 3 * (sg * S.rho (sel x))) ∧
      -- (PP-int)
      (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 2), ∀ q : W.pieceInterior ⊤,
        (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val) = x →
        ∀ m : S.MarkerIdx_BAUGC, S.rho (S.markerCentre_BAUGC m) < S.rho q / 5 →
          ∀ v : ℝ, ((fderiv ℝ (Kint (ref ⟨x, hx⟩) ∘ Ψ (ref ⟨x, hx⟩))
            (S.slimEta_BIF (ref ⟨x, hx⟩) (pre ⟨x, hx⟩)) v) (S.markerTag_BAUGC m)).snd = 0) ∧
      -- (SB-int)
      (∀ a ∈ S.stageCentres_BIF 2, ∀ m : S.MarkerIdx_BAUGC,
        S.rho (S.markerCentre_BAUGC m) ≤ smallBlockFactor_BAUGC 2 * S.rho a →
        ∀ u, (Kint a ∘ Ψ a) u (S.markerTag_BAUGC m) = 0) ∧
      -- (FM*-int)
      (∀ εc σ' : ℝ, 0 < εc → 0 ≤ σ' → σ' ≤ εc / 10000 → ∀ (x₀ : W.pieceInterior ⊤)
        (m : S.MarkerIdx_BAUGC), S.markerStage_BAUGC m = 2 → ∀ p ∈ S.markerCore7_BAUGC m,
        ∀ y (hy : y ∈ (actualSlotsV2_BAUGD S).stageCloud 2),
          (closedBall y (80 * εc⁻¹ * (σ' * S.rho (if hyT : y ∈
              (actualSlotsV2_BAUGD S).stageCloudEnlarged 2
              then rpre ⟨y, hyT⟩ else x₀))) ∩
            ball ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap p.val))
              (8 * εc⁻¹ * (σ' * S.rho (if hpT : (actualSlotsV2_BAUGD S).stageProj 2
                  (S.boundaryOriginalMap p.val) ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 2
                then rpre ⟨_, hpT⟩ else x₀)))).Nonempty →
          S.markerCLM_BAUGC m y = S.rho (S.markerCentre_BAUGC m) ∧
          ∀ v : ℝ, ((fderiv ℝ (Kint (ref ⟨y, hy⟩) ∘ Ψ (ref ⟨y, hy⟩))
            (S.slimEta_BIF (ref ⟨y, hy⟩) (pre ⟨y, hy⟩)) v) (S.markerTag_BAUGC m)).snd = 0) ∧
      -- (ZB*-int)
      (∀ εc σ' : ℝ, 0 < εc → σ' ≤ εc / 10000 → ∀ (x₀ : W.pieceInterior ⊤)
        (k : S.ZeroIdx_BAUGC) (p : W.pieceInterior ⊤),
        (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap p.val) ∈
          (actualSlotsV2_BAUGD S).stageCloud 2 →
        200 * S.zeroRadius_BAUGC k / T < S.rho p →
        ∀ y (hy : y ∈ (actualSlotsV2_BAUGD S).stageCloud 2),
          (closedBall y (80 * εc⁻¹ * (σ' * S.rho (if hyT : y ∈
              (actualSlotsV2_BAUGD S).stageCloudEnlarged 2
              then rpre ⟨y, hyT⟩ else x₀))) ∩
            ball ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap p.val))
              (8 * εc⁻¹ * (σ' * S.rho (if hpT : (actualSlotsV2_BAUGD S).stageProj 2
                  (S.boundaryOriginalMap p.val) ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 2
                then rpre ⟨_, hpT⟩ else x₀)))).Nonempty →
          S.zeroBlockCLM_BAUGC k y = 0 ∧
          ∀ v : ℝ, (fderiv ℝ (Kint (ref ⟨y, hy⟩) ∘ Ψ (ref ⟨y, hy⟩))
            (S.slimEta_BIF (ref ⟨y, hy⟩) (pre ⟨y, hy⟩)) v) (S.zeroTag_BAUGC k) = 0) :=
  (fun _ _ _ => port_slim_interior_table_BAUGP hΓ hsg hsgΓ heg heg1) hΓ1 hsgC hegΓ

/-- **PORT TARGET (PRE~), SLIM, stage `2`** (frozen supplement, verbatim): two preimages in `W°` of
the same point of the enlarged slim cloud `S̃₃ = π₂F_∂(Ã₂)` have `ρ q₁ ≤ 5/3·ρ q₂`.
Closed twin: the fourth clause of `fc27_slim_cloud_scale` at distance `0`; here
`slim_scale_ratio_BPS` with `σ = L' = 0`. -/
theorem port_slim_cloud_scale_BAUGP :
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
      ∀ x ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 2, ∀ q₁ q₂ : W.pieceInterior ⊤,
        (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q₁.val) = x →
        (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q₂.val) = x →
        S.rho q₁ ≤ 5 / 3 * S.rho q₂ := by
  intro Δ hΔ K A β βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W _ g δn n B oM
    S hΛ _ _ hΛΔ' _ _ _ _ _ hV hβ1 hb _ _ x hx q₁ q₂ h1 h2
  have h6 : (10 : ℝ) ^ 6 = 1000000 := by norm_num
  have h5 : (10 : ℝ) ^ 5 = 100000 := by norm_num
  rw [h6, h5] at hΛΔ'
  have hp : (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q₂.val) ∈
      (actualSlotsV2_BAUGD S).stageCloudEnlarged 2 := by
    rw [h2]
    exact hx
  have hq : (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q₁.val) ∈
      (actualSlotsV2_BAUGD S).stageCloudEnlarged 2 := by
    rw [h1]
    exact hx
  have hd : dist ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q₁.val))
      ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q₂.val)) ≤
      0 * max (0 * S.rho q₁.val) (0 * S.rho q₂.val) := by
    rw [h1, h2, dist_self, zero_mul]
  exact (S.slim_scale_ratio_BPS hΛ (by linarith only [hΔ]) hΛΔ' hV hβ1 hb le_rfl le_rfl
    (by norm_num) hp hq hd).2

end DifferentialGeometry.Geometry.Collapse

import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortCircleTableA

/-!
# PORT target: the interior circle stage table (lane O-PORT-A)

**`port_circle_interior_table_BAUGP`** (PortTargets v3.1,
`docs/geometrization/chapter14/evidence/boundary/PortTargets-v3.1.lean.txt`, l.77–212), strengthened
by dropping the three frozen premises it does not use (`Γ < 1`, `sg < Γ³/(100·tcpGraphConst)`,
`eg < Γ·sg/100`); the verbatim frozen form is the `example` at the end. Closed twin:
`exists_firstStagePlanes_PLN` (`Fibration/ActualStageFirstPlanes.lean`). Data: `Ψ a =
circleStageModel_BPC` (TCP05's model graph of the circle centre `a` with the actual lists and the
comparison data of `circle_row_supply_BPC`, pruned by CFS27), `Kint a = id`,
`Pc a = circleStageOwn_BPC` (vector part of the own block), core preimages `pre` with references
`ref` (threshold-`7` cores), radius preimages `rpre` (any preimage).

* `circleTable_FM_BPC` (FM*-int) and `circleTable_ZB_BPC` (ZB*-int) on the classical contributor
  windows (the frozen `dite` radii), from the one-window lemmas of `BoundaryPortCircleClausesB`;
* `port_circle_interior_table_BAUGP` and its verbatim frozen form.
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
  θ W g δn n B oM) (Acf : S.CircleIdx_BAUGD → S.IntTag_BAUGA → ℝ² →L[ℝ] ℝ²)
  (ccf : S.CircleIdx_BAUGD → S.IntTag_BAUGA → ℝ²)
  (A1f : S.CircleIdx_BAUGD → S.IntTag_BAUGA → ℝ² →L[ℝ] ℝ)
  (c1f : S.CircleIdx_BAUGD → S.IntTag_BAUGA → ℝ) (Bτf : S.CircleIdx_BAUGD → ℝ² →L[ℝ] ℝ)
  (cτf : S.CircleIdx_BAUGD → ℝ)
  (jref : (actualSlotsV2_BAUGD S).stageCloud 0 → S.CircleIdx_BAUGD)
  (pre : (actualSlotsV2_BAUGD S).stageCloud 0 → W.pieceInterior ⊤)
  (rpre : (actualSlotsV2_BAUGD S).stageCloudEnlarged 0 → W.pieceInterior ⊤)

open Classical in
/-- **(FM*-int)** on the classical contributor windows: a stage-`0` marker with a threshold-`7`
core point `p` is full at every cloud point `y` of the window and annihilates the plane
`D(K_aΦ_a)(η_a(pre y))`. -/
theorem circleTable_FM_BPC (hΔ1 : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) {eg : ℝ} (heg0 : 0 ≤ eg) (heg : eg < 1 / 100)
    (hTG : ∀ i : S.CircleIdx_BAUGD, ∀ x : W.pieceInterior ⊤,
      (letI := inducedMetricSpace S.completion.metric
       dist x i.1 < 200 * S.rho i.1) → ‖S.circleEta_BIF i.1 x‖ ≤ 8 →
      ‖(S.rho i.1)⁻¹ • S.interiorMapOn_BAUGA x -
          S.circleModelOf_BPC i (Acf i) (ccf i) (A1f i) (c1f i) (Bτf i) (cτf i)
            (S.circleEta_BIF i.1 x)‖ < eg)
    (hpre : ∀ x, (letI := inducedMetricSpace S.completion.metric
        dist (pre x) (jref x).1 < 200 * S.rho (jref x).1) ∧
      ‖S.circleEta_BIF (jref x).1 (pre x)‖ ≤ 7 ∧
      (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap (pre x).val) = x.1)
    (hrpre : ∀ x, (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap (rpre x).val) = x.1) :
    ∀ εc σ' : ℝ, 0 < εc → 0 ≤ σ' → σ' ≤ εc / 10000 → ∀ (x₀ : W.pieceInterior ⊤)
      (m : S.MarkerIdx_BAUGC), S.markerStage_BAUGC m = 0 → ∀ p ∈ S.markerCore7_BAUGC m,
      ∀ y (hy : y ∈ (actualSlotsV2_BAUGD S).stageCloud 0),
        (closedBall y (80 * εc⁻¹ * (σ' * S.rho (if hyT : y ∈
            (actualSlotsV2_BAUGD S).stageCloudEnlarged 0
            then rpre ⟨y, hyT⟩ else x₀))) ∩
          ball ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap p.val))
            (8 * εc⁻¹ * (σ' * S.rho (if hpT : (actualSlotsV2_BAUGD S).stageProj 0
                (S.boundaryOriginalMap p.val) ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 0
              then rpre ⟨_, hpT⟩ else x₀)))).Nonempty →
        S.markerCLM_BAUGC m y = S.rho (S.markerCentre_BAUGC m) ∧
        ∀ v : ℝ², ((fderiv ℝ
            (⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
            S.circleStageModel_BPC Acf ccf A1f c1f Bτf cτf (jref ⟨y, hy⟩).1)
          (S.circleEta_BIF (jref ⟨y, hy⟩).1 (pre ⟨y, hy⟩)) v) (S.markerTag_BAUGC m)).snd = 0 := by
  intro εc σ' hε hσ hσε x₀ m hm p hp y hy hwin
  rcases m with i | i | i
  · have hp' : (letI := inducedMetricSpace S.completion.metric
        dist p i.1 < 200 * S.rho i.1) ∧ ‖S.circleEta_BIF i.1 p‖ ≤ 7 := hp
    have h := hpre ⟨y, hy⟩
    have hΔ0 : 0 < Δ := by linarith only [hΔ1]
    have hyT : y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 0 :=
      actualSlotsV2_stageCloud_subset_BAUGD S hΔ0.le 0 hy
    have hpT := S.stageProj_mem_stageCloudEnlarged_zero_BPC i hp'.1
      (by linarith only [hp'.2])
    rw [dite_eq_left hyT, dite_eq_left hpT] at hwin
    have hj := (Set.Finite.mem_toFinset _).mp (jref ⟨y, hy⟩).2
    rw [S.circleStageModel_comp_BPC Acf ccf A1f c1f Bτf cτf hj]
    exact S.circle_full_marker_point_BPC (jref ⟨y, hy⟩) (Acf _) (ccf _) (A1f _) (c1f _) (Bτf _)
      (cτf _) hΔ1 hΛ hΛΔ hV hβ1 hb heg0 heg hε hσ hσε i hp'.1 hp'.2 h.1 h.2.1 h.2.2
      (hrpre ⟨y, hyT⟩) (hrpre ⟨_, hpT⟩) hwin
      (hTG _ (pre ⟨y, hy⟩) h.1 (by linarith only [h.2.1]))
  · exact absurd hm (by simp [BoundarySupplyCore.markerStage_BAUGC])
  · exact absurd hm (by simp [BoundarySupplyCore.markerStage_BAUGC])

open Classical in
/-- **(ZB*-int)** on the classical contributor windows: for a zero centre `k` and a preimage `p`
of a point of `S₀` with `ρ(p) > 200R_k/T`, the zero block of every window cloud point `y` and of
the plane `D(K_aΦ_a)(η_a(pre y))` vanish. -/
theorem circleTable_ZB_BPC (hΔ1 : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) (hT : 1600 * (1000000 * Δ) ≤ T) (he : e < 1 / 40)
    (hpre : ∀ x, (letI := inducedMetricSpace S.completion.metric
        dist (pre x) (jref x).1 < 200 * S.rho (jref x).1) ∧
      ‖S.circleEta_BIF (jref x).1 (pre x)‖ ≤ 7 ∧
      (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap (pre x).val) = x.1)
    (hrpre : ∀ x, (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap (rpre x).val) = x.1) :
    ∀ εc σ' : ℝ, 0 < εc → σ' ≤ εc / 10000 → ∀ (x₀ : W.pieceInterior ⊤)
      (k : S.ZeroIdx_BAUGC) (p : W.pieceInterior ⊤),
      (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap p.val) ∈
        (actualSlotsV2_BAUGD S).stageCloud 0 →
      200 * S.zeroRadius_BAUGC k / T < S.rho p →
      ∀ y (hy : y ∈ (actualSlotsV2_BAUGD S).stageCloud 0),
        (closedBall y (80 * εc⁻¹ * (σ' * S.rho (if hyT : y ∈
            (actualSlotsV2_BAUGD S).stageCloudEnlarged 0
            then rpre ⟨y, hyT⟩ else x₀))) ∩
          ball ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap p.val))
            (8 * εc⁻¹ * (σ' * S.rho (if hpT : (actualSlotsV2_BAUGD S).stageProj 0
                (S.boundaryOriginalMap p.val) ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 0
              then rpre ⟨_, hpT⟩ else x₀)))).Nonempty →
        S.zeroBlockCLM_BAUGC k y = 0 ∧
        ∀ v : ℝ², (fderiv ℝ
            (⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
            S.circleStageModel_BPC Acf ccf A1f c1f Bτf cτf (jref ⟨y, hy⟩).1)
          (S.circleEta_BIF (jref ⟨y, hy⟩).1 (pre ⟨y, hy⟩)) v) (S.zeroTag_BAUGC k) = 0 := by
  intro εc σ' hε hσε x₀ k p hp hρp y hy hwin
  have h := hpre ⟨y, hy⟩
  have hΔ0 : 0 < Δ := by linarith only [hΔ1]
  have hyT : y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 0 :=
    actualSlotsV2_stageCloud_subset_BAUGD S hΔ0.le 0 hy
  have hpT : (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap p.val) ∈
      (actualSlotsV2_BAUGD S).stageCloudEnlarged 0 :=
    actualSlotsV2_stageCloud_subset_BAUGD S hΔ0.le 0 hp
  rw [dite_eq_left hyT, dite_eq_left hpT] at hwin
  have hj := (Set.Finite.mem_toFinset _).mp (jref ⟨y, hy⟩).2
  rw [S.circleStageModel_comp_BPC Acf ccf A1f c1f Bτf cτf hj]
  exact S.circle_zero_block_point_BPC (jref ⟨y, hy⟩) (Acf _) (ccf _) (A1f _) (c1f _) (Bτf _)
    (cτf _) hΔ1 hΛ hΛΔ hV hβ1 hb hT he hε hσε k hp hρp h.1 h.2.1 h.2.2 (hrpre ⟨y, hyT⟩)
    (hrpre ⟨_, hpT⟩) hwin

end BoundarySupply

open Classical in
/-- **PORT TARGET (CIRCLE (TCP03–TCP06), stage `0`)**: the interior stage table of the actual slot
(PortTargets v3.1), STRENGTHENED: the frozen premises `Γ < 1`, `sg < Γ³/(100·tcpGraphConst)` and
`eg < Γ·sg/100` are not needed and are dropped (the verbatim frozen form is the `example` below).
Data: `Ψ a = circleStageModel_BPC` (TCP05's model graph of the circle centre `a`, pruned by CFS27),
`Kint a = id`, `Pc a = circleStageOwn_BPC`, core preimages `pre` with references `ref`
(threshold-`7` cores), radius preimages `rpre` (any preimage). Closed twin
`exists_firstStagePlanes_PLN`. -/
theorem port_circle_interior_table_BAUGP {ν Γ sg eg : ℝ} (hΓ : 0 < Γ)
    (hsg : 0 < sg) (hsgΓ : sg < Γ / 200)
    (heg : 0 < eg) (heg1 : eg < 1 / 100) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ γ₀ ηc θt : ℝ, 0 < η₂ ∧ 0 < γ₀ ∧
    0 < ηc ∧ 0 < θt ∧ θt < 1 ∧ ∀ Δ : ℝ, 1200 ≤ Δ → ∃ η₁ : ℝ, 0 < η₁ ∧
    ∀ {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
      {βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
      {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
      {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {n : ℕ}
      {B : NearlyCuspidalBoundary W g K δn} {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤)
          3}
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
              fderiv ℝ (Kint a ∘ Ψ a) (S.circleEta_BIF a x) (mvfderiv 𝓘(ℝ, E3) (S.circleEta_BIF a)
                  x w)‖ ≤
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
        (dist q (ref ⟨x, hx⟩) < 200 * S.rho (ref ⟨x, hx⟩) ∧ ‖S.circleEta_BIF (ref ⟨x, hx⟩) q‖ ≤ 8)
            ∧ dist q (ref ⟨x, hx⟩) < stageDomain_BIF Δ 0 * S.rho (ref ⟨x, hx⟩) ∧
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
      -- (SCL) [v3.1]
      (∀ a ∈ S.stageCentres_BIF 0, ∀ u v : ℝ²,
        ((fderiv ℝ (Kint a ∘ Ψ a) u v) S.scaleTag_BAUGA).snd = 0) := by
  have hR : sg / Γ < 1 / 100 := by
    rw [div_lt_iff₀ hΓ]
    linarith only [hsgΓ, hΓ]
  have hR0 : 0 ≤ sg / Γ := div_nonneg hsg.le hΓ.le
  have h2sg : 2 * sg / Γ ≤ 1 := by
    rw [div_le_iff₀ hΓ]
    linarith only [hsgΓ, hΓ]
  have hrs := circle_row_supply_BPC heg heg1 hν hν1
  obtain ⟨σ, hσ, hσ1, η₂, γ₀, ηc, θt, hη₂, hγ₀, hηc, hθt, hθt1, hrow⟩ := hrs
  refine ⟨σ, hσ, hσ1, η₂, γ₀, ηc, θt, hη₂, hγ₀, hηc, hθt, hθt1, fun Δ hΔ => ?_⟩
  have hrΔ := hrow Δ hΔ
  obtain ⟨η₁, hη₁, hrowΔ⟩ := hrΔ
  refine ⟨η₁, hη₁, ?_⟩
  intro K A β βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W _ g δn n B oM S
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
    h26 h27 h28 h29 h30 h31 _ _ hV hβ1 hb _ _
  have e6 : (10 : ℝ) ^ 6 = 1000000 := by norm_num
  have e5 : (10 : ℝ) ^ 5 = 100000 := by norm_num
  rw [e6, e5] at h4
  have hΔ1 : 1 ≤ Δ := by linarith only [hΔ]
  choose Acf ccf A1f c1f Bτf cτf hprops hTG hscl using fun a : S.CircleIdx_BAUGD =>
    hrowΔ S h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23
      h24 h25 h26 h27 h28 h29 h30 h31 a
  choose jref pre hpre using fun x : (actualSlotsV2_BAUGD S).stageCloud 0 =>
    S.exists_core_of_mem_stageCloud_zero_BPC x.2
  have hrp : ∀ x : (actualSlotsV2_BAUGD S).stageCloudEnlarged 0, ∃ r : W.pieceInterior ⊤,
      (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap r.val) = x.1 := by
    intro x
    obtain ⟨r, -, hr⟩ := x.2
    exact ⟨r, hr⟩
  choose rpre hrpre using hrp
  exact ⟨S.circleStageModel_BPC Acf ccf A1f c1f Bτf cτf, fun _ => ContinuousLinearMap.id ℝ _,
    S.circleStageOwn_BPC, rpre, pre, fun x => (jref x).1,
    S.circleTable_M_BPC Acf ccf A1f c1f Bτf cτf (fun i => ⟨(hprops i).1, (hprops i).2.2⟩),
    S.circleTable_OWN_BPC Acf ccf A1f c1f Bτf cτf (fun i => (hprops i).2.1),
    S.circleTable_Q_BPC Acf ccf A1f c1f Bτf cτf,
    S.circleTable_TG_BPC Acf ccf A1f c1f Bτf cτf hTG, hrpre,
    S.circleTable_SEL_BPC jref pre hpre,
    S.circleTable_LOC_BPC jref pre hR0 hR hpre,
    S.circleTable_COV_BPC jref pre h2sg hpre,
    S.circleTable_PRE_BPC jref pre hpre,
    S.circleTable_PP_BPC Acf ccf A1f c1f Bτf cτf jref pre h1 h4 hΔ1 hpre,
    S.circleTable_SB_BPC Acf ccf A1f c1f Bτf cτf,
    S.circleTable_FM_BPC Acf ccf A1f c1f Bτf cτf jref pre rpre hΔ1 h1 h4 hV hβ1 hb heg.le heg1
      (fun i x h1 h2 => (hTG i x h1 h2).1) hpre hrpre,
    S.circleTable_ZB_BPC Acf ccf A1f c1f Bτf cτf jref pre rpre hΔ1 h1 h4 hV hβ1 hb h7 h6 hpre hrpre,
    S.circleTable_SCL_BPC Acf ccf A1f c1f Bτf cτf hscl⟩

open Classical in
/-- `port_circle_interior_table_BAUGP` in the verbatim frozen form of PortTargets v3.1 (with the
three unused premises `hΓ1`, `hsgC`, `hegΓ`; the long frozen comments are shortened to their clause
labels). -/
example {ν Γ sg eg : ℝ} (hΓ : 0 < Γ) (hΓ1 : Γ < 1)
    (hsg : 0 < sg) (hsgΓ : sg < Γ / 200) (hsgC : sg < Γ ^ 3 / (100 * tcpGraphConst))
    (heg : 0 < eg) (heg1 : eg < 1 / 100) (hegΓ : eg < Γ * sg / 100) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ γ₀ ηc θt : ℝ, 0 < η₂ ∧ 0 < γ₀ ∧
    0 < ηc ∧ 0 < θt ∧ θt < 1 ∧ ∀ Δ : ℝ, 1200 ≤ Δ → ∃ η₁ : ℝ, 0 < η₁ ∧
    ∀ {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
      {βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
      {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
      {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {n : ℕ}
      {B : NearlyCuspidalBoundary W g K δn} {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤)
          3}
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
              fderiv ℝ (Kint a ∘ Ψ a) (S.circleEta_BIF a x) (mvfderiv 𝓘(ℝ, E3) (S.circleEta_BIF a)
                  x w)‖ ≤
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
        (dist q (ref ⟨x, hx⟩) < 200 * S.rho (ref ⟨x, hx⟩) ∧ ‖S.circleEta_BIF (ref ⟨x, hx⟩) q‖ ≤ 8)
            ∧ dist q (ref ⟨x, hx⟩) < stageDomain_BIF Δ 0 * S.rho (ref ⟨x, hx⟩) ∧
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
      -- (SCL) [v3.1]
      (∀ a ∈ S.stageCentres_BIF 0, ∀ u v : ℝ²,
        ((fderiv ℝ (Kint a ∘ Ψ a) u v) S.scaleTag_BAUGA).snd = 0)
  := (fun _ _ _ => port_circle_interior_table_BAUGP hΓ hsg hsgΓ heg heg1 hν hν1) hΓ1 hsgC hegΓ

end DifferentialGeometry.Geometry.Collapse

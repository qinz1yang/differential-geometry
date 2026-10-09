import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortCircleTransport
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortCircleModelFacts
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSlimClausesB

/-!
# The marker clauses of the circle stage table on a boundary supply (lane O-PORT-A)

The clauses (FM*-int) and (ZB*-int) of `port_circle_interior_table_BAUGP` (PortTargets v3.1) at
ONE window, on the actual slot `actualSlotsV2_BAUGD S` (`f(q) = π₀F_∂(q) = F_∂(q)`, `q ∈ W°`), for
the stage-`0` model `circleModelOf_BPC` (TCP05's model graph pruned by CFS27). Closed twins:
`FirstStagePlanes_PLN.pre_plateau_PLN` / `.full_marker` (`ActualStagePlaneFullMarker.lean`) and
`zero_chain_PLN` / `FirstStagePlanes_PLN.zero_block` (`ActualStagePlaneZeroBlock.lean`); the
boundary differences are only that the preimages lie in `W°` and that the circle blocks of `F_∂`
are read through BAUG-D's `circleBlock_boundaryOriginalMap_BAUGD`.

* the circle marker layer of `S̃₀`: `interiorMapOn_circle_block_BPC`, `circleBlock_stageZero_BPC`,
  `circleMarker_stageZero_BPC`, `circle_cutoff_eq_one_BPC` (plateau), `circle_full_marker_BPC`,
  `circle_marker_scale_BPC` ((AS)), `lipschitzWith_circleMarker_BPC`,
  **`circle_scale_ratio_BPC`** (CFS07's (MC) for ANY preimages of points of `S̃₀`);
* `zeroBlockCLM_stageZero_BPC`, `markerCLM_circle_BPC`, `markerTag_circle_BPC`;
* **`circle_full_marker_point_BPC`** (FM*) and **`circle_zero_block_point_BPC`** (ZB*).
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
  θ W g δn n B oM)

/-- The circle block of the interior formula: `F_int(q)_j = (ρ_jζ_j(q) η_j(q), ρ_jζ_j(q))`. -/
theorem interiorMapOn_circle_block_BPC (j : S.CircleIdx_BAUGD) (q : W.pieceInterior ⊤) :
    S.interiorMapOn_BAUGA q (.inl j) =
      WithLp.toLp 2 ((S.rho j.1 * (letI := inducedMetricSpace S.completion.metric
          letI := S.completion.complete
          S.family.circle.cutoff j.1 q)) • S.circleEta_BIF j.1 q,
        S.rho j.1 * (letI := inducedMetricSpace S.completion.metric
          letI := S.completion.complete
          S.family.circle.cutoff j.1 q)) := by
  rw [S.circleEta_eq_circleCoordW_BAUGD j q, S.circleCoordW_val_BAUGD j q]
  rfl

/-- The circle block of `f(q) = π₀F_∂(q)` is the circle block of the interior formula. -/
theorem circleBlock_stageZero_BPC (j : S.CircleIdx_BAUGD) (q : W.pieceInterior ⊤) :
    (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val) (Sum.inl (.inl j)) =
      WithLp.toLp 2 ((S.rho j.1 * (letI := inducedMetricSpace S.completion.metric
          letI := S.completion.complete
          S.family.circle.cutoff j.1 q)) • S.circleEta_BIF j.1 q,
        S.rho j.1 * (letI := inducedMetricSpace S.completion.metric
          letI := S.completion.complete
          S.family.circle.cutoff j.1 q)) := by
  rw [stageProj_zero_V2_BAUGD S, S.boundaryOriginalMap_inl_BPS q (.inl j),
    S.interiorMapOn_circle_block_BPC j q]

/-- The circle marker `j` of `f(q) = π₀F_∂(q)` is `ρ_j ζ_j(q)`. -/
theorem circleMarker_stageZero_BPC (j : S.CircleIdx_BAUGD) (q : W.pieceInterior ⊤) :
    S.circleMarker_BAUGD j ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val)) =
      S.rho j.1 * (letI := inducedMetricSpace S.completion.metric
        letI := S.completion.complete
        S.family.circle.cutoff j.1 q) := by
  rw [BoundarySupplyCore.circleMarker_BAUGD, blockMarkerCLM_apply, S.circleBlock_stageZero_BPC j q]
  rfl

/-- **The circle plateau**: `ζ_j(q) = 1` on the threshold-`8` core of `j`. -/
theorem circle_cutoff_eq_one_BPC (j : S.CircleIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hd : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 200 * S.rho j.1)
    (hη : ‖S.circleEta_BIF j.1 q‖ ≤ 8) :
    (letI := inducedMetricSpace S.completion.metric
     letI := S.completion.complete
     S.family.circle.cutoff j.1 q) = 1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  rw [S.circleEta_eq_cgpCircleCoord_BBP j] at hη
  exact circle_cutoff_eq_one_of_coord_le_GAF_BAUGP S.family.toLocalPacketsOnB S.family.zero j hd hη

/-- **Full markers on `S̃₀`**: at a point of the enlarged cloud some circle marker is `ρ_j`. -/
theorem circle_full_marker_BPC {x : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 0) :
    ∃ j : S.CircleIdx_BAUGD, S.circleMarker_BAUGD j x = S.rho j.1 := by
  obtain ⟨j, p, hd, hη, rfl⟩ := S.exists_core_of_mem_stageCloudEnlarged_zero_BPC hx
  refine ⟨j, ?_⟩
  rw [S.circleMarker_stageZero_BPC j p, S.circle_cutoff_eq_one_BPC j hd hη, mul_one]

/-- **(AS)**: a positive circle marker `j` at `f(q)` gives `3ρ_j/4 ≤ ρ(q) ≤ 5ρ_j/4`. -/
theorem circle_marker_scale_BPC (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) (j : S.CircleIdx_BAUGD) (q : W.pieceInterior ⊤)
    (hpos : 0 < S.circleMarker_BAUGD j
      ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val))) :
    3 * S.rho j.1 / 4 ≤ S.rho q.val ∧ S.rho q.val ≤ 5 * S.rho j.1 / 4 := by
  rw [stageProj_zero_V2_BAUGD S, (S.circleBlock_boundaryOriginalMap_BAUGD j q.val).2] at hpos
  have hrj := S.rho_pos j.1
  have hc : 0 < S.circleCutoffW_BAUGD j q.val := pos_of_mul_pos_right hpos hrj.le
  obtain ⟨h1, h2⟩ := S.circle_scale_comparable_BAUGD hΛ hΔ1 hΛΔ hV hβ1 hb j q.val hc
  constructor <;> linarith

/-- The circle markers are `1`-Lipschitz on `H^∂`. -/
theorem lipschitzWith_circleMarker_BPC (j : S.CircleIdx_BAUGD) :
    LipschitzWith 1 (S.circleMarker_BAUGD j) :=
  ContinuousLinearMap.lipschitzWith_of_opNorm_le (by
    rw [NNReal.coe_one]
    exact norm_blockMarkerCLM_le _)

/-- **CFS07's (MC) on the enlarged circle cloud for ANY preimages**: if `f(p), f(q) ∈ S̃₀` and
`|f(q) − f(p)| ≤ L'·max(σρ(q), σρ(p))` with `L'σ ≤ 1/5`, then `3/5 ≤ ρ(q)/ρ(p) ≤ 5/3`. -/
theorem circle_scale_ratio_BPC (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) {σ L' : ℝ} (hσ : 0 ≤ σ) (hL' : 0 ≤ L')
    (hLσ : L' * σ ≤ 1 / 5) {p q : W.pieceInterior ⊤}
    (hp : (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap p.val) ∈
      (actualSlotsV2_BAUGD S).stageCloudEnlarged 0)
    (hq : (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val) ∈
      (actualSlotsV2_BAUGD S).stageCloudEnlarged 0)
    (hd : dist ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val))
        ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap p.val)) ≤
      L' * max (σ * S.rho q.val) (σ * S.rho p.val)) :
    3 / 5 * S.rho p.val ≤ S.rho q.val ∧ S.rho q.val ≤ 5 / 3 * S.rho p.val := by
  obtain ⟨i, hi⟩ := S.circle_full_marker_BPC hp
  obtain ⟨j, hj⟩ := S.circle_full_marker_BPC hq
  exact scale_ratio_of_any_preimages_KA3
    (fun p : W.pieceInterior ⊤ =>
      (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap p.val))
    (fun p : W.pieceInterior ⊤ => S.rho p.val) (fun j : S.CircleIdx_BAUGD => S.circleMarker_BAUGD j)
    (fun j : S.CircleIdx_BAUGD => S.rho j.1) (fun j => S.rho_pos j.1)
    (fun j => S.lipschitzWith_circleMarker_BPC j)
    (fun j q h => S.circle_marker_scale_BPC hΛ hΔ1 hΛΔ hV hβ1 hb j q h) hσ hL' hLσ hi hj hd

/-- The marker functional of a circle marker chart is its circle marker. -/
theorem markerCLM_circle_BPC (j : S.CircleIdx_BAUGD) :
    S.markerCLM_BAUGC (.inl j) = S.circleMarker_BAUGD j :=
  rfl

/-- The interior tag of a circle marker chart. -/
theorem markerTag_circle_BPC (j : S.CircleIdx_BAUGD) : S.markerTag_BAUGC (.inl j) = .inl j :=
  rfl

/-- The zero block of `f(q)` is the zero block of the interior formula. -/
theorem zeroBlockCLM_stageZero_BPC (k : S.ZeroIdx_BAUGC) (q : W.pieceInterior ⊤) :
    S.zeroBlockCLM_BAUGC k ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val)) =
      S.interiorMapOn_BAUGA q (S.zeroTag_BAUGC k) := by
  rw [BoundarySupplyCore.zeroBlockCLM_BAUGC, blockProjCLM_apply_PLN, stageProj_zero_V2_BAUGD S]
  exact S.boundaryOriginalMap_inl_BPS q _

variable (a : S.CircleIdx_BAUGD) (Ac : S.IntTag_BAUGA → ℝ² →L[ℝ] ℝ²) (cc : S.IntTag_BAUGA → ℝ²)
  (A1 : S.IntTag_BAUGA → ℝ² →L[ℝ] ℝ) (c1 : S.IntTag_BAUGA → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ)

/-- **The plateau step of (FM*), transported**: if the (TG) value bound holds at `q` (a point of
the threshold-`8` core of `a`) and the circle chart `j` is in its plateau at `q`
(`ζ_j(q) = 1`, `‖η_j(q)‖ ≤ 351/49`, `q ∈ B(j, 200ρ_j)`), the circle marker of `j` annihilates the
derivative of the stage-`0` model of `a` at `η_a(q)`. -/
theorem circleModelOf_marker_fderiv_BPC (hΛ : 0 ≤ Λ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    (hΔ1 : 1 ≤ Δ) {eg : ℝ} (heg0 : 0 ≤ eg) (heg : eg < 1 / 100) (j : S.CircleIdx_BAUGD)
    {q : W.pieceInterior ⊤}
    (hqa : letI := inducedMetricSpace S.completion.metric; dist q a.1 < 200 * S.rho a.1)
    (hqj : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 200 * S.rho j.1)
    (hcq : (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.circle.cutoff j.1 q) = 1)
    (hηq : ‖S.circleEta_BIF j.1 q‖ ≤ 351 / 49 * 1)
    (hTG : ‖(S.rho a.1)⁻¹ • S.interiorMapOn_BAUGA q -
      S.circleModelOf_BPC a Ac cc A1 c1 Bτ cτ (S.circleEta_BIF a.1 q)‖ < eg) (v : ℝ²) :
    ((fderiv ℝ (S.circleModelOf_BPC a Ac cc A1 c1 Bτ cτ) (S.circleEta_BIF a.1 q) v)
      (S.markerTag_BAUGC (.inl j))).snd = 0 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  have hra := S.rho_pos a.1
  have hrj := S.rho_pos j.1
  have hC : Λ * 200 ≤ 1 / 200 := by nlinarith
  have hratio := ratio_ge_of_common_point_PLN (ρ := fun x : W.pieceInterior ⊤ => S.rho x)
    S.family.lipschitz_scale hΛ hra hrj hqa hqj hC hC
  have hs : 99 / 100 ≤ S.rho j.1 / S.rho a.1 := by rw [le_div_iff₀ hra]; exact hratio
  have hy : S.interiorMapOn_BAUGA q (.inl j) =
      WithLp.toLp 2 ((S.rho j.1 * 1) • S.circleEta_BIF j.1 q, S.rho j.1 * 1) := by
    rw [S.interiorMapOn_circle_block_BPC j q, hcq]
  have h := tcpPrunedModel_marker_fderiv_BPC S.family.toLocalPacketsOnB S.family.zero a.1 Ac cc A1
    c1 Bτ cτ j hs heg0 heg hηq hy hTG v
  rw [blockMarkerCLM_apply] at h
  exact h

/-- **(FM*-int) at one window** (closed `FirstStagePlanes_PLN.pre_plateau_PLN` + `.full_marker`):
for a circle chart `j` with a threshold-`7` core point `p`, a cloud point `f(q)` (`q` in the
threshold-`7` core of the reference `a`), the (TG) value bound at `q`, radius preimages `r_y`,
`r_x` of `f(q)`, `f(p)` and the contributor window
`B̄(f(q), 80ε⁻¹σρ(r_y)) ∩ B(f(p), 8ε⁻¹σρ(r_x)) ≠ ∅` (`0 ≤ σ ≤ ε/10000`): the circle marker of `j`
is full at `f(q)` and annihilates `D(K_aΦ_a)(η_a q)`. -/
theorem circle_full_marker_point_BPC (hΔ1 : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) {eg : ℝ}
    (heg0 : 0 ≤ eg) (heg : eg < 1 / 100) {εc σ' : ℝ} (hε : 0 < εc) (hσ : 0 ≤ σ')
    (hσε : σ' ≤ εc / 10000) (j : S.CircleIdx_BAUGD) {p q ry rx : W.pieceInterior ⊤}
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hpd : letI := inducedMetricSpace S.completion.metric; dist p j.1 < 200 * S.rho j.1)
    (hpη : ‖S.circleEta_BIF j.1 p‖ ≤ 7)
    (hqd : letI := inducedMetricSpace S.completion.metric; dist q a.1 < 200 * S.rho a.1)
    (hqη : ‖S.circleEta_BIF a.1 q‖ ≤ 7)
    (hqy : (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val) = y)
    (hry : (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap ry.val) = y)
    (hrx : (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap rx.val) =
      (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap p.val))
    (hmeet : (closedBall y (80 * εc⁻¹ * (σ' * S.rho ry)) ∩
      ball ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap p.val))
        (8 * εc⁻¹ * (σ' * S.rho rx))).Nonempty)
    (hTG : ‖(S.rho a.1)⁻¹ • S.interiorMapOn_BAUGA q -
      S.circleModelOf_BPC a Ac cc A1 c1 Bτ cτ (S.circleEta_BIF a.1 q)‖ < eg) :
    S.markerCLM_BAUGC (.inl j) y = S.rho j.1 ∧
      ∀ v : ℝ², ((fderiv ℝ (S.circleModelOf_BPC a Ac cc A1 c1 Bτ cτ) (S.circleEta_BIF a.1 q) v)
        (S.markerTag_BAUGC (.inl j))).snd = 0 := by
  subst hqy
  have hrj := S.rho_pos j.1
  have hcp := S.circle_cutoff_eq_one_BPC j hpd (by linarith only [hpη])
  have hp8 := S.stageProj_mem_stageCloudEnlarged_zero_BPC j hpd (by linarith only [hpη])
  have hq8 := S.stageProj_mem_stageCloudEnlarged_zero_BPC a hqd (by linarith only [hqη])
  -- (FD): the contributor is within `ρ_j/50`
  have hFD : dist ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val))
      ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap p.val)) < S.rho j.1 / 50 := by
    have h := contributor_dist_lt_fiftieth_of_full_marker
      (P := {z : W.pieceInterior ⊤ // (actualSlotsV2_BAUGD S).stageProj 0
        (S.boundaryOriginalMap z.val) ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 0})
      (fun z => (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap z.1.val))
      (fun z => S.rho z.1.val) (fun j : S.CircleIdx_BAUGD => S.circleMarker_BAUGD j)
      (fun j : S.CircleIdx_BAUGD => S.rho j.1) (fun j => S.rho_pos j.1)
      (fun j => S.lipschitzWith_circleMarker_BPC j) (fun z => S.circle_full_marker_BPC z.2)
      (fun j z h => S.circle_marker_scale_BPC hΛ hΔ1 hΛΔ hV hβ1 hb j z.1 h) hε hσ hσε
      ⟨rx, by rw [hrx]; exact hp8⟩ ⟨ry, by rw [hry]; exact hq8⟩ j
      (by
        change S.circleMarker_BAUGD j ((actualSlotsV2_BAUGD S).stageProj 0
          (S.boundaryOriginalMap rx.val)) = S.rho j.1
        rw [hrx, S.circleMarker_stageZero_BPC j p, hcp, mul_one])
      (by
        obtain ⟨z, hz1, hz2⟩ := hmeet
        refine ⟨z, ?_, ?_⟩
        · change z ∈ closedBall ((actualSlotsV2_BAUGD S).stageProj 0
            (S.boundaryOriginalMap ry.val)) (80 * εc⁻¹ * (σ' * S.rho ry.val))
          rw [hry]
          exact hz1
        · change z ∈ ball ((actualSlotsV2_BAUGD S).stageProj 0
            (S.boundaryOriginalMap rx.val)) (8 * εc⁻¹ * (σ' * S.rho rx.val))
          rw [hrx]
          exact hz2)
    beta_reduce at h
    rw [hry, hrx] at h
    exact h
  -- the `j`-block of `f(q)` is near the full block of `f(p)`
  have hxb : (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap p.val)
      (Sum.inl (.inl j)) =
      WithLp.toLp 2 ((S.rho j.1 * 1) • S.circleEta_BIF j.1 p, S.rho j.1 * 1) := by
    rw [S.circleBlock_stageZero_BPC j p, hcp]
  have hblk := dist_block_lt_of_eq_BPS (S.circleBlock_stageZero_BPC j q) hxb hFD
  have hfv := fv_of_block_dist_GAF hrj le_rfl (by linarith only [hpη]) hblk
  have hζ := hfv.1
  have hv := hfv.2
  have hcq0 : 0 < S.circleCutoffW_BAUGD j q.val := by
    rw [S.circleCutoffW_val_BAUGD j q]
    linarith only [hζ]
  have hqj := S.circle_dist_lt_of_cutoff_pos_BAUGD j q hcq0
  have hcq := S.circle_cutoff_eq_one_BPC j hqj (by linarith only [hv])
  refine ⟨?_, fun v => ?_⟩
  · rw [S.markerCLM_circle_BPC j, S.circleMarker_stageZero_BPC j q, hcq, mul_one]
  exact S.circleModelOf_marker_fderiv_BPC a Ac cc A1 c1 Bτ cτ hΛ hΛΔ hΔ1 heg0 heg j hqd hqj hcq
    hv.le hTG v

/-- **The model's zero block vanishes at a large reference**: if `ρ(a) > (80/3)R_k/T`, the zero
block of the stage-`0` model of `a` is identically zero. -/
theorem circleModelOf_zero_eq_zero_BPC (hΛ : 0 ≤ Λ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    (hΔ1 : 1 ≤ Δ) (hT : 0 < T) (he : e < 1 / 40) (k : S.ZeroIdx_BAUGC)
    (hρa : 80 / 3 * (S.zeroRadius_BAUGC k / T) < S.rho a.1) (u : ℝ²) :
    S.circleModelOf_BPC a Ac cc A1 c1 Bτ cτ u (S.zeroTag_BAUGC k) = 0 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  have hΛ10 : Λ * 10 ≤ 1 / 4 := by nlinarith
  have habs := zero_not_listed_BPC S.family.toLocalPacketsOnBFR.toLocalPacketsOnBF hΛ hΛ10 hT he
    (i := a.1) k hρa
  exact tcpPrunedModel_zero_of_not_listed_BPC S.family.toLocalPacketsOnB S.family.zero a.1 Ac cc
    A1 c1 Bτ cτ k habs u

/-- **(ZB*-int) at one window** (closed `zero_chain_PLN` + `FirstStagePlanes_PLN.zero_block`): for
a zero centre `k`, a preimage `p` of a point of `S₀` with `ρ(p) > 200R_k/T`, a cloud point `f(q)`
(`q` in the threshold-`7` core of the reference `a`), radius preimages `r_y`, `r_x` of `f(q)`,
`f(p)` and the contributor window (`σ ≤ ε/10000`): the zero block of `f(q)` and of
`D(K_aΦ_a)(η_a q)` vanish. -/
theorem circle_zero_block_point_BPC (hΔ1 : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b)
    (hT : 1600 * (1000000 * Δ) ≤ T) (he : e < 1 / 40) {εc σ' : ℝ} (hε : 0 < εc)
    (hσε : σ' ≤ εc / 10000) (k : S.ZeroIdx_BAUGC) {p q ry rx : W.pieceInterior ⊤}
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hp : (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap p.val) ∈
      (actualSlotsV2_BAUGD S).stageCloud 0)
    (hρp : 200 * S.zeroRadius_BAUGC k / T < S.rho p)
    (hqd : letI := inducedMetricSpace S.completion.metric; dist q a.1 < 200 * S.rho a.1)
    (hqη : ‖S.circleEta_BIF a.1 q‖ ≤ 7)
    (hqy : (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val) = y)
    (hry : (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap ry.val) = y)
    (hrx : (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap rx.val) =
      (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap p.val))
    (hmeet : (closedBall y (80 * εc⁻¹ * (σ' * S.rho ry)) ∩
      ball ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap p.val))
        (8 * εc⁻¹ * (σ' * S.rho rx))).Nonempty) :
    S.zeroBlockCLM_BAUGC k y = 0 ∧
      ∀ v : ℝ², (fderiv ℝ (S.circleModelOf_BPC a Ac cc A1 c1 Bτ cτ) (S.circleEta_BIF a.1 q) v)
        (S.zeroTag_BAUGC k) = 0 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  subst hqy
  have hΔ : 0 < Δ := by linarith only [hΔ1]
  have hT0 : 0 < T := by linarith only [hT, hΔ]
  have hR := (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  have hRk : 0 < S.zeroRadius_BAUGC k := hR
  have hra := S.rho_pos a.1
  have hp8 : (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap p.val) ∈
      (actualSlotsV2_BAUGD S).stageCloudEnlarged 0 :=
    actualSlotsV2_stageCloud_subset_BAUGD S hΔ.le 0 hp
  have hq8 := S.stageProj_mem_stageCloudEnlarged_zero_BPC a hqd (by linarith only [hqη])
  have hrx8 : (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap rx.val) ∈
      (actualSlotsV2_BAUGD S).stageCloudEnlarged 0 := by rw [hrx]; exact hp8
  have hry8 : (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap ry.val) ∈
      (actualSlotsV2_BAUGD S).stageCloudEnlarged 0 := by rw [hry]; exact hq8
  -- the window radius is positive, the window distance is `≤ 88ε⁻¹·max`
  obtain ⟨z, hz1, hz2⟩ := hmeet
  have hεi : 0 < εc⁻¹ := inv_pos.mpr hε
  have hrxp := S.rho_pos rx.val
  have hryp := S.rho_pos ry.val
  have h1 := mem_closedBall.mp hz1
  have h2 := mem_ball.mp hz2
  have hσ : 0 < σ' := by
    by_contra hneg
    replace hneg := not_lt.mp hneg
    have h3 : σ' * S.rho rx.val ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hrxp.le
    have h4 : 8 * εc⁻¹ * (σ' * S.rho rx.val) ≤ 0 := by
      have := mul_nonneg (by linarith only [hεi] : (0 : ℝ) ≤ 8 * εc⁻¹) (neg_nonneg.mpr h3)
      linarith only [this]
    linarith only [dist_nonneg (x := z) (y := (actualSlotsV2_BAUGD S).stageProj 0
      (S.boundaryOriginalMap p.val)), h2, h4]
  have hd : dist ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap ry.val))
      ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap rx.val)) ≤
      88 * εc⁻¹ * max (σ' * S.rho ry.val) (σ' * S.rho rx.val) := by
    rw [hry, hrx]
    have h3 := dist_triangle_left ((actualSlotsV2_BAUGD S).stageProj 0
      (S.boundaryOriginalMap q.val)) ((actualSlotsV2_BAUGD S).stageProj 0
      (S.boundaryOriginalMap p.val)) z
    have hm1 : σ' * S.rho ry.val ≤ max (σ' * S.rho ry.val) (σ' * S.rho rx.val) := le_max_left _ _
    have hm2 : σ' * S.rho rx.val ≤ max (σ' * S.rho ry.val) (σ' * S.rho rx.val) := le_max_right _ _
    have h5 : 80 * εc⁻¹ * (σ' * S.rho ry.val) ≤
        80 * εc⁻¹ * max (σ' * S.rho ry.val) (σ' * S.rho rx.val) :=
      mul_le_mul_of_nonneg_left hm1 (by linarith only [hεi])
    have h6 : 8 * εc⁻¹ * (σ' * S.rho rx.val) ≤
        8 * εc⁻¹ * max (σ' * S.rho ry.val) (σ' * S.rho rx.val) :=
      mul_le_mul_of_nonneg_left hm2 (by linarith only [hεi])
    linarith only [h1, h2, h3, h5, h6]
  have hLs : 88 * εc⁻¹ * σ' ≤ 1 / 5 := by
    have h7 : εc⁻¹ * σ' ≤ 1 / 10000 := by
      rw [inv_mul_le_iff₀ hε]
      linarith only [hσε]
    linarith only [h7]
  -- CFS07 (MCb) and the two preimage ratios: `ρ(q) ≥ (27/125)ρ(p)`
  have hm := (S.circle_scale_ratio_BPC hΛ hΔ1 hΛΔ hV hβ1 hb hσ.le (by positivity) hLs hrx8 hry8
    hd).1
  have hpr1 := (S.circle_scale_ratio_BPC hΛ hΔ1 hΛΔ hV hβ1 hb (σ := 0) (L' := 0) le_rfl le_rfl
    (by norm_num) hp8 hrx8 (by rw [hrx, dist_self]; simp)).1
  have hpr2 := (S.circle_scale_ratio_BPC hΛ hΔ1 hΛΔ hV hβ1 hb (σ := 0) (L' := 0) le_rfl le_rfl
    (by norm_num) hry8 hq8 (by rw [hry, dist_self]; simp)).1
  have hρq : 27 / 125 * S.rho p.val ≤ S.rho q.val := by
    have hrp := S.rho_pos p.val
    nlinarith only [hm, hpr1, hpr2, hrp, hrxp, hryp]
  have hρq20 : 20 * S.zeroRadius_BAUGC k / T < S.rho q.val := by
    have h8 : 20 * S.zeroRadius_BAUGC k / T < 27 / 125 * (200 * S.zeroRadius_BAUGC k / T) := by
      have := div_pos hRk hT0
      rw [mul_div_assoc, mul_div_assoc]
      nlinarith only [this]
    have h9 : 27 / 125 * (200 * S.zeroRadius_BAUGC k / T) < 27 / 125 * S.rho p.val :=
      mul_lt_mul_of_pos_left hρp (by norm_num)
    linarith only [h8, h9, hρq]
  refine ⟨?_, fun v => ?_⟩
  · rw [S.zeroBlockCLM_stageZero_BPC k q]
    exact S.interiorMapOn_zero_eq_zero_BPS hT0 he k hρq20
  -- the zero support misses `D_a`: the model's zero block vanishes
  have hqa := (scale_mem_of_dist_lt_KC (ρ := fun x : W.pieceInterior ⊤ => S.rho x)
    S.family.lipschitz_scale hΛ hra hqd (by nlinarith only [hΛΔ, hΛ, hΔ1])).2
  change S.rho q.val ≤ 5 / 4 * S.rho a.1 at hqa
  have hρa : 80 / 3 * (S.zeroRadius_BAUGC k / T) < S.rho a.1 := by
    have h10 : 200 * S.zeroRadius_BAUGC k / T = 200 * (S.zeroRadius_BAUGC k / T) := by ring
    have h11 : 27 / 125 * (200 * S.zeroRadius_BAUGC k / T) < S.rho q.val :=
      lt_of_lt_of_le (mul_lt_mul_of_pos_left hρp (by norm_num)) hρq
    linarith only [h11, hqa, h10, div_pos hRk hT0]
  exact fderiv_block_eq_zero_of_block_zero_BPS (S.circleModelOf_BPC a Ac cc A1 c1 Bτ cτ) _
    (fun w => S.circleModelOf_zero_eq_zero_BPC a Ac cc A1 c1 Bτ cτ hΛ hΛΔ hΔ1 hT0 he k hρa w) _ v

end BoundarySupply

end DifferentialGeometry.Geometry.Collapse

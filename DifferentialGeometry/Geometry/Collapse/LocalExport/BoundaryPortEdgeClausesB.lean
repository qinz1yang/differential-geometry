import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeModelFacts
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeTableA

/-!
# Pointwise marker clauses of the edge stage table on a boundary supply (lane S-PORT-EDGE)

The clauses (SB-int), (PP-int), (FM*-int), (ZB*-int) of `port_edge_interior_table_BAUGP` for ONE
reference `a`, signs / translations `sgn c` and EGP06's model `Φ_a = S.edgeModelOf_BPE a sgn c`, on
the actual slot (`f(q) = π₁F_∂(q)`, `q ∈ W°`, `d_ĝ`). Closed twins:
`EdgeStagePlanes_PLN.small_block_zero`, `…small_pp`, `…full_marker` (`ActualStagePlaneFullMarker`),
`zero_chain_PLN` / `…zero_block` (`ActualStagePlaneZeroBlock`); the cloud-level CFS07 / GAF04 (FD)
inputs are applied to the ACTUAL `f` on `{q : f(q) ∈ S̃₁}` (`edge_scale_ratio_BPE`,
`contributor_dist_lt_fiftieth_of_full_marker`).

* `edge_small_block_BPE` — the whole block of a marker with `ρ(c) ≤ .99ρ(a)` vanishes;
* `edge_pp_point_BPE` — for every preimage `q` of `f(p₀)` (`p₀` in the core of `a`) and every marker
  with `ρ(c) < ρ(q)/5`, the marker of `DΦ_a` vanishes;
* `edge_full_marker_point_BPE` — (FM*): full marker of `i` at `f(q)` and `v_i ∘ DΦ_a(η_a q) = 0`;
* `edge_zero_block_point_BPE` — (ZB*): the zero block of `f(q)` and of `DΦ_a(η_a q)` vanish.
Twin of `BoundaryPortSlimClausesB`.
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

/-- The marker functional of an edge marker chart is its edge marker. -/
theorem markerCLM_edge_BPE (j : S.EdgeIdx_BAUGD) :
    S.markerCLM_BAUGC (.inr (.inr j)) = S.edgeMarker_BAUGD j :=
  rfl

/-- The interior tag of an edge marker chart. -/
theorem markerTag_edge_BPE (j : S.EdgeIdx_BAUGD) :
    S.markerTag_BAUGC (.inr (.inr j)) = .inr (.inr (.inl j)) :=
  rfl

/-- **(SB-int) for EGP06's model**: a marker block with `ρ(c) ≤ .99ρ(a)` vanishes identically. -/
theorem edge_small_block_BPE (hΔ : 0 < Δ) (hΛ : 0 ≤ Λ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    (a : S.EdgeIdx_BAUGD) (sgn c : S.IntTag_BAUGA → ℝ) (m : S.MarkerIdx_BAUGC)
    (hm : S.rho (S.markerCentre_BAUGC m) ≤ 99 / 100 * S.rho a.1) (u : ℝ) :
    S.edgeModelOf_BPE a sgn c u (S.markerTag_BAUGC m) = 0 := by
  rcases m with j | j | j
  · exact S.edgeModelOf_circle_BPE a sgn c j u
  · exact S.edgeModelOf_slim_eq_zero_of_small_BPE a sgn c hΔ hΛ hΛΔ j hm u
  · exact S.edgeModelOf_edge_eq_zero_of_small_BPE a sgn c hΔ hΛ hΛΔ j hm u

/-- **(PP-int) at one core witness** (closed `EdgeStagePlanes_PLN.small_pp`): every preimage `q` of
`f(p₀)`, `p₀` in the threshold-`8` core of `a`, has `ρ(q) ≤ 5ρ(a)/4` (full marker of `a`); a marker
with `ρ(c) < ρ(q)/5` is then small and the marker of `DΦ_a(u)` vanishes. -/
theorem edge_pp_point_BPE (hΔ1 : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) (a : S.EdgeIdx_BAUGD) (sgn c : S.IntTag_BAUGA → ℝ)
    {p₀ q : W.pieceInterior ⊤}
    (hd : letI := inducedMetricSpace S.completion.metric; dist p₀ a.1 < 100 * Δ * S.rho a.1)
    (hη : |S.edgeEta_BIF a.1 p₀| ≤ 8 * Δ) (ht : S.edgeHeightRaw p₀ ≤ 8 * Δ)
    (hq : (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val) =
      (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap p₀.val))
    (m : S.MarkerIdx_BAUGC) (hm : S.rho (S.markerCentre_BAUGC m) < S.rho q / 5) (u v : ℝ) :
    ((fderiv ℝ (S.edgeModelOf_BPE a sgn c) u v) (S.markerTag_BAUGC m)).snd = 0 := by
  have hΔ : 0 < Δ := by linarith only [hΔ1]
  have hra := S.rho_pos a.1
  have hcp := S.edge_cutoff_eq_one_BPE hΔ a hd hη ht
  have hpos : 0 < S.edgeMarker_BAUGD a
      ((actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val)) := by
    rw [hq, S.edgeMarker_stageOne_BPE a p₀, hcp, mul_one]
    exact hra
  have hqa := (S.edge_marker_scale_BPE hΛ hΔ1 hΛΔ hV hβ1 hb a q hpos).2
  have hsmall : S.rho (S.markerCentre_BAUGC m) ≤ 99 / 100 * S.rho a.1 := by
    have h1 : S.rho q.val / 5 ≤ 99 / 100 * S.rho a.1 := by linarith only [hqa, hra]
    exact (hm.trans_le h1).le
  have h0 := S.edge_small_block_BPE hΔ hΛ hΛΔ a sgn c m hsmall
  rw [fderiv_block_eq_zero_of_block_zero_BPS (S.edgeModelOf_BPE a sgn c) _ h0 u v]
  rfl

/-- **(FM*-int) at one window** (closed `EdgeStagePlanes_PLN.full_marker`): for an edge chart `i`
with a threshold-`7` core point `p`, a cloud point `f(q)` (`q` in the threshold-`7` core of the
reference `a`), EGP06's model `Φ_a = S.edgeModelOf_BPE a sgn c` with the (TG) value bound at `q`,
radius preimages `r_y`, `r_x` of `f(q)`, `f(p)` and the contributor window
`B̄(f(q), 80ε⁻¹σρ(r_y)) ∩ B(f(p), 8ε⁻¹σρ(r_x)) ≠ ∅` (`0 ≤ σ ≤ ε/10000`): the edge marker of `i` is
full at `f(q)` and annihilates `DΦ_a(η_a q)`. -/
theorem edge_full_marker_point_BPE (hΔ1 : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) {eg : ℝ}
    (heg0 : 0 ≤ eg) (heg : eg < 1 / 100) {εc σ' : ℝ} (hε : 0 < εc) (hσ : 0 ≤ σ')
    (hσε : σ' ≤ εc / 10000) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    ∀ (i : S.EdgeIdx_BAUGD) {p : W.pieceInterior ⊤}, dist p i.1 < 100 * Δ * S.rho i.1 →
      |S.edgeEta_BIF i.1 p| ≤ 7 * Δ → S.edgeHeightRaw p ≤ 7 * Δ →
      ∀ (a : S.EdgeIdx_BAUGD) (sgn c : S.IntTag_BAUGA → ℝ),
      ∀ {q ry rx : W.pieceInterior ⊤}
        {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)},
      dist q a.1 < 100 * Δ * S.rho a.1 → |S.edgeEta_BIF a.1 q| ≤ 7 * Δ →
      S.edgeHeightRaw q ≤ 7 * Δ →
      (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val) = y →
      (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap ry.val) = y →
      (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap rx.val) =
        (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap p.val) →
      (closedBall y (80 * εc⁻¹ * (σ' * S.rho ry)) ∩
        ball ((actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap p.val))
          (8 * εc⁻¹ * (σ' * S.rho rx))).Nonempty →
      ‖(S.rho a.1)⁻¹ • blockRestrict (S.stageTagsV2_BAUGD 1) (S.interiorMapOn_BAUGA q) -
          S.edgeModelOf_BPE a sgn c (S.edgeEta_BIF a.1 q)‖ < eg →
      S.markerCLM_BAUGC (.inr (.inr i)) y = S.rho i.1 ∧
        ∀ v : ℝ, ((fderiv ℝ (S.edgeModelOf_BPE a sgn c) (S.edgeEta_BIF a.1 q) v)
          (S.markerTag_BAUGC (.inr (.inr i)))).snd = 0 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  intro i p hpd hpη hpt a sgn c q ry rx y hqd hqη hqt hqy hry hrx hmeet hTG
  subst hqy
  have hΔ : 0 < Δ := by linarith only [hΔ1]
  have hri := S.rho_pos i.1
  have hra := S.rho_pos a.1
  have hcp := S.edge_cutoff_eq_one_BPE hΔ i hpd (by linarith only [hpη, hΔ])
    (by linarith only [hpt, hΔ])
  have hp8 := S.stageProj_mem_stageCloudEnlarged_one_BPE i hpd (by linarith only [hpη, hΔ])
    (by linarith only [hpt, hΔ])
  have hq8 := S.stageProj_mem_stageCloudEnlarged_one_BPE a hqd (by linarith only [hqη, hΔ])
    (by linarith only [hqt, hΔ])
  -- (FD): the contributor is within `ρ_i/50`
  have hFD : dist ((actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val))
      ((actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap p.val)) < S.rho i.1 / 50 := by
    have h := contributor_dist_lt_fiftieth_of_full_marker
      (P := {z : W.pieceInterior ⊤ // (actualSlotsV2_BAUGD S).stageProj 1
        (S.boundaryOriginalMap z.val) ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 1})
      (fun z => (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap z.1.val))
      (fun z => S.rho z.1.val) (fun j : S.EdgeIdx_BAUGD => S.edgeMarker_BAUGD j)
      (fun j : S.EdgeIdx_BAUGD => S.rho j.1) (fun j => S.rho_pos j.1)
      (fun j => S.lipschitzWith_edgeMarker_BPE j) (fun z => S.edge_full_marker_BPE hΔ z.2)
      (fun j z h => S.edge_marker_scale_BPE hΛ hΔ1 hΛΔ hV hβ1 hb j z.1 h) hε hσ hσε
      ⟨rx, by rw [hrx]; exact hp8⟩ ⟨ry, by rw [hry]; exact hq8⟩ i
      (by
        change S.edgeMarker_BAUGD i ((actualSlotsV2_BAUGD S).stageProj 1
          (S.boundaryOriginalMap rx.val)) = S.rho i.1
        rw [hrx, S.edgeMarker_stageOne_BPE i p, hcp, mul_one])
      (by
        obtain ⟨z, hz1, hz2⟩ := hmeet
        refine ⟨z, ?_, ?_⟩
        · change z ∈ closedBall ((actualSlotsV2_BAUGD S).stageProj 1
            (S.boundaryOriginalMap ry.val)) (80 * εc⁻¹ * (σ' * S.rho ry.val))
          rw [hry]
          exact hz1
        · change z ∈ ball ((actualSlotsV2_BAUGD S).stageProj 1
            (S.boundaryOriginalMap rx.val)) (8 * εc⁻¹ * (σ' * S.rho rx.val))
          rw [hrx]
          exact hz2)
    beta_reduce at h
    rw [hry, hrx] at h
    exact h
  -- the `i`-block of `f(q)` is near the full block of `f(p)`
  have hxb : (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap p.val)
      (Sum.inl (.inr (.inr (.inl i)))) =
      WithLp.toLp 2 ((S.rho i.1 * 1) • planeAxis (S.edgeEta_BIF i.1 p), S.rho i.1 * 1) := by
    rw [S.edgeBlock_stageOne_BPE i p, hcp]
  have hblk := dist_block_lt_of_eq_BPS (S.edgeBlock_stageOne_BPE i q) hxb hFD
  have hfv := fv_of_block_dist_GAF hri hΔ1 (by rw [norm_planeAxis]; linarith only [hpη]) hblk
  have hζ := hfv.1
  have hv := hfv.2
  rw [norm_planeAxis] at hv
  have hcq0 : S.family.edgeB.cutoff_BAUGA i.1 q ≠ 0 := by
    intro h
    rw [h] at hζ
    norm_num at hζ
  have hqi := S.edge_dist_lt_of_cutoff_ne_zero_BPE hΔ i hcq0
  have hcq := S.edge_cutoff_eq_one_BPE hΔ i hqi (by linarith only [hv, hΔ])
    (by linarith only [hqt, hΔ])
  refine ⟨?_, fun v => ?_⟩
  · rw [S.markerCLM_edge_BPE i, S.edgeMarker_stageOne_BPE i q, hcq, mul_one]
  -- the plateau of the model block
  have hC : Λ * (100 * Δ) ≤ 1 / 200 := by linarith only [hΛΔ]
  have hratio := ratio_ge_of_common_point_PLN (ρ := fun x : W.pieceInterior ⊤ => S.rho x)
    S.family.lipschitz_scale hΛ hra hri hqd hqi hC hC
  have hs : 99 / 100 ≤ S.rho i.1 / S.rho a.1 := by rw [le_div_iff₀ hra]; exact hratio
  rw [S.markerTag_edge_BPE i]
  by_cases hia : i = a
  · subst hia
    have hc : ∀ w, (S.edgeModelOf_BPE i sgn c w (.inr (.inr (.inl i)))).snd = 1 := fun w => by
      rw [S.edgeModelOf_own_BPE]
      rfl
    exact snd_fderiv_eq_zero_of_const_BPS (S.edgeModelOf_BPE i sgn c) _ 1 hc _ v
  · have hne : i.1 ≠ a.1 := fun h => hia (Subtype.ext h)
    by_cases hS : i.1 ∈ egpEdgeList_BAUGP S.family.toLocalPacketsOnB a.1
    · exact marker_fderiv_of_close_edge_BPE
        ((S.contDiff_edgeModelOf_BPE a sgn c).differentiable (by simp)) (.inr (.inr (.inl i)))
        hra hri heg0 heg hs (by linarith only [hv]) hΔ1 hTG
        (S.interiorMapOn_edge_block_BPE i hcq)
        (fun w => S.edgeModelOf_edge_listed_BPE a sgn c i hne hS w) v
    · have hc : ∀ w, (S.edgeModelOf_BPE a sgn c w (.inr (.inr (.inl i)))).snd = 0 := fun w => by
        rw [S.edgeModelOf_edge_unlisted_BPE a sgn c i hne hS w]
        rfl
      exact snd_fderiv_eq_zero_of_const_BPS (S.edgeModelOf_BPE a sgn c) _ 0 hc _ v

/-- A kept interior block of `f(q) = π₁F_∂(q)` is the interior formula: `f(q)_t = F_int(q)_t` for
`t ∈ Q₂`. -/
theorem stageOne_inl_of_mem_BPE (q : W.pieceInterior ⊤) {t : S.IntTag_BAUGA}
    (ht : t ∈ S.stageTagsV2_BAUGD 1) :
    (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val) (Sum.inl t) =
      S.interiorMapOn_BAUGA q t := by
  simp only [BoundaryInteriorSlots_BIF.stageProj, BoundaryInteriorSlots_BIF.stageTagsAug,
    blockRestrict_apply, Finset.inl_mem_disjSum, actualSlotsV2_stageTags_BAUGD, ht, ite_true]
  exact S.boundaryOriginalMap_inl_BPS q t

/-- The zero block of `f(q)` is the zero block of the interior formula. -/
theorem zeroBlockCLM_stageOne_BPE (k : S.ZeroIdx_BAUGC) (q : W.pieceInterior ⊤) :
    S.zeroBlockCLM_BAUGC k ((actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val)) =
      S.interiorMapOn_BAUGA q (S.zeroTag_BAUGC k) := by
  rw [BoundarySupplyCore.zeroBlockCLM_BAUGC, blockProjCLM_apply_PLN]
  exact S.stageOne_inl_of_mem_BPE q (BoundarySupplyCore.mem_stageTagsV2_one_BAUGD.mpr rfl)

/-- **No zero support meets a large edge reference** (closed `zero_meet_absurd_PLN`): if
`ρ(a) > (80/3)R_k/T`, the zero support of `k` misses `D_a = B(a, 20Δρ(a))`. -/
theorem not_zeroMeets_edge_BPE (hΛ : 0 ≤ Λ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    (hT : 0 < T) (he : e < 1 / 40) (a : S.EdgeIdx_BAUGD) (k : S.ZeroIdx_BAUGC)
    (hρa : 80 / 3 * (S.zeroRadius_BAUGC k / T) < S.rho a.1) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    k.1 ∉ zeroMeetingList_BPE S.family.zero a.1 (20 * Δ) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  rintro ⟨hk, z, hz, hza⟩
  have h1 := zero_cutoff_ratio_BPS S.family.toLocalPacketsOnBFR.toLocalPacketsOnBF hT he hk hz
  have hk4 : Λ * (20 * Δ) ≤ 1 / 4 := by linarith only [hΛΔ]
  have h2 := (scale_mem_of_dist_lt_KC (ρ := fun x : W.pieceInterior ⊤ => S.rho x)
    S.family.lipschitz_scale hΛ (S.rho_pos a.1) (mem_ball.mp hza) hk4).1
  have h3 : 20 * (S.family.zero.zero k.1 hk).radius / T =
      20 * (S.zeroRadius_BAUGC k / T) := by
    change 20 * (S.family.zero.zero k.1 hk).radius / T =
      20 * ((S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / T)
    ring
  change S.rho z.val ≤ 20 * (S.family.zero.zero k.1 hk).radius / T at h1
  change 3 / 4 * S.rho a.1 ≤ S.rho z.val at h2
  linarith only [h1, h2, h3, hρa]

/-- **(ZB*-int) at one window** (closed `zero_chain_PLN` + `EdgeStagePlanes_PLN.zero_block`): for a
zero centre `k`, a preimage `p` of a point of `S₁` with `ρ(p) > 200R_k/T`, a cloud point `f(q)`
(`q` in the threshold-`7` core of the reference `a`), radius preimages `r_y`, `r_x` of `f(q)`,
`f(p)` and the contributor window (`σ ≤ ε/10000`): the zero block of `f(q)` and of `DΦ_a(η_a q)`
vanish. -/
theorem edge_zero_block_point_BPE (hΔ1 : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b)
    (hT : 1600 * (1000000 * Δ) ≤ T) (he : e < 1 / 40) {εc σ' : ℝ} (hε : 0 < εc)
    (hσε : σ' ≤ εc / 10000) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    ∀ (k : S.ZeroIdx_BAUGC) {p : W.pieceInterior ⊤},
      (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap p.val) ∈
        (actualSlotsV2_BAUGD S).stageCloud 1 →
      200 * S.zeroRadius_BAUGC k / T < S.rho p →
      ∀ (a : S.EdgeIdx_BAUGD) (sgn c : S.IntTag_BAUGA → ℝ),
      ∀ {q ry rx : W.pieceInterior ⊤}
        {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)},
      dist q a.1 < 100 * Δ * S.rho a.1 → |S.edgeEta_BIF a.1 q| ≤ 7 * Δ →
      S.edgeHeightRaw q ≤ 7 * Δ →
      (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val) = y →
      (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap ry.val) = y →
      (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap rx.val) =
        (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap p.val) →
      (closedBall y (80 * εc⁻¹ * (σ' * S.rho ry)) ∩
        ball ((actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap p.val))
          (8 * εc⁻¹ * (σ' * S.rho rx))).Nonempty →
      S.zeroBlockCLM_BAUGC k y = 0 ∧
        ∀ v : ℝ, (fderiv ℝ (S.edgeModelOf_BPE a sgn c) (S.edgeEta_BIF a.1 q) v)
          (S.zeroTag_BAUGC k) = 0 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  intro k p hp hρp a sgn c q ry rx y hqd hqη hqt hqy hry hrx hmeet
  subst hqy
  have hΔ : 0 < Δ := by linarith only [hΔ1]
  have hT0 : 0 < T := by linarith only [hT, hΔ]
  have hR := (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  have hRk : 0 < S.zeroRadius_BAUGC k := hR
  have hra := S.rho_pos a.1
  have hp8 : (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap p.val) ∈
      (actualSlotsV2_BAUGD S).stageCloudEnlarged 1 :=
    actualSlotsV2_stageCloud_subset_BAUGD S hΔ.le 1 hp
  have hq8 := S.stageProj_mem_stageCloudEnlarged_one_BPE a hqd (by linarith only [hqη, hΔ])
    (by linarith only [hqt, hΔ])
  have hrx8 : (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap rx.val) ∈
      (actualSlotsV2_BAUGD S).stageCloudEnlarged 1 := by rw [hrx]; exact hp8
  have hry8 : (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap ry.val) ∈
      (actualSlotsV2_BAUGD S).stageCloudEnlarged 1 := by rw [hry]; exact hq8
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
    linarith only [dist_nonneg (x := z) (y := (actualSlotsV2_BAUGD S).stageProj 1
      (S.boundaryOriginalMap p.val)), h2, h4]
  have hd : dist ((actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap ry.val))
      ((actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap rx.val)) ≤
      88 * εc⁻¹ * max (σ' * S.rho ry.val) (σ' * S.rho rx.val) := by
    rw [hry, hrx]
    have h3 := dist_triangle_left ((actualSlotsV2_BAUGD S).stageProj 1
      (S.boundaryOriginalMap q.val)) ((actualSlotsV2_BAUGD S).stageProj 1
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
  have hm := (S.edge_scale_ratio_BPE hΛ hΔ1 hΛΔ hV hβ1 hb hσ.le (by positivity) hLs hrx8 hry8
    hd).1
  have hpr1 := (S.edge_scale_ratio_BPE hΛ hΔ1 hΛΔ hV hβ1 hb (σ := 0) (L' := 0) le_rfl le_rfl
    (by norm_num) hp8 hrx8 (by rw [hrx, dist_self]; simp)).1
  have hpr2 := (S.edge_scale_ratio_BPE hΛ hΔ1 hΛΔ hV hβ1 hb (σ := 0) (L' := 0) le_rfl le_rfl
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
  · rw [S.zeroBlockCLM_stageOne_BPE k q]
    exact S.interiorMapOn_zero_eq_zero_BPS hT0 he k hρq20
  -- the zero support misses `D_a`: the model's zero block vanishes
  have hqa := (scale_mem_of_dist_lt_KC (ρ := fun x : W.pieceInterior ⊤ => S.rho x)
    S.family.lipschitz_scale hΛ hra hqd (by linarith only [hΛΔ])).2
  change S.rho q.val ≤ 5 / 4 * S.rho a.1 at hqa
  have hρa : 80 / 3 * (S.zeroRadius_BAUGC k / T) < S.rho a.1 := by
    have h10 : 200 * S.zeroRadius_BAUGC k / T = 200 * (S.zeroRadius_BAUGC k / T) := by ring
    have h11 : 27 / 125 * (200 * S.zeroRadius_BAUGC k / T) < S.rho q.val :=
      lt_of_lt_of_le (mul_lt_mul_of_pos_left hρp (by norm_num)) hρq
    linarith only [h11, hqa, h10, div_pos hRk hT0]
  have habs := S.not_zeroMeets_edge_BPE hΛ hΛΔ hT0 he a k hρa
  refine fderiv_block_eq_zero_of_block_zero_BPS (S.edgeModelOf_BPE a sgn c) _ (fun w => ?_) _ v
  exact S.edgeModelOf_zero_eq_zero_BPE a sgn c k habs w

end BoundarySupply

end DifferentialGeometry.Geometry.Collapse

import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSlimClauses

/-!
# Pointwise marker clauses of the slim stage table on a boundary supply (lane B-PORT-SLIMb)

The clauses (SB-int), (PP-int), (FM*-int), (ZB*-int) of `port_slim_interior_table_BAUGP` for ONE
reference `a`, signs / translations `sgn c zsgn zc` and SGP04's full model
`Φ_a = sgpFullGraph_BAUGP S.family.toLocalPacketsOnB S.family.zero a sgn c zsgn zc`, on the actual slot
(`f(q) = π₂F_∂(q)`, `q ∈ W°`, `d_ĝ`). Closed twins: `SlimStagePlanes_PLN.small_block_zero`,
`slim_pp_point_GAF4`, `SlimStagePlanes_PLN.pre_plateau_PLN` / `.full_marker`, `zero_chain_PLN` /
`SlimStagePlanes_PLN.zero_block`; the cloud-level CFS07 / GAF04 (FD) inputs are applied to the ACTUAL
`f` on `{q : f(q) ∈ S̃₂}` (`slim_scale_ratio_BPS`, `contributor_dist_lt_fiftieth_of_full_marker`).

* `slim_small_block_BPS` — the whole block of a marker with `ρ(c) ≤ .99ρ(a)` vanishes;
* `slim_pp_point_BPS` — for every preimage `q` of `f(p₀)` (`p₀` in the core of `a`) and every marker
  with `ρ(c) < ρ(q)/5`, the marker of `DΦ_a` vanishes;
* `slim_full_marker_point_BPS` — (FM*): full marker of `i` at `f(q)` and `v_i ∘ DΦ_a(η_a q) = 0`;
* `slim_zero_block_point_BPS` — (ZB*): the zero block of `f(q)` and of `DΦ_a(η_a q)` vanish.
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

section Generic

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A single block is controlled by the distance, in distance form: `d(y_t, x_t) ≤ d(y, x)`. -/
theorem dist_inl_le_BPS (y x : BlockSpace (fun _ : ι ⊕ κ => ℝ²)) (t : ι) :
    dist (y (Sum.inl t)) (x (Sum.inl t)) ≤ dist y x := by
  rw [dist_eq_norm, dist_eq_norm]
  exact norm_inl_sub_le_BPS y x t

/-- Numerics: `d ≤ .91·10⁶Δr ⟹ d < 10⁶Δr`. -/
theorem lt_of_le_support_BPS {d Δ r : ℝ} (hΔ : 0 < Δ) (hr : 0 < r) (h : d ≤ 910000 * Δ * r) :
    d < 1000000 * Δ * r := by
  nlinarith [mul_pos hΔ hr]

/-- The distance of two blocks with known values is controlled by the distance. -/
theorem dist_block_lt_of_eq_BPS {y x : BlockSpace (fun _ : ι ⊕ κ => ℝ²)} {t : ι}
    {u v : WithLp 2 (ℝ² × ℝ)} (hy : y (Sum.inl t) = u) (hx : x (Sum.inl t) = v) {r : ℝ}
    (h : dist y x < r) : dist u v < r := by
  rw [← hy, ← hx]
  exact (dist_inl_le_BPS y x t).trans_lt h

end Generic

section GenericModel

variable {τ : Type*} [Fintype τ]

omit [Fintype τ] in
/-- A marker component that is constant along the model has vanishing derivative, in `.snd` form. -/
theorem snd_fderiv_eq_zero_of_const_BPS [Finite τ] (Φ : ℝ → BlockSpace (fun _ : τ => ℝ²)) (t : τ) (c : ℝ)
    (hc : ∀ u, (Φ u t).snd = c) (u v : ℝ) : ((fderiv ℝ Φ u v) t).snd = 0 :=
  blockMarkerCLM_fderiv_eq_zero_of_const_GAF4 Φ t c hc u v

/-- **The plateau step of (FM\*)**, for ANY finite tag type and ANY model `Φ` (closed
`SlimStagePlanes_PLN.full_marker`, last step): if `‖r_a⁻¹y − Φ(u)‖ < e` (`e < 1/100`), the `t`-block of
`y` is the full block `(r_i·1 η, r_i·1)` with `|η| ≤ (351/49)ℓ`, `r_i/r_a ≥ 99/100`, and the `t`-block of
`Φ` is SGP04's listed block `sgpBlockEmbed (sgpModelBlock ℓ (r_i/r_a) (σw + c))`, then the marker of `t`
annihilates `DΦ(u)`. -/
theorem marker_fderiv_of_close_BPS {Φ : ℝ → BlockSpace (fun _ : τ => ℝ²)}
    (hΦ : Differentiable ℝ Φ) (t : τ) {y : BlockSpace (fun _ : τ => ℝ²)}
    {u η eg ra ri ℓ sg cc : ℝ} (hra : 0 < ra) (hri : 0 < ri) (heg0 : 0 ≤ eg) (heg : eg < 1 / 100)
    (hs : 99 / 100 ≤ ri / ra) (hη : |η| ≤ 351 / 49 * ℓ) (hℓ : 1 ≤ ℓ) (hTG : ‖ra⁻¹ • y - Φ u‖ < eg)
    (hy : y t = WithLp.toLp 2 ((ri * 1) • planeAxis η, ri * 1))
    (hmt : ∀ w, Φ w t = sgpBlockEmbed (sgpModelBlock ℓ (ri / ra) (sg * w + cc))) (v : ℝ) :
    ((fderiv ℝ Φ u v) t).snd = 0 := by
  have hnum := plateau_numbers_PLN hℓ (s := ri / ra) hs heg0 heg
  have hcl := embed_block_close_PLN t hTG hy (hmt u)
  have harg := scaledCutoffBlock_arg_lt_of_close_PLN (div_pos hri hra) hnum.1
    (by rw [Real.norm_eq_abs]; exact hη) hcl hnum.2
  have hℓ0 : 0 < ℓ := by linarith
  have hev := scaledCutoffBlock_snd_eventually_GAFS (s := ri / ra) (r := 8 * ℓ) (φ := sgpProfile ℓ)
    (fun z hz => sgpProfile_eq_one hℓ0 (by rwa [Real.norm_eq_abs] at hz))
    (u := fun w => sg * w + cc)
    ((continuous_const.mul continuous_id).add continuous_const).continuousAt harg
  have hloc : (fun w => (Φ w t).snd) =ᶠ[𝓝 u] fun _ => ri / ra := by
    filter_upwards [hev] with w hw
    rw [hmt w]
    exact hw
  exact blockMarkerCLM_fderiv_eq_zero_GAFS t (hΦ u) hloc v

end GenericModel

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundarySupply

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
  θ W g δn n B oM)

/-- **(SB-int) for SGP04's model** (CGP04), for a model `Φ` on the interior tags with SGP04's blocks
(circle and `edgeB` blocks zero, slim blocks `sgpSlimModelBlock_BAUGP`): a marker block with
`ρ(c) ≤ .99ρ(a)` vanishes identically. -/
theorem slim_small_block_BPS (hΔ : 0 < Δ) (hΛ : 0 ≤ Λ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    ∀ (a : S.SlimIdx_BAUGD) (sgn c : W.pieceInterior ⊤ → ℝ)
      (Φ : ℝ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²)),
      (∀ j w, Φ w (.inl j) = 0) → (∀ j w, Φ w (.inr (.inr (.inl j))) = 0) →
      (∀ j w, Φ w (.inr (.inl j)) = sgpSlimModelBlock_BAUGP S.family.toLocalPacketsOnB a sgn c j w) →
      ∀ m : S.MarkerIdx_BAUGC, S.rho (S.markerCentre_BAUGC m) ≤ 99 / 100 * S.rho a.1 → ∀ u : ℝ,
        Φ u (S.markerTag_BAUGC m) = 0 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  intro a sgn c Φ hcirc hedge hslim m hm u
  rcases m with j | j | j
  · exact hcirc j u
  · change Φ u (.inr (.inl j)) = 0
    rw [hslim j u]
    exact sgpSlimModelBlock_eq_zero_of_small_BPS S.family.toLocalPacketsOnB hΔ hΛ hΛΔ a sgn c j hm u
  · exact hedge j u

/-- **(PP-int) at one core witness** (closed `slim_pp_point_GAF4`): every preimage `q` of `f(p₀)`,
`p₀` in the threshold-`8` core of `a`, has `ρ(q) ≤ 5ρ(a)/4` (full marker of `a`); a marker with
`ρ(c) < ρ(q)/5` is then small and the marker of `DΦ(u)` vanishes (`Φ` with SGP04's blocks). -/
theorem slim_pp_point_BPS (hΔ1 : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    ∀ (a : S.SlimIdx_BAUGD) (sgn c : W.pieceInterior ⊤ → ℝ)
      (Φ : ℝ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²)),
      (∀ j w, Φ w (.inl j) = 0) → (∀ j w, Φ w (.inr (.inr (.inl j))) = 0) →
      (∀ j w, Φ w (.inr (.inl j)) = sgpSlimModelBlock_BAUGP S.family.toLocalPacketsOnB a sgn c j w) →
      ∀ {p₀ q : W.pieceInterior ⊤},
      dist p₀ a.1 < 1000000 * Δ * S.rho a.1 → |S.slimEta_BIF a.1 p₀| ≤ 8 * (100000 * Δ) →
      (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val) =
        (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap p₀.val) →
      ∀ m : S.MarkerIdx_BAUGC, S.rho (S.markerCentre_BAUGC m) < S.rho q / 5 → ∀ u v : ℝ,
        ((fderiv ℝ Φ u v) (S.markerTag_BAUGC m)).snd = 0 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  intro a sgn c Φ hcirc hedge hslim p₀ q hd hη hq m hm u v
  have hΔ : 0 < Δ := by linarith only [hΔ1]
  have hra := S.rho_pos a.1
  have hcp := S.slim_cutoff_eq_one_BPS a hd hη
  have hpos : 0 < S.slimMarker_BAUGD a
      ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val)) := by
    rw [hq, S.slimMarker_stageTwo_BPS a p₀, hcp, mul_one]
    exact hra
  have hqa := (S.slim_marker_scale_BPS hΛ hΔ1 hΛΔ hV hβ1 hb a q hpos).2
  have hsmall : S.rho (S.markerCentre_BAUGC m) ≤ 99 / 100 * S.rho a.1 := by
    have h1 : S.rho q.val / 5 ≤ 99 / 100 * S.rho a.1 := by linarith only [hqa, hra]
    exact (hm.trans_le h1).le
  have h0 := S.slim_small_block_BPS hΔ hΛ hΛΔ a sgn c Φ hcirc hedge hslim m hsmall
  rw [fderiv_block_eq_zero_of_block_zero_BPS Φ _ h0 u v]
  rfl

/-- The marker functional of a slim marker chart is its slim marker. -/
theorem markerCLM_slim_BPS (j : S.SlimIdx_BAUGD) :
    S.markerCLM_BAUGC (.inr (.inl j)) = S.slimMarker_BAUGD j :=
  rfl

/-- The interior tag of a slim marker chart. -/
theorem markerTag_slim_BPS (j : S.SlimIdx_BAUGD) :
    S.markerTag_BAUGC (.inr (.inl j)) = .inr (.inl j) :=
  rfl

/-- The full slim block of the interior formula: `F_int(q)_i = (ρ_i·1 η_i(q), ρ_i·1)` where `ζ_i(q) = 1`. -/
theorem interiorMapOn_slim_block_BPS (i : S.SlimIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.slim.cutoff_BCNT i.1 q) = 1) :
    blockRestrict (S.stageTagsV2_BAUGD 2) (S.interiorMapOn_BAUGA q) (.inr (.inl i)) =
      WithLp.toLp 2 ((S.rho i.1 * 1) • planeAxis (S.slimEta_BIF i.1 q), S.rho i.1 * 1) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  rw [blockRestrict_apply, ite_eq_left (S.slimTag_mem_stageTagsV2_BAUGD 2 i), ← hq,
    S.slimEta_eq_coord_BAUGP2]
  rfl

/-- **(FM*-int) at one window** (closed `SlimStagePlanes_PLN.pre_plateau_PLN` + `.full_marker`): for a
slim chart `i` with a threshold-`7` core point `p`, a cloud point `f(q)` (`q` in the threshold-`7` core of
the reference `a`), a model `Φ` on the interior tags with SGP04's slim block at `i` and the (SG) value
bound at `q`, radius preimages `r_y`, `r_x` of `f(q)`, `f(p)` and the contributor window
`B̄(f(q), 80ε⁻¹σρ(r_y)) ∩ B(f(p), 8ε⁻¹σρ(r_x)) ≠ ∅` (`0 ≤ σ ≤ ε/10000`): the slim marker of `i` is full
at `f(q)` and annihilates `DΦ(η_a q)`. -/
theorem slim_full_marker_point_BPS (hΔ1 : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) {eg : ℝ}
    (heg0 : 0 ≤ eg) (heg : eg < 1 / 100) {εc σ' : ℝ} (hε : 0 < εc) (hσ : 0 ≤ σ')
    (hσε : σ' ≤ εc / 10000) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    ∀ (i : S.SlimIdx_BAUGD) {p : W.pieceInterior ⊤}, dist p i.1 < 1000000 * Δ * S.rho i.1 →
      |S.slimEta_BIF i.1 p| ≤ 7 * (100000 * Δ) →
      ∀ (a : S.SlimIdx_BAUGD) (sgn c : W.pieceInterior ⊤ → ℝ)
        (Φ : ℝ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²)), Differentiable ℝ Φ →
      (∀ w, Φ w (.inr (.inl i)) = sgpSlimModelBlock_BAUGP S.family.toLocalPacketsOnB a sgn c i w) →
      ∀ {q ry rx : W.pieceInterior ⊤} {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)},
      dist q a.1 < 1000000 * Δ * S.rho a.1 → |S.slimEta_BIF a.1 q| ≤ 7 * (100000 * Δ) →
      (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val) = y →
      (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap ry.val) = y →
      (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap rx.val) =
        (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap p.val) →
      (closedBall y (80 * εc⁻¹ * (σ' * S.rho ry)) ∩
        ball ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap p.val))
          (8 * εc⁻¹ * (σ' * S.rho rx))).Nonempty →
      ‖(S.rho a.1)⁻¹ • blockRestrict (S.stageTagsV2_BAUGD 2) (S.interiorMapOn_BAUGA q) -
          Φ (S.slimEta_BIF a.1 q)‖ < eg →
      S.markerCLM_BAUGC (.inr (.inl i)) y = S.rho i.1 ∧
        ∀ v : ℝ, ((fderiv ℝ Φ (S.slimEta_BIF a.1 q) v) (S.markerTag_BAUGC (.inr (.inl i)))).snd = 0 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  intro i p hpd hpη a sgn c Φ hΦd hslim q ry rx y hqd hqη hqy hry hrx hmeet hTG
  subst hqy
  have hΔ : 0 < Δ := by linarith
  have hri := S.rho_pos i.1
  have hra := S.rho_pos a.1
  have hℓ : (1 : ℝ) ≤ 100000 * Δ := by linarith only [hΔ1]
  have hcp := S.slim_cutoff_eq_one_BPS i hpd (by linarith only [hpη, hΔ])
  have hp8 := S.stageProj_mem_stageCloudEnlarged_two_BPS i hpd (by linarith only [hpη, hΔ])
  have hq8 := S.stageProj_mem_stageCloudEnlarged_two_BPS a hqd (by linarith only [hqη, hΔ])
  -- (FD): the contributor is within `ρ_i/50`
  have hFD : dist ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val))
      ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap p.val)) < S.rho i.1 / 50 := by
    have h := contributor_dist_lt_fiftieth_of_full_marker
      (P := {z : W.pieceInterior ⊤ // (actualSlotsV2_BAUGD S).stageProj 2
        (S.boundaryOriginalMap z.val) ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 2})
      (fun z => (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap z.1.val))
      (fun z => S.rho z.1.val) (fun j : S.SlimIdx_BAUGD => S.slimMarker_BAUGD j)
      (fun j : S.SlimIdx_BAUGD => S.rho j.1) (fun j => S.rho_pos j.1)
      (fun j => S.lipschitzWith_slimMarker_BPS j) (fun z => S.slim_full_marker_BPS z.2)
      (fun j z h => S.slim_marker_scale_BPS hΛ hΔ1 hΛΔ hV hβ1 hb j z.1 h) hε hσ hσε
      ⟨rx, by rw [hrx]; exact hp8⟩ ⟨ry, by rw [hry]; exact hq8⟩ i
      (by
        change S.slimMarker_BAUGD i ((actualSlotsV2_BAUGD S).stageProj 2
          (S.boundaryOriginalMap rx.val)) = S.rho i.1
        rw [hrx, S.slimMarker_stageTwo_BPS i p, hcp, mul_one])
      (by
        obtain ⟨z, hz1, hz2⟩ := hmeet
        refine ⟨z, ?_, ?_⟩
        · change z ∈ closedBall ((actualSlotsV2_BAUGD S).stageProj 2
            (S.boundaryOriginalMap ry.val)) (80 * εc⁻¹ * (σ' * S.rho ry.val))
          rw [hry]
          exact hz1
        · change z ∈ ball ((actualSlotsV2_BAUGD S).stageProj 2
            (S.boundaryOriginalMap rx.val)) (8 * εc⁻¹ * (σ' * S.rho rx.val))
          rw [hrx]
          exact hz2)
    beta_reduce at h
    rw [hry, hrx] at h
    exact h
  -- the `i`-block of `f(q)` is near the full block of `f(p)`
  have hxb : (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap p.val)
      (Sum.inl (.inr (.inl i))) =
      WithLp.toLp 2 ((S.rho i.1 * 1) • planeAxis (S.slimEta_BIF i.1 p), S.rho i.1 * 1) := by
    rw [S.slimBlock_stageTwo_BPS i p, hcp]
  have hblk := dist_block_lt_of_eq_BPS (S.slimBlock_stageTwo_BPS i q) hxb hFD
  have hfv := fv_of_block_dist_GAF hri hℓ (by rw [norm_planeAxis]; exact hpη) hblk
  have hζ := hfv.1
  have hv := hfv.2
  rw [norm_planeAxis] at hv
  have hcq0 : S.family.slim.cutoff_BCNT i.1 q ≠ 0 := by
    intro h
    rw [h] at hζ
    norm_num at hζ
  have hdq := S.slim_dist_le_of_cutoff_ne_zero_BPS i hcq0
  have hqi : dist q i.1 < 1000000 * Δ * S.rho i.1 := lt_of_le_support_BPS hΔ hri hdq
  have hcq := S.slim_cutoff_eq_one_BPS i hqi (by linarith only [hv, hΔ])
  refine ⟨?_, fun v => ?_⟩
  · rw [S.markerCLM_slim_BPS i, S.slimMarker_stageTwo_BPS i q, hcq, mul_one]
  -- the plateau of the model block
  have hC : Λ * (1000000 * Δ) ≤ 1 / 200 := by linarith only [hΛΔ]
  have hratio := ratio_ge_of_common_point_PLN (ρ := fun x : W.pieceInterior ⊤ => S.rho x)
    S.family.lipschitz_scale hΛ hra hri hqd hqi hC hC
  have hs : 99 / 100 ≤ S.rho i.1 / S.rho a.1 := by rw [le_div_iff₀ hra]; exact hratio
  by_cases hia : i = a
  · have hc : ∀ w, (Φ w (.inr (.inl i))).snd = 1 := fun w => by
      rw [hslim w]
      simp only [sgpSlimModelBlock_BAUGP, hia, ite_true]
      rfl
    exact snd_fderiv_eq_zero_of_const_BPS Φ _ 1 hc _ v
  · by_cases hS : i.1 ∈ sgpSlimList_BAUGP S.family.slim a.1
    · have hmt : ∀ w, Φ w (.inr (.inl i)) = sgpBlockEmbed (sgpModelBlock (10 ^ 5 * Δ)
          (S.rho i.1 / S.rho a.1) (sgn i.1 * w + c i.1)) := fun w => by
        rw [hslim w]
        simp only [sgpSlimModelBlock_BAUGP, hia, hS, ite_true, ite_false]
      exact marker_fderiv_of_close_BPS hΦd (.inr (.inl i)) hra hri heg0 heg hs
        (by linarith only [hv]) (by linarith only [hΔ1]) hTG (S.interiorMapOn_slim_block_BPS i hcq)
        hmt v
    · have hc : ∀ w, (Φ w (.inr (.inl i))).snd = 0 := fun w => by
        rw [hslim w]
        simp only [sgpSlimModelBlock_BAUGP, hia, hS, ite_false]
        rfl
      exact snd_fderiv_eq_zero_of_const_BPS Φ _ 0 hc _ v

/-- A kept interior block of `f(q)` is the interior formula: `f(q)_t = F_int(q)_t` for `t ∈ Q₃`. -/
theorem stageTwo_inl_of_mem_BPS (q : W.pieceInterior ⊤) {t : S.IntTag_BAUGA}
    (ht : t ∈ S.stageTagsV2_BAUGD 2) :
    (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val) (Sum.inl t) =
      S.interiorMapOn_BAUGA q t := by
  simp only [BoundaryInteriorSlots_BIF.stageProj, BoundaryInteriorSlots_BIF.stageTagsAug,
    blockRestrict_apply, Finset.inl_mem_disjSum, actualSlotsV2_stageTags_BAUGD, ht, ite_true]
  exact S.boundaryOriginalMap_inl_BPS q t

/-- The zero block of `f(q)` is the zero block of the interior formula. -/
theorem zeroBlockCLM_stageTwo_BPS (k : S.ZeroIdx_BAUGC) (q : W.pieceInterior ⊤) :
    S.zeroBlockCLM_BAUGC k ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val)) =
      S.interiorMapOn_BAUGA q (S.zeroTag_BAUGC k) := by
  rw [BoundarySupplyCore.zeroBlockCLM_BAUGC, blockProjCLM_apply_PLN]
  exact S.stageTwo_inl_of_mem_BPS q (BoundarySupplyCore.mem_stageTagsV2_two_BAUGD.mpr rfl)

/-- **ZSP01 on `W°`**: `20R_k/T < ρ(q)` kills the whole zero block of the interior formula. -/
theorem interiorMapOn_zero_eq_zero_BPS (hT : 0 < T) (he : e < 1 / 40) (k : S.ZeroIdx_BAUGC)
    {q : W.pieceInterior ⊤} (hρq : 20 * S.zeroRadius_BAUGC k / T < S.rho q.val) :
    S.interiorMapOn_BAUGA q (S.zeroTag_BAUGC k) = 0 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  have h := congrArg (fun F => F q (S.zeroTag_BAUGC k)) S.interiorMapOn_eq_cgpGlobalMap_BAUGP
  exact h.trans (zsp01_original_zero_block_BPS S.family.toLocalPacketsOnBFR.toLocalPacketsOnBF hT he
    k hρq)

/-- **No zero support meets a large slim reference** (closed `zero_meet_absurd_PLN`): if
`ρ(a) > (80/3)R_k/T`, the zero support of `k` misses `D_a = B(a, .95·10⁶Δρ(a))`. -/
theorem not_sgpZeroMeets_BPS (hΛ : 0 ≤ Λ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hT : 0 < T)
    (he : e < 1 / 40) (a : S.SlimIdx_BAUGD) (k : S.ZeroIdx_BAUGC)
    (hρa : 80 / 3 * (S.zeroRadius_BAUGC k / T) < S.rho a.1) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    ¬ sgpZeroMeets_BAUGP S.family.zero (Δ := Δ) (ρ := fun x : W.pieceInterior ⊤ => S.rho x) a.1 k.1
      ((Set.Finite.mem_toFinset _).mp k.2) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  rintro ⟨z, hz, hza⟩
  have h1 := zero_cutoff_ratio_BPS S.family.toLocalPacketsOnBFR.toLocalPacketsOnBF hT he
    ((Set.Finite.mem_toFinset _).mp k.2) hz
  have hk : Λ * (95 / 100 * (1000000 * Δ)) ≤ 1 / 4 := by linarith only [hΛΔ]
  have h2 := (scale_mem_of_dist_lt_KC (ρ := fun x : W.pieceInterior ⊤ => S.rho x)
    S.family.lipschitz_scale hΛ (S.rho_pos a.1) (mem_ball.mp hza) hk).1
  have h3 : 20 * S.zeroRadius_BAUGC k / T = 20 * (S.zeroRadius_BAUGC k / T) := by ring
  change S.rho z.val ≤ 20 * S.zeroRadius_BAUGC k / T at h1
  change 3 / 4 * S.rho a.1 ≤ S.rho z.val at h2
  linarith only [h1, h2, h3, hρa]

/-- **(ZB*-int) at one window** (closed `zero_chain_PLN` + `SlimStagePlanes_PLN.zero_block`): for a
zero centre `k`, a preimage `p` of a point of `S₂` with `ρ(p) > 200R_k/T`, a cloud point `f(q)` (`q` in
the threshold-`7` core of the reference `a`), radius preimages `r_y`, `r_x` of `f(q)`, `f(p)` and the
contributor window (`σ ≤ ε/10000`): the zero block of `f(q)` and of `DΦ_a(η_a q)` vanish. -/
theorem slim_zero_block_point_BPS (hΔ1 : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b)
    (hT : 1600 * (1000000 * Δ) ≤ T) (he : e < 1 / 40) {εc σ' : ℝ} (hε : 0 < εc)
    (hσε : σ' ≤ εc / 10000) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    ∀ (k : S.ZeroIdx_BAUGC) {p : W.pieceInterior ⊤},
      (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap p.val) ∈
        (actualSlotsV2_BAUGD S).stageCloud 2 →
      200 * S.zeroRadius_BAUGC k / T < S.rho p →
      ∀ (a : S.SlimIdx_BAUGD) (zsgn zc : W.pieceInterior ⊤ → ℝ)
        (Φ : ℝ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²)),
      (∀ w, Φ w (S.zeroTag_BAUGC k) =
        sgpZeroModelBlock_BAUGP S.family.toLocalPacketsOnB S.family.zero a zsgn zc k w) →
      ∀ {q ry rx : W.pieceInterior ⊤} {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)},
      dist q a.1 < 1000000 * Δ * S.rho a.1 → |S.slimEta_BIF a.1 q| ≤ 7 * (100000 * Δ) →
      (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val) = y →
      (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap ry.val) = y →
      (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap rx.val) =
        (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap p.val) →
      (closedBall y (80 * εc⁻¹ * (σ' * S.rho ry)) ∩
        ball ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap p.val))
          (8 * εc⁻¹ * (σ' * S.rho rx))).Nonempty →
      S.zeroBlockCLM_BAUGC k y = 0 ∧
        ∀ v : ℝ, (fderiv ℝ Φ (S.slimEta_BIF a.1 q) v) (S.zeroTag_BAUGC k) = 0 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  intro k p hp hρp a zsgn zc Φ hzblk q ry rx y hqd hqη hqy hry hrx hmeet
  subst hqy
  have hΔ : 0 < Δ := by linarith only [hΔ1]
  have hT0 : 0 < T := by linarith only [hT, hΔ]
  have hR := (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  have hRk : 0 < S.zeroRadius_BAUGC k := hR
  have hra := S.rho_pos a.1
  have hp8 : (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap p.val) ∈
      (actualSlotsV2_BAUGD S).stageCloudEnlarged 2 :=
    actualSlotsV2_stageCloud_subset_BAUGD S hΔ.le 2 hp
  have hq8 := S.stageProj_mem_stageCloudEnlarged_two_BPS a hqd (by linarith only [hqη, hΔ])
  have hrx8 : (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap rx.val) ∈
      (actualSlotsV2_BAUGD S).stageCloudEnlarged 2 := by rw [hrx]; exact hp8
  have hry8 : (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap ry.val) ∈
      (actualSlotsV2_BAUGD S).stageCloudEnlarged 2 := by rw [hry]; exact hq8
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
    linarith only [dist_nonneg (x := z) (y := (actualSlotsV2_BAUGD S).stageProj 2
      (S.boundaryOriginalMap p.val)), h2, h4]
  have hd : dist ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap ry.val))
      ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap rx.val)) ≤
      88 * εc⁻¹ * max (σ' * S.rho ry.val) (σ' * S.rho rx.val) := by
    rw [hry, hrx]
    have h3 := dist_triangle_left ((actualSlotsV2_BAUGD S).stageProj 2
      (S.boundaryOriginalMap q.val)) ((actualSlotsV2_BAUGD S).stageProj 2
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
  have hm := (S.slim_scale_ratio_BPS hΛ hΔ1 hΛΔ hV hβ1 hb hσ.le (by positivity) hLs hrx8 hry8
    hd).1
  have hpr1 := (S.slim_scale_ratio_BPS hΛ hΔ1 hΛΔ hV hβ1 hb (σ := 0) (L' := 0) le_rfl le_rfl
    (by norm_num) hp8 hrx8 (by rw [hrx, dist_self]; simp)).1
  have hpr2 := (S.slim_scale_ratio_BPS hΛ hΔ1 hΛΔ hV hβ1 hb (σ := 0) (L' := 0) le_rfl le_rfl
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
  · rw [S.zeroBlockCLM_stageTwo_BPS k q]
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
  have habs := S.not_sgpZeroMeets_BPS hΛ hΛΔ hT0 he a k hρa
  refine fderiv_block_eq_zero_of_block_zero_BPS Φ _ (fun w => ?_) _ v
  rw [hzblk w]
  unfold sgpZeroModelBlock_BAUGP
  rw [ite_eq_right habs]

end BoundarySupply

end DifferentialGeometry.Geometry.Collapse

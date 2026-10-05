import DifferentialGeometry.Geometry.Fibration.ActualStagePlaneTypes
import DifferentialGeometry.Geometry.Fibration.ActualFullMarkerContributors

/-!
# (FM*) on the enhanced stage planes: full marker and plane in the marker kernel

Blueprint `master207B.tex`, GAF04 (`lem:fibration-actual-full-marker-contributors`, B:5896–5970)
plane half; draft 59 §1.4 (D59-2). For a stage witness `A`, a marked chart `i` of the stage with a
threshold-`7` core point `p`, `x = π_st𝓔⁰(p)`, and a cloud point `y ∈ S_st` in the contributor
window `B̄(y, 80ε⁻¹r(y)) ∩ B(x, 8ε⁻¹r(x)) ≠ ∅` (`r = Σρ ∘ A.rsel x₀`, `Σ ≤ ε/10000`):

  `v_i(y) = R_i` and `A.plane y ≤ ker v_i`.                                            (FM*)

Route (draft §1.4, with the plateau step through (TG) instead of the unexported affine
comparisons, sheet §0): (FD) with the RADIUS preimages (`gaf04_fd_projected`); transfer to the
MODEL preimage `q = A.pre y` (block distance ⇒ (FV), full original marker at `q`); the radius ratio
`ρ(i) ≥ .99ρ(a)` of the two constant-radius charts through `q` (`a = A.ref y`); (TG) of the model
`Φ_a` at `q`, block `i` ⇒ the model's cutoff argument lies strictly in its plateau
(`scaledCutoffBlock_arg_lt_of_close_PLN`) ⇒ the model marker is locally constant at `η_a(q)` ⇒
`im DΦ_a(η_a q) ≤ ker v_i` (`egpModelGraph_marker_fderiv_GAFS`, …).

* `plateau_numbers_PLN`, `smul_fullBlock_PLN`, `block_close_PLN`, `lift_block_close_PLN`,
  `embed_block_close_PLN`.
* `FirstStagePlanes_PLN.full_marker` (stage `0`, through the pruning `K_a`),
  `EdgeStagePlanes_PLN.full_marker` (stage `1`), `SlimStagePlanes_PLN.full_marker` (stage `2`);
  first halves `FirstStagePlanes_PLN.pre_plateau_PLN`, `SlimStagePlanes_PLN.pre_plateau_PLN`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14_PLNm {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_PLNm {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_PLNm {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

section Generic

/-- The plateau numbers of (FM*): with `ℓ ≥ 1`, `s ≥ .99`, `0 ≤ e < 1/100`: `e < s` and
`(351/49)ℓ + e/s ≤ 8ℓ(1 − e/s)`. -/
theorem plateau_numbers_PLN {e s ℓ : ℝ} (hℓ : 1 ≤ ℓ) (hs : 99 / 100 ≤ s) (he0 : 0 ≤ e)
    (he : e < 1 / 100) : e < s ∧ 351 / 49 * ℓ + e / s ≤ 8 * ℓ * (1 - e / s) := by
  have hs0 : 0 < s := by linarith
  refine ⟨by linarith, ?_⟩
  have ht : e / s ≤ 1 / 99 := by
    rw [div_le_iff₀ hs0]
    linarith
  have ht0 : 0 ≤ e / s := div_nonneg he0 hs0.le
  nlinarith

/-- `r⁻¹ • (R·1 η, R·1) = (R/r η, R/r)` for a full-marker block. -/
theorem smul_fullBlock_PLN {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (R r : ℝ) (η : F) :
    r⁻¹ • (WithLp.toLp 2 ((R * 1) • η, R * 1) : WithLp 2 (F × ℝ)) =
      WithLp.toLp 2 ((R / r) • η, R / r) := by
  rw [← WithLp.toLp_smul, Prod.smul_mk, smul_smul, smul_eq_mul, mul_one, div_eq_inv_mul]

variable {κ : Type*} [Fintype κ] {V : κ → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace ℝ (V i)]

/-- **(TG) at one block**: if `‖r⁻¹ • y − m‖ < e` in the block space and the `t`-block of `y` is the
full-marker block `(R·1 η, R·1)` and that of `m` is `m_t`, then `‖(R/r η, R/r) − m_t‖ < e`. -/
theorem block_close_PLN {y m : BlockSpace V} {r e R : ℝ} (t : κ) {η : V t}
    (h : ‖r⁻¹ • y - m‖ < e) (hy : y t = WithLp.toLp 2 ((R * 1) • η, R * 1)) :
    ‖(WithLp.toLp 2 ((R / r) • η, R / r) : WithLp 2 (V t × ℝ)) - m t‖ < e := by
  have h1 : ‖(r⁻¹ • y - m) t‖ ≤ ‖r⁻¹ • y - m‖ := PiLp.norm_apply_le _ _
  have h2 : (r⁻¹ • y - m) t = r⁻¹ • y t - m t := rfl
  rw [h2, hy, smul_fullBlock_PLN] at h1
  exact lt_of_le_of_lt h1 h

end Generic

/-- **The lifted block of an edge / slim chart**: if the `t`-block of `‖r⁻¹ • y − m‖ < e` has
`y t = (R·1 planeAxis η, R·1)` and `m t = lift(b)`, then `‖(R/r η, R/r) − b‖ < e`. -/
theorem lift_block_close_PLN {κ : Type*} [Fintype κ] {y m : BlockSpace (fun _ : κ => ℝ²)}
    {r e R : ℝ} (t : κ) {η : ℝ} {b : WithLp 2 (ℝ × ℝ)} (h : ‖r⁻¹ • y - m‖ < e)
    (hy : y t = WithLp.toLp 2 ((R * 1) • planeAxis η, R * 1)) (hm : m t = blockLift_KC3 b) :
    ‖(WithLp.toLp 2 ((R / r) • η, R / r) : WithLp 2 (ℝ × ℝ)) - b‖ < e := by
  have h1 : ‖(r⁻¹ • y - m) t‖ ≤ ‖r⁻¹ • y - m‖ := PiLp.norm_apply_le _ _
  have h2 : (r⁻¹ • y - m) t = r⁻¹ • y t - m t := rfl
  have h3 : (WithLp.toLp 2 ((R * 1) • planeAxis η, R * 1) : WithLp 2 (ℝ² × ℝ)) =
      blockLift_KC3 (WithLp.toLp 2 ((R * 1) • η, R * 1)) := by
    rw [blockLift_apply_KC3]
    show _ = WithLp.toLp 2 (planeAxis ((R * 1) • η), R * 1)
    rw [map_smul]
  rw [h2, hy, hm, h3, ← map_smul, ← map_sub, norm_blockLift_apply_KC3, smul_fullBlock_PLN] at h1
  exact lt_of_le_of_lt h1 h

/-- **The embedded block of a slim chart** (`sgpBlockEmbed`, as `lift_block_close_PLN`). -/
theorem embed_block_close_PLN {κ : Type*} [Fintype κ] {y m : BlockSpace (fun _ : κ => ℝ²)}
    {r e R : ℝ} (t : κ) {η : ℝ} {b : WithLp 2 (ℝ × ℝ)} (h : ‖r⁻¹ • y - m‖ < e)
    (hy : y t = WithLp.toLp 2 ((R * 1) • planeAxis η, R * 1)) (hm : m t = sgpBlockEmbed b) :
    ‖(WithLp.toLp 2 ((R / r) • η, R / r) : WithLp 2 (ℝ × ℝ)) - b‖ < e := by
  have h1 : ‖(r⁻¹ • y - m) t‖ ≤ ‖r⁻¹ • y - m‖ := PiLp.norm_apply_le _ _
  have h2 : (r⁻¹ • y - m) t = r⁻¹ • y t - m t := rfl
  have h3 : (WithLp.toLp 2 ((R * 1) • planeAxis η, R * 1) : WithLp 2 (ℝ² × ℝ)) =
      sgpBlockEmbed (WithLp.toLp 2 ((R * 1) • η, R * 1)) := by
    show _ = WithLp.toLp 2 (planeAxis ((R * 1) • η), R * 1)
    rw [map_smul]
  rw [h2, hy, hm, h3, ← map_smul, ← map_sub, LinearIsometry.norm_map, smul_fullBlock_PLN] at h1
  exact lt_of_le_of_lt h1 h

section C14

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- **(FM\*) at the edge stage** (stage `1`): for an edge chart `i` with a threshold-`7` core point
`p` (`p ∈ B(i, 100Δρ(i))`, `|η_i(p)| ≤ 7Δ`, `t(p) ≤ 7Δ`), `x = π₂𝓔⁰(p)`, and `y ∈ S₂` in the
contributor window of the radius `Σρ ∘ A.rsel x₀` (`0 ≤ Σ ≤ ε_c/10000`): the edge marker of `i` is
full at `y` and the plane `A.plane y` lies in its kernel. -/
theorem EdgeStagePlanes_PLN.full_marker
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Γ sg eg : ℝ} (A : EdgeStagePlanes_PLN P Γ sg eg) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (heg0 : 0 ≤ eg) (heg : eg < 1 / 100) {εc σ : ℝ}
    (hε : 0 < εc) (hσ : 0 ≤ σ) (hσε : σ ≤ εc / 10000) (x₀ : X)
    (i : P.toLocalChartFamily.edge.finite_centres.toFinset) {p : X}
    (hpi : p ∈ ball i.1 (100 * Δ * ρ i.1)) (hηp : |P.edge.coord i.1 p| ≤ 7 * Δ)
    (htp : cgpHeight P.toLocalChartFamily p ≤ 7 * Δ) {x y :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hpx : cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1) p =
      x)
    (hy : y ∈ gafCloud P.toLocalChartFamily P.zero 1)
    (hmeet : (closedBall y (80 * εc⁻¹ * A.radius x₀ σ ρ y) ∩
      ball x (8 * εc⁻¹ * A.radius x₀ σ ρ x)).Nonempty) :
    cgpMarker P.toLocalChartFamily P.zero (.inr (.inr i)) y = ρ i.1 ∧
      A.plane y ≤ LinearMap.ker ((blockMarkerCLM
        (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr i))) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ) := by
  have hΔ0 : 0 < Δ := by linarith
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by nlinarith
  have hi := (Set.Finite.mem_toFinset _).mp i.2
  have hri := hρ i.1
  have hpx' : cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) p =
      x := hpx
  -- the two cloud points and their radius preimages
  have hp8 : p ∈ fc27EdgeSet P.toLocalChartFamily 8 := ⟨i, hpi, by linarith, by linarith⟩
  have hxT : x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 1 := ⟨p, hp8, hpx⟩
  have hyT := gafCloud_subset_enlarged P.toLocalChartFamily P.zero hΔ0.le 1 hy
  have hsel := A.toStagePlaneData_PLN.rsel_spec x₀ _ fun z => (A.rpre_spec z).2
  have hselm : ∀ z ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 1,
      A.rsel x₀ z ∈ fc27EdgeSet P.toLocalChartFamily 8 := fun z hz => by
    rw [A.toStagePlaneData_PLN.rsel_of_mem x₀ hz]
    exact (A.rpre_spec ⟨z, hz⟩).1
  have hrx : cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero)
      (A.rsel x₀ x) = x := hsel x hxT
  have hry : cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero)
      (A.rsel x₀ y) = y := hsel y hyT
  -- (FD) with the radius preimages
  have hcutp : P.edge.cutoff i.1 p = 1 :=
    P.edge.cutoff_eq_one_of_le hΔ0 hi hpi (by linarith) (by unfold cgpHeight at htp; linarith)
  have hfullx : cgpMarker P.toLocalChartFamily P.zero (.inr (.inr i))
      (cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero)
        (A.rsel x₀ x)) = ρ i.1 := by
    rw [hrx, ← hpx', cgpMarker_projMap P.toLocalChartFamily P.zero
      (edge_mem_cgpQ2Tags P.toLocalChartFamily P.zero i)]
    change ρ i.1 * P.edge.cutoff i.1 p = ρ i.1
    rw [hcutp, mul_one]
  have hmeet' : (closedBall (cgpProjMap P.toLocalChartFamily P.zero
      (cgpQ2Tags P.toLocalChartFamily P.zero) (A.rsel x₀ y)) (80 * εc⁻¹ * (σ * ρ (A.rsel x₀ y))) ∩
      ball (cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero)
        (A.rsel x₀ x)) (8 * εc⁻¹ * (σ * ρ (A.rsel x₀ x)))).Nonempty := by
    rw [hrx, hry]
    exact hmeet
  have hFD := gaf04_fd_projected P.toLocalChartFamily P.zero hΔ hΛ hsmall
    (fun j : P.toLocalChartFamily.edge.finite_centres.toFinset =>
      (.inr (.inr j) : CGPMarkerIndex P.toLocalChartFamily))
    (cgpQ2Tags P.toLocalChartFamily P.zero)
    (fun j => edge_mem_cgpQ2Tags P.toLocalChartFamily P.zero j)
    (fun j => {q | q ∈ ball j.1 (100 * Δ * ρ j.1) ∧ |P.edge.coord j.1 q| ≤ 8 * Δ ∧
      cgpHeight P.toLocalChartFamily q ≤ 8 * Δ})
    (fun j q hq => hq.1)
    (fun j q hq => P.edge.cutoff_eq_one_of_le hΔ0 ((Set.Finite.mem_toFinset _).mp j.2) hq.1
      hq.2.1 hq.2.2)
    (fc27EdgeSet P.toLocalChartFamily 8) (fun q hq => hq) hε hσ hσε (hselm x hxT) (hselm y hyT) i
    hfullx hmeet'
  rw [hrx, hry] at hFD
  -- the model preimage of `y`
  set q := A.pre ⟨y, hy⟩ with hqdef
  set a := A.ref ⟨y, hy⟩ with hadef
  obtain ⟨hqa, hηq, htq, hqy⟩ := A.pre_spec ⟨y, hy⟩
  have hqy' : cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) q =
      y := hqy
  have hblk := dist_block_le_projMap_GAF P.toLocalChartFamily P.zero
    (edge_mem_cgpQ2Tags P.toLocalChartFamily P.zero i) q p
  rw [hqy', hpx'] at hblk
  have hblk' : dist (WithLp.toLp 2 ((ρ i.1 * P.edge.cutoff i.1 q) •
      planeAxis (P.edge.coord i.1 q), ρ i.1 * P.edge.cutoff i.1 q))
      (WithLp.toLp 2 ((ρ i.1 * 1) • planeAxis (P.edge.coord i.1 p), ρ i.1 * 1)) <
        ρ i.1 / 50 := by
    rw [← hcutp]
    exact lt_of_le_of_lt hblk hFD
  obtain ⟨hζ, hv⟩ := fv_of_block_dist_GAF hri hΔ (by rw [norm_planeAxis]; exact hηp) hblk'
  rw [norm_planeAxis] at hv
  have hcutq_ne : P.edge.cutoff i.1 q ≠ 0 := by
    intro h
    rw [h] at hζ
    norm_num at hζ
  have hdom := cgpMarkerCutoff_ne_zero P.toLocalChartFamily hΔ0 (.inr (.inr i)) q hcutq_ne
  have hdom' : q ∈ ball i.1 (100 * Δ * ρ i.1) := by
    simpa [cgpMarkerCentre, cgpMarkerDomain] using hdom
  have hcutq : P.edge.cutoff i.1 q = 1 :=
    P.edge.cutoff_eq_one_of_le hΔ0 hi hdom' (by linarith) (by unfold cgpHeight at htq; linarith)
  refine ⟨?_, ?_⟩
  · rw [← hqy', cgpMarker_projMap P.toLocalChartFamily P.zero
      (edge_mem_cgpQ2Tags P.toLocalChartFamily P.zero i)]
    change ρ i.1 * P.edge.cutoff i.1 q = ρ i.1
    rw [hcutq, mul_one]
  -- the radius ratio of the two constant-radius charts through `q`
  have hra := hρ a.1
  have hC : Λ * (100 * Δ) ≤ 1 / 200 := by nlinarith
  have hratio := ratio_ge_of_common_point_PLN P.lipschitz_scale hΛ hra hri (mem_ball.mp hqa)
    (mem_ball.mp hdom') hC hC
  have hnum := plateau_numbers_PLN hΔ (s := ρ i.1 / ρ a.1)
    (by rw [le_div_iff₀ hra]; linarith) heg0 heg
  -- (TG) at `q`, edge block of `i`
  have hTG := (A.model_tg a q hqa (by linarith) (by linarith)).1
  rw [A.coord_eq a] at hηq hTG
  rw [A.prune_eq a, A.model_eq a] at hTG
  rw [A.toStagePlaneData_PLN.plane_of_mem hy, A.prune_eq a, A.model_eq a, A.coord_eq a]
  rintro _ ⟨h, rfl⟩
  rw [LinearMap.mem_ker]
  refine egpModelGraph_marker_fderiv_GAFS P.toLocalChartFamily P.zero hΔ0 a.1 (A.sgn a)
    (A.trans a) i (P.edge.coord a.1 q) (fun hia hlist => ?_) h
  have hyt : cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) q
      (.inr (.inr (.inl i))) = WithLp.toLp 2 ((ρ i.1 * 1) • planeAxis (P.edge.coord i.1 q),
        ρ i.1 * 1) := by
    rw [cgpProjMap_apply_of_mem P.toLocalChartFamily P.zero (a := .inr (.inr (.inl i)))
      (edge_mem_cgpQ2Tags P.toLocalChartFamily P.zero i), ← hcutq]
    rfl
  have hmt : (⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero =>
      ℝ²))) ∘ egpModelGraph P.toLocalChartFamily P.zero a.1
      (A.sgn a) (A.trans a)) (P.edge.coord a.1 q) (.inr (.inr (.inl i))) =
      blockLift_KC3 (graphPacketModelBlock Δ (ρ i.1 / ρ a.1)
        (A.sgn a (.inr (.inr (.inl i))) * P.edge.coord a.1 q + A.trans a (.inr (.inr
            (.inl i))))) := by
    change egpModelComponent P.toLocalChartFamily P.zero a.1 (A.sgn a) (A.trans a)
      (.inr (.inr (.inl i))) (P.edge.coord a.1 q) = _
    simp only [egpModelComponent, hia, hlist, ite_true, ite_false]
  have hcl := lift_block_close_PLN _ hTG hyt hmt
  have harg := scaledCutoffBlock_arg_lt_of_close_PLN (by positivity) hnum.1
    (by rw [Real.norm_eq_abs]; exact hv.le) hcl hnum.2
  rw [smul_eq_mul, Real.norm_eq_abs] at harg
  exact harg

/-- **(FM\*), first stage, first half** (FD with the radius preimages, transfer to the model
preimage): for a circle chart `i` with a threshold-`7` core point `p` (`p ∈ B(i, 200ρ(i))`,
`‖η_i(p)‖ ≤ 7`), `x = 𝓔⁰(p)` and `y ∈ S₁` in the contributor window of the radius
`Σρ ∘ A.rsel x₀` (`0 ≤ Σ ≤ ε_c/10000`): the model preimage `q = A.pre y` lies in the plateau of `i`
(cutoff one, `q ∈ B(i, 200ρ(i))`, `‖η_i(q)‖ < 351/49`). -/
theorem FirstStagePlanes_PLN.pre_plateau_PLN
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Γ sg eg : ℝ} (A : FirstStagePlanes_PLN P Γ sg eg) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) {εc σ : ℝ}
    (hε : 0 < εc) (hσ : 0 ≤ σ) (hσε : σ ≤ εc / 10000) (x₀ : X)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset) {p : X}
    (hpi : p ∈ ball i.1 (200 * ρ i.1)) (hηp : ‖cgpCircleCoord P.toLocalChartFamily i.1
        ((Set.Finite.mem_toFinset _).mp i.2) p‖ ≤ 7)
    {x y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hpx : cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0) p =
      x)
    (hy : y ∈ gafCloud P.toLocalChartFamily P.zero 0)
    (hmeet : (closedBall y (80 * εc⁻¹ * A.radius x₀ σ ρ y) ∩
      ball x (8 * εc⁻¹ * A.radius x₀ σ ρ x)).Nonempty) :
    P.circle.cutoff i.1 (A.pre ⟨y, hy⟩) = 1 ∧ A.pre ⟨y, hy⟩ ∈ ball i.1 (200 * ρ i.1) ∧
      ‖cgpCircleCoord P.toLocalChartFamily i.1 ((Set.Finite.mem_toFinset _).mp i.2)
          (A.pre ⟨y, hy⟩)‖ < 351 / 49 := by
  have hΔ0 : 0 < Δ := by linarith
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by nlinarith
  have hri := hρ i.1
  have hmemt : ∀ t : CGPTag P.toLocalChartFamily P.zero,
      t ∈ gafStageTags P.toLocalChartFamily P.zero 0 := fun t => Finset.mem_univ t
  have hp8 : p ∈ fc04Set P.toLocalChartFamily P.zero 8 := ⟨i, hpi, by
    change ‖cgpCircleCoord P.toLocalChartFamily i.1 ((Set.Finite.mem_toFinset _).mp i.2) p‖ ≤ 8
    linarith⟩
  have hxT : x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 0 := ⟨p, hp8, hpx⟩
  have hyT := gafCloud_subset_enlarged P.toLocalChartFamily P.zero hΔ0.le 0 hy
  have hsel := A.toStagePlaneData_PLN.rsel_spec x₀ _ fun z => (A.rpre_spec z).2
  have hselm : ∀ z ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 0,
      A.rsel x₀ z ∈ fc04Set P.toLocalChartFamily P.zero 8 := fun z hz => by
    rw [A.toStagePlaneData_PLN.rsel_of_mem x₀ hz]
    exact (A.rpre_spec ⟨z, hz⟩).1
  have hrx := hsel x hxT
  have hry := hsel y hyT
  have hcutp : P.circle.cutoff i.1 p = 1 :=
    circle_cutoff_eq_one_of_coord_le_GAF P.toLocalChartFamilyE.toLocalChartFamilyQ P.zero i hpi
      (le_trans hηp (by norm_num))
  have hfullx : cgpMarker P.toLocalChartFamily P.zero (.inl i)
      (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0)
        (A.rsel x₀ x)) = ρ i.1 := by
    rw [hrx, ← hpx, cgpMarker_projMap P.toLocalChartFamily P.zero (hmemt _)]
    change ρ i.1 * P.circle.cutoff i.1 p = ρ i.1
    rw [hcutp, mul_one]
  have hmeet' : (closedBall (cgpProjMap P.toLocalChartFamily P.zero
      (gafStageTags P.toLocalChartFamily P.zero 0) (A.rsel x₀ y))
        (80 * εc⁻¹ * (σ * ρ (A.rsel x₀ y))) ∩
      ball (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0)
        (A.rsel x₀ x)) (8 * εc⁻¹ * (σ * ρ (A.rsel x₀ x)))).Nonempty := by
    rw [hrx, hry]
    exact hmeet
  have hFD := gaf04_fd_projected P.toLocalChartFamily P.zero hΔ hΛ hsmall
    (fun j : P.toLocalChartFamily.circle.finite_centres.toFinset =>
      (.inl j : CGPMarkerIndex P.toLocalChartFamily))
    (gafStageTags P.toLocalChartFamily P.zero 0) (fun _ => hmemt _)
    (fun j => {q | q ∈ ball j.1 (200 * ρ j.1) ∧
      ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) q‖ ≤ 8})
    (fun j q hq => hq.1)
    (fun j q hq => circle_cutoff_eq_one_of_coord_le_GAF P.toLocalChartFamilyE.toLocalChartFamilyQ
      P.zero j hq.1 hq.2)
    (fc04Set P.toLocalChartFamily P.zero 8) (fun q hq => hq) hε hσ hσε (hselm x hxT)
    (hselm y hyT) i hfullx hmeet'
  rw [hrx, hry] at hFD
  obtain ⟨-, -, hqy⟩ := A.pre_spec ⟨y, hy⟩
  have hblk := dist_block_le_projMap_GAF P.toLocalChartFamily P.zero (hmemt (.inl i))
    (A.pre ⟨y, hy⟩) p
  rw [hqy, hpx] at hblk
  have hblk' : dist (WithLp.toLp 2 ((ρ i.1 * P.circle.cutoff i.1 (A.pre ⟨y, hy⟩)) •
      cgpCoord P.toLocalChartFamily P.zero (.inl i) (A.pre ⟨y, hy⟩),
      ρ i.1 * P.circle.cutoff i.1 (A.pre ⟨y, hy⟩)))
      (WithLp.toLp 2 ((ρ i.1 * 1) • cgpCoord P.toLocalChartFamily P.zero (.inl i) p, ρ i.1 * 1)) <
        ρ i.1 / 50 := by
    rw [← hcutp]
    exact lt_of_le_of_lt hblk hFD
  obtain ⟨hζ, hv⟩ := fv_of_block_dist_GAF hri le_rfl
    (by rw [mul_one]; exact hηp) hblk'
  have hcutq_ne : P.circle.cutoff i.1 (A.pre ⟨y, hy⟩) ≠ 0 := by
    intro h
    rw [h] at hζ
    norm_num at hζ
  have hdom := cgpMarkerCutoff_ne_zero P.toLocalChartFamily hΔ0 (.inl i) (A.pre ⟨y, hy⟩) hcutq_ne
  have hv8 : ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) (A.pre ⟨y, hy⟩)‖ ≤ 8 := by linarith
  have hcutq : P.circle.cutoff i.1 (A.pre ⟨y, hy⟩) = 1 :=
    circle_cutoff_eq_one_of_coord_le_GAF P.toLocalChartFamilyE.toLocalChartFamilyQ P.zero i hdom
      hv8
  exact ⟨hcutq, hdom, lt_of_lt_of_eq hv (mul_one _)⟩

open Classical in
/-- **(FM\*) at the first stage** (stage `0`): for a circle chart `i` with a threshold-`7` core
point `p` (`p ∈ B(i, 200ρ(i))`, `‖η_i(p)‖ ≤ 7`), `x = 𝓔⁰(p)` and `y ∈ S₁` in the contributor window
of the radius `Σρ ∘ A.rsel x₀`
    (`0 ≤ Σ ≤ ε_c/10000`): the circle marker of `i` is full at `y` and the
plane `A.plane y = im D(K_a ∘ Φ_a)(η_a q)` lies in its kernel (through the SAME pruning `K_a`). -/
theorem FirstStagePlanes_PLN.full_marker
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Γ sg eg : ℝ} (A : FirstStagePlanes_PLN P Γ sg eg) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (heg0 : 0 ≤ eg) (heg : eg < 1 / 100) {εc σ : ℝ}
    (hε : 0 < εc) (hσ : 0 ≤ σ) (hσε : σ ≤ εc / 10000) (x₀ : X)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset) {p : X}
    (hpi : p ∈ ball i.1 (200 * ρ i.1)) (hηp : ‖cgpCircleCoord P.toLocalChartFamily i.1
        ((Set.Finite.mem_toFinset _).mp i.2) p‖ ≤ 7)
    {x y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hpx : cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0) p =
      x)
    (hy : y ∈ gafCloud P.toLocalChartFamily P.zero 0)
    (hmeet : (closedBall y (80 * εc⁻¹ * A.radius x₀ σ ρ y) ∩
      ball x (8 * εc⁻¹ * A.radius x₀ σ ρ x)).Nonempty) :
    cgpMarker P.toLocalChartFamily P.zero (.inl i) y = ρ i.1 ∧
      A.plane y ≤ LinearMap.ker ((blockMarkerCLM
        (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inl i)) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ) := by
  have hri := hρ i.1
  have hmemt : ∀ t : CGPTag P.toLocalChartFamily P.zero,
      t ∈ gafStageTags P.toLocalChartFamily P.zero 0 := fun t => Finset.mem_univ t
  obtain ⟨hcutq, hdom, hv⟩ := A.pre_plateau_PLN hΔ hΛ hLΛ hε hσ hσε x₀ i hpi hηp hpx hy hmeet
  set q := A.pre ⟨y, hy⟩ with hqdef
  set a := A.ref ⟨y, hy⟩ with hadef
  obtain ⟨hqa, hηq, hqy⟩ := A.pre_spec ⟨y, hy⟩
  have hqy' : cgpProjMap P.toLocalChartFamily P.zero
      (gafStageTags P.toLocalChartFamily P.zero 0) q =
      y := hqy
  refine ⟨?_, ?_⟩
  · rw [← hqy', cgpMarker_projMap P.toLocalChartFamily P.zero (hmemt _)]
    change ρ i.1 * P.circle.cutoff i.1 q = ρ i.1
    rw [hcutq, mul_one]
  have hra := hρ a.1
  have hC : Λ * 200 ≤ 1 / 200 := by nlinarith
  have hratio := ratio_ge_of_common_point_PLN P.lipschitz_scale hΛ hra hri (mem_ball.mp hqa)
    (mem_ball.mp hdom) hC hC
  have hnum := plateau_numbers_PLN le_rfl (s := ρ i.1 / ρ a.1)
    (by rw [le_div_iff₀ hra]; linarith) heg0 heg
  have hTG := (A.model_tg a q hqa (by linarith)).1
  rw [A.toStagePlaneData_PLN.plane_of_mem hy]
  rintro _ ⟨h, rfl⟩
  rw [LinearMap.mem_ker]
  have hdiff : DifferentiableAt ℝ (A.model a) (A.coord a q) := by
    rw [A.model_eq a]
    exact ((contDiff_tcpModelGraph _ _ _ _ _ _ _ _ _ _ _).differentiable (by simp)) _
  change blockMarkerCLM _ (fderiv ℝ (A.prune a ∘ A.model a) (A.coord a q) h) = 0
  rw [fderiv_comp _ (A.prune a).differentiableAt hdiff, (A.prune a).fderiv,
    ContinuousLinearMap.comp_apply, A.prune_eq a, blockMarkerCLM_apply, blockRestrict_apply]
  split_ifs with hkeep
  swap
  · rfl
  rw [← blockMarkerCLM_apply, A.model_eq a]
  refine tcpModelGraph_marker_fderiv_GAFS P.toLocalChartFamily P.zero a.1 _ _ (A.Ac a) (A.cc a)
    (A.A1 a) (A.c1 a) (A.Bτ a) (A.cτ a) i (A.coord a q) (fun hlist hia => ?_) h
  have hyt : cgpGlobalMap P.toLocalChartFamily P.zero q (.inl i) =
      WithLp.toLp 2 ((ρ i.1 * 1) • cgpCoord P.toLocalChartFamily P.zero (.inl i) q, ρ i.1 * 1) := by
    rw [← hcutq]
    rfl
  have hmt : (A.prune a ∘ A.model a) (A.coord a q) (.inl i) =
      scaledCutoffBlock (ρ i.1 / ρ a.1) (circleCutoffBump_LC87 : ℝ² → ℝ)
        (A.Ac a (.inl i) (A.coord a q) + A.cc a (.inl i)) := by
    change A.prune a (A.model a (A.coord a q)) (.inl i) = _
    have hkeep' : (.inl i : CGPTag P.toLocalChartFamily P.zero) ∈
        firstKeepTags_GAF5 P.toLocalChartFamily P.zero (ρ a.1) := hkeep
    rw [A.prune_eq a, blockRestrict_apply, ite_eq_left hkeep', A.model_eq a]
    change tcpModelComponent P.toLocalChartFamily P.zero a.1
      (tcpListedTags P.toLocalChartFamily P.zero a.1) (tcpListedEdges P.toLocalChartFamily a.1)
      (A.Ac a) (A.cc a) (A.A1 a) (A.c1 a) (A.Bτ a) (A.cτ a) (.inl i) (A.coord a q) = _
    simp only [tcpModelComponent, hia, hlist, ite_true, ite_false]
  have hcl := block_close_PLN (.inl i) hTG hyt
  rw [hmt] at hcl
  exact scaledCutoffBlock_arg_lt_of_close_PLN (by positivity) hnum.1 hv.le hcl
    (by simpa using hnum.2)

/-- **(FM\*), slim stage, first half** (FD with the radius preimages, transfer to the model
preimage): in the situation of `SlimStagePlanes_PLN.full_marker`, the model preimage `q = A.pre y`
lies in the plateau of the slim chart `i` (cutoff one, `q ∈ B(i, 10⁶Δρ(i))`, `|η_i(q)| < 351ℓ/49`).
For a slim chart `i` with a threshold-`7` core point
`p` (`p ∈ B(i, 10⁶Δρ(i))`, `|η_i(p)| ≤ 7·10⁵Δ`), `x = π₃𝓔⁰(p)`, and `y ∈ S₃` in the contributor
window of the radius `Σρ ∘ A.rsel x₀` (`0 ≤ Σ ≤ ε_c/10000`): the slim marker of `i` is full at `y`
and the plane `A.plane y` lies in its kernel. -/
theorem SlimStagePlanes_PLN.pre_plateau_PLN
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Γ sg eg : ℝ} (A : SlimStagePlanes_PLN P Γ sg eg) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) {εc σ : ℝ}
    (hε : 0 < εc) (hσ : 0 ≤ σ) (hσε : σ ≤ εc / 10000) (x₀ : X)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset) {p : X}
    (hpi : p ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1))
    (hηp : |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤ 7 * (10 ^ 5 * Δ))
    {x y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hpx : cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2) p =
      x)
    (hy : y ∈ gafCloud P.toLocalChartFamily P.zero 2)
    (hmeet : (closedBall y (80 * εc⁻¹ * A.radius x₀ σ ρ y) ∩
      ball x (8 * εc⁻¹ * A.radius x₀ σ ρ x)).Nonempty) :
    P.slim.cutoff i.1 (A.pre ⟨y, hy⟩) = 1 ∧ A.pre ⟨y, hy⟩ ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1) ∧
      |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord (A.pre ⟨y, hy⟩)| <
        351 / 49 * (10 ^ 5 * Δ) := by
  have hΔ0 : 0 < Δ := by linarith
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by nlinarith
  have hi := (Set.Finite.mem_toFinset _).mp i.2
  have hri := hρ i.1
  have hcut : P.slim.cutoff i.1 = (P.slim.centre i.1 hi).cutoff :=
    slimFamily_cutoff_eq_KA2 P.toLocalChartFamily hi
  have hpx' : cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) p =
      x := hpx
  have hp8 : p ∈ fc27SlimSet P.toLocalChartFamily 8 := ⟨i, hpi, by linarith⟩
  have hxT : x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 2 := ⟨p, hp8, hpx⟩
  have hyT := gafCloud_subset_enlarged P.toLocalChartFamily P.zero hΔ0.le 2 hy
  have hsel := A.toStagePlaneData_PLN.rsel_spec x₀ _ fun z => (A.rpre_spec z).2
  have hselm : ∀ z ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 2,
      A.rsel x₀ z ∈ fc27SlimSet P.toLocalChartFamily 8 := fun z hz => by
    rw [A.toStagePlaneData_PLN.rsel_of_mem x₀ hz]
    exact (A.rpre_spec ⟨z, hz⟩).1
  have hrx : cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)
      (A.rsel x₀ x) = x := hsel x hxT
  have hry : cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)
      (A.rsel x₀ y) = y := hsel y hyT
  have hcutp : P.slim.cutoff i.1 p = 1 := by
    rw [hcut]
    exact SlimCentre.cutoff_eq_one_of_abs_coord_le _ hpi (by linarith)
  have hfullx : cgpMarker P.toLocalChartFamily P.zero (.inr (.inl i))
      (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)
        (A.rsel x₀ x)) = ρ i.1 := by
    rw [hrx, ← hpx', cgpMarker_projMap P.toLocalChartFamily P.zero
      (slim_mem_cgpQ3Tags P.toLocalChartFamily P.zero i)]
    change ρ i.1 * P.slim.cutoff i.1 p = ρ i.1
    rw [hcutp, mul_one]
  have hmeet' : (closedBall (cgpProjMap P.toLocalChartFamily P.zero
      (cgpQ3Tags P.toLocalChartFamily P.zero) (A.rsel x₀ y)) (80 * εc⁻¹ * (σ * ρ (A.rsel x₀ y))) ∩
      ball (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)
        (A.rsel x₀ x)) (8 * εc⁻¹ * (σ * ρ (A.rsel x₀ x)))).Nonempty := by
    rw [hrx, hry]
    exact hmeet
  have hFD := gaf04_fd_projected P.toLocalChartFamily P.zero hΔ hΛ hsmall
    (fun j : P.toLocalChartFamily.slim.finite_centres.toFinset =>
      (.inr (.inl j) : CGPMarkerIndex P.toLocalChartFamily))
    (cgpQ3Tags P.toLocalChartFamily P.zero)
    (fun j => slim_mem_cgpQ3Tags P.toLocalChartFamily P.zero j)
    (fun j => {q | q ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1) ∧
      |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord q| ≤ 8 * 10 ^ 5 * Δ})
    (fun j q hq => by
      have h := hq.1
      change q ∈ ball j.1 (1000000 * Δ * ρ j.1)
      rw [mem_ball] at h ⊢
      norm_num at h ⊢
      exact h)
    (fun j q hq => by
      change P.slim.cutoff j.1 q = 1
      rw [slimFamily_cutoff_eq_KA2 P.toLocalChartFamily ((Set.Finite.mem_toFinset _).mp j.2)]
      exact SlimCentre.cutoff_eq_one_of_abs_coord_le _ hq.1 hq.2)
    (fc27SlimSet P.toLocalChartFamily 8) (fun q hq => hq) hε hσ hσε (hselm x hxT) (hselm y hyT) i
    hfullx hmeet'
  rw [hrx, hry] at hFD
  set q := A.pre ⟨y, hy⟩ with hqdef
  set a := A.ref ⟨y, hy⟩ with hadef
  obtain ⟨hqa, hηq, hqy⟩ := A.pre_spec ⟨y, hy⟩
  have hqy' : cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q =
      y := hqy
  have hblk := dist_block_le_projMap_GAF P.toLocalChartFamily P.zero
    (slim_mem_cgpQ3Tags P.toLocalChartFamily P.zero i) q p
  rw [hqy', hpx'] at hblk
  have hblk' : dist (WithLp.toLp 2 ((ρ i.1 * P.slim.cutoff i.1 q) •
      planeAxis ((P.slim.centre i.1 hi).coord q), ρ i.1 * P.slim.cutoff i.1 q))
      (WithLp.toLp 2 ((ρ i.1 * 1) • planeAxis ((P.slim.centre i.1 hi).coord p), ρ i.1 * 1)) <
        ρ i.1 / 50 := by
    rw [← hcutp]
    exact lt_of_le_of_lt hblk hFD
  have hℓ : (1 : ℝ) ≤ 10 ^ 5 * Δ := by nlinarith
  obtain ⟨hζ, hv⟩ := fv_of_block_dist_GAF hri hℓ (by rw [norm_planeAxis]; linarith) hblk'
  rw [norm_planeAxis] at hv
  have hcutq_ne : P.slim.cutoff i.1 q ≠ 0 := by
    intro h
    rw [h] at hζ
    norm_num at hζ
  have hdom := cgpMarkerCutoff_ne_zero P.toLocalChartFamily hΔ0 (.inr (.inl i)) q hcutq_ne
  have hdom' : q ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1) := by
    change q ∈ ball i.1 (1000000 * Δ * ρ i.1) at hdom
    rw [mem_ball] at hdom ⊢
    norm_num at hdom ⊢
    exact hdom
  have hcutq : P.slim.cutoff i.1 q = 1 := by
    rw [hcut]
    exact SlimCentre.cutoff_eq_one_of_abs_coord_le _ hdom' (by nlinarith)
  exact ⟨hcutq, hdom', hv⟩

/-- **(FM\*) at the slim stage** (stage `2`): for a slim chart `i` with a threshold-`7` core point
`p` (`p ∈ B(i, 10⁶Δρ(i))`, `|η_i(p)| ≤ 7·10⁵Δ`), `x = π₃𝓔⁰(p)`, and `y ∈ S₃` in the contributor
window of the radius `Σρ ∘ A.rsel x₀` (`0 ≤ Σ ≤ ε_c/10000`): the slim marker of `i` is full at `y`
and the plane `A.plane y` lies in its kernel. -/
theorem SlimStagePlanes_PLN.full_marker
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Γ sg eg : ℝ} (A : SlimStagePlanes_PLN P Γ sg eg) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (heg0 : 0 ≤ eg) (heg : eg < 1 / 100) {εc σ : ℝ}
    (hε : 0 < εc) (hσ : 0 ≤ σ) (hσε : σ ≤ εc / 10000) (x₀ : X)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset) {p : X}
    (hpi : p ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1))
    (hηp : |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤ 7 * (10 ^ 5 * Δ))
    {x y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hpx : cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2) p =
      x)
    (hy : y ∈ gafCloud P.toLocalChartFamily P.zero 2)
    (hmeet : (closedBall y (80 * εc⁻¹ * A.radius x₀ σ ρ y) ∩
      ball x (8 * εc⁻¹ * A.radius x₀ σ ρ x)).Nonempty) :
    cgpMarker P.toLocalChartFamily P.zero (.inr (.inl i)) y = ρ i.1 ∧
      A.plane y ≤ LinearMap.ker ((blockMarkerCLM
        (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inl i))) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ) := by
  have hΔ0 : 0 < Δ := by linarith
  have hi := (Set.Finite.mem_toFinset _).mp i.2
  have hri := hρ i.1
  obtain ⟨hcutq, hdom', hv⟩ := A.pre_plateau_PLN hΔ hΛ hLΛ hε hσ hσε x₀ i hpi hηp hpx hy
    hmeet
  have hℓ : (1 : ℝ) ≤ 10 ^ 5 * Δ := by nlinarith
  set q := A.pre ⟨y, hy⟩ with hqdef
  set a := A.ref ⟨y, hy⟩ with hadef
  obtain ⟨hqa, hηq, hqy⟩ := A.pre_spec ⟨y, hy⟩
  have hqy' : cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q =
      y := hqy
  refine ⟨?_, ?_⟩
  · rw [← hqy', cgpMarker_projMap P.toLocalChartFamily P.zero
      (slim_mem_cgpQ3Tags P.toLocalChartFamily P.zero i)]
    change ρ i.1 * P.slim.cutoff i.1 q = ρ i.1
    rw [hcutq, mul_one]
  have hra := hρ a.1
  have hC : Λ * (10 ^ 6 * Δ) ≤ 1 / 200 := by nlinarith
  have hratio := ratio_ge_of_common_point_PLN P.lipschitz_scale hΛ hra hri (mem_ball.mp hqa)
    (mem_ball.mp hdom') hC hC
  have hnum := plateau_numbers_PLN hℓ (s := ρ i.1 / ρ a.1)
    (by rw [le_div_iff₀ hra]; linarith) heg0 heg
  have hTG := (A.model_tg a q hqa (by linarith)).1
  rw [A.coord_eq a] at hTG
  rw [A.prune_eq a, A.model_eq a] at hTG
  rw [A.toStagePlaneData_PLN.plane_of_mem hy, A.prune_eq a, A.model_eq a, A.coord_eq a]
  rintro _ ⟨h, rfl⟩
  rw [LinearMap.mem_ker]
  refine sgpFullGraph_marker_fderiv_GAFS P.toLocalChartFamily P.zero hΔ0 a (A.sgn a) (A.trans a)
    (A.zsgn a) (A.ztrans a) i ((P.slim.centre a.1 ((Set.Finite.mem_toFinset _).mp a.2)).coord q)
    (fun hia hlist => ?_) h
  have hyt : cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q
      (.inr (.inl i)) = WithLp.toLp 2 ((ρ i.1 * 1) • planeAxis ((P.slim.centre i.1 hi).coord q),
        ρ i.1 * 1) := by
    rw [cgpProjMap_apply_of_mem P.toLocalChartFamily P.zero (a := .inr (.inl i))
      (slim_mem_cgpQ3Tags P.toLocalChartFamily P.zero i), ← hcutq]
    rfl
  have hmt : (⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero =>
      ℝ²))) ∘ sgpFullGraph P.toLocalChartFamily P.zero a (A.sgn a) (A.trans a) (A.zsgn a)
      (A.ztrans a)) ((P.slim.centre a.1 ((Set.Finite.mem_toFinset _).mp a.2)).coord q)
      (.inr (.inl i)) =
      sgpBlockEmbed (sgpModelBlock (10 ^ 5 * Δ) (ρ i.1 / ρ a.1)
        (A.sgn a i.1 * (P.slim.centre a.1 ((Set.Finite.mem_toFinset _).mp a.2)).coord q +
          A.trans a i.1)) := by
    change sgpSlimModelBlock P.toLocalChartFamily a (A.sgn a) (A.trans a) i
      ((P.slim.centre a.1 ((Set.Finite.mem_toFinset _).mp a.2)).coord q) = _
    simp only [sgpSlimModelBlock, hia, hlist, ite_true, ite_false]
  have hcl := embed_block_close_PLN _ hTG hyt hmt
  have harg := scaledCutoffBlock_arg_lt_of_close_PLN (by positivity) hnum.1
    (by rw [Real.norm_eq_abs]; exact hv.le) hcl hnum.2
  rw [smul_eq_mul, Real.norm_eq_abs] at harg
  linarith

end C14

end DifferentialGeometry.Geometry.Collapse

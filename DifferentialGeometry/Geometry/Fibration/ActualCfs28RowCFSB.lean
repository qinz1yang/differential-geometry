import DifferentialGeometry.Geometry.Fibration.ActualStageChainE
import DifferentialGeometry.Geometry.Fibration.ActualStagePlaneZeroBlock
import DifferentialGeometry.Geometry.Fibration.ActualStageSmallMarkers
import DifferentialGeometry.Geometry.Fibration.ActualCfs26RowCFSB

/-!
# CFS28 on the enhanced chain: every contributing centre and plane has WHOLE-block locality

Blueprint `master207B.tex`, CFS28 (`lem:fibration-all-contributors-locality`, B:3686–3731). On the
chain `C : Gaf02ChainE P …` (final family `LocalChartPacketsC14`), stage `st`: the planes are the
(PP)/(PDEF) planes `L_x = im D(K_a Φ_a)(η_a(q(x)))` of the enhanced plane witnesses (reference `a`
with a full marker at the model preimage `q(x)` in its core; stage `0` pruned by CFS27's `K_a`,
stages `1, 2` with EGP06 / SGP04 models), `b = Ξ_st⁻¹`, `128 b Σ_st ≤ 1/5`
(i.e. `Σ_st ≤ 1/(640b)`), the radii `r = Σ_st ρ ∘ sel_st` at ARBITRARY selected radius preimages.

For `x = π_st 𝓔⁰(p) ∈ S_st` and ANY retained block `i` with `R_i < ρ(p)/16`, every selected centre
`u ∈ S_st` whose closed `80 b r(u)` ball meets `B(x, 8 b r(x))` has (AL): the WHOLE `i` block of
`u` vanishes and the WHOLE `i` block of every vector of `L_u` vanishes. The radius preimage
(`sel`) and the model preimage (`q(u)`) at `u` may differ.

* `ratio_chain_CFSB`: (AM)'s scale chain `ρ(q) ≥ (27/125)ρ(p)` under `128 b Σ ≤ 1/5`.
* `block_fderiv_eq_zero_of_zero_CFSB`: a block that is identically zero has zero derivative block.
* `egpModel_smallBlock_CFSB`, `sgpFull_smallBlock_CFSB`: the WHOLE small blocks of the EGP06 / SGP04
  models are zero (`ρ(c_i) ≤ (99/100)ρ(a)`).
* **`Gaf02ChainE.cfs28_row_CFSB`**.
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

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

section Generic

variable {κ : Type*} [Finite κ] {W : κ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace ℝ (W i)]

/-- A block of `Φ` that is identically zero has zero derivative block: `(DΦ(a)h)_t = 0`. -/
theorem block_fderiv_eq_zero_of_zero_CFSB {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : E → BlockSpace W) (t : κ) (hc : ∀ u, Φ u t = 0) (a h : E) :
    fderiv ℝ Φ a h t = 0 := by
  have := Fintype.ofFinite κ
  by_cases hd : DifferentiableAt ℝ Φ a
  · have h1 : HasFDerivAt (fun u => PiLp.proj (𝕜 := ℝ) 2 (fun i => WithLp 2 (W i × ℝ)) t (Φ u))
        ((PiLp.proj (𝕜 := ℝ) 2 (fun i => WithLp 2 (W i × ℝ)) t).comp (fderiv ℝ Φ a)) a :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun i => WithLp 2 (W i × ℝ)) t).hasFDerivAt.comp a hd.hasFDerivAt
    have hfun : (fun u => PiLp.proj (𝕜 := ℝ) 2 (fun i => WithLp 2 (W i × ℝ)) t (Φ u)) = fun _ => 0 :=
      funext hc
    rw [hfun] at h1
    have h3 := h1.unique (hasFDerivAt_const 0 a)
    have h4 := congrArg (fun L : E →L[ℝ] WithLp 2 (W t × ℝ) => L h) h3
    simpa using h4
  · rw [fderiv_zero_of_not_differentiableAt hd]
    rfl

end Generic

section Models

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

variable (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

open Classical in
/-- **The whole small blocks of EGP06's model vanish**: `ρ(c_i) ≤ (99/100)ρ(a)` ⇒ the `i` block of
`egpModelGraph a` is identically zero. -/
theorem egpModel_smallBlock_CFSB (hΔ : 0 < Δ) (hΛ : 0 ≤ Λ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (a : X) (sgn c : CGPTag L Z → ℝ) (i : CGPMarkerIndex L)
    (hi : ρ (cgpMarkerCentre L i) ≤ 99 / 100 * ρ a) (u : ℝ) :
    egpModelGraph L Z a sgn c u (cgpMarkerTag L Z i) = 0 := by
  have hra := hρ a
  rcases i with j | j | j
  · rfl
  · change egpModelComponent L Z a sgn c (.inr (.inl j)) u = 0
    have hS : j.1 ∉ egpSlimList L a := by
      intro hS
      have h1 := egpSlimList_ratio_GAF4 L hΔ hΛ hLΛ hS
      change ρ j.1 ≤ 99 / 100 * ρ a at hi
      linarith
    simp only [egpModelComponent, hS, ↓reduceIte]
    rfl
  · change egpModelComponent L Z a sgn c (.inr (.inr (.inl j))) u = 0
    have hja : j.1 ≠ a := by
      intro hja
      change ρ j.1 ≤ 99 / 100 * ρ a at hi
      rw [hja] at hi
      linarith
    have hS : j.1 ∉ egpEdgeList L a := by
      intro hS
      have h1 := egpEdgeList_ratio_GAF4 L hΔ hΛ hLΛ hS
      change ρ j.1 ≤ 99 / 100 * ρ a at hi
      linarith
    simp only [egpModelComponent, hja, hS, ↓reduceIte]
    rfl

open Classical in
/-- **The whole small blocks of SGP04's full model vanish**: `ρ(c_i) ≤ (99/100)ρ(a)` ⇒ the `i`
block of `sgpFullGraph a` is identically zero. -/
theorem sgpFull_smallBlock_CFSB (hΔ : 0 < Δ) (hΛ : 0 ≤ Λ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (a : L.slim.finite_centres.toFinset) (sgn c zsgn zc : X → ℝ) (i : CGPMarkerIndex L)
    (hi : ρ (cgpMarkerCentre L i) ≤ 99 / 100 * ρ a.1) (u : ℝ) :
    sgpFullGraph L Z a sgn c zsgn zc u (cgpMarkerTag L Z i) = 0 := by
  have hra := hρ a.1
  rcases i with j | j | j
  · rfl
  · change sgpSlimModelBlock L a sgn c j u = 0
    have hja : j ≠ a := by
      rintro rfl
      change ρ j.1 ≤ 99 / 100 * ρ j.1 at hi
      linarith
    have hS : j.1 ∉ sgpSlimList L.slim a.1 := by
      intro hS
      have h1 := (sgpSlimList_bounds L hΔ hΛ hLΛ hS).2.1
      have h2 := (lt_div_iff₀ hra).mp h1
      change ρ j.1 ≤ 99 / 100 * ρ a.1 at hi
      linarith
    unfold sgpSlimModelBlock
    rw [ite_eq_right hja, ite_eq_right hS]
  · rfl

/-- **(AM)'s scale chain** under the blueprint's `128 b Σ ≤ 1/5` (`b = ε_c⁻¹`): if `x = π_st𝓔⁰(p)`
and `y = π_st𝓔⁰(q)` are points of `S_st` whose windows meet, then `ρ(q) ≥ (27/125)ρ(p)`. -/
theorem ratio_chain_CFSB (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4)
    (st : Fin 3) (sel : BlockSpace (fun _ : CGPTag L Z => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged L Z st, cgpProjMap L Z (gafStageTags L Z st) (sel x) = x)
    {εc σ : ℝ} (hε : 0 < εc) (hσ : 0 < σ) (hσε : 128 * εc⁻¹ * σ ≤ 1 / 5) {p q : X}
    {x y : BlockSpace (fun _ : CGPTag L Z => ℝ²)}
    (hpx : cgpProjMap L Z (gafStageTags L Z st) p = x) (hx : x ∈ gafCloud L Z st)
    (hy : y ∈ gafCloud L Z st) (hqy : cgpProjMap L Z (gafStageTags L Z st) q = y)
    (hmeet : (closedBall y (80 * εc⁻¹ * (σ * ρ (sel y))) ∩
      ball x (8 * εc⁻¹ * (σ * ρ (sel x)))).Nonempty) :
    27 / 125 * ρ p ≤ ρ q := by
  classical
  obtain ⟨z, hz1, hz2⟩ := hmeet
  have hεi : 0 < εc⁻¹ := inv_pos.mpr hε
  have hrx := hρ (sel x)
  have hry := hρ (sel y)
  have h1 := mem_closedBall.mp hz1
  have h2 := mem_ball.mp hz2
  have hd : dist y x ≤ 88 * εc⁻¹ * max (σ * ρ (sel y)) (σ * ρ (sel x)) := by
    have h3 : dist y x ≤ dist z y + dist z x := dist_triangle_left y x z
    have hm1 : σ * ρ (sel y) ≤ max (σ * ρ (sel y)) (σ * ρ (sel x)) := le_max_left _ _
    have hm2 : σ * ρ (sel x) ≤ max (σ * ρ (sel y)) (σ * ρ (sel x)) := le_max_right _ _
    nlinarith
  have hΔ0 : (0 : ℝ) ≤ Δ := by linarith
  have hxT := gafCloud_subset_enlarged L Z hΔ0 st hx
  have hyT := gafCloud_subset_enlarged L Z hΔ0 st hy
  have hLs : 88 * εc⁻¹ * σ ≤ 1 / 5 := by
    have : 0 ≤ εc⁻¹ * σ := by positivity
    nlinarith
  have hmcb := (gafCloud_mcb_GAF2 L Z hΔ hΛ hsmall st sel hsel hσ.le (by positivity) hLs x hxT y
    hyT hd).1
  have h5 : 3 / 5 * ρ (sel x) ≤ ρ (sel y) := by
    have h6 : σ * (3 / 5 * ρ (sel x)) ≤ σ * ρ (sel y) := by
      have : σ * ρ (sel x) / (5 / 3) = σ * (3 / 5 * ρ (sel x)) := by ring
      linarith
    exact le_of_mul_le_mul_left h6 hσ
  have h7 := gafCloud_preimage_ratio_GAF4 L Z hΔ hΛ hsmall st sel hsel x hx p
    (by rw [gafStageQ_starProjection_globalMap]; exact hpx)
  have hsel' : ∀ w ∈ gafCloudEnlarged L Z st,
      cgpProjMap L Z (gafStageTags L Z st) (Function.update sel y q w) = w := by
    intro w hw
    by_cases hwy : w = y
    · subst hwy
      rw [Function.update_self]
      exact hqy
    · rw [Function.update_of_ne hwy]
      exact hsel w hw
  have h8 := gafCloud_preimage_ratio_GAF4 L Z hΔ hΛ hsmall st (Function.update sel y q) hsel' y hy
    (sel y) (by rw [gafStageQ_starProjection_globalMap]; exact hsel y hyT)
  rw [Function.update_self] at h8
  nlinarith

/-- The whole retained block of `π_st𝓔⁰(q)` vanishes where the cutoff vanishes. -/
theorem projMap_block_eq_zero_CFSB (st : Fin 3) (i : CGPMarkerIndex L) (q : X)
    (h0 : cgpMarkerCutoff L i q = 0) :
    cgpProjMap L Z (gafStageTags L Z st) q (cgpMarkerTag L Z i) = 0 := by
  classical
  by_cases hmem : cgpMarkerTag L Z i ∈ gafStageTags L Z st
  · rw [cgpProjMap_apply_of_mem L Z hmem]
    have hb := cgpGlobalMap_markerBlock_GAF2 L Z i q
    rw [h0, mul_zero, zero_smul] at hb
    exact withLp_prod_ext_KC4 hb.1 hb.2
  · exact cgpProjMap_apply_of_not_mem_SGP4 L Z hmem q

end Models

namespace Gaf02ChainE

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X]
  [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
    V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- The model preimage of a reference chart lies within the (AS) range of the reference:
`ρ(a) ≥ (4/5)ρ(q)` for `q ∈ B(a, D_a ρ(a))`. -/
theorem ref_ge_CFSB (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4)
    (a : CGPMarkerIndex P.toLocalChartFamily) {q : X}
    (hq : q ∈ ball (cgpMarkerCentre P.toLocalChartFamily a)
      (cgpMarkerDomain P.toLocalChartFamily a * ρ (cgpMarkerCentre P.toLocalChartFamily a))) :
    4 / 5 * ρ q ≤ ρ (cgpMarkerCentre P.toLocalChartFamily a) := by
  have h := cgpMarker_domain_scale_CFSB P.toLocalChartFamily hΔ hΛ hsmall a q
    (ball_subset_closedBall hq)
  linarith [h.2]

/-- **CFS28** (`lem:fibration-all-contributors-locality`) on the enhanced chain, stage `st`. For
`x = π_st𝓔⁰(p) ∈ S_st`, every centre `u ∈ S_st` whose closed `80b r(u)` ball meets `B(x, 8b r(x))`
(`b = Ξ_st⁻¹`, `r = Σ_st ρ ∘ sel_st`, arbitrary radius preimages), and every retained block `i`
with `R_i < ρ(p)/16`: the WHOLE `i` block of `u` is zero and `L_u` lies in the kernel of the WHOLE
`i` block (AL). -/
theorem cfs28_row_CFSB (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) (st : Fin 3) {p : X}
    {x u : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hpx : cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st) p =
      x) (hx : x ∈ gafCloud P.toLocalChartFamily P.zero st)
    (hu : u ∈ gafCloud P.toLocalChartFamily P.zero st)
    (hmeet : (closedBall u (80 * (Ξ st)⁻¹ * (S st * ρ (C.toChain.sel st u))) ∩
      ball x (8 * (Ξ st)⁻¹ * (S st * ρ (C.toChain.sel st x)))).Nonempty)
    (i : CGPMarkerIndex P.toLocalChartFamily)
    (hi : ρ (cgpMarkerCentre P.toLocalChartFamily i) < ρ p / 16) :
    u (cgpMarkerTag P.toLocalChartFamily P.zero i) = 0 ∧
      ∀ w ∈ C.toChain.plane st u, w (cgpMarkerTag P.toLocalChartFamily P.zero i) = 0 := by
  classical
  obtain ⟨hΛ, hΔ, -, -, hLΛ, -, -, -, hσs, hσs1, -⟩ := C.toChain.std
  obtain ⟨hnum, -⟩ := C.toChain.numbers
  obtain ⟨hΞ, hsg, hmo, -⟩ := hnum st
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := C.toChain.small_BAS
  have hΔ0 : 0 < Δ := by linarith
  have hdat := gafMarker_data_GAF7 P.toLocalChartPackets hΛ hΔ hLΛ hσs hσs1
  -- the model preimage `q` of `u` and the scale chain
  have key : ∀ q : X, cgpProjMap P.toLocalChartFamily P.zero
      (gafStageTags P.toLocalChartFamily P.zero st) q = u →
      27 / 125 * ρ p ≤ ρ q ∧ cgpMarkerCutoff P.toLocalChartFamily i q = 0 := by
    intro q hq
    have hr := ratio_chain_CFSB P.toLocalChartFamily P.zero hΔ hΛ hsmall st (C.toChain.sel st)
      (C.toChain.hsel st) hΞ hsg hmo hpx hx hu hq hmeet
    refine ⟨hr, le_antisymm ?_ (hdat.1 i q)⟩
    by_contra hpos
    have h := hdat.2.2 i q (lt_of_not_ge hpos)
    have hp := hρ p
    nlinarith [h.2]
  have hcore : ∀ q : X, cgpProjMap P.toLocalChartFamily P.zero
      (gafStageTags P.toLocalChartFamily P.zero st) q = u →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        q ∈ ball (cgpMarkerCentre P.toLocalChartFamily a)
          (cgpMarkerDomain P.toLocalChartFamily a * ρ (cgpMarkerCentre P.toLocalChartFamily a)) →
        ρ (cgpMarkerCentre P.toLocalChartFamily i) ≤
          1 / 2 * ρ (cgpMarkerCentre P.toLocalChartFamily a) := by
    intro q hq a ha
    have h1 := (key q hq).1
    have h2 := ref_ge_CFSB hΔ hΛ hsmall a ha
    have hp := hρ p
    nlinarith
  have hsel := C.toChain.hsel st
  have hΔ' : (0 : ℝ) ≤ Δ := hΔ0.le
  refine ⟨?_, ?_⟩
  · have hq := hsel u (gafCloud_subset_enlarged P.toLocalChartFamily P.zero hΔ' st hu)
    rw [← hq]
    exact projMap_block_eq_zero_CFSB P.toLocalChartFamily P.zero st i _ (key _ hq).2
  · intro w hw
    fin_cases st
    · have hu0 : u ∈ gafCloud P.toLocalChartFamily P.zero 0 := hu
      change w ∈ C.toChain.plane 0 u at hw
      rw [C.plane_eq.1] at hw
      have hdef : C.planes₀.plane u = stagePlane_PLN C.planes₀.model C.planes₀.prune
          C.planes₀.coord (C.planes₀.ref ⟨u, hu0⟩) (C.planes₀.pre ⟨u, hu0⟩) := by
        simp only [StagePlaneData_PLN.plane, hu0, ↓reduceDIte]
      rw [hdef] at hw
      obtain ⟨h, rfl⟩ := hw
      obtain ⟨hb, -, hpu⟩ := C.planes₀.pre_spec ⟨u, hu0⟩
      have hle := hcore _ hpu (.inl (C.planes₀.ref ⟨u, hu0⟩)) hb
      refine block_fderiv_eq_zero_of_zero_CFSB _ _ (fun v => ?_) _ h
      change _ ≤ 1 / 2 * ρ (C.planes₀.ref ⟨u, hu0⟩).1 at hle
      exact C.planes₀.small_block_zero _ i (by linarith) v
    · have hu0 : u ∈ gafCloud P.toLocalChartFamily P.zero 1 := hu
      change w ∈ C.toChain.plane 1 u at hw
      rw [C.plane_eq.2.1] at hw
      have hdef : C.planes₁.plane u = stagePlane_PLN C.planes₁.model C.planes₁.prune
          C.planes₁.coord (C.planes₁.ref ⟨u, hu0⟩) (C.planes₁.pre ⟨u, hu0⟩) := by
        simp only [StagePlaneData_PLN.plane, hu0, ↓reduceDIte]
      rw [hdef] at hw
      obtain ⟨h, rfl⟩ := hw
      obtain ⟨hb, -, -, hpu⟩ := C.planes₁.pre_spec ⟨u, hu0⟩
      have hle := hcore _ hpu (.inr (.inr (C.planes₁.ref ⟨u, hu0⟩))) hb
      refine block_fderiv_eq_zero_of_zero_CFSB _ _ (fun v => ?_) _ h
      rw [Function.comp_apply, C.planes₁.prune_eq, C.planes₁.model_eq,
        ContinuousLinearMap.id_apply]
      exact egpModel_smallBlock_CFSB P.toLocalChartFamily P.zero hΔ0 hΛ hLΛ _ _ _ i
        (by
          change _ ≤ 1 / 2 * ρ (C.planes₁.ref ⟨u, hu0⟩).1 at hle
          have := hρ (C.planes₁.ref ⟨u, hu0⟩).1
          linarith) v
    · have hu0 : u ∈ gafCloud P.toLocalChartFamily P.zero 2 := hu
      change w ∈ C.toChain.plane 2 u at hw
      rw [C.plane_eq.2.2] at hw
      have hdef : C.planes₂.plane u = stagePlane_PLN C.planes₂.model C.planes₂.prune
          C.planes₂.coord (C.planes₂.ref ⟨u, hu0⟩) (C.planes₂.pre ⟨u, hu0⟩) := by
        simp only [StagePlaneData_PLN.plane, hu0, ↓reduceDIte]
      rw [hdef] at hw
      obtain ⟨h, rfl⟩ := hw
      obtain ⟨hb, -, hpu⟩ := C.planes₂.pre_spec ⟨u, hu0⟩
      have hle := hcore _ hpu (.inr (.inl (C.planes₂.ref ⟨u, hu0⟩))) (by
        change _ ∈ ball (C.planes₂.ref ⟨u, hu0⟩).1 (1000000 * Δ * ρ (C.planes₂.ref ⟨u, hu0⟩).1)
        convert hb using 2
        norm_num)
      refine block_fderiv_eq_zero_of_zero_CFSB _ _ (fun v => ?_) _ h
      rw [Function.comp_apply, C.planes₂.prune_eq, C.planes₂.model_eq,
        ContinuousLinearMap.id_apply]
      exact sgpFull_smallBlock_CFSB P.toLocalChartFamily P.zero hΔ0 hΛ hLΛ _ _ _ _ _ i
        (by
          change _ ≤ 1 / 2 * ρ (C.planes₂.ref ⟨u, hu0⟩).1 at hle
          have := hρ (C.planes₂.ref ⟨u, hu0⟩).1
          linarith) v

end Gaf02ChainE

end DifferentialGeometry.Geometry.Collapse

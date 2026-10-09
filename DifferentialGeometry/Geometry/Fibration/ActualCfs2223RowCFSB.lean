import DifferentialGeometry.Geometry.Fibration.ActualStageChain
import DifferentialGeometry.Geometry.Metric.UniformCutoffConsumer

/-!
# CFS22 and CFS23 on the actual data: the uniform cutoffs at the chain's own preceding maps

Blueprint `master207B.tex`, CFS22 (`lem:fibration-uniform-axis-cutoff`, B:3264–3351) and CFS23
(`prop:fibration-uniform-edge-cutoff`, B:3353–3475). On the actual packets
`P : LocalChartPackets …` (ancestor of `LocalChartPacketsC14Z`) with `F = 𝓔⁰ = cgpGlobalMap`:

* the row's hypotheses on the ORIGINAL data hold for the actual slim family (`ℓ = 10⁵Δ`) and edge
  family (`ℓ = Δ`): block formula `F_i = (R_iζ_iη_i, R_iζ_i)`, `0 ≤ ζ_i ≤ 1`, zero off `U_i`, at most
  `N = gafMultiplicity` positive markers, `ζ_i > 0 ⇒ 3R_i/4 ≤ ρ ≤ 5R_i/4, |η_i| ≤ 9ℓ`, the slim
  plateau `ζ_i = 1` on `|η_i| < 6ℓ`, and CFS23's edge identity `ζ_i = g(t/Δ)` on `|η_i| < 8Δ`
  with the `E'` block `(ρtz₀, ρz₀)`;
* the PRECEDING MAP is the actual preceding adjustment of the chain (`f = g₂` for the slim stage,
  `f = g₁` for the edge stage; review 43), and its two hypotheses `|f − F| ≤ (4κ/5)ρ` and (ZM)
  are PRODUCED by the chain (`Gaf02Chain.core_analytic`, not assumed);
* the conclusions: smoothness (on `{x_ρ > 0}` for the edge cutoff), values in `[0, 1]`, the EXACT
  plateau on `f` of the threshold-`6` union, CLOSED-support localization to the threshold-`7`
  union, `‖Dψ‖ ≤ C/ρ(p)` on every segment `[F p, f p]`, with `C = 10⁴(N+1)²P⁴`,
  `κ = 1/(1000(N+1)P²)` (`P = cgpProfileBound`; no `ℓ`, `Δ`, index count or dimension), and for
  the slim formula the factorization through `Q₃` (and `Q₂`).

Main theorems: `Gaf02Chain.cfs22_row_CFSB`, `Gaf02Chain.cfs23_row_CFSB`.
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

section Factor

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

variable (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

/-- The slim tags are tags of `Q₂` and of `Q₃`. -/
theorem slimTag_mem_stageTags_CFSB (j : L.slim.finite_centres.toFinset) :
    (.inr (.inl j) : CGPTag L Z) ∈ gafStageTags L Z 1 ∧
      (.inr (.inl j) : CGPTag L Z) ∈ gafStageTags L Z 2 := by
  constructor
  · change _ ∈ cgpQ2Tags L Z
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  · change _ ∈ cgpQ3Tags L Z
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩

open Classical in
/-- A slim block is unchanged by `π_{Q₂}` and by `π_{Q₃}`. -/
theorem gafSlim_stageQ_CFSB (j : L.slim.finite_centres.toFinset) {st : Fin 3}
    (hst : st = 1 ∨ st = 2) (z : BlockSpace (fun _ : CGPTag L Z => ℝ²)) :
    gafSlimVector L Z j ((gafStageQ L Z st).starProjection z) = gafSlimVector L Z j z ∧
      gafSlimMarker L Z j ((gafStageQ L Z st).starProjection z) = gafSlimMarker L Z j z := by
  have hmem : (.inr (.inl j) : CGPTag L Z) ∈ gafStageTags L Z st := by
    rcases hst with rfl | rfl
    · exact (slimTag_mem_stageTags_CFSB L Z j).1
    · exact (slimTag_mem_stageTags_CFSB L Z j).2
  rw [gafStageQ_starProjection]
  constructor
  · change (blockRestrict (gafStageTags L Z st) z (.inr (.inl j))).fst = (z (.inr (.inl j))).fst
    simp only [blockRestrict_apply, hmem, ↓reduceIte]
  · change (blockRestrict (gafStageTags L Z st) z (.inr (.inl j))).snd = (z (.inr (.inl j))).snd
    simp only [blockRestrict_apply, hmem, ↓reduceIte]

/-- **The slim formula factors through `Q₃` and `Q₂`** (CFS22's last clause; FC32): `ψ₃ ∘ π_{Q₃} =
ψ₃` and `ψ₃ ∘ π_{Q₂} = ψ₃`. -/
theorem gafStageThreeCutoff_factor_CFSB :
    gafStageThreeCutoff L Z ∘ (gafStageQ L Z 2).starProjection = gafStageThreeCutoff L Z ∧
      gafStageThreeCutoff L Z ∘ (gafStageQ L Z 1).starProjection = gafStageThreeCutoff L Z :=
  ⟨cfsUniformAxisCutoff_comp_of_factor _ _ _ _ _ _
      (fun j z => (gafSlim_stageQ_CFSB L Z j (Or.inr rfl) z).1)
      (fun j z => (gafSlim_stageQ_CFSB L Z j (Or.inr rfl) z).2),
    cfsUniformAxisCutoff_comp_of_factor _ _ _ _ _ _
      (fun j z => (gafSlim_stageQ_CFSB L Z j (Or.inl rfl) z).1)
      (fun j z => (gafSlim_stageQ_CFSB L Z j (Or.inl rfl) z).2)⟩

end Factor

namespace Gaf02Chain

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
  {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- The chain's preceding maps carry CFS31's boxed contract: `|g_j − F| ≤ (4κ/5)ρ` (`j = 1, 2`)
and (ZM) for every retained marker. -/
theorem prior_contract_CFSB (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    (∀ q, ‖C.g₁ q - cgpGlobalMap P.toLocalChartFamily P.zero q‖ ≤ 4 * gafKappa / 5 * ρ q) ∧
    (∀ q, ‖C.g₂ q - cgpGlobalMap P.toLocalChartFamily P.zero q‖ ≤ 4 * gafKappa / 5 * ρ q) ∧
    (∀ (j : P.edge.finite_centres.toFinset) p, P.edge.cutoff j.1 p = 0 →
      |gafEdgeMarker P.toLocalChartFamily P.zero j (C.g₁ p)| ≤ ρ j.1 / 32) ∧
    ∀ (j : P.slim.finite_centres.toFinset) p, P.slim.cutoff j.1 p = 0 →
      |gafSlimMarker P.toLocalChartFamily P.zero j (C.g₂ p)| ≤ ρ j.1 / 32 := by
  obtain ⟨-, -, -, -, hc₀κ, -, -, -, -, hc₁κ, -, -, -, -⟩ := C.numbers
  obtain ⟨-, -, -, k4, k5, -, -, -, -, -, -, -, k13, k14, -, -⟩ := C.core_analytic
  exact ⟨fun q => (k4 q).le.trans (mul_le_mul_of_nonneg_right hc₀κ (hρ q).le),
    fun q => (k5 q).le.trans (mul_le_mul_of_nonneg_right hc₁κ (hρ q).le),
    (gaf02_familyZM_GAF7 P _ k13).1, (gaf02_familyZM_GAF7 P _ k14).2⟩

/-- **CFS22** (`lem:fibration-uniform-axis-cutoff`) on the actual slim family (`ℓ = 10⁵Δ`) at the
chain's preceding map `f = g₂`. Original data: the slim blocks `(R_jζ_jη_j, R_jζ_j)` of `𝓔⁰`,
`ζ_j ∈ [0, 1]` vanishing off `U_j = B(c_j, 10⁶ΔR_j)`, at most `N` positive markers, (AS) and
`|η_j| ≤ 9ℓ` at positive markers, `ζ_j = 1` on `U_j ∩ {|η_j| < 6ℓ}`. Preceding map (PRODUCED by the
chain): `|g₂ − F| ≤ (4κ/5)ρ` and (ZM). Conclusions for `ψ_s = gafStageThreeCutoff`: smooth,
`[0,1]`-valued, one on `g₂` of the threshold-`6ℓ` union, closed support along `g₂(M)` only from the
threshold-`7ℓ` union, `‖Dψ_s‖ ≤ C/ρ(p)` on every segment `[F p, g₂ p]`, `ψ_s` factors through
`Q₃` (and `Q₂`); `C = 10⁴(N+1)²P⁴`, `κ = 1/(1000(N+1)P²)`. -/
theorem cfs22_row_CFSB (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    (∀ (j : P.slim.finite_centres.toFinset) p,
      gafSlimVector P.toLocalChartFamily P.zero j (cgpGlobalMap P.toLocalChartFamily P.zero p) =
          (ρ j.1 * P.slim.cutoff j.1 p) •
            planeAxis ((P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p) ∧
        gafSlimMarker P.toLocalChartFamily P.zero j (cgpGlobalMap P.toLocalChartFamily P.zero p) =
          ρ j.1 * P.slim.cutoff j.1 p) ∧
    (∀ (j : P.slim.finite_centres.toFinset) p, P.slim.cutoff j.1 p ∈ Icc (0 : ℝ) 1 ∧
      (p ∉ ball j.1 (1000000 * Δ * ρ j.1) → P.slim.cutoff j.1 p = 0)) ∧
    (∀ p, (Finset.univ.filter fun j : P.slim.finite_centres.toFinset =>
      0 < P.slim.cutoff j.1 p).card ≤ gafMultiplicity) ∧
    (∀ (j : P.slim.finite_centres.toFinset) p, 0 < P.slim.cutoff j.1 p →
      3 / 4 * ρ j.1 ≤ ρ p ∧ ρ p ≤ 5 / 4 * ρ j.1 ∧
        |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| ≤ 9 * (10 ^ 5 * Δ)) ∧
    (∀ (j : P.slim.finite_centres.toFinset) p, p ∈ ball j.1 (1000000 * Δ * ρ j.1) →
      |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| < 6 * (10 ^ 5 * Δ) →
      P.slim.cutoff j.1 p = 1) ∧
    (∀ q, ‖C.g₂ q - cgpGlobalMap P.toLocalChartFamily P.zero q‖ ≤ 4 * gafKappa / 5 * ρ q) ∧
    (∀ (j : P.slim.finite_centres.toFinset) p, P.slim.cutoff j.1 p = 0 →
      |gafSlimMarker P.toLocalChartFamily P.zero j (C.g₂ p)| ≤ ρ j.1 / 32) ∧
    ContDiff ℝ ∞ (gafStageThreeCutoff P.toLocalChartFamily P.zero) ∧
    (∀ z, (gafStageThreeCutoff P.toLocalChartFamily P.zero) z ∈ Icc (0 : ℝ) 1) ∧
    (∀ p, (∃ j : P.slim.finite_centres.toFinset, p ∈ ball j.1 (1000000 * Δ * ρ j.1) ∧
        |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| < 6 * (10 ^ 5 * Δ)) →
      (gafStageThreeCutoff P.toLocalChartFamily P.zero) (C.g₂ p) = 1) ∧
    (∀ p, C.g₂ p ∈ tsupport (gafStageThreeCutoff P.toLocalChartFamily P.zero) →
      ∃ j : P.slim.finite_centres.toFinset, p ∈ ball j.1 (1000000 * Δ * ρ j.1) ∧
        |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| <
          7 * (10 ^ 5 * Δ)) ∧
    (∀ p, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (gafStageThreeCutoff P.toLocalChartFamily P.zero) ((1 - t) • cgpGlobalMap
          P.toLocalChartFamily P.zero p + t • C.g₂ p)‖ ≤ gafCutoffConstant / ρ p) ∧
    (gafStageThreeCutoff P.toLocalChartFamily P.zero ∘
        (gafStageQ P.toLocalChartFamily P.zero 2).starProjection =
      gafStageThreeCutoff P.toLocalChartFamily P.zero) ∧
    (gafStageThreeCutoff P.toLocalChartFamily P.zero ∘
        (gafStageQ P.toLocalChartFamily P.zero 1).starProjection =
      gafStageThreeCutoff P.toLocalChartFamily P.zero) ∧
    gafCutoffConstant = 10 ^ 4 * ((gafMultiplicity : ℝ) + 1) ^ 2 * cgpProfileBound ^ 4 ∧
    gafKappa = 1 / (1000 * ((gafMultiplicity : ℝ) + 1) * cgpProfileBound ^ 2) := by
  obtain ⟨hΛ, hΔ, hμ, hτ, hLΛ, hLmax, he, hT, hσs, hσs1, -, -, -⟩ := C.std
  have hΔ0 : 0 < Δ := by linarith
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by nlinarith
  obtain ⟨-, hpert, -, hZM⟩ := C.prior_contract_CFSB
  obtain ⟨-, -, b1, b2, b3, b4, b5⟩ := C.cutoff_bindings
  have hfac := gafStageThreeCutoff_factor_CFSB P.toLocalChartFamily P.zero
  refine ⟨gafSlim_block_GAF2 P.toLocalChartFamily P.zero, fun j p => ⟨?_, fun hp => ?_⟩,
    gafSlim_count_GAF2 P hΛ hΔ hμ hτ hLΛ hLmax he hT, fun j p hpos => ?_, fun j p hp hη => ?_,
    hpert, hZM, b1, b2, b3, b4, b5, hfac.1, hfac.2, rfl, rfl⟩
  · have hj := (Set.Finite.mem_toFinset _).mp j.2
    rw [slimFamily_cutoff_eq_KA2 P.toLocalChartFamily hj]
    exact (P.slim.centre j.1 hj).cutoff_mem_Icc p
  · by_contra h
    exact hp (cgpMarkerCutoff_ne_zero P.toLocalChartFamily hΔ0 (.inr (.inl j)) p h)
  · have hj := (Set.Finite.mem_toFinset _).mp j.2
    obtain ⟨h1, h2⟩ := cgpMarkerCutoff_scale_GAF2 P.toLocalChartFamily P.zero hΔ hσs hσs1 hΛ
      hsmall (.inr (.inl j)) p hpos
    change 3 * ρ j.1 / 4 ≤ ρ p at h1
    change ρ p ≤ 5 * ρ j.1 / 4 at h2
    have hpos' : 0 < (P.slim.centre j.1 hj).cutoff p := by
      rw [← slimFamily_cutoff_eq_KA2 P.toLocalChartFamily hj]
      exact hpos
    have h3 := (P.slim.centre j.1 hj).abs_coord_le_of_mem_tsupport (subset_tsupport _ hpos'.ne')
    refine ⟨by linarith, by linarith, by linarith⟩
  · have hj := (Set.Finite.mem_toFinset _).mp j.2
    rw [slimFamily_cutoff_eq_KA2 P.toLocalChartFamily hj]
    refine (P.slim.centre j.1 hj).cutoff_eq_one_of_abs_coord_le ?_ (by linarith)
    convert hp using 2
    norm_num

/-- **CFS23** (`prop:fibration-uniform-edge-cutoff`) on the actual edge family (`ℓ = Δ ≥ 1`) at the
chain's preceding map `f = g₁`. Original data: the edge blocks `(R_jζ_jη_j, R_jζ_j)` of `𝓔⁰`,
`ζ_j ∈ [0, 1]` vanishing off `U_j = B(c_j, 100ΔR_j)`, at most `N` positive markers, (AS) and
`|η_j| ≤ 9Δ` at positive markers, the scale coordinate `x_ρ(F) = ρ`, the `E'` block
`|u_{E'}| = ρtz₀`, `v_{E'} = ρz₀` with `z₀ = h(t/Δ)χ_{1/2,1}(Σζ_i)`, and the actual edge identity
`ζ_j = g(t/Δ) = 1 − χ_{8,9}(t/Δ)` on `U_j ∩ {|η_j| < 8Δ}` (hence `ζ_j = 1` when also `t < 6Δ`).
Preceding map (PRODUCED by the chain): `|g₁ − F| ≤ (4κ/5)ρ` and (ZM). Conclusions for
`ψ_e = gafStageTwoCutoff`: smooth on `O = {x_ρ > 0}`, `[0,1]`-valued, one on `g₁` of the union
`{|η_j| < 6Δ, t < 6Δ}`, closed support along `g₁(M)` only from `{|η_j| < 7Δ, t < 7Δ}`, and on
every segment `[F p, g₁ p]` the scale coordinate is positive and `‖Dψ_e‖ ≤ C/ρ(p)`. -/
theorem cfs23_row_CFSB (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    (∀ (j : P.edge.finite_centres.toFinset) p,
      gafEdgeVector P.toLocalChartFamily P.zero j (cgpGlobalMap P.toLocalChartFamily P.zero p) =
          (ρ j.1 * P.edge.cutoff j.1 p) • planeAxis (P.edge.coord j.1 p) ∧
        gafEdgeMarker P.toLocalChartFamily P.zero j (cgpGlobalMap P.toLocalChartFamily P.zero p) =
          ρ j.1 * P.edge.cutoff j.1 p) ∧
    (∀ (j : P.edge.finite_centres.toFinset) p, P.edge.cutoff j.1 p ∈ Icc (0 : ℝ) 1 ∧
      (p ∉ ball j.1 (100 * Δ * ρ j.1) → P.edge.cutoff j.1 p = 0)) ∧
    (∀ p, (Finset.univ.filter fun j : P.edge.finite_centres.toFinset =>
      0 < P.edge.cutoff j.1 p).card ≤ gafMultiplicity) ∧
    (∀ (j : P.edge.finite_centres.toFinset) p, 0 < P.edge.cutoff j.1 p →
      3 / 4 * ρ j.1 ≤ ρ p ∧ ρ p ≤ 5 / 4 * ρ j.1 ∧ |P.edge.coord j.1 p| ≤ 9 * Δ) ∧
    (∀ p, gafScaleMarker P.toLocalChartFamily P.zero (cgpGlobalMap P.toLocalChartFamily P.zero p) =
      ρ p) ∧
    (∀ p, ‖gafHeightVector P.toLocalChartFamily P.zero (cgpGlobalMap P.toLocalChartFamily P.zero p)‖ =
        ρ p * cgpHeight P.toLocalChartFamily p *
          (cgpEdgeH (cgpHeight P.toLocalChartFamily p / Δ) * cfsRamp lc87EdgeTransition (1 / 2) 1
            (∑ j : P.toLocalChartFamily.edge.finite_centres.toFinset,
              P.toLocalChartFamily.edge.cutoff j.1 p)) ∧
      gafHeightMarker P.toLocalChartFamily P.zero (cgpGlobalMap P.toLocalChartFamily P.zero p) =
        ρ p * (cgpEdgeH (cgpHeight P.toLocalChartFamily p / Δ) *
          cfsRamp lc87EdgeTransition (1 / 2) 1
            (∑ j : P.toLocalChartFamily.edge.finite_centres.toFinset,
              P.toLocalChartFamily.edge.cutoff j.1 p))) ∧
    (∀ (j : P.edge.finite_centres.toFinset) p, p ∈ ball j.1 (100 * Δ * ρ j.1) →
      |P.edge.coord j.1 p| < 8 * Δ →
      P.edge.cutoff j.1 p =
        1 - cfsRamp lc87EdgeTransition 8 9 (cgpHeight P.toLocalChartFamily p / Δ)) ∧
    (∀ q, ‖C.g₁ q - cgpGlobalMap P.toLocalChartFamily P.zero q‖ ≤ 4 * gafKappa / 5 * ρ q) ∧
    (∀ (j : P.edge.finite_centres.toFinset) p, P.edge.cutoff j.1 p = 0 →
      |gafEdgeMarker P.toLocalChartFamily P.zero j (C.g₁ p)| ≤ ρ j.1 / 32) ∧
    ContDiffOn ℝ ∞ (gafStageTwoCutoff P.toLocalChartFamily P.zero)
        {z | 0 < gafScaleMarker P.toLocalChartFamily P.zero z} ∧
    (∀ z, (gafStageTwoCutoff P.toLocalChartFamily P.zero) z ∈ Icc (0 : ℝ) 1) ∧
    (∀ p, (∃ j : P.edge.finite_centres.toFinset, p ∈ ball j.1 (100 * Δ * ρ j.1) ∧
        |P.edge.coord j.1 p| < 6 * Δ ∧ cgpHeight P.toLocalChartFamily p < 6 * Δ) →
      (gafStageTwoCutoff P.toLocalChartFamily P.zero) (C.g₁ p) = 1) ∧
    (∀ p, C.g₁ p ∈ tsupport (gafStageTwoCutoff P.toLocalChartFamily P.zero) →
      ∃ j : P.edge.finite_centres.toFinset, p ∈ ball j.1 (100 * Δ * ρ j.1) ∧
        |P.edge.coord j.1 p| < 7 * Δ ∧ cgpHeight P.toLocalChartFamily p < 7 * Δ) ∧
    (∀ p, ∀ t ∈ Icc (0 : ℝ) 1,
      0 < gafScaleMarker P.toLocalChartFamily P.zero ((1 - t) • cgpGlobalMap P.toLocalChartFamily
          P.zero p + t • C.g₁ p) ∧
      ‖fderiv ℝ (gafStageTwoCutoff P.toLocalChartFamily P.zero) ((1 - t) • cgpGlobalMap
          P.toLocalChartFamily P.zero p + t • C.g₁ p)‖ ≤ gafCutoffConstant / ρ p) ∧
    gafCutoffConstant = 10 ^ 4 * ((gafMultiplicity : ℝ) + 1) ^ 2 * cgpProfileBound ^ 4 ∧
    gafKappa = 1 / (1000 * ((gafMultiplicity : ℝ) + 1) * cgpProfileBound ^ 2) := by
  obtain ⟨hΛ, hΔ, hμ, hτ, hLΛ, hLmax, he, hT, hσs, hσs1, -, -, -⟩ := C.std
  have hΔ0 : 0 < Δ := by linarith
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by nlinarith
  obtain ⟨hpert, -, hZM, -⟩ := C.prior_contract_CFSB
  obtain ⟨-, ⟨b1, b2, b3, b4, b5⟩, -⟩ := C.cutoff_bindings
  refine ⟨gafEdge_block_GAF2 P.toLocalChartFamily P.zero, fun j p => ⟨cgpEdgeCutoff_mem_Icc
    P.toLocalChartFamily hΔ0 j.1 p, fun hp => ?_⟩,
    gafEdge_count_GAF2 P hΛ hΔ hμ hτ hLΛ hLmax he hT, fun j p hpos => ?_,
    gafScaleMarker_globalMap_GAF2 P.toLocalChartFamily P.zero,
    gafHeight_block_GAF2 P.toLocalChartFamily P.zero,
    fun j p hp hη => cgp01_edge_identity P.toLocalChartFamily ((Set.Finite.mem_toFinset _).mp j.2)
      hp hη hΔ0, hpert, hZM, b1, b2, b3, b4, b5, rfl, rfl⟩
  · by_contra h
    exact hp (cgpMarkerCutoff_ne_zero P.toLocalChartFamily hΔ0 (.inr (.inr j)) p h)
  · obtain ⟨h1, h2⟩ := cgpMarkerCutoff_scale_GAF2 P.toLocalChartFamily P.zero hΔ hσs hσs1 hΛ
      hsmall (.inr (.inr j)) p hpos
    obtain ⟨-, -, h3, -⟩ := P.edge.mem_of_cutoff_ne_zero hΔ0 hpos.ne'
    change 3 * ρ j.1 / 4 ≤ ρ p at h1
    change ρ p ≤ 5 * ρ j.1 / 4 at h2
    exact ⟨by linarith, by linarith, h3.le⟩

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse

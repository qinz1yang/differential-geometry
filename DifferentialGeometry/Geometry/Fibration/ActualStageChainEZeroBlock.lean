import DifferentialGeometry.Geometry.Fibration.ActualStageChainZeroBlock
import DifferentialGeometry.Geometry.Fibration.ActualStageChainE
import DifferentialGeometry.Geometry.Fibration.ActualStagePlaneZeroBlock

/-!
# ZSP01 closed on `Gaf02ChainE`: zero blocks stay isolated through the stages

Blueprint `master207B.tex`, ZSP01 (B:6323); dispositions D59-2 (ZB* derived on the enhanced
planes), D66-8
(ZSP01 stage part needs ZB*), lead decision 2026-10-05 (ZSP01 closes on `Gaf02ChainE`).

* KERNEL (stage propagation, hypothesis `hZB` in the form ZB* supplies — with the localization
  `x = π_st𝓔⁰(p) ∈ S_st`): `Gaf02Chain.zsp01_slot_zero_hx_GAF8`,
  `Gaf02Chain.zsp01_stage_step_hx_GAF8`,
  `Gaf02Chain.zsp01_ZI_hx_GAF8`, `Gaf02Chain.zsp01_ZE_hx_GAF8` (as in `ActualStageChainZeroBlock`,
  whose
  `hZB` omits the localization and is therefore not dischargeable by ZB*; those statements stay as
  tiers).
* CLOSURE: `Gaf02ChainE.zsp01_hZB_GAF8` (ZB* of lane C14-PLANES, `A_j.zero_block`, on the chain's
own planes
  and radius selections via `plane_eq`, `sel_eq`, with `Σ_j < ε_j/10000` from the rough data),
  `Gaf02ChainE.zsp01_ZI_GAF8` ((ZI) at `g₁, g₂, E`), `Gaf02ChainE.zsp01_ZE_GAF8` ((ZE),
  `δ₀ = 200c₃/T`, at
  `g₁, g₂, E` and on `[𝓔⁰ p, E p]`, every `p`) — UNCONDITIONAL on `Ĉ`.
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

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14_GAF8Z {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_GAF8Z {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_GAF8Z {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **ZSP01, the stage map keeps the zero block** (kernel; `hZB`): at a (ZI) point `p` with
`x = π_st𝓔⁰(p)` in the stage cloud, the slot's map has zero `i` block on `B(x, Σρ(sel x))` (GAF03
locality
with `K = (ker J_i)ᗮ`, `c = 0`; contributors from `zsp01_contributor_zero_GAF8` and `hZB`). -/
theorem Gaf02Chain.zsp01_slot_zero_hx_GAF8 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) (st : Fin 3)
    (i : P.zero.finite_centres.toFinset)
    (hZB : ∀ st : Fin 3, ∀ p : X, 200 * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp
        i.2)).radius / T < ρ p →
      (gafStageQ P.toLocalChartFamily P.zero st).starProjection (cgpGlobalMap P.toLocalChartFamily
          P.zero p) ∈ gafCloud P.toLocalChartFamily P.zero st → ∀ y ∈ gafCloud P.toLocalChartFamily
              P.zero st,
      (closedBall y (80 * (Ξ st)⁻¹ * (S st * ρ (C.sel st y))) ∩
        ball ((gafStageQ P.toLocalChartFamily P.zero st).starProjection (cgpGlobalMap
            P.toLocalChartFamily P.zero p)) (8 * (Ξ st)⁻¹ * (S st * ρ (C.sel st ((gafStageQ
                P.toLocalChartFamily P.zero st).starProjection (cgpGlobalMap P.toLocalChartFamily
                    P.zero p)))))).Nonempty →
      C.plane st y ≤ LinearMap.ker ((blockProjCLM_PLN (V := fun _ : CGPTag P.toLocalChartFamily
          P.zero => ℝ²) (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero)) :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] WithLp 2 (ℝ² × ℝ))) {p
            : X} (hp : 200 * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius / T < ρ
                p)
    (hx : (gafStageQ P.toLocalChartFamily P.zero st).starProjection (cgpGlobalMap
        P.toLocalChartFamily P.zero p) ∈ gafCloud P.toLocalChartFamily P.zero st) {z : BlockSpace
            (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hz : z ∈ ball ((gafStageQ P.toLocalChartFamily P.zero st).starProjection (cgpGlobalMap
        P.toLocalChartFamily P.zero p)) (S st * ρ (C.sel st ((gafStageQ P.toLocalChartFamily P.zero
            st).starProjection (cgpGlobalMap P.toLocalChartFamily P.zero p))))) :
    (C.slot st).map z (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) = 0 := by
  have hcontrib : ∀ y ∈ gafCloud P.toLocalChartFamily P.zero st,
      (closedBall y (80 * (Ξ st)⁻¹ * (S st * ρ (C.sel st y))) ∩
        ball ((gafStageQ P.toLocalChartFamily P.zero st).starProjection (cgpGlobalMap
            P.toLocalChartFamily P.zero p)) (8 * (Ξ st)⁻¹ * (S st * ρ (C.sel st ((gafStageQ
                P.toLocalChartFamily P.zero st).starProjection (cgpGlobalMap P.toLocalChartFamily
                    P.zero p)))))).Nonempty →
      (LinearMap.ker ((blockProjCLM_PLN (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero)) :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] WithLp 2 (ℝ² ×
            ℝ)))ᗮ.starProjection y = 0 ∧
      C.plane st y ≤ (LinearMap.ker ((blockProjCLM_PLN (V := fun _ : CGPTag P.toLocalChartFamily
          P.zero => ℝ²) (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero)) :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] WithLp 2 (ℝ² × ℝ)))ᗮᗮ
            := fun y hy hwy =>
    zeroBlock_input_PLN _ _ (C.zsp01_contributor_zero_GAF8 st i hp rfl hx hy hwy) (hZB st p hp hx y
        hy hwy)
  have hloc' := ((C.slot st).bounds _ hx _ hz).2.2.2 _ 0 hcontrib
  rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal,
    LinearMap.mem_ker, ContinuousLinearMap.coe_coe, blockProjCLM_apply_PLN] at hloc'
  exact hloc'

/-- **ZSP01, one stage** (kernel; `hZB` = PLANES' whole-zero-block property of the contributing
planes):
if the stage input `w` has zero `i` block and, whenever the cutoff is nonzero at `w`, the stage
localizes
(`x = π_st𝓔⁰(p)` in the cloud, `π_st w ∈ B(x, Σρ(sel x))`), then the stage output
`adjustmentMap Q_st (π_st ∘ a_st) ψ w` has zero `i` block, for any cutoff `ψ`. -/
theorem Gaf02Chain.zsp01_stage_step_hx_GAF8 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) (st : Fin 3)
    (i : P.zero.finite_centres.toFinset)
    (hZB : ∀ st : Fin 3, ∀ p : X, 200 * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp
        i.2)).radius / T < ρ p →
      (gafStageQ P.toLocalChartFamily P.zero st).starProjection (cgpGlobalMap P.toLocalChartFamily
          P.zero p) ∈ gafCloud P.toLocalChartFamily P.zero st → ∀ y ∈ gafCloud P.toLocalChartFamily
              P.zero st,
      (closedBall y (80 * (Ξ st)⁻¹ * (S st * ρ (C.sel st y))) ∩
        ball ((gafStageQ P.toLocalChartFamily P.zero st).starProjection (cgpGlobalMap
            P.toLocalChartFamily P.zero p)) (8 * (Ξ st)⁻¹ * (S st * ρ (C.sel st ((gafStageQ
                P.toLocalChartFamily P.zero st).starProjection (cgpGlobalMap P.toLocalChartFamily
                    P.zero p)))))).Nonempty →
      C.plane st y ≤ LinearMap.ker ((blockProjCLM_PLN (V := fun _ : CGPTag P.toLocalChartFamily
          P.zero => ℝ²) (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero)) :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] WithLp 2 (ℝ² × ℝ))) {p
            : X} (hp : 200 * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius / T < ρ
                p) (ψ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → ℝ) (w :
                    BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hw : w (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) = 0)
    (hloc : ψ w ≠ 0 → (gafStageQ P.toLocalChartFamily P.zero st).starProjection (cgpGlobalMap
        P.toLocalChartFamily P.zero p) ∈ gafCloud P.toLocalChartFamily P.zero st ∧
      (gafStageQ P.toLocalChartFamily P.zero st).starProjection w ∈ ball ((gafStageQ
          P.toLocalChartFamily P.zero st).starProjection (cgpGlobalMap P.toLocalChartFamily P.zero
              p))
        (S st * ρ (C.sel st ((gafStageQ P.toLocalChartFamily P.zero st).starProjection
            (cgpGlobalMap P.toLocalChartFamily P.zero p))))) :
    adjustmentMap (gafStageQ P.toLocalChartFamily P.zero st)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero st).starProjection ((C.slot st).map y)) ψ w
          (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) = 0 := by
  rw [adjustmentMap_apply]
  by_cases hψ : ψ w = 0
  · rw [hψ, zero_smul, add_zero]
    exact hw
  obtain ⟨hx, hz⟩ := hloc hψ
  have ha := C.zsp01_slot_zero_hx_GAF8 st i hZB hp hx hz
  rw [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, gafStageQ_starProjection_zeroTag_GAF8 P st i,
    gafStageQ_starProjection_zeroTag_GAF8 P st i, ha, hw, sub_zero, smul_zero, add_zero]

/-- **ZSP01 (ZI) at every stage** (given `hZB`): `200R_i/T < ρ(p) ⇒` the `i` blocks of `g₁(p)`,
`g₂(p)`,
`E(p)` vanish (with the original half for `𝓔⁰`). -/
theorem Gaf02Chain.zsp01_ZI_hx_GAF8 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) (i : P.zero.finite_centres.toFinset)
    (hZB : ∀ st : Fin 3, ∀ p : X, 200 * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp
        i.2)).radius / T < ρ p →
      (gafStageQ P.toLocalChartFamily P.zero st).starProjection (cgpGlobalMap P.toLocalChartFamily
          P.zero p) ∈ gafCloud P.toLocalChartFamily P.zero st → ∀ y ∈ gafCloud P.toLocalChartFamily
              P.zero st,
      (closedBall y (80 * (Ξ st)⁻¹ * (S st * ρ (C.sel st y))) ∩
        ball ((gafStageQ P.toLocalChartFamily P.zero st).starProjection (cgpGlobalMap
            P.toLocalChartFamily P.zero p)) (8 * (Ξ st)⁻¹ * (S st * ρ (C.sel st ((gafStageQ
                P.toLocalChartFamily P.zero st).starProjection (cgpGlobalMap P.toLocalChartFamily
                    P.zero p)))))).Nonempty →
      C.plane st y ≤ LinearMap.ker ((blockProjCLM_PLN (V := fun _ : CGPTag P.toLocalChartFamily
          P.zero => ℝ²) (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero)) :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] WithLp 2 (ℝ² × ℝ))) {p
            : X} (hp : 200 * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius / T < ρ
                p) :
    C.g₁ p (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) = 0 ∧ C.g₂ p (.inr
        (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) = 0 ∧ C.E p (.inr (.inr (.inr
            (.inl i))) : CGPTag P.toLocalChartFamily P.zero) = 0 := by
  obtain ⟨-, hΔ, -, -, -, -, he, hT, -, -, -, -, hεr⟩ := C.std
  have hT0 : 0 < T := by linarith only [hT, hΔ]
  have h0 : cgpGlobalMap P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl i))) : CGPTag
      P.toLocalChartFamily P.zero) = 0 :=
    zsp01_original_zero_block_ZI P.toLocalChartPacketsR hT0 (by linarith only [he])
      (by linarith only [hεr.1]) i hp
  have tube := C.stage_input_mem_tube p
  have h1 : C.g₁ p (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) = 0 := by
    rw [(C.stage_formula 0 p).2.2.2.1, C.Ψ_eq.1]
    exact C.zsp01_stage_step_hx_GAF8 0 i hZB hp _ _ h0 fun hψ => tube.1 (subset_tsupport _ hψ)
  have h2 : C.g₂ p (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) = 0 := by
    rw [(C.stage_formula 0 p).2.2.2.2.1, C.Ψ_eq.2.1]
    exact C.zsp01_stage_step_hx_GAF8 1 i hZB hp _ _ h1 fun hψ => tube.2.1 (subset_tsupport _ hψ)
  have h3 : C.E p (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) = 0 := by
    rw [(C.stage_formula 0 p).2.2.2.2.2, C.Ψ_eq.2.2]
    exact C.zsp01_stage_step_hx_GAF8 2 i hZB hp _ _ h2 fun hψ => tube.2.2 (subset_tsupport _ hψ)
  exact ⟨h1, h2, h3⟩

/-- **ZSP01 (ZE)** (given `hZB`): with `δ₀ = 200c₃/T`, `‖J_i(f(p) − 𝓔⁰(p))‖ < δ₀R_i` for
`f = g₁, g₂, E` and
for every point of the segment `[𝓔⁰ p, E p]`, at EVERY `p` (no global bound on `ρ/R_i`). -/
theorem Gaf02Chain.zsp01_ZE_hx_GAF8 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) (i : P.zero.finite_centres.toFinset)
    (hZB : ∀ st : Fin 3, ∀ p : X, 200 * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp
        i.2)).radius / T < ρ p →
      (gafStageQ P.toLocalChartFamily P.zero st).starProjection (cgpGlobalMap P.toLocalChartFamily
          P.zero p) ∈ gafCloud P.toLocalChartFamily P.zero st → ∀ y ∈ gafCloud P.toLocalChartFamily
              P.zero st,
      (closedBall y (80 * (Ξ st)⁻¹ * (S st * ρ (C.sel st y))) ∩
        ball ((gafStageQ P.toLocalChartFamily P.zero st).starProjection (cgpGlobalMap
            P.toLocalChartFamily P.zero p)) (8 * (Ξ st)⁻¹ * (S st * ρ (C.sel st ((gafStageQ
                P.toLocalChartFamily P.zero st).starProjection (cgpGlobalMap P.toLocalChartFamily
                    P.zero p)))))).Nonempty →
      C.plane st y ≤ LinearMap.ker ((blockProjCLM_PLN (V := fun _ : CGPTag P.toLocalChartFamily
          P.zero => ℝ²) (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero)) :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] WithLp 2 (ℝ² × ℝ))) (p
            : X) :
    ‖C.g₁ p (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) - cgpGlobalMap
        P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily
            P.zero)‖ < 200 * c 2 / T * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp
                i.2)).radius ∧
    ‖C.g₂ p (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) - cgpGlobalMap
        P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily
            P.zero)‖ < 200 * c 2 / T * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp
                i.2)).radius ∧
    ‖C.E p (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) - cgpGlobalMap
        P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily
            P.zero)‖ < 200 * c 2 / T * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp
                i.2)).radius ∧
    ∀ z ∈ segment ℝ (cgpGlobalMap P.toLocalChartFamily P.zero p) (C.E p),
      ‖z (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) - cgpGlobalMap
          P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily
              P.zero)‖ < 200 * c 2 / T * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp
                  i.2)).radius := by
  obtain ⟨-, hΔ, -, -, -, -, he, hT, -, -, -, -, hεr⟩ := C.std
  obtain ⟨hnum, hv₁, -, -, -, -, hv₂, -, -, -, -, hv₃, -, -⟩ := C.numbers
  obtain ⟨hΞ₀, hS₀, -, -⟩ := hnum 0
  obtain ⟨hΞ₁, hS₁, -, -⟩ := hnum 1
  obtain ⟨hΞ₂, hS₂, -, -⟩ := hnum 2
  have hT0 : 0 < T := by linarith only [hT, hΔ]
  have hR := (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius_pos
  have hc0 : 0 < c 0 := lt_of_le_of_lt (by positivity) hv₁
  have hc1 : c 0 < c 1 := by
    have : 0 ≤ 5 / 3 * Ξ 1 * S 1 + (1 + Ξ 1) * c 0 := by positivity
    linarith only [this, hv₂]
  have hc2 : c 1 < c 2 := by
    have : 0 ≤ 5 / 3 * Ξ 2 * S 2 + (1 + Ξ 2) * c 1 := by
      have : 0 ≤ c 1 := by linarith only [hc0, hc1]
      positivity
    linarith only [this, hv₃]
  have hδ : 0 < 200 * c 2 / T * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius := by
    have : 0 < c 2 := by linarith only [hc0, hc1, hc2]
    positivity
  obtain ⟨-, -, -, k4, k5, k6, -⟩ := C.core_analytic
  have hbound : ∀ (f : X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) (cf : ℝ),
      cf ≤ c 2 →
      (∀ q, ‖f q - cgpGlobalMap P.toLocalChartFamily P.zero q‖ < cf * ρ q) →
      (200 * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius / T < ρ p → f p (.inr
          (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) = 0) →
      ‖f p (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) - cgpGlobalMap
          P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily
              P.zero)‖ < 200 * c 2 / T * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp
                  i.2)).radius := by
    intro f cf hcf herr hZI
    by_cases hp : 200 * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius / T < ρ p
    · have h0 : cgpGlobalMap P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl i))) : CGPTag
        P.toLocalChartFamily P.zero) = 0 :=
        zsp01_original_zero_block_ZI P.toLocalChartPacketsR hT0 (by linarith only [he])
          (by linarith only [hεr.1]) i hp
      rw [hZI hp, h0, sub_zero, norm_zero]
      exact hδ
    · replace hp := not_lt.mp hp
      have h1 : ‖f p (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) -
          cgpGlobalMap P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl i))) : CGPTag
              P.toLocalChartFamily P.zero)‖ ≤ ‖f p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ :=
                  by
        rw [← PiLp.sub_apply]
        exact PiLp.norm_apply_le _ _
      have h2 := herr p
      have hcf0 : 0 ≤ cf := by
        have := norm_nonneg (f p - cgpGlobalMap P.toLocalChartFamily P.zero p)
        by_contra hneg
        replace hneg := not_le.mp hneg
        have : cf * ρ p < 0 := mul_neg_of_neg_of_pos hneg (hρ p)
        linarith
      have h3 : cf * ρ p ≤ c 2 * (200 * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp
          i.2)).radius / T) :=
        mul_le_mul hcf hp (hρ p).le (by linarith only [hcf0, hcf])
      have h4 : c 2 * (200 * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius / T) =
          200 * c 2 / T * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius := by ring
      linarith only [h1, h2, h3, h4]
  have hZI := fun hp => C.zsp01_ZI_hx_GAF8 i hZB (p := p) hp
  have hE := hbound C.E (c 2) le_rfl k6 fun hp => (hZI hp).2.2
  refine ⟨hbound C.g₁ (c 0) (by linarith only [hc1, hc2]) k4 fun hp => (hZI hp).1,
    hbound C.g₂ (c 1) hc2.le k5 fun hp => (hZI hp).2.1, hE, fun z hz => ?_⟩
  obtain ⟨a', b', ha', hb', hab, rfl⟩ := hz
  have hsub : (a' • cgpGlobalMap P.toLocalChartFamily P.zero p + b' • C.E p) (.inr (.inr (.inr
      (.inl i))) : CGPTag P.toLocalChartFamily P.zero) - cgpGlobalMap P.toLocalChartFamily P.zero p
          (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) =
      b' • (C.E p (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) - cgpGlobalMap
          P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily
              P.zero)) := by
    rw [PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, smul_sub,
      show a' = 1 - b' by linarith only [hab], sub_smul, one_smul]
    abel
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb']
  have hb1 : b' ≤ 1 := by linarith only [ha', hab]
  calc b' * ‖C.E p (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) -
      cgpGlobalMap P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl i))) : CGPTag
          P.toLocalChartFamily P.zero)‖ ≤ ‖C.E p (.inr (.inr (.inr (.inl i))) : CGPTag
              P.toLocalChartFamily P.zero) - cgpGlobalMap P.toLocalChartFamily P.zero p (.inr (.inr
                  (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero)‖ :=
        mul_le_of_le_one_left (norm_nonneg _) hb1
    _ < 200 * c 2 / T * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius := hE

/-- **ZB\* on the chain object** (lane C14-PLANES' `zero_block`, on the chain's own planes and
radius
selections): the hypothesis `hZB` of the ZSP01 kernel holds for `Ĉ.toChain`. -/
theorem Gaf02ChainE.zsp01_hZB_GAF8 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) (i : P.zero.finite_centres.toFinset) :
    ∀ st : Fin 3, ∀ p : X, 200 * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius / T
        < ρ p →
      (gafStageQ P.toLocalChartFamily P.zero st).starProjection (cgpGlobalMap P.toLocalChartFamily
          P.zero p) ∈ gafCloud P.toLocalChartFamily P.zero st → ∀ y ∈ gafCloud P.toLocalChartFamily
              P.zero st,
      (closedBall y (80 * (Ξ st)⁻¹ * (S st * ρ (C.toChain.sel st y))) ∩
        ball ((gafStageQ P.toLocalChartFamily P.zero st).starProjection (cgpGlobalMap
            P.toLocalChartFamily P.zero p)) (8 * (Ξ st)⁻¹ * (S st * ρ (C.toChain.sel st ((gafStageQ
                P.toLocalChartFamily P.zero st).starProjection (cgpGlobalMap P.toLocalChartFamily
                    P.zero p)))))).Nonempty →
      C.toChain.plane st y ≤ LinearMap.ker ((blockProjCLM_PLN (V := fun _ : CGPTag
          P.toLocalChartFamily P.zero => ℝ²) (.inr (.inr (.inr (.inl i))) : CGPTag
              P.toLocalChartFamily P.zero)) :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] WithLp 2 (ℝ² × ℝ)) := by
  obtain ⟨hΛ, hΔ, -, -, hLΛ, -, he, hT, -, -, -, -, hεr⟩ := C.toChain.std
  obtain ⟨hnum, -⟩ := C.toChain.numbers
  have hT0 : 0 < T := by linarith only [hT, hΔ]
  have hZB₀ : ∀ p : X, 200 * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius / T < ρ
      p →
      (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (cgpGlobalMap P.toLocalChartFamily
          P.zero p) ∈ gafCloud P.toLocalChartFamily P.zero 0 → ∀ y ∈ gafCloud P.toLocalChartFamily
              P.zero 0,
      (closedBall y (80 * (Ξ 0)⁻¹ * (S 0 * ρ (C.toChain.sel 0 y))) ∩
        ball ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (cgpGlobalMap
            P.toLocalChartFamily P.zero p)) (8 * (Ξ 0)⁻¹ * (S 0 * ρ (C.toChain.sel 0 ((gafStageQ
                P.toLocalChartFamily P.zero 0).starProjection (cgpGlobalMap P.toLocalChartFamily
                    P.zero p)))))).Nonempty →
      C.toChain.plane 0 y ≤ LinearMap.ker ((blockProjCLM_PLN (V := fun _ : CGPTag
          P.toLocalChartFamily P.zero => ℝ²) (.inr (.inr (.inr (.inl i))) : CGPTag
              P.toLocalChartFamily P.zero)) :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] WithLp 2 (ℝ² × ℝ)) := by
    intro p hp hx y hy hw
    rw [C.sel_eq.1] at hw
    rw [C.plane_eq.1]
    exact (C.planes₀.zero_block hΔ hΛ hLΛ hT0 (by linarith only [he]) (by linarith only [hεr.1])
      (hnum 0).1 (C.rough.sigma_le 0).le C.x₀ i
      (gafStageQ_starProjection_globalMap P.toLocalChartFamily P.zero 0 p).symm hx hp hy hw).2
  have hZB₁ : ∀ p : X, 200 * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius / T < ρ
      p →
      (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (cgpGlobalMap P.toLocalChartFamily
          P.zero p) ∈ gafCloud P.toLocalChartFamily P.zero 1 → ∀ y ∈ gafCloud P.toLocalChartFamily
              P.zero 1,
      (closedBall y (80 * (Ξ 1)⁻¹ * (S 1 * ρ (C.toChain.sel 1 y))) ∩
        ball ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (cgpGlobalMap
            P.toLocalChartFamily P.zero p)) (8 * (Ξ 1)⁻¹ * (S 1 * ρ (C.toChain.sel 1 ((gafStageQ
                P.toLocalChartFamily P.zero 1).starProjection (cgpGlobalMap P.toLocalChartFamily
                    P.zero p)))))).Nonempty →
      C.toChain.plane 1 y ≤ LinearMap.ker ((blockProjCLM_PLN (V := fun _ : CGPTag
          P.toLocalChartFamily P.zero => ℝ²) (.inr (.inr (.inr (.inl i))) : CGPTag
              P.toLocalChartFamily P.zero)) :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] WithLp 2 (ℝ² × ℝ)) := by
    intro p hp hx y hy hw
    rw [C.sel_eq.2.1] at hw
    rw [C.plane_eq.2.1]
    exact (C.planes₁.zero_block hΔ hΛ hLΛ hT0 (by linarith only [he]) (by linarith only [hεr.1])
      (hnum 1).1 (C.rough.sigma_le 1).le C.x₀ i
      (gafStageQ_starProjection_globalMap P.toLocalChartFamily P.zero 1 p).symm hx hp hy hw).2
  have hZB₂ : ∀ p : X, 200 * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius / T < ρ
      p →
      (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (cgpGlobalMap P.toLocalChartFamily
          P.zero p) ∈ gafCloud P.toLocalChartFamily P.zero 2 → ∀ y ∈ gafCloud P.toLocalChartFamily
              P.zero 2,
      (closedBall y (80 * (Ξ 2)⁻¹ * (S 2 * ρ (C.toChain.sel 2 y))) ∩
        ball ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (cgpGlobalMap
            P.toLocalChartFamily P.zero p)) (8 * (Ξ 2)⁻¹ * (S 2 * ρ (C.toChain.sel 2 ((gafStageQ
                P.toLocalChartFamily P.zero 2).starProjection (cgpGlobalMap P.toLocalChartFamily
                    P.zero p)))))).Nonempty →
      C.toChain.plane 2 y ≤ LinearMap.ker ((blockProjCLM_PLN (V := fun _ : CGPTag
          P.toLocalChartFamily P.zero => ℝ²) (.inr (.inr (.inr (.inl i))) : CGPTag
              P.toLocalChartFamily P.zero)) :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] WithLp 2 (ℝ² × ℝ)) := by
    intro p hp hx y hy hw
    rw [C.sel_eq.2.2] at hw
    rw [C.plane_eq.2.2]
    exact (C.planes₂.zero_block hΔ hΛ hLΛ hT0 (by linarith only [he]) (by linarith only [hεr.1])
      (hnum 2).1 (C.rough.sigma_le 2).le C.x₀ i
      (gafStageQ_starProjection_globalMap P.toLocalChartFamily P.zero 2 p).symm hx hp hy hw).2
  intro st
  fin_cases st
  · exact hZB₀
  · exact hZB₁
  · exact hZB₂

/-- **ZSP01 (ZI) on `Gaf02ChainE`** (unconditional): `200R_i/T < ρ(p) ⇒` the whole `i` blocks of
`g₁(p)`,
`g₂(p)`, `E(p)` vanish (`Ĉ.toChain`'s stage outputs). -/
theorem Gaf02ChainE.zsp01_ZI_GAF8 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) (i : P.zero.finite_centres.toFinset) {p : X}
    (hp : 200 * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius / T < ρ p) :
    C.toChain.g₁ p (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) = 0 ∧
        C.toChain.g₂ p (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) = 0 ∧
            C.toChain.E p (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) = 0 :=
  C.toChain.zsp01_ZI_hx_GAF8 i (C.zsp01_hZB_GAF8 i) hp

/-- **ZSP01 (ZE) on `Gaf02ChainE`** (unconditional): with `δ₀ = 200c₃/T`,
`‖J_i(f(p) − 𝓔⁰(p))‖ < δ₀R_i` for
`f = g₁, g₂, E` and on the segment `[𝓔⁰ p, E p]`, at every `p`. -/
theorem Gaf02ChainE.zsp01_ZE_GAF8 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) (i : P.zero.finite_centres.toFinset) (p : X) :
    ‖C.toChain.g₁ p (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) -
        cgpGlobalMap P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl i))) : CGPTag
            P.toLocalChartFamily P.zero)‖ < 200 * c 2 / T * (P.zero.zero i.1
                ((Set.Finite.mem_toFinset _).mp i.2)).radius ∧
    ‖C.toChain.g₂ p (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) -
        cgpGlobalMap P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl i))) : CGPTag
            P.toLocalChartFamily P.zero)‖ < 200 * c 2 / T * (P.zero.zero i.1
                ((Set.Finite.mem_toFinset _).mp i.2)).radius ∧
    ‖C.toChain.E p (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) -
        cgpGlobalMap P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl i))) : CGPTag
            P.toLocalChartFamily P.zero)‖ < 200 * c 2 / T * (P.zero.zero i.1
                ((Set.Finite.mem_toFinset _).mp i.2)).radius ∧
    ∀ z ∈ segment ℝ (cgpGlobalMap P.toLocalChartFamily P.zero p) (C.toChain.E p),
      ‖z (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) - cgpGlobalMap
          P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily
              P.zero)‖ < 200 * c 2 / T * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp
                  i.2)).radius :=
  C.toChain.zsp01_ZE_hx_GAF8 i (C.zsp01_hZB_GAF8 i) p

end DifferentialGeometry.Geometry.Collapse

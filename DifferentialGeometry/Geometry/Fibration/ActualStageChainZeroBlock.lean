import DifferentialGeometry.Geometry.Fibration.ActualStageChainRow
import DifferentialGeometry.Geometry.Fibration.ActualZeroBlockIsolationApplications
import DifferentialGeometry.Geometry.Fibration.ActualStagePlaneData

/-!
# ZSP01 on the chain object: zero blocks stay isolated through the stages

Blueprint `master207B.tex`, ZSP01 (B:6323): for a zero index `i`, (ZI)
`ρ(p) > 200R_i/T ⇒ J_i f(p) = 0`
for every intermediate map `f ∈ {𝓔⁰, g₁, g₂, E}` (`J_i` = projection onto the WHOLE zero block,
PLANES'
`blockProjCLM_PLN`), and (ZE) `|J_i(f(p) − 𝓔⁰(p))| < δ₀R_i`, `δ₀ = 200c₃/T`, also on `[𝓔⁰ p, E p]`.

Unconditional pieces:
* `gafStage_zeroTag_mem_GAF8`, `gafStageQ_starProjection_zeroTag_GAF8`: every zero block is a stage
tag of
  every stage, so `π_{Q_j}` keeps it (B: "all zero blocks are retained in every `Q_j`").
* `Gaf02Chain.zsp01_contributor_zero_GAF8`: at a (ZI) point `p` (`x = π_j𝓔⁰(p)` in the stage
cloud), every
  cloud point `y` whose reference window meets `B(x, 8br_x)` has zero block `J_i y = 0` (CFS14's
  (MCb),
  the preimage ratio, `ρ(sel y) ≥ (9/25)ρ(p) > 20R_i/T`, and the original half on `sel y`).
Stage propagation (KERNEL form; the whole-zero-block property of the contributing planes, PLANES'
ZB*,
is an explicit hypothesis `hZB` on the chain's planes — dispositions: ZSP01 closes on
`Gaf02ChainE`):
* `Gaf02Chain.zsp01_stage_step_GAF8`: one stage keeps a zero block (GAF03 locality with
  `K = (ker J_i)ᗮ`, `c = 0`, on the stage-input tube);
* `Gaf02Chain.zsp01_ZI_GAF8`: (ZI) at `g₁, g₂, E`; `Gaf02Chain.zsp01_ZE_GAF8`: (ZE) at `g₁, g₂, E`
and on
  the segment `[𝓔⁰ p, E p]`.
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
local instance instMetricNC14_GAF8z {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_GAF8z {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_GAF8z {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- Every zero block is a stage tag of every stage. -/
theorem gafStage_zeroTag_mem_GAF8 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (st : Fin 3)
    (i : P.zero.finite_centres.toFinset) : (.inr (.inr (.inr (.inl i))) : CGPTag
        P.toLocalChartFamily P.zero) ∈ gafStageTags P.toLocalChartFamily P.zero st := by
  have h1 : (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) ∈ gafStageTags
      P.toLocalChartFamily P.zero 1 := by
    change (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) ∈ cgpQ2Tags
        P.toLocalChartFamily P.zero
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have h2 : (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) ∈ gafStageTags
      P.toLocalChartFamily P.zero 2 := by
    change (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) ∈ cgpQ3Tags
        P.toLocalChartFamily P.zero
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  fin_cases st
  · exact Finset.mem_univ _
  · exact h1
  · exact h2

/-- The stage projections keep every zero block. -/
theorem gafStageQ_starProjection_zeroTag_GAF8 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (st : Fin 3)
    (i : P.zero.finite_centres.toFinset) (z : BlockSpace (fun _ : CGPTag P.toLocalChartFamily
        P.zero => ℝ²)) :
    (gafStageQ P.toLocalChartFamily P.zero st).starProjection z (.inr (.inr (.inr (.inl i))) :
        CGPTag P.toLocalChartFamily P.zero) = z (.inr (.inr (.inr (.inl i))) : CGPTag
            P.toLocalChartFamily P.zero) := by
  classical
  rw [gafStageQ_starProjection, blockRestrict_apply]
  simp only [gafStage_zeroTag_mem_GAF8 P st i, ↓reduceIte]

/-- **ZSP01, the contributors' zero blocks** (unconditional): at a point `p` with `200R_i/T < ρ(p)`
and
`x = π_st𝓔⁰(p)` in the stage cloud, every cloud point `y` whose window
`B̄(y, 80Ξ⁻¹r_y) ∩ B(x, 8Ξ⁻¹r_x)`
is nonempty has zero `i` block. -/
theorem Gaf02Chain.zsp01_contributor_zero_GAF8 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) (st : Fin 3)
    (i : P.zero.finite_centres.toFinset) {p : X} (hp : 200 * (P.zero.zero i.1
        ((Set.Finite.mem_toFinset _).mp i.2)).radius / T < ρ p) {x : BlockSpace (fun _ : CGPTag
            P.toLocalChartFamily P.zero => ℝ²)}
    (hxp : (gafStageQ P.toLocalChartFamily P.zero st).starProjection (cgpGlobalMap
        P.toLocalChartFamily P.zero p) = x)
    (hx : x ∈ gafCloud P.toLocalChartFamily P.zero st) {y : BlockSpace (fun _ : CGPTag
        P.toLocalChartFamily P.zero => ℝ²)} (hy : y ∈ gafCloud P.toLocalChartFamily P.zero st)
    (hw : (closedBall y (80 * (Ξ st)⁻¹ * (S st * ρ (C.sel st y))) ∩
        ball x (8 * (Ξ st)⁻¹ * (S st * ρ (C.sel st x)))).Nonempty) :
    y (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) = 0 := by
  obtain ⟨hΛ, hΔ, hμ, hτ, hLΛ, -, he, hT, -, -, -, -, hεr⟩ := C.std
  obtain ⟨hnum, -⟩ := C.numbers
  obtain ⟨hΞ, hS, hmo, -⟩ := hnum st
  have hT0 : 0 < T := by linarith only [hT, hΔ]
  have hΔ0 : 0 ≤ Δ := by linarith only [hΔ]
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by
    have h' : Λ * (1000000 * Δ) = 1000000 * Δ * Λ := by ring
    linarith only [h', hLΛ]
  have hin := cfs14_stage_inputs_GAF2 P.toLocalChartPackets hΛ hΔ hμ hτ (by linarith only [he]) hLΛ
      st
    (C.sel st) (C.hsel st) hΞ hS hmo
  have hyE := gafCloud_subset_enlarged P.toLocalChartFamily P.zero hΔ0 st hy
  have hxE := gafCloud_subset_enlarged P.toLocalChartFamily P.zero hΔ0 st hx
  obtain ⟨z, hz1, hz2⟩ := hw
  have hA : 0 < (Ξ st)⁻¹ := inv_pos.mpr hΞ
  have hry : 0 < S st * ρ (C.sel st y) := mul_pos hS (hρ _)
  have hd1 : dist z y ≤ 80 * (Ξ st)⁻¹ * (S st * ρ (C.sel st y)) := mem_closedBall.mp hz1
  have hd2 : dist z x < 8 * (Ξ st)⁻¹ * (S st * ρ (C.sel st x)) := mem_ball.mp hz2
  have hm1 := le_max_left (S st * ρ (C.sel st y)) (S st * ρ (C.sel st x))
  have hm2 := le_max_right (S st * ρ (C.sel st y)) (S st * ρ (C.sel st x))
  have e1 : 80 * (Ξ st)⁻¹ * (S st * ρ (C.sel st y)) ≤
      80 * (Ξ st)⁻¹ * max (S st * ρ (C.sel st y)) (S st * ρ (C.sel st x)) :=
    mul_le_mul_of_nonneg_left hm1 (mul_nonneg (by norm_num) hA.le)
  have e2 : 8 * (Ξ st)⁻¹ * (S st * ρ (C.sel st x)) ≤
      8 * (Ξ st)⁻¹ * max (S st * ρ (C.sel st y)) (S st * ρ (C.sel st x)) :=
    mul_le_mul_of_nonneg_left hm2 (mul_nonneg (by norm_num) hA.le)
  have hAM : 0 ≤ (Ξ st)⁻¹ * max (S st * ρ (C.sel st y)) (S st * ρ (C.sel st x)) :=
    mul_nonneg hA.le (hry.le.trans hm1)
  have e3 : 80 * (Ξ st)⁻¹ * max (S st * ρ (C.sel st y)) (S st * ρ (C.sel st x)) +
      8 * (Ξ st)⁻¹ * max (S st * ρ (C.sel st y)) (S st * ρ (C.sel st x)) ≤
      128 * (Ξ st)⁻¹ * max (S st * ρ (C.sel st y)) (S st * ρ (C.sel st x)) := by
    have q1 : 80 * (Ξ st)⁻¹ * max (S st * ρ (C.sel st y)) (S st * ρ (C.sel st x)) +
        8 * (Ξ st)⁻¹ * max (S st * ρ (C.sel st y)) (S st * ρ (C.sel st x)) =
        88 * ((Ξ st)⁻¹ * max (S st * ρ (C.sel st y)) (S st * ρ (C.sel st x))) := by ring
    have q2 : 128 * (Ξ st)⁻¹ * max (S st * ρ (C.sel st y)) (S st * ρ (C.sel st x)) =
        128 * ((Ξ st)⁻¹ * max (S st * ρ (C.sel st y)) (S st * ρ (C.sel st x))) := by ring
    rw [q1, q2]
    linarith only [hAM]
  have hdyx : dist y x ≤
      128 * (Ξ st)⁻¹ * max (S st * ρ (C.sel st y)) (S st * ρ (C.sel st x)) := by
    have htri := dist_triangle_left y x z
    linarith only [htri, hd1, hd2, e1, e2, e3]
  have hrat := (hin.2.2.2 x hxE y hyE hdyx).1
  have hpre := (gafCloud_preimage_ratio_two_GAF5 P.toLocalChartFamily P.zero hΔ hΛ hsmall st (C.sel
      st)
    (C.hsel st) x hx p hxp).1
  have hρxy : ρ (C.sel st x) * 3 / 5 ≤ ρ (C.sel st y) := by
    refine le_of_mul_le_mul_left ?_ hS
    rw [show S st * (ρ (C.sel st x) * 3 / 5) = S st * ρ (C.sel st x) / (5 / 3) by ring]
    exact hrat
  have hR := (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius_pos
  have hRT : 0 < (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius / T := div_pos hR hT0
  have key : 20 * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius / T < ρ (C.sel st
      y) := by
    have q1 : 200 * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius / T = 200 *
        ((P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius / T) := by ring
    have q2 : 20 * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius / T = 20 *
        ((P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius / T) := by ring
    rw [q1] at hp
    rw [q2]
    linarith only [hp, hpre, hρxy, hRT]
  rw [← C.hsel st y hyE]
  classical
  rw [cgpProjMap, blockRestrict_apply]
  simp only [gafStage_zeroTag_mem_GAF8 P st i, ↓reduceIte]
  exact zsp01_original_zero_block P.toLocalChartPacketsR hT0 (by linarith only [he])
    (by linarith only [hεr.1]) i key

/-- **ZSP01, the stage map keeps the zero block** (kernel; `hZB`): at a (ZI) point `p` with
`x = π_st𝓔⁰(p)` in the stage cloud, the slot's map has zero `i` block on `B(x, Σρ(sel x))` (GAF03
locality
with `K = (ker J_i)ᗮ`, `c = 0`; contributors from `zsp01_contributor_zero_GAF8` and `hZB`). -/
theorem Gaf02Chain.zsp01_slot_zero_GAF8 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
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
      ∀ y ∈ gafCloud P.toLocalChartFamily P.zero st,
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
    zeroBlock_input_PLN _ _ (C.zsp01_contributor_zero_GAF8 st i hp rfl hx hy hwy) (hZB st p hp y hy
        hwy)
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
theorem Gaf02Chain.zsp01_stage_step_GAF8 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
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
      ∀ y ∈ gafCloud P.toLocalChartFamily P.zero st,
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
  have ha := C.zsp01_slot_zero_GAF8 st i hZB hp hx hz
  rw [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, gafStageQ_starProjection_zeroTag_GAF8 P st i,
    gafStageQ_starProjection_zeroTag_GAF8 P st i, ha, hw, sub_zero, smul_zero, add_zero]

/-- **ZSP01 (ZI) at every stage** (given `hZB`): `200R_i/T < ρ(p) ⇒` the `i` blocks of `g₁(p)`,
`g₂(p)`,
`E(p)` vanish (with the original half for `𝓔⁰`). -/
theorem Gaf02Chain.zsp01_ZI_GAF8 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) (i : P.zero.finite_centres.toFinset)
    (hZB : ∀ st : Fin 3, ∀ p : X, 200 * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp
        i.2)).radius / T < ρ p →
      ∀ y ∈ gafCloud P.toLocalChartFamily P.zero st,
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
    exact C.zsp01_stage_step_GAF8 0 i hZB hp _ _ h0 fun hψ => tube.1 (subset_tsupport _ hψ)
  have h2 : C.g₂ p (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) = 0 := by
    rw [(C.stage_formula 0 p).2.2.2.2.1, C.Ψ_eq.2.1]
    exact C.zsp01_stage_step_GAF8 1 i hZB hp _ _ h1 fun hψ => tube.2.1 (subset_tsupport _ hψ)
  have h3 : C.E p (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) = 0 := by
    rw [(C.stage_formula 0 p).2.2.2.2.2, C.Ψ_eq.2.2]
    exact C.zsp01_stage_step_GAF8 2 i hZB hp _ _ h2 fun hψ => tube.2.2 (subset_tsupport _ hψ)
  exact ⟨h1, h2, h3⟩

/-- **ZSP01 (ZE)** (given `hZB`): with `δ₀ = 200c₃/T`, `‖J_i(f(p) − 𝓔⁰(p))‖ < δ₀R_i` for
`f = g₁, g₂, E` and
for every point of the segment `[𝓔⁰ p, E p]`, at EVERY `p` (no global bound on `ρ/R_i`). -/
theorem Gaf02Chain.zsp01_ZE_GAF8 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) (i : P.zero.finite_centres.toFinset)
    (hZB : ∀ st : Fin 3, ∀ p : X, 200 * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp
        i.2)).radius / T < ρ p →
      ∀ y ∈ gafCloud P.toLocalChartFamily P.zero st,
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
  have hZI := fun hp => C.zsp01_ZI_GAF8 i hZB (p := p) hp
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

end DifferentialGeometry.Geometry.Collapse

import DifferentialGeometry.Geometry.Fibration.ActualStageChainFinalSubmersion
import DifferentialGeometry.Geometry.Fibration.ActualStageChainE

/-!
# GAF02 BASES as ONE object: `Gaf02Bases C R` and its producer

Blueprint `master207B.tex`, GAF02 (B:5797–5870), BASES part: "FC33's EXACT original threshold-5
domains `U_j` have smooth submersions `π_jE : U_j → W_j` onto their images in embedded bases of
dimensions `2, 1, 1`. Each marked patch has the coordinate diffeomorphism of CGP07 over
`B(0, 5.5ℓ_i)`. The later maps are diffeomorphisms on the entire earlier marked bases and preserve
fibers [...] on CGP08's specified threshold-6 carriers. No whole-preimage claim is implicit."
External draft 59 §4 (seven steps), review 66 D66-7 (acceptance list), review 71 D71-13 ("packing
as ONE object"), lead decision 11:1x (`Gaf02Bases C R`, `R : Gaf02RoughData C`; final ordered row
`gaf02_bases_row_BAS`). Lane C14-BASESc (successor of C14-BASES / C14-BASESb).

* **`Gaf02Bases C R`** (`Type`): the CGP07 chart inverses `circleChart j`, `edgeChart j`,
  `slimChart j` of the marked patches `V_j⁰` (data; model spaces `ℝ², ℝ, ℝ` = dimensions
  `2, 1, 1`) and, all on the SAME chain `C` (no second map, no re-chosen family):
  CGP07 one sheet / smooth inverse / compact preimages per patch, threshold-6 exhaustion of every
  patch by the chart's original plateau, the native scope `V_st⁰ ⊆ Z_st⁰`, the later transports
  `Θ_st` (factorization `π_stE = Θ_st ∘ f_st` at EVERY point, `Θ₃ = id`, injective = no merging and
  smooth on the WHOLE marked base), the embedded final bases `W_st = Θ_st(V_st⁰)` in chart form
  (`Θ_st ∘ chart_j` onto the open piece `W_st ∩ {marked j}` with the LINEAR left inverse
  `κ_j = R_j⁻¹u_j`; the pieces cover `W_st`), smoothness of `π_stE`, the stage submersions on the
  threshold-6 plateaux, the threshold-5 submersions `π_stE : U_st → W_st` (chart form) with
  `π_stE(U_st) ⊆ W_st`, and (RF) on the carriers `D_st` only.
* **`Gaf02Chain.gaf02Bases_BAS C R`**: the producer (no hypotheses besides `(C, R)`).
* `Gaf02ChainE.bases_BAS Ĉ : Gaf02Bases Ĉ.toChain Ĉ.rough` (kernel form on the enhanced chain).
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

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- The properties of the circle stage package for a given chart family `chart` (see
`Gaf02CircleBases_BAS`). -/
structure Gaf02CircleBasesSpec_BAS
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
      Lmax τ γ δ εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (chart : P.toLocalChartFamily.circle.finite_centres.toFinset → ℝ² →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) : Prop where
  /-- CGP07, circle: `κ_j` is a bijection of `V_j⁰` onto the ball, with the smooth inverse
  `chart j`. -/
  patch : ∀ j, BijOn ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j)
      (C.circlePatch_BAS j) (ball 0 (11 / 2 * 1)) ∧
    ContDiffOn ℝ ∞ (chart j) (ball 0 (11 / 2 * 1)) ∧
    InvOn (chart j) ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j)
      (C.circlePatch_BAS j) (ball 0 (11 / 2 * 1)) ∧
    MapsTo (chart j) (ball 0 (11 / 2 * 1)) (C.circlePatch_BAS j)
  /-- CGP07's threshold-6 exhaustion, circle: every patch point is `f₁ p` for a point `p` of the
  chart's ORIGINAL threshold-6 plateau. -/
  exhaust : ∀ j, ∀ w ∈ C.circlePatch_BAS j, ∃ p, (p ∈ ball j.1 (200 * ρ j.1) ∧
    ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ < 6) ∧ C.stageMap_BAS 0 p = w
  /-- Compact preimages, circle: `κ_j|V_j⁰` is proper onto the ball. -/
  proper : ∀ j, ∀ K ⊆ ball (0 : ℝ²) (11 / 2 * 1), IsCompact K →
    IsCompact (C.circlePatch_BAS j ∩ ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j) ⁻¹' K)
  /-- `W₁` is embedded, chart by chart: `Θ₁ ∘ chart j` is smooth on the ball, onto the open
  piece `W₁ ∩ {marked j}`, with the linear left inverse `κ_j`. -/
  base_chart : ∀ j, ContDiffOn ℝ ∞ (C.Θ_BAS 0 ∘ chart j) (ball 0 (11 / 2 * 1)) ∧
    (∀ b ∈ ball (0 : ℝ²) (11 / 2 * 1),
      C.Θ_BAS 0 (chart j b) ∈ C.finalBase_BAS 0 ∩ markedCondition_BPRE
        (gafCircleVector P.toLocalChartPackets j) (gafCircleMarker P.toLocalChartPackets j)
        (ρ j.1) 1 ∧
      ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j) (C.Θ_BAS 0 (chart j b)) = b) ∧
    ∀ y ∈ C.finalBase_BAS 0 ∩ markedCondition_BPRE (gafCircleVector P.toLocalChartPackets j)
        (gafCircleMarker P.toLocalChartPackets j) (ρ j.1) 1,
      ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j) y ∈ ball (0 : ℝ²) (11 / 2 * 1) ∧
      C.Θ_BAS 0 (chart j (((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j) y)) = y
  /-- The marked pieces cover `W₁`. -/
  cover : C.finalBase_BAS 0 ⊆ ⋃ j, markedCondition_BPRE
    (gafCircleVector P.toLocalChartPackets j) (gafCircleMarker P.toLocalChartPackets j) (ρ j.1) 1
  /-- Step 1, circle: the stage submersion on the original threshold-6 plateau (chart form). -/
  stage_submersion : ∀ j {p : X}, p ∈ ball j.1 (200 * ρ j.1) →
    ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ < 6 →
    Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (fun q =>
      ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j) (C.stageMap_BAS 0 q)) p)
  /-- Step 7, circle: the threshold-5 submersion `π₁E : U₁ → W₁` (chart form). -/
  submersion : ∀ j {p : X}, p ∈ ball j.1 (200 * ρ j.1) →
    ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ < 5 →
    (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p) ∈
        C.finalBase_BAS 0 ∩ markedCondition_BPRE (gafCircleVector P.toLocalChartPackets j)
          (gafCircleMarker P.toLocalChartPackets j) (ρ j.1) 1 ∧
      Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (fun q =>
        ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j)
          ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E q))) p)

/-- **GAF02 BASES, circle stage** (`W₁`, dimension 2): CGP07's chart inverses of the circle patches
`V_j⁰` (data), CGP07 per patch, threshold-6 exhaustion, compact preimages, `W₁` embedded chart by
chart (`Θ₁ ∘ chart_j`, linear left inverse `κ_j`), the cover of `W₁` by the marked pieces, the stage
submersion on the threshold-6 plateau and the threshold-5 submersion `π₁E : U₁ → W₁` (chart form).
-/
structure Gaf02CircleBases_BAS
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
      Lmax τ γ δ εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) : Type where
  /-- CGP07's chart inverse of the circle patch `V_j⁰` on `B(0, 5.5)`. -/
  chart : P.toLocalChartFamily.circle.finite_centres.toFinset → ℝ² →
    BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
  /-- The properties (CGP07, embedding of the final base, submersions). -/
  spec : Gaf02CircleBasesSpec_BAS C chart


/-- The properties of the edge stage package for a given chart family `chart` (see
`Gaf02EdgeBases_BAS`). -/
structure Gaf02EdgeBasesSpec_BAS
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
      Lmax τ γ δ εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (chart : P.edge.finite_centres.toFinset → ℝ →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) : Prop where
  /-- CGP07, edge (one-dimensional axis coordinate). -/
  patch : ∀ j, BijOn ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp
      (gafEdgeVector P.toLocalChartFamily P.zero j)) (C.edgePatch_BAS j) (ball 0 (11 / 2 * Δ)) ∧
    ContDiffOn ℝ ∞ (chart j) (ball 0 (11 / 2 * Δ)) ∧
    InvOn (chart j) ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp
      (gafEdgeVector P.toLocalChartFamily P.zero j)) (C.edgePatch_BAS j) (ball 0 (11 / 2 * Δ)) ∧
    MapsTo (chart j) (ball 0 (11 / 2 * Δ)) (C.edgePatch_BAS j)
  /-- CGP07's threshold-6 exhaustion, edge. -/
  exhaust : ∀ j, ∀ w ∈ C.edgePatch_BAS j, ∃ p, (p ∈ ball j.1 (100 * Δ * ρ j.1) ∧
    |P.edge.coord j.1 p| < 6 * Δ ∧ cgpHeight P.toLocalChartFamily p < 6 * Δ) ∧
    C.stageMap_BAS 1 p = w
  /-- Compact preimages, edge. -/
  proper : ∀ j, ∀ K ⊆ ball (0 : ℝ) (11 / 2 * Δ), IsCompact K →
    IsCompact (C.edgePatch_BAS j ∩ ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp
      (gafEdgeVector P.toLocalChartFamily P.zero j)) ⁻¹' K)
  /-- `W₂` is embedded, chart by chart. -/
  base_chart : ∀ j, ContDiffOn ℝ ∞ (C.Θ_BAS 1 ∘ chart j) (ball 0 (11 / 2 * Δ)) ∧
    (∀ b ∈ ball (0 : ℝ) (11 / 2 * Δ),
      C.Θ_BAS 1 (chart j b) ∈ C.finalBase_BAS 1 ∩ markedCondition_BPRE
        (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
        (gafEdgeMarker P.toLocalChartFamily P.zero j) (ρ j.1) Δ ∧
      ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
        (C.Θ_BAS 1 (chart j b)) = b) ∧
    ∀ y ∈ C.finalBase_BAS 1 ∩ markedCondition_BPRE
        (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
        (gafEdgeMarker P.toLocalChartFamily P.zero j) (ρ j.1) Δ,
      ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) y ∈
        ball (0 : ℝ) (11 / 2 * Δ) ∧
      C.Θ_BAS 1 (chart j (((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp
        (gafEdgeVector P.toLocalChartFamily P.zero j)) y)) = y
  /-- The marked pieces cover `W₂`. -/
  cover : C.finalBase_BAS 1 ⊆ ⋃ j, markedCondition_BPRE
    (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
    (gafEdgeMarker P.toLocalChartFamily P.zero j) (ρ j.1) Δ
  /-- Step 1, edge. -/
  stage_submersion : ∀ j {p : X}, p ∈ ball j.1 (100 * Δ * ρ j.1) →
    |P.edge.coord j.1 p| < 6 * Δ → cgpHeight P.toLocalChartFamily p < 6 * Δ →
    Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun q =>
      ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
        (C.stageMap_BAS 1 q)) p)
  /-- Step 7, edge. -/
  submersion : ∀ j {p : X}, p ∈ ball j.1 (100 * Δ * ρ j.1) →
    |P.edge.coord j.1 p| < 5 * Δ → cgpHeight P.toLocalChartFamily p < 5 * Δ →
    (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.E p) ∈
        C.finalBase_BAS 1 ∩ markedCondition_BPRE
          (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
          (gafEdgeMarker P.toLocalChartFamily P.zero j) (ρ j.1) Δ ∧
      Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun q =>
        ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
          ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.E q))) p)

/-- **GAF02 BASES, edge stage** (`W₂`, dimension 1; the ACTUAL one-dimensional axis coordinate): as
`Gaf02CircleBases_BAS`. -/
structure Gaf02EdgeBases_BAS
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
      Lmax τ γ δ εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) : Type where
  /-- CGP07's chart inverse of the edge patch `V_j⁰` on `(-5.5Δ, 5.5Δ)`. -/
  chart : P.edge.finite_centres.toFinset → ℝ →
    BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
  /-- The properties (CGP07, embedding of the final base, submersions). -/
  spec : Gaf02EdgeBasesSpec_BAS C chart


/-- The properties of the slim stage package for a given chart family `chart` (see
`Gaf02SlimBases_BAS`). -/
structure Gaf02SlimBasesSpec_BAS
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
      Lmax τ γ δ εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (chart : P.slim.finite_centres.toFinset → ℝ →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) : Prop where
  /-- CGP07, slim (one-dimensional axis coordinate). -/
  patch : ∀ j, BijOn ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp
      (gafSlimVector P.toLocalChartFamily P.zero j)) (C.slimPatch_BAS j)
      (ball 0 (11 / 2 * (10 ^ 5 * Δ))) ∧
    ContDiffOn ℝ ∞ (chart j) (ball 0 (11 / 2 * (10 ^ 5 * Δ))) ∧
    InvOn (chart j) ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp
      (gafSlimVector P.toLocalChartFamily P.zero j)) (C.slimPatch_BAS j)
      (ball 0 (11 / 2 * (10 ^ 5 * Δ))) ∧
    MapsTo (chart j) (ball 0 (11 / 2 * (10 ^ 5 * Δ))) (C.slimPatch_BAS j)
  /-- CGP07's threshold-6 exhaustion, slim. -/
  exhaust : ∀ j, ∀ w ∈ C.slimPatch_BAS j, ∃ p, (p ∈ ball j.1 (1000000 * Δ * ρ j.1) ∧
    |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| < 6 * (10 ^ 5 * Δ)) ∧
    C.stageMap_BAS 2 p = w
  /-- Compact preimages, slim. -/
  proper : ∀ j, ∀ K ⊆ ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ)), IsCompact K →
    IsCompact (C.slimPatch_BAS j ∩ ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp
      (gafSlimVector P.toLocalChartFamily P.zero j)) ⁻¹' K)
  /-- `W₃` is embedded, chart by chart (`Θ₃ = id`). -/
  base_chart : ∀ j, ContDiffOn ℝ ∞ (C.Θ_BAS 2 ∘ chart j)
      (ball 0 (11 / 2 * (10 ^ 5 * Δ))) ∧
    (∀ b ∈ ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ)),
      C.Θ_BAS 2 (chart j b) ∈ C.finalBase_BAS 2 ∩ markedCondition_BPRE
        (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
        (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ) ∧
      ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
        (C.Θ_BAS 2 (chart j b)) = b) ∧
    ∀ y ∈ C.finalBase_BAS 2 ∩ markedCondition_BPRE
        (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
        (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ),
      ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j)) y ∈
        ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ)) ∧
      C.Θ_BAS 2 (chart j (((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp
        (gafSlimVector P.toLocalChartFamily P.zero j)) y)) = y
  /-- The marked pieces cover `W₃`. -/
  cover : C.finalBase_BAS 2 ⊆ ⋃ j, markedCondition_BPRE
    (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
    (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ)
  /-- Step 1, slim. -/
  stage_submersion : ∀ j {p : X}, p ∈ ball j.1 (1000000 * Δ * ρ j.1) →
    |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| < 6 * (10 ^ 5 * Δ) →
    Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun q =>
      ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
        (C.stageMap_BAS 2 q)) p)
  /-- Step 7, slim. -/
  submersion : ∀ j {p : X}, p ∈ ball j.1 (1000000 * Δ * ρ j.1) →
    |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| < 5 * (10 ^ 5 * Δ) →
    (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E p) ∈
        C.finalBase_BAS 2 ∩ markedCondition_BPRE
          (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
          (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ) ∧
      Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun q =>
        ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
          ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E q))) p)

/-- **GAF02 BASES, slim stage** (`W₃`, dimension 1, `Θ₃ = id`): as `Gaf02CircleBases_BAS`. -/
structure Gaf02SlimBases_BAS
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
      Lmax τ γ δ εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) : Type where
  /-- CGP07's chart inverse of the slim patch `V_j⁰` on `(-5.5·10⁵Δ, 5.5·10⁵Δ)`. -/
  chart : P.slim.finite_centres.toFinset → ℝ →
    BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
  /-- The properties (CGP07, embedding of the final base, submersions). -/
  spec : Gaf02SlimBasesSpec_BAS C chart


/-- **GAF02 BASES, the later transports and the final maps** (CGP08; draft 59 §4 steps 6–7): native
scope `V_st⁰ ⊆ Z_st⁰`, `π_stE = Θ_st ∘ f_st` at EVERY point, `Θ₃ = id`, no merging and smoothness of
`Θ_st` on the WHOLE marked base, smoothness of `π_stE`, `π_stE(U_st) ⊆ W_st`, (RF) on `D_st` only.
-/
structure Gaf02LaterBases_BAS
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
      Lmax τ γ δ εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) : Prop where
  /-- Native scope: the marked stage base `V_st⁰` lies in the stage slot's native zero set. -/
  native_scope : ∀ st, C.markedBase_BAS st ⊆ (C.slot st).zeroSet
  /-- The final factorization `π_stE = Θ_st ∘ f_st` at EVERY point. -/
  final_factor : ∀ st p, (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E p) =
    C.Θ_BAS st (C.stageMap_BAS st p)
  /-- The last later transport is the identity. -/
  later_last : C.Θ_BAS 2 = id
  /-- No merging (CGP08): `Θ_st` is injective on the WHOLE marked base. -/
  later_injOn : ∀ st, InjOn (C.Θ_BAS st) (C.markedBase_BAS st)
  /-- `Θ_st` is smooth at every point of the WHOLE marked base. -/
  later_contDiffAt : ∀ st, ∀ w ∈ C.markedBase_BAS st, ContDiffAt ℝ ∞ (C.Θ_BAS st) w
  /-- `π_stE` is smooth. -/
  final_smooth : ∀ st, ContMDiff 𝓘(ℝ, E3)
    𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞
    (fun p => (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E p))
  /-- `π_stE(U_st) ⊆ W_st` on FC33's exact original threshold-5 domain. -/
  mapsTo_final : ∀ st, MapsTo (fun p => (gafStageQ P.toLocalChartFamily P.zero st).starProjection
    (C.E p)) (gafStageDomain5_BAS P.toLocalChartPackets st) (C.finalBase_BAS st)
  /-- (RF) on the restricted carrier `D_st` only (no whole-fibre claim). -/
  rf : ∀ st {w₀ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)},
    w₀ ∈ C.markedBase_BAS st →
    {p | p ∈ C.carrier_BAS st ∧
        (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E p) = C.Θ_BAS st w₀} =
      {p | p ∈ C.carrier_BAS st ∧ C.stageMap_BAS st p = w₀}

/-- **The GAF02 BASES object of a chain** (blueprint GAF02, BASES part; draft 59 §4; D66-7;
D71-13 "packing as ONE object"): the three stage packages (CGP07 chart inverses of the marked
patches as data, the embedded final bases `W_st = Θ_st(V_st⁰)` of dimensions `2, 1, 1` in chart
form, the stage and threshold-5 submersions) and the later-transport package, all on the SAME chain
`C`, indexed by its rough data `R` (the producer `Gaf02Chain.gaf02Bases_BAS` reads `R`). -/
structure Gaf02Bases {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
      Lmax τ γ δ εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) (R : Gaf02RoughData C) : Type where
  /-- The circle stage package (`W₁`). -/
  circle : Gaf02CircleBases_BAS C
  /-- The edge stage package (`W₂`). -/
  edge : Gaf02EdgeBases_BAS C
  /-- The slim stage package (`W₃`). -/
  slim : Gaf02SlimBases_BAS C
  /-- The later transports and the final maps. -/
  later : Gaf02LaterBases_BAS C

namespace Gaf02Chain

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- The native scope `V_st⁰ ⊆ Z_st⁰` (every marked patch lies in the slot's zero set). -/
theorem markedBase_subset_zeroSet_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (st : Fin 3) : C.markedBase_BAS st ⊆ (C.slot st).zeroSet := by
  fin_cases st
  · exact iUnion_subset fun _ _ hw => hw.1
  · exact iUnion_subset fun _ _ hw => hw.1
  · exact iUnion_subset fun _ _ hw => hw.1

/-- `π_stE` is smooth (`E` smooth, `π_st` continuous linear). -/
theorem final_contMDiff_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (st : Fin 3) : ContMDiff 𝓘(ℝ, E3)
      𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞
      (fun p => (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E p)) :=
  ((gafStageQ P.toLocalChartFamily P.zero st).starProjection).contMDiff.comp C.stage_smooth.2.2

/-- `Θ_st` is smooth at every point of the whole marked base. -/
theorem theta_contDiffAt_markedBase_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (st : Fin 3) :
    ∀ w ∈ C.markedBase_BAS st, ContDiffAt ℝ ∞ (C.Θ_BAS st) w := by
  fin_cases st
  · intro w hw
    exact (mem_iUnion.mp hw).elim fun j hj => C.theta_contDiffAt_circlePatch_BAS R j w hj
  · intro w hw
    exact (mem_iUnion.mp hw).elim fun j hj => C.theta_contDiffAt_edgePatch_BAS R j w hj
  · intro _ _
    exact contDiffAt_id

/-- The properties of the circle stage package for CGP07's chosen chart inverses. -/
theorem circleBasesSpec_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) :
    Gaf02CircleBasesSpec_BAS C (fun j => Classical.choose (C.cgp07_circle_BAS R j).2.2) where
  patch j := ⟨(C.cgp07_circle_BAS R j).1,
    (Classical.choose_spec (C.cgp07_circle_BAS R j).2.2).1,
    (Classical.choose_spec (C.cgp07_circle_BAS R j).2.2).2.1,
    (Classical.choose_spec (C.cgp07_circle_BAS R j).2.2).2.2.1⟩
  exhaust j := (C.cgp07_circle_BAS R j).2.1
  proper j := (C.cgp07_circle_BAS R j).2.2.elim fun _ h => h.2.2.2
  base_chart j := embedded_piece_of_chart_BAS (C.slot 0).zeroSet _ _ (ρ j.1) 1 (C.Θ_BAS 0)
    _ (C.finalBase_BAS 0) (Classical.choose_spec (C.cgp07_circle_BAS R j).2.2).1
    (C.cgp07_circle_BAS R j).1 (Classical.choose_spec (C.cgp07_circle_BAS R j).2.2).2.1
    (Classical.choose_spec (C.cgp07_circle_BAS R j).2.2).2.2.1
    (C.theta_contDiffAt_circlePatch_BAS R j) (fun w _ => (C.theta_retains_circle_BAS j w).1)
    (C.finalBase_inter_circle_BAS j)
  cover := C.finalBase_circle_cover_BAS
  stage_submersion j _ hp hη := C.stage_submersion_circle_BAS R j hp hη
  submersion j _ hp hη := C.final_submersion_circle_BAS R j hp hη

/-- **The circle stage package** of the chain (charts = CGP07's chart inverses, chosen once per
patch). -/
def circleBases_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) : Gaf02CircleBases_BAS C :=
  ⟨fun j => Classical.choose (C.cgp07_circle_BAS R j).2.2, C.circleBasesSpec_BAS R⟩

/-- The properties of the edge stage package for CGP07's chosen chart inverses. -/
theorem edgeBasesSpec_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) :
    Gaf02EdgeBasesSpec_BAS C (fun j => Classical.choose (C.cgp07_edge_BAS R j).2.2) where
  patch j := ⟨(C.cgp07_edge_BAS R j).1,
    (Classical.choose_spec (C.cgp07_edge_BAS R j).2.2).1,
    (Classical.choose_spec (C.cgp07_edge_BAS R j).2.2).2.1,
    (Classical.choose_spec (C.cgp07_edge_BAS R j).2.2).2.2.1⟩
  exhaust j := (C.cgp07_edge_BAS R j).2.1
  proper j := (C.cgp07_edge_BAS R j).2.2.elim fun _ h => h.2.2.2
  base_chart j := embedded_piece_of_chart_BAS (C.slot 1).zeroSet _ _ (ρ j.1) Δ (C.Θ_BAS 1)
    _ (C.finalBase_BAS 1) (Classical.choose_spec (C.cgp07_edge_BAS R j).2.2).1
    (C.cgp07_edge_BAS R j).1 (Classical.choose_spec (C.cgp07_edge_BAS R j).2.2).2.1
    (Classical.choose_spec (C.cgp07_edge_BAS R j).2.2).2.2.1
    (C.theta_contDiffAt_edgePatch_BAS R j) (fun w _ => (C.theta_retains_edgeAxis_BAS j w).1)
    (C.finalBase_inter_edge_BAS j)
  cover := C.finalBase_edge_cover_BAS
  stage_submersion j _ hp hη ht := C.stage_submersion_edge_BAS R j hp hη ht
  submersion j _ hp hη ht := C.final_submersion_edge_BAS R j hp hη ht

/-- **The edge stage package** of the chain (charts = CGP07's chart inverses, chosen once per
patch). -/
def edgeBases_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) : Gaf02EdgeBases_BAS C :=
  ⟨fun j => Classical.choose (C.cgp07_edge_BAS R j).2.2, C.edgeBasesSpec_BAS R⟩

/-- The properties of the slim stage package for CGP07's chosen chart inverses. -/
theorem slimBasesSpec_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) :
    Gaf02SlimBasesSpec_BAS C (fun j => Classical.choose (C.cgp07_slim_BAS R j).2.2) where
  patch j := ⟨(C.cgp07_slim_BAS R j).1,
    (Classical.choose_spec (C.cgp07_slim_BAS R j).2.2).1,
    (Classical.choose_spec (C.cgp07_slim_BAS R j).2.2).2.1,
    (Classical.choose_spec (C.cgp07_slim_BAS R j).2.2).2.2.1⟩
  exhaust j := (C.cgp07_slim_BAS R j).2.1
  proper j := (C.cgp07_slim_BAS R j).2.2.elim fun _ h => h.2.2.2
  base_chart j := embedded_piece_of_chart_BAS (C.slot 2).zeroSet _ _ (ρ j.1) (10 ^ 5 * Δ)
    (C.Θ_BAS 2) _ (C.finalBase_BAS 2) (Classical.choose_spec (C.cgp07_slim_BAS R j).2.2).1
    (C.cgp07_slim_BAS R j).1 (Classical.choose_spec (C.cgp07_slim_BAS R j).2.2).2.1
    (Classical.choose_spec (C.cgp07_slim_BAS R j).2.2).2.2.1 (fun _ _ => contDiffAt_id)
    (fun _ _ => rfl) (C.finalBase_inter_slim_BAS j)
  cover := C.finalBase_slim_cover_BAS
  stage_submersion j _ hp hη := C.stage_submersion_slim_BAS R j hp hη
  submersion j _ hp hη := C.final_submersion_slim_BAS R j hp hη

/-- **The slim stage package** of the chain (charts = CGP07's chart inverses, chosen once per
patch). -/
def slimBases_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) : Gaf02SlimBases_BAS C :=
  ⟨fun j => Classical.choose (C.cgp07_slim_BAS R j).2.2, C.slimBasesSpec_BAS R⟩

/-- **The later-transport package** of the chain. -/
theorem laterBases_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) : Gaf02LaterBases_BAS C where
  native_scope := C.markedBase_subset_zeroSet_BAS
  final_factor := C.final_factor_BAS
  later_last := C.theta_two_eq_id_BAS
  later_injOn := C.theta_injOn_BAS R
  later_contDiffAt := C.theta_contDiffAt_markedBase_BAS R
  final_smooth := C.final_contMDiff_BAS
  mapsTo_final st _ hp := C.final_mem_finalBase_BAS R st hp
  rf st _ hw₀ := C.rf_BAS R st hw₀

/-- **The GAF02 BASES producer**: every chain with its rough data carries the bases object (no
hypotheses besides `(C, R)`). -/
def gaf02Bases_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) : Gaf02Bases C R where
  circle := C.circleBases_BAS R
  edge := C.edgeBases_BAS R
  slim := C.slimBases_BAS R
  later := C.laterBases_BAS R

end Gaf02Chain

namespace Gaf02ChainE

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **The bases object of an enhanced chain** (kernel form of the row, D66-8 "ONE bases object"):
on `Ĉ.toChain` with `Ĉ`'s OWN rough data. -/
def bases_BAS (Ĉ : Gaf02ChainE P Kj Ξ Γ S eg c cw) : Gaf02Bases Ĉ.toChain Ĉ.rough :=
  Ĉ.toChain.gaf02Bases_BAS Ĉ.rough

end Gaf02ChainE

end DifferentialGeometry.Geometry.Collapse

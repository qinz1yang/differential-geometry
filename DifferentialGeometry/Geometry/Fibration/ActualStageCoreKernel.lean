import DifferentialGeometry.Geometry.Fibration.ActualStageZeroMarkerTwo
import DifferentialGeometry.Geometry.Fibration.ActualStagePackageApplications
import DifferentialGeometry.Geometry.Fibration.ActualStageSmoothApplications
import DifferentialGeometry.Geometry.Fibration.ActualStageTwoThreeStepApplications

/-!
# GAF02 CORE, stage by stage: the actual adjustment chain `g₁, g₂, E` on abstract stage data

Blueprint `master207B.tex`, GAF02 (B:5797) first paragraph and proof ("execute the three stages in
increasing order"). Each stage `st` is given by a selection `sel`, planes `plane x ≤ Q_st` with the
small-marker rule (PP) and the stage test's normal-error clause, and a nearest map `a` with the
per-stage conclusions of GAF01's nearest-map row (smoothness on `Ω`, value / derivative bounds `Ξ`,
GAF03 locality); the stage projection is `P = π_{Q_st} ∘ a` and `Ψ = adjustmentMap Q_st P ψ` with
CFS31's cutoffs `ψ₁` (source), `ψ₂` (edge, CFS23), `ψ₃` (slim, CFS22). The numbers `c₀ < c₁ < c₂`
satisfy exactly GAF01's CHOICE inequalities used (`E + a < c`, derivative budget `< c`, `c ≤ 4κ/5`,
`c ≤ 3Σ_next/10`, `c ≤ 1/512`), with the prior errors `E = H = c_{j−1}`.

* `gaf02_core_stageOne_GAF8`: `g₁ = Ψ₁ ∘ 𝓔⁰` smooth, `‖g₁ − 𝓔⁰‖ < c₀ρ`, derivative error, small
  markers vanish at `g₁`, (AM0) on `[𝓔⁰ p, g₁ p]`.
* `gaf02_core_stageTwo_GAF8`: the same for `g₂ = Ψ₂ ∘ g₁` with `c₁` ((ZM) at `g₁` from the prefix).
* `gaf02_core_stageThree_GAF8`: the same for `E = Ψ₃ ∘ g₂` with `c₂` ((ZM) at `g₂` from the prefix).
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

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_GAF8k
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_GAF8k
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_GAF8k
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **GAF02 CORE, stage one** on abstract stage data: `g₁ = Ψ₁ ∘ 𝓔⁰` is smooth,
`‖g₁ − 𝓔⁰‖ < c₀ρ`, `‖dg₁ − d𝓔⁰‖ ≤ ((5/3)Ξ₀Σ₀·b·L + Ξ₀L + e₀)√g`, small markers vanish at `g₁`, and
(AM0) holds on `[𝓔⁰ p, g₁ p]`. -/
theorem gaf02_core_stageOne_GAF8
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hσc : σc ∈ Icc (0 : ℝ) 1) (hγc : γc ∈ Icc (0 : ℝ) 1) (hεr : εr ∈ Icc (0 : ℝ) 1)
    (sel₀ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel₀ : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 0,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0)
        (sel₀ x) = x)
    {Ξ₀ sg₀ eg₀ : ℝ} (hsg₀ : 0 < sg₀) (hΞ₀ : 0 < Ξ₀) (hmo₀ : 128 * Ξ₀⁻¹ * sg₀ ≤ 1 / 5)
    (heg₀ : 0 ≤ eg₀)
    (plane₀ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (hplaneQ₀ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      plane₀ x ≤ gafStageQ P.toLocalChartFamily P.zero 0)
    (hpp₀ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ∀ q,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0) q =
        x →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
        plane₀ x ≤ LinearMap.ker ((blockMarkerCLM
          (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero a) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))
    (hrank₀ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      ∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
      ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x → ∀ v,
        ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) q v -
            ((plane₀ x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (cgpGlobalMap P.toLocalChartFamily P.zero) q) v :
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))‖ ≤
          eg₀ * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v))
    (a₀ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hsm₀ : ContDiffOn ℝ ∞ a₀ (⋃ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      ball x (sg₀ * ρ (sel₀ x))))
    (hab₀ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ∀ z ∈ ball x (sg₀ * ρ (sel₀ x)),
      ‖a₀ z - (x + (plane₀ x).starProjection (z - x))‖ ≤ Ξ₀ * (sg₀ * ρ (sel₀ x)) ∧
      DifferentiableAt ℝ a₀ z ∧ ‖fderiv ℝ a₀ z - (plane₀ x).starProjection‖ ≤ Ξ₀ ∧
      ∀ (Kk : Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
        (c : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (∀ i ∈ gafCloud P.toLocalChartFamily P.zero 0,
          (closedBall i (80 * Ξ₀⁻¹ * (sg₀ * ρ (sel₀ i))) ∩
            ball x (8 * Ξ₀⁻¹ * (sg₀ * ρ (sel₀ x)))).Nonempty →
          Kk.starProjection i = c ∧ plane₀ i ≤ Kkᗮ) →
        Kk.starProjection (a₀ z) = c)
    {c₀ : ℝ} (hv₁ : 5 / 3 * Ξ₀ * sg₀ < c₀) (hc₀ : c₀ ≤ 1 / 512) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
      (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
        (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero) ∧
    (∀ p, ‖(adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
      (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
        (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero) p -
      cgpGlobalMap P.toLocalChartFamily P.zero p‖ < c₀ * ρ p) ∧
    (∀ p w, ‖mvfderiv 𝓘(ℝ, E3)
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
      (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
        (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero) p w -
      mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤
        (5 / 3 * Ξ₀ * sg₀ * gafCutoffConstant * gafDerivativeBound +
        Ξ₀ * gafDerivativeBound + eg₀) *
          Real.sqrt (g.inner p w w)) ∧
    (∀ q (a : CGPMarkerIndex P.toLocalChartFamily),
      ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
      blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a)
        ((adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
      (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
        (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero) q) = 0) ∧
    ∀ (a : CGPMarkerIndex P.toLocalChartFamily) p,
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      ∀ z ∈ segment ℝ (cgpGlobalMap P.toLocalChartFamily P.zero p)
        ((adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
      (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
        (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero) p),
      |blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) z| ≤
        ρ (cgpMarkerCentre P.toLocalChartFamily a) / 32 := by
  have hpk := gafStage_package_GAF6 P hΔ hΛ hLΛ 0 sel₀ hsel₀ hsg₀ hΞ₀ hmo₀ plane₀ hplaneQ₀ hpp₀ a₀
    hsm₀ hab₀
  have hone := gaf02_stageOne_projected_GAF6 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 hσc hγc hεr
    sel₀ hsel₀ hsg₀ hΞ₀ hmo₀ heg₀ plane₀ hplaneQ₀ hpp₀ hrank₀ a₀ hsm₀ hab₀
  have hpos : 0 < 5 / 3 * Ξ₀ * sg₀ := by positivity
  have hcum : ∀ q, ‖adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
        (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
        (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
          (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero q) -
      cgpGlobalMap P.toLocalChartFamily P.zero q‖ ≤ c₀ * ρ q := fun q =>
    (hone.2.1 q).trans (mul_le_mul_of_nonneg_right hv₁.le (hρ q).le)
  have hzm := gaf02_stageOne_zeroMarker_GAF7 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 sel₀ hsel₀
    (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
    hpk.1 hsg₀ hpk.2.2.2.2
    (hpos.trans hv₁).le hc₀ hcum
  exact ⟨hone.1, fun p => (hone.2.1 p).trans_lt (mul_lt_mul_of_pos_right hv₁ (hρ p)), hone.2.2,
    hzm.1, hzm.2⟩

/-- **GAF02 CORE, stage two** on abstract stage data: `g₂ = Ψ₂ ∘ g₁` is smooth,
`‖g₂ − 𝓔⁰‖ < c₁ρ`, `‖dg₂ − d𝓔⁰‖ ≤ (a·b·(L + c₀) + Ξ₁(L + c₀) + e₁ + 2c₀)√g` with
`a = (5/3)Ξ₁Σ₁ + (1 + Ξ₁)c₀`, small markers vanish at `g₂`, and (AM0) holds on `[𝓔⁰ p, g₂ p]`;
the zero-marker input at `g₁` comes from the stage-one prefix. -/
theorem gaf02_core_stageTwo_GAF8
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hσc : σc ∈ Icc (0 : ℝ) 1) (hγc : γc ∈ Icc (0 : ℝ) 1) (hεr : εr ∈ Icc (0 : ℝ) 1)
    (sel₀ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel₀ : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 0,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0)
        (sel₀ x) = x)
    {Ξ₀ sg₀ eg₀ : ℝ} (hsg₀ : 0 < sg₀) (hΞ₀ : 0 < Ξ₀) (hmo₀ : 128 * Ξ₀⁻¹ * sg₀ ≤ 1 / 5)
    (heg₀ : 0 ≤ eg₀)
    (plane₀ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (hplaneQ₀ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      plane₀ x ≤ gafStageQ P.toLocalChartFamily P.zero 0)
    (hpp₀ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ∀ q,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0) q =
        x →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
        plane₀ x ≤ LinearMap.ker ((blockMarkerCLM
          (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero a) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))
    (hrank₀ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      ∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
      ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x → ∀ v,
        ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) q v -
            ((plane₀ x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (cgpGlobalMap P.toLocalChartFamily P.zero) q) v :
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))‖ ≤
          eg₀ * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v))
    (a₀ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hsm₀ : ContDiffOn ℝ ∞ a₀ (⋃ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      ball x (sg₀ * ρ (sel₀ x))))
    (hab₀ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ∀ z ∈ ball x (sg₀ * ρ (sel₀ x)),
      ‖a₀ z - (x + (plane₀ x).starProjection (z - x))‖ ≤ Ξ₀ * (sg₀ * ρ (sel₀ x)) ∧
      DifferentiableAt ℝ a₀ z ∧ ‖fderiv ℝ a₀ z - (plane₀ x).starProjection‖ ≤ Ξ₀ ∧
      ∀ (Kk : Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
        (c : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (∀ i ∈ gafCloud P.toLocalChartFamily P.zero 0,
          (closedBall i (80 * Ξ₀⁻¹ * (sg₀ * ρ (sel₀ i))) ∩
            ball x (8 * Ξ₀⁻¹ * (sg₀ * ρ (sel₀ x)))).Nonempty →
          Kk.starProjection i = c ∧ plane₀ i ≤ Kkᗮ) →
        Kk.starProjection (a₀ z) = c)
    (sel₁ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel₁ : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 1,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1)
        (sel₁ x) = x)
    {Ξ₁ sg₁ eg₁ : ℝ} (hsg₁ : 0 < sg₁) (hΞ₁ : 0 < Ξ₁) (hmo₁ : 128 * Ξ₁⁻¹ * sg₁ ≤ 1 / 5)
    (heg₁ : 0 ≤ eg₁)
    (plane₁ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (hplaneQ₁ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1,
      plane₁ x ≤ gafStageQ P.toLocalChartFamily P.zero 1)
    (hpp₁ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1, ∀ q,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1) q =
        x →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
        plane₁ x ≤ LinearMap.ker ((blockMarkerCLM
          (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero a) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))
    (hrank₁ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1, ∃ i ∈ P.edge.centres,
      ∀ q : X,
      cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) q = x →
        ∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 →
          ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
              (cgpQ2Tags P.toLocalChartFamily P.zero)) q w -
            (plane₁ x).starProjection
              ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ2Tags P.toLocalChartFamily P.zero)) q w)‖ < eg₁)
    (a₁ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hsm₁ : ContDiffOn ℝ ∞ a₁ (⋃ x ∈ gafCloud P.toLocalChartFamily P.zero 1,
      ball x (sg₁ * ρ (sel₁ x))))
    (hab₁ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1, ∀ z ∈ ball x (sg₁ * ρ (sel₁ x)),
      ‖a₁ z - (x + (plane₁ x).starProjection (z - x))‖ ≤ Ξ₁ * (sg₁ * ρ (sel₁ x)) ∧
      DifferentiableAt ℝ a₁ z ∧ ‖fderiv ℝ a₁ z - (plane₁ x).starProjection‖ ≤ Ξ₁ ∧
      ∀ (Kk : Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
        (c : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (∀ i ∈ gafCloud P.toLocalChartFamily P.zero 1,
          (closedBall i (80 * Ξ₁⁻¹ * (sg₁ * ρ (sel₁ i))) ∩
            ball x (8 * Ξ₁⁻¹ * (sg₁ * ρ (sel₁ x)))).Nonempty →
          Kk.starProjection i = c ∧ plane₁ i ≤ Kkᗮ) →
        Kk.starProjection (a₁ z) = c)
    {c₀ : ℝ} (hv₁ : 5 / 3 * Ξ₀ * sg₀ < c₀) (hc₀ : c₀ ≤ 1 / 512)
    (hd₁ : (5 / 3 * Ξ₀ * sg₀ * gafCutoffConstant * gafDerivativeBound +
        Ξ₀ * gafDerivativeBound + eg₀) < c₀)
    (hc₀κ : c₀ ≤ 4 * gafKappa / 5) (hc₀s : c₀ ≤ 3 * sg₁ / 10) {c₁ : ℝ}
    (hv₂ : (c₀ + (5 / 3 * Ξ₁ * sg₁ + (1 + Ξ₁) * c₀)) < c₁) (hc₁ : c₁ ≤ 1 / 512) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
      (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
        (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
        (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
          (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero)) ∧
    (∀ p, ‖(adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
      (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
        (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
        (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
          (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero)) p -
      cgpGlobalMap P.toLocalChartFamily P.zero p‖ < c₁ * ρ p) ∧
    (∀ p w, ‖mvfderiv 𝓘(ℝ, E3)
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
      (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
        (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
        (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
          (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero)) p w -
      mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤
        ((5 / 3 * Ξ₁ * sg₁ + (1 + Ξ₁) * c₀) * gafCutoffConstant * (gafDerivativeBound + c₀) +
        Ξ₁ * (gafDerivativeBound + c₀) + eg₁ + 2 * c₀) *
          Real.sqrt (g.inner p w w)) ∧
    (∀ q (a : CGPMarkerIndex P.toLocalChartFamily),
      ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
      blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a)
        ((adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
      (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
        (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
        (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
          (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero)) q) = 0) ∧
    ∀ (a : CGPMarkerIndex P.toLocalChartFamily) p,
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      ∀ z ∈ segment ℝ (cgpGlobalMap P.toLocalChartFamily P.zero p)
        ((adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
      (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
        (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
        (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
          (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero)) p),
      |blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) z| ≤
        ρ (cgpMarkerCentre P.toLocalChartFamily a) / 32 := by
  have h1 := gaf02_core_stageOne_GAF8 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 hσc hγc hεr
    sel₀ hsel₀ hsg₀ hΞ₀ hmo₀ heg₀ plane₀ hplaneQ₀ hpp₀ hrank₀ a₀ hsm₀ hab₀ hv₁ hc₀
  have hpk₀ := gafStage_package_GAF6 P hΔ hΛ hLΛ 0 sel₀ hsel₀ hsg₀ hΞ₀ hmo₀ plane₀
    hplaneQ₀ hpp₀ a₀ hsm₀ hab₀
  have hpk₁ := gafStage_package_GAF6 P hΔ hΛ hLΛ 1 sel₁ hsel₁ hsg₁ hΞ₁ hmo₁ plane₁
    hplaneQ₁ hpp₁ a₁ hsm₁ hab₁
  have hpos : 0 < 5 / 3 * Ξ₀ * sg₀ := by positivity
  have hc₀0 : 0 ≤ c₀ := (hpos.trans hv₁).le
  have hc₁0 : 0 ≤ c₁ := le_of_lt (lt_of_le_of_lt (by positivity) hv₂)
  have hprior : ∀ p, ‖(adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
      (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
        (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero) p -
      cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤ c₀ * ρ p := fun p => (h1.2.1 p).le
  have hpriorD : ∀ p w, ‖mvfderiv 𝓘(ℝ, E3)
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
      (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
        (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero) p w -
      mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤
        c₀ * Real.sqrt (g.inner p w w) := fun p w =>
    (h1.2.2.1 p w).trans (mul_le_mul_of_nonneg_right hd₁.le (Real.sqrt_nonneg _))
  have hZM : ∀ (a : CGPMarkerIndex P.toLocalChartFamily) p,
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      |blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a)
        ((adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
      (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
        (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero) p)| ≤
        ρ (cgpMarkerCentre P.toLocalChartFamily a) / 32 :=
    fun a p hp => h1.2.2.2.2 a p hp _ (right_mem_segment ℝ _ _)
  have hfam := gaf02_familyZM_GAF7 P _ hZM
  have hout := gaf02_stageTwo_output_GAF6 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 hσc hγc hεr
    sel₁ hsel₁ plane₁
    (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
    hΞ₁.le hsg₁ heg₁ hc₀0 hc₀s hc₀κ hc₀0 hpk₁.2.2.1 hpk₁.2.2.2.1 hrank₁ _
    (fun p => (h1.1 p).mdifferentiableAt (by simp)) hprior hpriorD hfam.1
  have hsm := gaf02_stageTwo_smooth_GAF6 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 sel₁ hsel₁
    (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
    hsg₁ hc₀s hc₀κ hpk₁.2.1 _ h1.1 hprior hfam.1
  have hcum₂ : ∀ q, ‖adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
        (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
        (gafStageTwoCutoff P.toLocalChartFamily P.zero)
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
         (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
         (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
           (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero q)) -
      cgpGlobalMap P.toLocalChartFamily P.zero q‖ ≤ c₁ * ρ q := fun q =>
    (hout.2.1 q).trans (mul_le_mul_of_nonneg_right hv₂.le (hρ q).le)
  have hz := gaf02_stageTwo_zeroMarker_GAF7 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 sel₀ hsel₀
    (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
    hpk₀.1 hsg₀ hpk₀.2.2.2.2 sel₁ hsel₁
    (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
    hpk₁.1 hsg₁ hpk₁.2.2.2.2 hc₀0 hc₀ hc₀κ hc₀s hc₁0 hc₁ (fun q => hprior q) hcum₂
  exact ⟨hsm, fun p => (hout.2.1 p).trans_lt (mul_lt_mul_of_pos_right hv₂ (hρ p)), hout.2.2,
    hz.2.1, hz.2.2⟩

/-- **GAF02 CORE, stage three** on abstract stage data: `E = Ψ₃ ∘ g₂` is smooth,
`‖E − 𝓔⁰‖ < c₂ρ`, `‖dE − d𝓔⁰‖ ≤ (a·b·(L + c₁) + Ξ₂(L + c₁) + e₂ + 2c₁)√g` with
`a = (5/3)Ξ₂Σ₂ + (1 + Ξ₂)c₁`, small markers vanish at `E`, and (AM0) holds on `[𝓔⁰ p, E p]`;
the zero-marker input at `g₂` comes from the two-stage prefix. -/
theorem gaf02_core_stageThree_GAF8
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hσc : σc ∈ Icc (0 : ℝ) 1) (hγc : γc ∈ Icc (0 : ℝ) 1) (hεr : εr ∈ Icc (0 : ℝ) 1)
    (sel₀ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel₀ : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 0,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0)
        (sel₀ x) = x)
    {Ξ₀ sg₀ eg₀ : ℝ} (hsg₀ : 0 < sg₀) (hΞ₀ : 0 < Ξ₀) (hmo₀ : 128 * Ξ₀⁻¹ * sg₀ ≤ 1 / 5)
    (heg₀ : 0 ≤ eg₀)
    (plane₀ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (hplaneQ₀ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      plane₀ x ≤ gafStageQ P.toLocalChartFamily P.zero 0)
    (hpp₀ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ∀ q,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0) q =
        x →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
        plane₀ x ≤ LinearMap.ker ((blockMarkerCLM
          (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero a) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))
    (hrank₀ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      ∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
      ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x → ∀ v,
        ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) q v -
            ((plane₀ x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (cgpGlobalMap P.toLocalChartFamily P.zero) q) v :
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))‖ ≤
          eg₀ * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v))
    (a₀ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hsm₀ : ContDiffOn ℝ ∞ a₀ (⋃ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      ball x (sg₀ * ρ (sel₀ x))))
    (hab₀ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ∀ z ∈ ball x (sg₀ * ρ (sel₀ x)),
      ‖a₀ z - (x + (plane₀ x).starProjection (z - x))‖ ≤ Ξ₀ * (sg₀ * ρ (sel₀ x)) ∧
      DifferentiableAt ℝ a₀ z ∧ ‖fderiv ℝ a₀ z - (plane₀ x).starProjection‖ ≤ Ξ₀ ∧
      ∀ (Kk : Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
        (c : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (∀ i ∈ gafCloud P.toLocalChartFamily P.zero 0,
          (closedBall i (80 * Ξ₀⁻¹ * (sg₀ * ρ (sel₀ i))) ∩
            ball x (8 * Ξ₀⁻¹ * (sg₀ * ρ (sel₀ x)))).Nonempty →
          Kk.starProjection i = c ∧ plane₀ i ≤ Kkᗮ) →
        Kk.starProjection (a₀ z) = c)
    (sel₁ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel₁ : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 1,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1)
        (sel₁ x) = x)
    {Ξ₁ sg₁ eg₁ : ℝ} (hsg₁ : 0 < sg₁) (hΞ₁ : 0 < Ξ₁) (hmo₁ : 128 * Ξ₁⁻¹ * sg₁ ≤ 1 / 5)
    (heg₁ : 0 ≤ eg₁)
    (plane₁ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (hplaneQ₁ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1,
      plane₁ x ≤ gafStageQ P.toLocalChartFamily P.zero 1)
    (hpp₁ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1, ∀ q,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1) q =
        x →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
        plane₁ x ≤ LinearMap.ker ((blockMarkerCLM
          (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero a) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))
    (hrank₁ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1, ∃ i ∈ P.edge.centres,
      ∀ q : X,
      cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) q = x →
        ∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 →
          ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
              (cgpQ2Tags P.toLocalChartFamily P.zero)) q w -
            (plane₁ x).starProjection
              ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ2Tags P.toLocalChartFamily P.zero)) q w)‖ < eg₁)
    (a₁ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hsm₁ : ContDiffOn ℝ ∞ a₁ (⋃ x ∈ gafCloud P.toLocalChartFamily P.zero 1,
      ball x (sg₁ * ρ (sel₁ x))))
    (hab₁ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1, ∀ z ∈ ball x (sg₁ * ρ (sel₁ x)),
      ‖a₁ z - (x + (plane₁ x).starProjection (z - x))‖ ≤ Ξ₁ * (sg₁ * ρ (sel₁ x)) ∧
      DifferentiableAt ℝ a₁ z ∧ ‖fderiv ℝ a₁ z - (plane₁ x).starProjection‖ ≤ Ξ₁ ∧
      ∀ (Kk : Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
        (c : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (∀ i ∈ gafCloud P.toLocalChartFamily P.zero 1,
          (closedBall i (80 * Ξ₁⁻¹ * (sg₁ * ρ (sel₁ i))) ∩
            ball x (8 * Ξ₁⁻¹ * (sg₁ * ρ (sel₁ x)))).Nonempty →
          Kk.starProjection i = c ∧ plane₁ i ≤ Kkᗮ) →
        Kk.starProjection (a₁ z) = c)
    (sel₂ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel₂ : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 2,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2)
        (sel₂ x) = x)
    {Ξ₂ sg₂ eg₂ : ℝ} (hsg₂ : 0 < sg₂) (hΞ₂ : 0 < Ξ₂) (hmo₂ : 128 * Ξ₂⁻¹ * sg₂ ≤ 1 / 5)
    (heg₂ : 0 ≤ eg₂)
    (plane₂ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (hplaneQ₂ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
      plane₂ x ≤ gafStageQ P.toLocalChartFamily P.zero 2)
    (hpp₂ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2, ∀ q,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2) q =
        x →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
        plane₂ x ≤ LinearMap.ker ((blockMarkerCLM
          (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero a) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))
    (hrank₂ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
      ∃ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
      ∀ q, cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q = x →
        ∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
            (cgpQ3Tags P.toLocalChartFamily P.zero)) q v -
            ((plane₂ x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero))
                q) v : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))‖ ≤
          eg₂ * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v))
    (a₂ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hsm₂ : ContDiffOn ℝ ∞ a₂ (⋃ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
      ball x (sg₂ * ρ (sel₂ x))))
    (hab₂ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2, ∀ z ∈ ball x (sg₂ * ρ (sel₂ x)),
      ‖a₂ z - (x + (plane₂ x).starProjection (z - x))‖ ≤ Ξ₂ * (sg₂ * ρ (sel₂ x)) ∧
      DifferentiableAt ℝ a₂ z ∧ ‖fderiv ℝ a₂ z - (plane₂ x).starProjection‖ ≤ Ξ₂ ∧
      ∀ (Kk : Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
        (c : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (∀ i ∈ gafCloud P.toLocalChartFamily P.zero 2,
          (closedBall i (80 * Ξ₂⁻¹ * (sg₂ * ρ (sel₂ i))) ∩
            ball x (8 * Ξ₂⁻¹ * (sg₂ * ρ (sel₂ x)))).Nonempty →
          Kk.starProjection i = c ∧ plane₂ i ≤ Kkᗮ) →
        Kk.starProjection (a₂ z) = c)
    {c₀ : ℝ} (hv₁ : 5 / 3 * Ξ₀ * sg₀ < c₀) (hc₀ : c₀ ≤ 1 / 512)
    (hd₁ : (5 / 3 * Ξ₀ * sg₀ * gafCutoffConstant * gafDerivativeBound +
        Ξ₀ * gafDerivativeBound + eg₀) < c₀)
    (hc₀κ : c₀ ≤ 4 * gafKappa / 5) (hc₀s : c₀ ≤ 3 * sg₁ / 10) {c₁ : ℝ}
    (hv₂ : (c₀ + (5 / 3 * Ξ₁ * sg₁ + (1 + Ξ₁) * c₀)) < c₁) (hc₁ : c₁ ≤ 1 / 512)
    (hd₂ : ((5 / 3 * Ξ₁ * sg₁ + (1 + Ξ₁) * c₀) * gafCutoffConstant * (gafDerivativeBound + c₀) +
        Ξ₁ * (gafDerivativeBound + c₀) + eg₁ + 2 * c₀) < c₁)
    (hc₁κ : c₁ ≤ 4 * gafKappa / 5) (hc₁s : c₁ ≤ 3 * sg₂ / 10) {c₂ : ℝ}
    (hv₃ : (c₁ + (5 / 3 * Ξ₂ * sg₂ + (1 + Ξ₂) * c₁)) < c₂) (hc₂ : c₂ ≤ 1 / 512) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 2)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (a₂ y))
      (gafStageThreeCutoff P.toLocalChartFamily P.zero) ∘
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
        (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
        (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
          (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
          (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
            (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero))) ∧
    (∀ p, ‖(adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 2)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (a₂ y))
      (gafStageThreeCutoff P.toLocalChartFamily P.zero) ∘
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
        (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
        (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
          (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
          (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
            (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero))) p -
      cgpGlobalMap P.toLocalChartFamily P.zero p‖ < c₂ * ρ p) ∧
    (∀ p w, ‖mvfderiv 𝓘(ℝ, E3)
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 2)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (a₂ y))
      (gafStageThreeCutoff P.toLocalChartFamily P.zero) ∘
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
        (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
        (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
          (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
          (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
            (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero))) p w -
      mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤
        ((5 / 3 * Ξ₂ * sg₂ + (1 + Ξ₂) * c₁) * gafCutoffConstant * (gafDerivativeBound + c₁) +
        Ξ₂ * (gafDerivativeBound + c₁) + eg₂ + 2 * c₁) *
          Real.sqrt (g.inner p w w)) ∧
    (∀ q (a : CGPMarkerIndex P.toLocalChartFamily),
      ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
      blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a)
        ((adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 2)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (a₂ y))
      (gafStageThreeCutoff P.toLocalChartFamily P.zero) ∘
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
        (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
        (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
          (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
          (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
            (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero))) q) = 0) ∧
    ∀ (a : CGPMarkerIndex P.toLocalChartFamily) p,
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      ∀ z ∈ segment ℝ (cgpGlobalMap P.toLocalChartFamily P.zero p)
        ((adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 2)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (a₂ y))
      (gafStageThreeCutoff P.toLocalChartFamily P.zero) ∘
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
        (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
        (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
          (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
          (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
            (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero))) p),
      |blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) z| ≤
        ρ (cgpMarkerCentre P.toLocalChartFamily a) / 32 := by
  have h1 := gaf02_core_stageOne_GAF8 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 hσc hγc hεr
    sel₀ hsel₀ hsg₀ hΞ₀ hmo₀ heg₀ plane₀ hplaneQ₀ hpp₀ hrank₀ a₀ hsm₀ hab₀ hv₁ hc₀
  have h2 := gaf02_core_stageTwo_GAF8 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 hσc hγc hεr
    sel₀ hsel₀ hsg₀ hΞ₀ hmo₀ heg₀ plane₀ hplaneQ₀ hpp₀ hrank₀ a₀ hsm₀ hab₀
    sel₁ hsel₁ hsg₁ hΞ₁ hmo₁ heg₁ plane₁ hplaneQ₁ hpp₁ hrank₁ a₁ hsm₁ hab₁
    hv₁ hc₀ hd₁ hc₀κ hc₀s hv₂ hc₁
  have hpk₀ := gafStage_package_GAF6 P hΔ hΛ hLΛ 0 sel₀ hsel₀ hsg₀ hΞ₀ hmo₀ plane₀
    hplaneQ₀ hpp₀ a₀ hsm₀ hab₀
  have hpk₁ := gafStage_package_GAF6 P hΔ hΛ hLΛ 1 sel₁ hsel₁ hsg₁ hΞ₁ hmo₁ plane₁
    hplaneQ₁ hpp₁ a₁ hsm₁ hab₁
  have hpk₂ := gafStage_package_GAF6 P hΔ hΛ hLΛ 2 sel₂ hsel₂ hsg₂ hΞ₂ hmo₂ plane₂
    hplaneQ₂ hpp₂ a₂ hsm₂ hab₂
  have hpos : 0 < 5 / 3 * Ξ₀ * sg₀ := by positivity
  have hc₀0 : 0 ≤ c₀ := (hpos.trans hv₁).le
  have hc₁0 : 0 ≤ c₁ := le_of_lt (lt_of_le_of_lt (by positivity) hv₂)
  have hc₂0 : 0 ≤ c₂ := le_of_lt (lt_of_le_of_lt (by positivity) hv₃)
  have hprior : ∀ p, ‖(adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
      (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
        (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
        (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
          (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero)) p -
      cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤ c₁ * ρ p := fun p => (h2.2.1 p).le
  have hpriorD : ∀ p w, ‖mvfderiv 𝓘(ℝ, E3)
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
      (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
        (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
        (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
          (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero)) p w -
      mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤
        c₁ * Real.sqrt (g.inner p w w) := fun p w =>
    (h2.2.2.1 p w).trans (mul_le_mul_of_nonneg_right hd₂.le (Real.sqrt_nonneg _))
  have hZM : ∀ (a : CGPMarkerIndex P.toLocalChartFamily) p,
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      |blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a)
        ((adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
      (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
        (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
        (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
          (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero)) p)| ≤
        ρ (cgpMarkerCentre P.toLocalChartFamily a) / 32 :=
    fun a p hp => h2.2.2.2.2 a p hp _ (right_mem_segment ℝ _ _)
  have hfam := gaf02_familyZM_GAF7 P _ hZM
  have hout := gaf02_stageThree_output_GAF6 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 hσc hγc hεr
    sel₂ hsel₂ plane₂
    (fun y => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (a₂ y))
    hΞ₂.le hsg₂ heg₂ hc₁0 hc₁s hc₁κ hc₁0 hpk₂.2.2.1 hpk₂.2.2.2.1 hrank₂ _
    (fun p => (h2.1 p).mdifferentiableAt (by simp)) hprior hpriorD hfam.2
  have hsm := gaf02_stageThree_smooth_GAF6 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 sel₂ hsel₂
    (fun y => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (a₂ y))
    hsg₂ hc₁s hc₁κ hpk₂.2.1 _ h2.1 hprior hfam.2
  have hcum₁ : ∀ q, ‖adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
        (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
        (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
          (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero q) -
      cgpGlobalMap P.toLocalChartFamily P.zero q‖ ≤ c₀ * ρ q := fun q => (h1.2.1 q).le
  have hcum₃ : ∀ q, ‖(adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 2)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (a₂ y))
      (gafStageThreeCutoff P.toLocalChartFamily P.zero) ∘
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
        (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
        (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
          (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
          (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
            (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero))) q -
      cgpGlobalMap P.toLocalChartFamily P.zero q‖ ≤ c₂ * ρ q := fun q =>
    (hout.2.1 q).trans (mul_le_mul_of_nonneg_right hv₃.le (hρ q).le)
  have hz := gaf02_stageThree_zeroMarker_GAF7 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 sel₀ hsel₀
    (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
    hpk₀.1 hsg₀ hpk₀.2.2.2.2 sel₁ hsel₁
    (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
    hpk₁.1 hsg₁ hpk₁.2.2.2.2 sel₂ hsel₂
    (fun y => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (a₂ y))
    hpk₂.1 hsg₂ hpk₂.2.2.2.2 hc₀0 hc₀ hc₀κ hc₀s hc₁0 hc₁ hc₁κ hc₁s hc₂0 hc₂ hcum₁
    (fun q => by simpa only [Function.comp_apply] using hprior q)
    (fun q => by simpa only [Function.comp_apply] using hcum₃ q)
  refine ⟨hsm, fun p => (hout.2.1 p).trans_lt (mul_lt_mul_of_pos_right hv₃ (hρ p)), hout.2.2,
    fun q a ha => ?_, fun a p hp z hz' => hz.2.2.2 a p hp z ?_⟩
  · simpa only [Function.comp_apply] using hz.2.2.1 q a ha
  · simpa only [Function.comp_apply] using hz'

/-- **GAF02 CORE kernel** (the analytic adjustment chain on abstract stage data): with
`P_j = π_{Q_j} ∘ a_j`, `Ψ_j = adjustmentMap Q_j P_j ψ_j`, `g₁ = Ψ₁ ∘ 𝓔⁰`, `g₂ = Ψ₂ ∘ g₁`,
`E = Ψ₃ ∘ g₂`: every stage output is smooth; the cumulative value errors are `< c_jρ` and the
derivative errors `≤ H√g` with `H < c_j` (strict, from GAF01's strict CHOICE inequalities); every
retained marker with `ρ(c_a) < ρ/16` vanishes at every stage; (AM0) holds at `g₁`, `g₂`, `E` and on
the segment from `𝓔⁰ p` to `E p`. -/
theorem gaf02_core_kernel_GAF8
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hσc : σc ∈ Icc (0 : ℝ) 1) (hγc : γc ∈ Icc (0 : ℝ) 1) (hεr : εr ∈ Icc (0 : ℝ) 1)
    (sel₀ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel₀ : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 0,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0)
        (sel₀ x) = x)
    {Ξ₀ sg₀ eg₀ : ℝ} (hsg₀ : 0 < sg₀) (hΞ₀ : 0 < Ξ₀) (hmo₀ : 128 * Ξ₀⁻¹ * sg₀ ≤ 1 / 5)
    (heg₀ : 0 ≤ eg₀)
    (plane₀ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (hplaneQ₀ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      plane₀ x ≤ gafStageQ P.toLocalChartFamily P.zero 0)
    (hpp₀ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ∀ q,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0) q =
        x →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
        plane₀ x ≤ LinearMap.ker ((blockMarkerCLM
          (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero a) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))
    (hrank₀ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      ∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
      ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x → ∀ v,
        ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) q v -
            ((plane₀ x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (cgpGlobalMap P.toLocalChartFamily P.zero) q) v :
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))‖ ≤
          eg₀ * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v))
    (a₀ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hsm₀ : ContDiffOn ℝ ∞ a₀ (⋃ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      ball x (sg₀ * ρ (sel₀ x))))
    (hab₀ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ∀ z ∈ ball x (sg₀ * ρ (sel₀ x)),
      ‖a₀ z - (x + (plane₀ x).starProjection (z - x))‖ ≤ Ξ₀ * (sg₀ * ρ (sel₀ x)) ∧
      DifferentiableAt ℝ a₀ z ∧ ‖fderiv ℝ a₀ z - (plane₀ x).starProjection‖ ≤ Ξ₀ ∧
      ∀ (Kk : Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
        (c : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (∀ i ∈ gafCloud P.toLocalChartFamily P.zero 0,
          (closedBall i (80 * Ξ₀⁻¹ * (sg₀ * ρ (sel₀ i))) ∩
            ball x (8 * Ξ₀⁻¹ * (sg₀ * ρ (sel₀ x)))).Nonempty →
          Kk.starProjection i = c ∧ plane₀ i ≤ Kkᗮ) →
        Kk.starProjection (a₀ z) = c)
    (sel₁ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel₁ : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 1,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1)
        (sel₁ x) = x)
    {Ξ₁ sg₁ eg₁ : ℝ} (hsg₁ : 0 < sg₁) (hΞ₁ : 0 < Ξ₁) (hmo₁ : 128 * Ξ₁⁻¹ * sg₁ ≤ 1 / 5)
    (heg₁ : 0 ≤ eg₁)
    (plane₁ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (hplaneQ₁ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1,
      plane₁ x ≤ gafStageQ P.toLocalChartFamily P.zero 1)
    (hpp₁ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1, ∀ q,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1) q =
        x →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
        plane₁ x ≤ LinearMap.ker ((blockMarkerCLM
          (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero a) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))
    (hrank₁ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1, ∃ i ∈ P.edge.centres,
      ∀ q : X,
      cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) q = x →
        ∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 →
          ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
              (cgpQ2Tags P.toLocalChartFamily P.zero)) q w -
            (plane₁ x).starProjection
              ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ2Tags P.toLocalChartFamily P.zero)) q w)‖ < eg₁)
    (a₁ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hsm₁ : ContDiffOn ℝ ∞ a₁ (⋃ x ∈ gafCloud P.toLocalChartFamily P.zero 1,
      ball x (sg₁ * ρ (sel₁ x))))
    (hab₁ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1, ∀ z ∈ ball x (sg₁ * ρ (sel₁ x)),
      ‖a₁ z - (x + (plane₁ x).starProjection (z - x))‖ ≤ Ξ₁ * (sg₁ * ρ (sel₁ x)) ∧
      DifferentiableAt ℝ a₁ z ∧ ‖fderiv ℝ a₁ z - (plane₁ x).starProjection‖ ≤ Ξ₁ ∧
      ∀ (Kk : Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
        (c : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (∀ i ∈ gafCloud P.toLocalChartFamily P.zero 1,
          (closedBall i (80 * Ξ₁⁻¹ * (sg₁ * ρ (sel₁ i))) ∩
            ball x (8 * Ξ₁⁻¹ * (sg₁ * ρ (sel₁ x)))).Nonempty →
          Kk.starProjection i = c ∧ plane₁ i ≤ Kkᗮ) →
        Kk.starProjection (a₁ z) = c)
    (sel₂ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel₂ : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 2,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2)
        (sel₂ x) = x)
    {Ξ₂ sg₂ eg₂ : ℝ} (hsg₂ : 0 < sg₂) (hΞ₂ : 0 < Ξ₂) (hmo₂ : 128 * Ξ₂⁻¹ * sg₂ ≤ 1 / 5)
    (heg₂ : 0 ≤ eg₂)
    (plane₂ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (hplaneQ₂ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
      plane₂ x ≤ gafStageQ P.toLocalChartFamily P.zero 2)
    (hpp₂ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2, ∀ q,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2) q =
        x →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
        plane₂ x ≤ LinearMap.ker ((blockMarkerCLM
          (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero a) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))
    (hrank₂ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
      ∃ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
      ∀ q, cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q = x →
        ∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
            (cgpQ3Tags P.toLocalChartFamily P.zero)) q v -
            ((plane₂ x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero))
                q) v : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))‖ ≤
          eg₂ * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v))
    (a₂ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hsm₂ : ContDiffOn ℝ ∞ a₂ (⋃ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
      ball x (sg₂ * ρ (sel₂ x))))
    (hab₂ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2, ∀ z ∈ ball x (sg₂ * ρ (sel₂ x)),
      ‖a₂ z - (x + (plane₂ x).starProjection (z - x))‖ ≤ Ξ₂ * (sg₂ * ρ (sel₂ x)) ∧
      DifferentiableAt ℝ a₂ z ∧ ‖fderiv ℝ a₂ z - (plane₂ x).starProjection‖ ≤ Ξ₂ ∧
      ∀ (Kk : Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
        (c : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (∀ i ∈ gafCloud P.toLocalChartFamily P.zero 2,
          (closedBall i (80 * Ξ₂⁻¹ * (sg₂ * ρ (sel₂ i))) ∩
            ball x (8 * Ξ₂⁻¹ * (sg₂ * ρ (sel₂ x)))).Nonempty →
          Kk.starProjection i = c ∧ plane₂ i ≤ Kkᗮ) →
        Kk.starProjection (a₂ z) = c)
    {c₀ : ℝ} (hv₁ : 5 / 3 * Ξ₀ * sg₀ < c₀) (hc₀ : c₀ ≤ 1 / 512)
    (hd₁ : (5 / 3 * Ξ₀ * sg₀ * gafCutoffConstant * gafDerivativeBound +
        Ξ₀ * gafDerivativeBound + eg₀) < c₀)
    (hc₀κ : c₀ ≤ 4 * gafKappa / 5) (hc₀s : c₀ ≤ 3 * sg₁ / 10) {c₁ : ℝ}
    (hv₂ : (c₀ + (5 / 3 * Ξ₁ * sg₁ + (1 + Ξ₁) * c₀)) < c₁) (hc₁ : c₁ ≤ 1 / 512)
    (hd₂ : ((5 / 3 * Ξ₁ * sg₁ + (1 + Ξ₁) * c₀) * gafCutoffConstant * (gafDerivativeBound + c₀) +
        Ξ₁ * (gafDerivativeBound + c₀) + eg₁ + 2 * c₀) < c₁)
    (hc₁κ : c₁ ≤ 4 * gafKappa / 5) (hc₁s : c₁ ≤ 3 * sg₂ / 10) {c₂ : ℝ}
    (hv₃ : (c₁ + (5 / 3 * Ξ₂ * sg₂ + (1 + Ξ₂) * c₁)) < c₂) (hc₂ : c₂ ≤ 1 / 512)
    (hd₃ : ((5 / 3 * Ξ₂ * sg₂ + (1 + Ξ₂) * c₁) * gafCutoffConstant * (gafDerivativeBound + c₁) +
        Ξ₂ * (gafDerivativeBound + c₁) + eg₂ + 2 * c₁) < c₂) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
      (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
        (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero) ∧
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
      (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
        (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
        (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
          (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero)) ∧
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 2)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (a₂ y))
      (gafStageThreeCutoff P.toLocalChartFamily P.zero) ∘
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
        (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
        (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
          (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
          (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
            (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero))) ∧
    (∀ p, ‖(adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
      (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
        (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero) p -
      cgpGlobalMap P.toLocalChartFamily P.zero p‖ < c₀ * ρ p) ∧
    (∀ p, ‖(adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
      (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
        (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
        (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
          (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero)) p -
      cgpGlobalMap P.toLocalChartFamily P.zero p‖ < c₁ * ρ p) ∧
    (∀ p, ‖(adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 2)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (a₂ y))
      (gafStageThreeCutoff P.toLocalChartFamily P.zero) ∘
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
        (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
        (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
          (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
          (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
            (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero))) p -
      cgpGlobalMap P.toLocalChartFamily P.zero p‖ < c₂ * ρ p) ∧
    (∃ Hd : ℝ, Hd < c₀ ∧ ∀ p w, ‖mvfderiv 𝓘(ℝ, E3)
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
      (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
        (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero) p w -
      mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤
        Hd * Real.sqrt (g.inner p w w)) ∧
    (∃ Hd : ℝ, Hd < c₁ ∧ ∀ p w, ‖mvfderiv 𝓘(ℝ, E3)
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
      (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
        (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
        (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
          (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero)) p w -
      mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤
        Hd * Real.sqrt (g.inner p w w)) ∧
    (∃ Hd : ℝ, Hd < c₂ ∧ ∀ p w, ‖mvfderiv 𝓘(ℝ, E3)
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 2)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (a₂ y))
      (gafStageThreeCutoff P.toLocalChartFamily P.zero) ∘
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
        (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
        (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
          (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
          (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
            (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero))) p w -
      mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤
        Hd * Real.sqrt (g.inner p w w)) ∧
    (∀ q (a : CGPMarkerIndex P.toLocalChartFamily),
      ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
      blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a)
        ((adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
      (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
        (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero) q) = 0) ∧
    (∀ q (a : CGPMarkerIndex P.toLocalChartFamily),
      ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
      blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a)
        ((adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
      (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
        (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
        (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
          (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero)) q) = 0) ∧
    (∀ q (a : CGPMarkerIndex P.toLocalChartFamily),
      ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
      blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a)
        ((adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 2)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (a₂ y))
      (gafStageThreeCutoff P.toLocalChartFamily P.zero) ∘
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
        (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
        (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
          (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
          (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
            (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero))) q) = 0) ∧
    (∀ (a : CGPMarkerIndex P.toLocalChartFamily) p,
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      |blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a)
        ((adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
      (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
        (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero) p)| ≤
        ρ (cgpMarkerCentre P.toLocalChartFamily a) / 32) ∧
    (∀ (a : CGPMarkerIndex P.toLocalChartFamily) p,
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      |blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a)
        ((adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
      (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
        (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
        (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
          (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero)) p)| ≤
        ρ (cgpMarkerCentre P.toLocalChartFamily a) / 32) ∧
    (∀ (a : CGPMarkerIndex P.toLocalChartFamily) p,
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      |blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a)
        ((adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 2)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (a₂ y))
      (gafStageThreeCutoff P.toLocalChartFamily P.zero) ∘
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
        (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
        (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
          (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
          (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
            (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero))) p)| ≤
        ρ (cgpMarkerCentre P.toLocalChartFamily a) / 32) ∧
    ∀ (a : CGPMarkerIndex P.toLocalChartFamily) p,
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      ∀ z ∈ segment ℝ (cgpGlobalMap P.toLocalChartFamily P.zero p)
        ((adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 2)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (a₂ y))
      (gafStageThreeCutoff P.toLocalChartFamily P.zero) ∘
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
        (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
        (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
          (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
          (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
            (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero))) p),
      |blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) z| ≤
        ρ (cgpMarkerCentre P.toLocalChartFamily a) / 32 := by
  have h1 := gaf02_core_stageOne_GAF8 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 hσc hγc hεr
    sel₀ hsel₀ hsg₀ hΞ₀ hmo₀ heg₀ plane₀ hplaneQ₀ hpp₀ hrank₀ a₀ hsm₀ hab₀ hv₁ hc₀
  have h2 := gaf02_core_stageTwo_GAF8 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 hσc hγc hεr
    sel₀ hsel₀ hsg₀ hΞ₀ hmo₀ heg₀ plane₀ hplaneQ₀ hpp₀ hrank₀ a₀ hsm₀ hab₀
    sel₁ hsel₁ hsg₁ hΞ₁ hmo₁ heg₁ plane₁ hplaneQ₁ hpp₁ hrank₁ a₁ hsm₁ hab₁
    hv₁ hc₀ hd₁ hc₀κ hc₀s hv₂ hc₁
  have h3 := gaf02_core_stageThree_GAF8 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 hσc hγc hεr
    sel₀ hsel₀ hsg₀ hΞ₀ hmo₀ heg₀ plane₀ hplaneQ₀ hpp₀ hrank₀ a₀ hsm₀ hab₀
    sel₁ hsel₁ hsg₁ hΞ₁ hmo₁ heg₁ plane₁ hplaneQ₁ hpp₁ hrank₁ a₁ hsm₁ hab₁
    sel₂ hsel₂ hsg₂ hΞ₂ hmo₂ heg₂ plane₂ hplaneQ₂ hpp₂ hrank₂ a₂ hsm₂ hab₂
    hv₁ hc₀ hd₁ hc₀κ hc₀s hv₂ hc₁ hd₂ hc₁κ hc₁s hv₃ hc₂
  exact ⟨h1.1, h2.1, h3.1, h1.2.1, h2.2.1, h3.2.1, ⟨_, hd₁, h1.2.2.1⟩, ⟨_, hd₂, h2.2.2.1⟩,
    ⟨_, hd₃, h3.2.2.1⟩, h1.2.2.2.1, h2.2.2.2.1, h3.2.2.2.1,
    fun a p hp => h1.2.2.2.2 a p hp _ (right_mem_segment ℝ _ _),
    fun a p hp => h2.2.2.2.2 a p hp _ (right_mem_segment ℝ _ _),
    fun a p hp => h3.2.2.2.2 a p hp _ (right_mem_segment ℝ _ _), h3.2.2.2.2⟩

end DifferentialGeometry.Geometry.Collapse

import DifferentialGeometry.Geometry.Fibration.ActualAdjustedScaleStageOne

/-!
# Consumer: EDP01, step — (SD) for the stage-one blend `s = (1 − χ)ρ + χz_ρ`

* `edp01_stage_one_blend_step_GAFS2`: with the INPUTS of `edp01_stage_one_zrho_step_GAFS2` (the
  stage-one nearest map with the literal conclusions of `gaf01_row_nearest_mean_GAFS2` at stage `0`,
  and the first-cloud planes with the scale clause — not yet a conclusion of the stage-0 test),
  `edp01_scale_C14` gives (SD) for `s` with `C_ρ = 100(L₀ + 1)(1 + b_cut + 1·c_w/Σ)` and `s > 0`
  once `C_ρΛ < 1`. A STEP of EDP01, not the row.
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

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14SOA_GAFS2
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14SOA_GAFS2
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14SOA_GAFS2
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **EDP01, step: (SD) for the stage-one blend.** With the inputs of
`edp01_stage_one_zrho_step_GAFS2`, the blend `s = (1 − χ)ρ + χz_ρ` satisfies `|s − ρ| ≤ C_ρΛρ`,
`|ds(v)| ≤ C_ρΛ|v|_g` with `C_ρ = 100(L₀ + 1)(1 + b_cut + 1·c_w/Σ)`, and `s > 0` if `C_ρΛ < 1`. -/
theorem edp01_stage_one_blend_step_GAFS2
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hσc : σc ∈ Icc (0 : ℝ) 1) (hγc : γc ∈ Icc (0 : ℝ) 1) (hεr : εr ∈ Icc (0 : ℝ) 1)
    {εc sg cw : ℝ} (hεc : 0 < εc) (hsg : 0 < sg) (hsgε : sg ≤ εc / 10000) (hcw : 0 ≤ cw)
    (sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 0,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0)
        (sel x) = x)
    (plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (hscale : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      plane x ≤ LinearMap.ker ((blockMarkerCLM (cgpScaleTag P.toLocalChartFamily P.zero) :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))
    (a : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hda : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ∀ z ∈ ball x (sg * ρ (sel x)),
      DifferentiableAt ℝ a z)
    (hmean : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ∀ z ∈ ball x (sg * ρ (sel x)),
      ∀ ℓ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ,
        (∀ i ∈ gafCloud P.toLocalChartFamily P.zero 0,
          (closedBall i (80 * εc⁻¹ * (sg * ρ (sel i))) ∩
            ball x (8 * εc⁻¹ * (sg * ρ (sel x)))).Nonempty →
          plane i ≤ LinearMap.ker
            (ℓ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ)) →
        ∀ R₀ β : ℝ,
        (∀ i ∈ gafCloud P.toLocalChartFamily P.zero 0,
          (closedBall i (80 * εc⁻¹ * (sg * ρ (sel i))) ∩
            ball x (8 * εc⁻¹ * (sg * ρ (sel x)))).Nonempty → |ℓ i - R₀| ≤ β) →
        |ℓ (a z) - R₀| ≤ β ∧ ‖ℓ.comp (fderiv ℝ a z)‖ ≤ 2 * cw * β / (sg * ρ (sel x))) :
    let χ : X → ℝ := fun p => markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1)
      (gafCircleVector P.toLocalChartPackets) (gafCircleMarker P.toLocalChartPackets)
      (cgpGlobalMap P.toLocalChartFamily P.zero p)
    let zρ : X → ℝ := fun p =>
      blockMarkerCLM (cgpScaleTag P.toLocalChartFamily P.zero)
        (a (cgpGlobalMap P.toLocalChartFamily P.zero p))
    let Cρ : ℝ := 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw / sg)
    ∀ p, MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun y => (1 - χ y) * ρ y + χ y * zρ y) p ∧
      |(1 - χ p) * ρ p + χ p * zρ p - ρ p| ≤ Cρ * Λ * ρ p ∧
      (∀ v : TangentSpace 𝓘(ℝ, E3) p,
        |mvfderiv 𝓘(ℝ, E3) (fun y => (1 - χ y) * ρ y + χ y * zρ y) p v| ≤
          Cρ * Λ * Real.sqrt (g.inner p v v)) ∧
      (Cρ * Λ < 1 → 0 < (1 - χ p) * ρ p + χ p * zρ p) := by
  intro χ zρ Cρ
  have hz := edp01_stage_one_zrho_step_GAFS2 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 hσc hγc hεr
    hεc hsg hsgε hcw sel hsel plane hscale a hda hmean
  exact edp01_scale_C14 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 hσc hγc hεr zero_le_one hcw hsg
    (fun p hp => ⟨(hz p hp).1, (hz p hp).2.1, fun v => by rw [mul_one]; exact (hz p hp).2.2 v⟩)

end DifferentialGeometry.Geometry.Collapse

import DifferentialGeometry.Geometry.Fibration.ActualStagePackage
import DifferentialGeometry.Geometry.Fibration.ActualAdjustedScaleStageOne
import DifferentialGeometry.Geometry.Metric.Cfs15StageOutput

/-!
# Consumers of `Cfs15StageOutput` on the actual stage clouds: GAF03 and EDP01 entries

External draft 59 §2.3–2.4 (D59-3). A `Cfs15StageOutput` on the actual stage cloud `S_st`
(`gafCloud`), radius `r = Σρ ∘ sel`, accuracy `Ξ` and the stage plane `plane` (the explicit plane
slot; PLANES' `A.plane` is plugged in there) feeds the present stage consumers with its OWN
ambient nearest map `a = O.ambient = ι ∘ p` (no re-chosen map):

* `gafStage_package_of_output_C15` (GAF03 entry): `gafStage_package_GAF6` for `pn := O.ambient`
  (smoothness, value/derivative bounds and GAF03's affine locality all from `O`), together with
  (PNATIVE) `π_{Q_st}(a z) = ι p(z)` on `Ω` — the projected stage map IS the native nearest map.
* `edp01_zrho_of_output_C15` (EDP01 entry, stage one): `edp01_stage_one_zrho_step_GAFS2` for
  `a := O.ambient` with (SMV) from `O` (`c_w` the output's total weight budget).
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

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_C15a
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_C15a
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_C15a
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **GAF03 entry: the stage package of the output's own nearest map.** For a `Cfs15StageOutput`
on the actual stage cloud (radius `Σρ ∘ sel`, accuracy `Ξ`, plane slot `plane` with planes in
`Q_st` and (PP)): `gafStage_package_GAF6`'s conclusion for `pn = O.ambient` (its smoothness,
value/derivative bounds and GAF03's affine locality are supplied by `O`), and (PNATIVE): on
`Ω = ⋃_{x ∈ S_st} B(x, Σρ(sel x))`, `π_{Q_st}(a z) = ι p(z)`. -/
theorem gafStage_package_of_output_C15
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (st : Fin 3)
    (sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st)
        (sel x) = x)
    {sg Ξ : ℝ} (hsg : 0 < sg) (hmo : 128 * Ξ⁻¹ * sg ≤ 1 / 5)
    (plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (hplaneQ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero st,
      plane x ≤ gafStageQ P.toLocalChartFamily P.zero st)
    (hpp : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero st, ∀ q,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st) q =
        x →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
        plane x ≤ LinearMap.ker ((blockMarkerCLM
          (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero a) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))
    {k Kj : ℕ} {cw : ℝ} {Tc : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))}
    (O : Cfs15StageOutput k Kj Ξ cw (gafCloud P.toLocalChartFamily P.zero st) Tc
      (fun x => sg * ρ (sel x)) plane) :
    ((∀ z, (gafStageQ P.toLocalChartFamily P.zero st).starProjection (O.ambient z) ∈
        gafStageQ P.toLocalChartFamily P.zero st) ∧
      (∀ x ∈ gafCloud P.toLocalChartFamily P.zero st, ∀ z ∈ ball x (sg * ρ (sel x)),
        ContDiffAt ℝ ∞ (fun y => (gafStageQ P.toLocalChartFamily P.zero st).starProjection
          (O.ambient y)) z) ∧
      (∀ x ∈ gafCloud P.toLocalChartFamily P.zero st, ∀ z ∈ ball x (sg * ρ (sel x)),
        ‖(gafStageQ P.toLocalChartFamily P.zero st).starProjection (O.ambient z) -
            (x + (plane x).starProjection (z - x))‖ ≤ Ξ * (sg * ρ (sel x))) ∧
      (∀ x ∈ gafCloud P.toLocalChartFamily P.zero st, ∀ z ∈ ball x (sg * ρ (sel x)),
        DifferentiableAt ℝ (fun y => (gafStageQ P.toLocalChartFamily P.zero st).starProjection
          (O.ambient y)) z ∧
        ‖fderiv ℝ (fun y => (gafStageQ P.toLocalChartFamily P.zero st).starProjection
          (O.ambient y)) z - (plane x).starProjection‖ ≤ Ξ) ∧
      ∀ x ∈ gafCloud P.toLocalChartFamily P.zero st, ∀ z ∈ ball x (sg * ρ (sel x)), ∀ q,
        (gafStageQ P.toLocalChartFamily P.zero st).starProjection
            (cgpGlobalMap P.toLocalChartFamily P.zero q) = x →
        ∀ a : CGPMarkerIndex P.toLocalChartFamily,
          ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
          blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a)
            ((gafStageQ P.toLocalChartFamily P.zero st).starProjection (O.ambient z)) = 0) ∧
      ∀ z (hz : z ∈ cfs15Omega_C15 (gafCloud P.toLocalChartFamily P.zero st)
          (fun x => sg * ρ (sel x))),
        (gafStageQ P.toLocalChartFamily P.zero st).starProjection (O.ambient z) = O.p ⟨z, hz⟩ := by
  have hab : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero st, ∀ z ∈ ball x (sg * ρ (sel x)),
      ‖O.ambient z - (x + (plane x).starProjection (z - x))‖ ≤ Ξ * (sg * ρ (sel x)) ∧
      DifferentiableAt ℝ O.ambient z ∧ ‖fderiv ℝ O.ambient z - (plane x).starProjection‖ ≤ Ξ ∧
      ∀ (Kk : Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
        (c : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (∀ i ∈ gafCloud P.toLocalChartFamily P.zero st,
          (closedBall i (80 * Ξ⁻¹ * (sg * ρ (sel i))) ∩
            ball x (8 * Ξ⁻¹ * (sg * ρ (sel x)))).Nonempty →
          Kk.starProjection i = c ∧ plane i ≤ Kkᗮ) →
        Kk.starProjection (O.ambient z) = c := by
    intro x hx z hz
    have hvd := O.ambient_value_deriv hx hz
    exact ⟨hvd.1, hvd.2.1, hvd.2.2, fun Kk c hc => (O.locality_of_cloud_C15 hx Kk c hc).2.2 z hz⟩
  refine ⟨gafStage_package_GAF6 P hΔ hΛ hLΛ st sel hsel hsg O.eps_pos hmo plane hplaneQ hpp
    O.ambient O.ambient_contDiffOn hab, fun z hz => ?_⟩
  exact O.projected_nearest_eq_native _ (fun x hx => gafCloud_subset_gafStageQ _ _ st hx)
    hplaneQ z hz

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14_C15a
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_C15a
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_C15a
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **EDP01 entry: the stage-one scale from the output's own nearest map.** For a
`Cfs15StageOutput` on the first stage cloud (radius `Σρ ∘ sel`, accuracy `ε_c`, total weight
budget `c_w`, plane slot `plane` with the scale clause), `z_ρ = ℓ_s ∘ a ∘ 𝓔⁰` with
`a = O.ambient` satisfies EDP01's step on `tsupport χ`: differentiable,
`|z_ρ − ρ| ≤ (80/3)Λρ` and `|dz_ρ(v)| ≤ (80c_wL₀/(3Σ))Λ|v|_g` ((SMV) from `O`). -/
theorem edp01_zrho_of_output_C15
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hσc : σc ∈ Icc (0 : ℝ) 1) (hγc : γc ∈ Icc (0 : ℝ) 1) (hεr : εr ∈ Icc (0 : ℝ) 1)
    {εc sg cw : ℝ} (hsg : 0 < sg) (hsgε : sg ≤ εc / 10000) (hcw : 0 ≤ cw)
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
    {k Kj : ℕ} {Tc : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))}
    (O : Cfs15StageOutput k Kj εc cw (gafCloud P.toLocalChartFamily P.zero 0) Tc
      (fun x => sg * ρ (sel x)) plane) :
    let χ : X → ℝ := fun p => markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1)
      (gafCircleVector P.toLocalChartPackets) (gafCircleMarker P.toLocalChartPackets)
      (cgpGlobalMap P.toLocalChartFamily P.zero p)
    let zρ : X → ℝ := fun p =>
      blockMarkerCLM (cgpScaleTag P.toLocalChartFamily P.zero)
        (O.ambient (cgpGlobalMap P.toLocalChartFamily P.zero p))
    ∀ p ∈ tsupport χ, MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) zρ p ∧
      |zρ p - ρ p| ≤ 80 / 3 * Λ * ρ p ∧
      ∀ v : TangentSpace 𝓘(ℝ, E3) p, |mvfderiv 𝓘(ℝ, E3) zρ p v| ≤
        80 * cw * gafDerivativeBound / (3 * sg) * Λ * Real.sqrt (g.inner p v v) :=
  edp01_stage_one_zrho_step_GAFS2 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 hσc hγc hεr O.eps_pos
    hsg hsgε hcw sel hsel plane hscale O.ambient
    (fun _ hx _ hz => (O.ambient_value_deriv hx hz).2.1)
    (fun _ hx z hz ℓ hpl R₀ β hβ => O.smv_of_cloud_C15 hx ℓ hpl R₀ β hβ z hz)

end DifferentialGeometry.Geometry.Collapse

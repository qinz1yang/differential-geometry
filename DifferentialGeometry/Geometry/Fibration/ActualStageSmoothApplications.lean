import DifferentialGeometry.Geometry.Fibration.ActualStageSmooth
import DifferentialGeometry.Geometry.Fibration.ActualStageTwoThreeStep

/-!
# GAF02 step 5 on the actual data: the stage outputs are smooth

`gaf02_stageOne_smooth_GAF6`, `gaf02_stageTwo_smooth_GAF6`, `gaf02_stageThree_smooth_GAF6`: with a
stage projection smooth on every ball `B(x, Σρ(sel x))`, `x ∈ S_st`, the stage output
`Ψ_st ∘ f` is smooth whenever the preceding map `f` is smooth with prior error `E ≤ 3Σ/10` (stage
one: `f = 𝓔⁰`, `E = 0`; stages two and three: CFS31's (ZM) and `E ≤ 4κ/5`, the cutoff rows'
inputs). Localization by the cutoffs' closed supports (`gaf02_stageOne_loc_GAF5`,
`gaf02_stageTwo/Three_cutoff_point_GAF6`) and the preimage ratio
(`gafCloud_preimage_ratio_two_GAF5`) feed `stage_step_contDiffAt_point_GAF6`.
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
local instance instMetricN_GAF6m
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_GAF6m
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_GAF6m
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **Stage one's output `Ψ₁ ∘ 𝓔⁰` is smooth** when the stage projection is smooth on the balls of
the first cloud. -/
theorem gaf02_stageOne_smooth_GAF6
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hσc : σc ∈ Icc (0 : ℝ) 1) (hγc : γc ∈ Icc (0 : ℝ) 1) (hεr : εr ∈ Icc (0 : ℝ) 1)
    (sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 0,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0)
        (sel x) = x)
    (Pst : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    {sg : ℝ} (hsg : 0 < sg)
    (hPsm : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ∀ z ∈ ball x (sg * ρ (sel x)),
      ContDiffAt ℝ ∞ Pst z) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0) Pst
        (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
          (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero) := by
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by
    have h' : Λ * (1000000 * Δ) = 1000000 * Δ * Λ := by ring
    linarith
  have hcut := gaf02_stageOne_sourceCutoff P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1
  have hder := gaf01_derivative_bound P hΛ hΔ hμ hτ hLΛ hLmax he hT ⟨hσs, by linarith⟩ hσc hγc
    hεr
  have hratio := gafCloud_preimage_ratio_two_GAF5 P.toLocalChartFamily P.zero hΔ hΛ hsmall 0 sel
    hsel
  have hE : (0 : ℝ) ≤ 3 * sg / 10 := by positivity
  refine contMDiff_comp_of_contDiffAt_GAF6 hder.1 fun p => ?_
  exact stage_step_contDiffAt_point_GAF6 (gafStageQ P.toLocalChartFamily P.zero 0)
    (gafCloud P.toLocalChartFamily P.zero 0) sel ρ Pst _ hsg hE hPsm
    (cgpGlobalMap P.toLocalChartFamily P.zero) (cgpGlobalMap P.toLocalChartFamily P.zero) (hρ p)
    (gaf02_stageOne_loc_GAF5 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 p) hratio (by simp)
    (fun _ => hcut.1.contDiffAt)

/-- **Stage two's output `Ψ₂ ∘ f` is smooth** for a smooth `f` with prior error `E ≤ 3Σ/10`,
`E ≤ 4κ/5` and CFS31's (ZM) for the edge family, when the stage projection is smooth on the balls
of the edge cloud. -/
theorem gaf02_stageTwo_smooth_GAF6
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 1,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1)
        (sel x) = x)
    (Pst : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    {sg E : ℝ} (hsg : 0 < sg) (hE : E ≤ 3 * sg / 10) (hEκ : E ≤ 4 * gafKappa / 5)
    (hPsm : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1, ∀ z ∈ ball x (sg * ρ (sel x)),
      ContDiffAt ℝ ∞ Pst z)
    (f : X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hf : ContMDiff 𝓘(ℝ, E3)
      𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞ f)
    (hprior : ∀ p, ‖f p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤ E * ρ p)
    (hZM : ∀ (j : P.edge.finite_centres.toFinset) p, P.edge.cutoff j.1 p = 0 →
      |gafEdgeMarker P.toLocalChartFamily P.zero j (f p)| ≤ ρ j.1 / 32) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1) Pst
        (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘ f) := by
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by
    have h' : Λ * (1000000 * Δ) = 1000000 * Δ * Λ := by ring
    linarith
  have hpert : ∀ q, ‖f q - cgpGlobalMap P.toLocalChartFamily P.zero q‖ ≤
      4 * gafKappa / 5 * ρ q := fun q =>
    (hprior q).trans (mul_le_mul_of_nonneg_right hEκ (hρ q).le)
  have hcut := gaf02_stageTwo_cutoff P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 f hpert hZM
  have hratio := gafCloud_preimage_ratio_two_GAF5 P.toLocalChartFamily P.zero hΔ hΛ hsmall 1 sel
    hsel
  have hopen : IsOpen {z | 0 < gafScaleMarker P.toLocalChartFamily P.zero z} :=
    isOpen_lt continuous_const (gafScaleMarker P.toLocalChartFamily P.zero).continuous
  refine contMDiff_comp_of_contDiffAt_GAF6 hf fun p => ?_
  have hseg := hcut.2.2.2.2 p 1 ⟨zero_le_one, le_rfl⟩
  have h1 : (1 - (1 : ℝ)) • cgpGlobalMap P.toLocalChartFamily P.zero p + (1 : ℝ) • f p = f p := by
    simp
  rw [h1] at hseg
  exact stage_step_contDiffAt_point_GAF6 (gafStageQ P.toLocalChartFamily P.zero 1)
    (gafCloud P.toLocalChartFamily P.zero 1) sel ρ Pst _ hsg hE hPsm
    (cgpGlobalMap P.toLocalChartFamily P.zero) f (hρ p)
    (gaf02_stageTwo_cutoff_point_GAF6 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 f hpert hZM p).1
    hratio (hprior p) (fun _ => hcut.1.contDiffAt (hopen.mem_nhds hseg.1))

/-- **Stage three's output `Ψ₃ ∘ f` is smooth** for a smooth `f` with prior error `E ≤ 3Σ/10`,
`E ≤ 4κ/5` and CFS31's (ZM) for the slim family, when the stage projection is smooth on the balls
of the slim cloud. -/
theorem gaf02_stageThree_smooth_GAF6
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 2,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2)
        (sel x) = x)
    (Pst : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    {sg E : ℝ} (hsg : 0 < sg) (hE : E ≤ 3 * sg / 10) (hEκ : E ≤ 4 * gafKappa / 5)
    (hPsm : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2, ∀ z ∈ ball x (sg * ρ (sel x)),
      ContDiffAt ℝ ∞ Pst z)
    (f : X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hf : ContMDiff 𝓘(ℝ, E3)
      𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞ f)
    (hprior : ∀ p, ‖f p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤ E * ρ p)
    (hZM : ∀ (j : P.slim.finite_centres.toFinset) p, P.slim.cutoff j.1 p = 0 →
      |gafSlimMarker P.toLocalChartFamily P.zero j (f p)| ≤ ρ j.1 / 32) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 2) Pst
        (gafStageThreeCutoff P.toLocalChartFamily P.zero) ∘ f) := by
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by
    have h' : Λ * (1000000 * Δ) = 1000000 * Δ * Λ := by ring
    linarith
  have hpert : ∀ q, ‖f q - cgpGlobalMap P.toLocalChartFamily P.zero q‖ ≤
      4 * gafKappa / 5 * ρ q := fun q =>
    (hprior q).trans (mul_le_mul_of_nonneg_right hEκ (hρ q).le)
  have hcut := gaf02_stageThree_cutoff P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 f hpert hZM
  have hratio := gafCloud_preimage_ratio_two_GAF5 P.toLocalChartFamily P.zero hΔ hΛ hsmall 2 sel
    hsel
  refine contMDiff_comp_of_contDiffAt_GAF6 hf fun p => ?_
  exact stage_step_contDiffAt_point_GAF6 (gafStageQ P.toLocalChartFamily P.zero 2)
    (gafCloud P.toLocalChartFamily P.zero 2) sel ρ Pst _ hsg hE hPsm
    (cgpGlobalMap P.toLocalChartFamily P.zero) f (hρ p)
    (gaf02_stageThree_cutoff_point_GAF6 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 f hpert hZM p).1
    hratio (hprior p) (fun _ => hcut.1.contDiffAt)

end DifferentialGeometry.Geometry.Collapse

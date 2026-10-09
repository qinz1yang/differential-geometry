import DifferentialGeometry.Geometry.Fibration.ActualStagePackage
import DifferentialGeometry.Geometry.Fibration.ActualStageSmoothApplications
import DifferentialGeometry.Geometry.Fibration.ActualStageTwoThreeStepApplications

/-!
# GAF02's first stage with the projected nearest map

`gaf02_stageOne_projected_GAF6`: with the first stage projection `P₁ = π_{Q₁} ∘ a` of a nearest map
`a` carrying the conclusions of the GAF01 nearest-map row (abstract data), planes in `Q₁` with
(PP) and the first test's rank clause, the stage-one output `g₁ = Ψ₁ ∘ 𝓔⁰` is smooth, has value
error `(5/3)ΞΣρ` and derivative error `((5/3)ΞΣ·b·L + ΞL + e)√g` — the first step of GAF02's
induction, with every stage-one input of CFS31 (`hPst`, `hnear`) available from
`gafStage_package_GAF6`.
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
local instance instMetricN_GAF6q
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_GAF6q
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_GAF6q
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **GAF02's first stage with `P₁ = π_{Q₁} ∘ a`**: the stage-one output `Ψ₁ ∘ 𝓔⁰` is smooth with
value error `(5/3)ΞΣρ` and derivative error `((5/3)ΞΣ·b·L + ΞL + e)√g`. -/
theorem gaf02_stageOne_projected_GAF6
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hσc : σc ∈ Icc (0 : ℝ) 1) (hγc : γc ∈ Icc (0 : ℝ) 1) (hεr : εr ∈ Icc (0 : ℝ) 1)
    (sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 0,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0)
        (sel x) = x)
    {sg Ξ eg : ℝ} (hsg : 0 < sg) (hΞ : 0 < Ξ) (hmo : 128 * Ξ⁻¹ * sg ≤ 1 / 5) (heg : 0 ≤ eg)
    (plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (hplaneQ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      plane x ≤ gafStageQ P.toLocalChartFamily P.zero 0)
    (hpp : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ∀ q,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0) q =
        x →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
        plane x ≤ LinearMap.ker ((blockMarkerCLM
          (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero a) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))
    (hrank : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      ∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
      ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x → ∀ v,
        ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) q v -
            ((plane x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (cgpGlobalMap P.toLocalChartFamily P.zero) q) v :
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))‖ ≤
          eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v))
    (pn : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hsm : ContDiffOn ℝ ∞ pn (⋃ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      ball x (sg * ρ (sel x))))
    (hab : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ∀ z ∈ ball x (sg * ρ (sel x)),
      ‖pn z - (x + (plane x).starProjection (z - x))‖ ≤ Ξ * (sg * ρ (sel x)) ∧
      DifferentiableAt ℝ pn z ∧ ‖fderiv ℝ pn z - (plane x).starProjection‖ ≤ Ξ ∧
      ∀ (Kk : Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
        (c : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (∀ i ∈ gafCloud P.toLocalChartFamily P.zero 0,
          (closedBall i (80 * Ξ⁻¹ * (sg * ρ (sel i))) ∩
            ball x (8 * Ξ⁻¹ * (sg * ρ (sel x)))).Nonempty →
          Kk.starProjection i = c ∧ plane i ≤ Kkᗮ) →
        Kk.starProjection (pn z) = c) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
          (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (pn y))
          (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
            (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero) ∧
      (∀ p, ‖(adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
          (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (pn y))
          (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
            (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero) p -
          cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤ 5 / 3 * Ξ * sg * ρ p) ∧
      ∀ p w, ‖mvfderiv 𝓘(ℝ, E3) (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
          (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (pn y))
          (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
            (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero) p w -
          mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤
        (5 / 3 * Ξ * sg * gafCutoffConstant * gafDerivativeBound + Ξ * gafDerivativeBound + eg) *
          Real.sqrt (g.inner p w w) := by
  have hpk := gafStage_package_GAF6 P hΔ hΛ hLΛ 0 sel hsel hsg hΞ hmo plane hplaneQ hpp pn hsm hab
  have hout := gaf02_stageOne_output_GAF6 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 hσc hγc hεr sel
    hsel plane (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (pn y)) hΞ.le
    hsg heg hpk.2.2.1 hpk.2.2.2.1 hrank
  have hsmooth := gaf02_stageOne_smooth_GAF6 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 hσc hγc hεr
    sel hsel (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (pn y)) hsg
    hpk.2.1
  exact ⟨hsmooth, hout.2.1, hout.2.2⟩

end DifferentialGeometry.Geometry.Collapse

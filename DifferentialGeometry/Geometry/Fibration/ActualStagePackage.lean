import DifferentialGeometry.Geometry.Fibration.ActualStageSmooth
import DifferentialGeometry.Geometry.Fibration.ActualStageNearMarkers

/-!
# GAF02's stage projections from the nearest maps (CFS31's `P_k = π_{Q_k} ∘ a_k`)

Blueprint `master207B.tex`, GAF02 (B:5797) with FC33's `P_j = π_{Q_j} ∘ p`: for a nearest map `a`
on an actual stage cloud with the conclusions of `gaf01_row_nearest_mean_GAFS2` (smooth on
`Ω = ⋃_{x ∈ S_st} B(x, Σρ(sel x))`, CFS14 (3)'s value/derivative bounds `Ξ`, GAF03's locality) and
planes inside `Q_st` with the small-marker rule (PP), the projected map
`P = π_{Q_st} ∘ a` (`gafStage_package_GAF6`):

* takes values in `Q_st` (CFS31's `hPst`),
* is smooth at every point of every ball `B(x, Σρ(sel x))` (CFS18's input),
* keeps the value/derivative bounds (the stage step's `hPst`, `hPd`),
* satisfies CFS31's `hnear` (via `gafStage_hnear_GAF4`).
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
local instance instMetricN_GAF6p
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_GAF6p
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_GAF6p
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **The stage projection package** `P = π_{Q_st} ∘ a` of a nearest map `a` with the conclusions
of `gaf01_row_nearest_mean_GAFS2` (smoothness on `Ω`, value/derivative bounds, GAF03 locality) and
planes in `Q_st` with (PP): `P` is `Q_st`-valued, smooth on every ball, keeps the bounds, and
satisfies CFS31's `hnear`. -/
theorem gafStage_package_GAF6
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (st : Fin 3)
    (sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st)
        (sel x) = x)
    {sg Ξ : ℝ} (hsg : 0 < sg) (hΞ : 0 < Ξ) (hmo : 128 * Ξ⁻¹ * sg ≤ 1 / 5)
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
    (pn : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hsm : ContDiffOn ℝ ∞ pn (⋃ x ∈ gafCloud P.toLocalChartFamily P.zero st,
      ball x (sg * ρ (sel x))))
    (hab : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero st, ∀ z ∈ ball x (sg * ρ (sel x)),
      ‖pn z - (x + (plane x).starProjection (z - x))‖ ≤ Ξ * (sg * ρ (sel x)) ∧
      DifferentiableAt ℝ pn z ∧ ‖fderiv ℝ pn z - (plane x).starProjection‖ ≤ Ξ ∧
      ∀ (Kk : Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
        (c : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (∀ i ∈ gafCloud P.toLocalChartFamily P.zero st,
          (closedBall i (80 * Ξ⁻¹ * (sg * ρ (sel i))) ∩
            ball x (8 * Ξ⁻¹ * (sg * ρ (sel x)))).Nonempty →
          Kk.starProjection i = c ∧ plane i ≤ Kkᗮ) →
        Kk.starProjection (pn z) = c) :
    (∀ z, (gafStageQ P.toLocalChartFamily P.zero st).starProjection (pn z) ∈
        gafStageQ P.toLocalChartFamily P.zero st) ∧
      (∀ x ∈ gafCloud P.toLocalChartFamily P.zero st, ∀ z ∈ ball x (sg * ρ (sel x)),
        ContDiffAt ℝ ∞ (fun y => (gafStageQ P.toLocalChartFamily P.zero st).starProjection
          (pn y)) z) ∧
      (∀ x ∈ gafCloud P.toLocalChartFamily P.zero st, ∀ z ∈ ball x (sg * ρ (sel x)),
        ‖(gafStageQ P.toLocalChartFamily P.zero st).starProjection (pn z) -
            (x + (plane x).starProjection (z - x))‖ ≤ Ξ * (sg * ρ (sel x))) ∧
      (∀ x ∈ gafCloud P.toLocalChartFamily P.zero st, ∀ z ∈ ball x (sg * ρ (sel x)),
        DifferentiableAt ℝ (fun y => (gafStageQ P.toLocalChartFamily P.zero st).starProjection
          (pn y)) z ∧
        ‖fderiv ℝ (fun y => (gafStageQ P.toLocalChartFamily P.zero st).starProjection (pn y)) z -
          (plane x).starProjection‖ ≤ Ξ) ∧
      ∀ x ∈ gafCloud P.toLocalChartFamily P.zero st, ∀ z ∈ ball x (sg * ρ (sel x)), ∀ q,
        (gafStageQ P.toLocalChartFamily P.zero st).starProjection
            (cgpGlobalMap P.toLocalChartFamily P.zero q) = x →
        ∀ a : CGPMarkerIndex P.toLocalChartFamily,
          ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
          blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a)
            ((gafStageQ P.toLocalChartFamily P.zero st).starProjection (pn z)) = 0 := by
  have hproj := projected_stage_map_GAF6 (gafStageQ P.toLocalChartFamily P.zero st)
    (gafCloud P.toLocalChartFamily P.zero st) (fun x => sg * ρ (sel x)) plane hplaneQ
    (gafCloud_subset_gafStageQ P.toLocalChartFamily P.zero st) pn
    (fun x hx z hz => ⟨(hab x hx z hz).1, (hab x hx z hz).2.1, (hab x hx z hz).2.2.1⟩)
  have hopen : IsOpen (⋃ x ∈ gafCloud P.toLocalChartFamily P.zero st, ball x (sg * ρ (sel x))) :=
    isOpen_biUnion fun x _ => isOpen_ball
  have hnear := gafStage_hnear_GAF4 P hΔ hΛ hLΛ st sel hsel hsg hΞ hmo plane hpp pn
    (fun x hx z hz => (hab x hx z hz).2.2.2)
  refine ⟨hproj.1, fun x hx z hz => hproj.2.1 z ?_, fun x hx z hz => (hproj.2.2 x hx z hz).1,
    fun x hx z hz => (hproj.2.2 x hx z hz).2, hnear⟩
  exact hsm.contDiffAt (hopen.mem_nhds (mem_biUnion hx hz))

end DifferentialGeometry.Geometry.Collapse

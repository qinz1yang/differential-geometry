import DifferentialGeometry.Geometry.Fibration.ActualCloudSpectralJets
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14

/-!
# Consumer: CFS12's first-derivative weight bound on the final family

* `cfs12_first_cloud_deriv_C14`: on `LocalChartPacketsC14`, one constant `c_w ≥ 0` (depending only
  on `b`) such that CFS11's selection on the first cloud carries weights with
  `Σ_i ‖D w_i‖ ≤ c_w / r_x` on every reference ball `B(x, 8br_x)`, `x ∈ S₁` — the bound `c_w` that
  EDP01's (SW) calls "CFS12's bound `‖Dw_y‖ ≤ c_w / r_x`" (`m = j = 1` of
  `cfs12_first_cloud_GAFS2`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14SJ_GAFS2 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14SJ_GAFS2 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14SJ_GAFS2 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **CFS12's `c_w` on the first cloud of the final family**: one `c_w ≥ 0` (depending only on `b`)
such that on every `LocalChartPacketsC14` with two-dimensional planes and the (CS) tests on `S₁` at
quality `δ` (`δ((80·5/3 + 31)b + 2) < 1`), CFS11's selection carries weights with
`Σ_i ‖D w_i‖ ≤ c_w / r_x` on every reference ball `B(x, 8br_x)`. -/
theorem cfs12_first_cloud_deriv_C14 (bb : ℝ) (hbb : 1 ≤ bb) :
    ∃ cw : ℝ, 0 ≤ cw ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        0 ≤ Λ → 0 < Δ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 100 * Δ * Λ ≤ 1 / 100 → e ≤ 1 / 8 →
        ∀ sg δc : ℝ, 0 < sg → 128 * bb * sg ≤ 1 / 5 →
        ∀ plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
          Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (∀ x ∈ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7,
          Module.finrank ℝ (plane x) = 2) →
        0 < δc → δc * ((80 * (5 / 3) + 31) * bb + 2) < 1 →
        (∀ x ∈ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7,
          hausdorffEDist (cgpGlobalMap P.toLocalChartFamily P.zero ''
              fc04Set P.toLocalChartFamily P.zero 8 ∩
              ball x (scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x / δc))
            ((AffineSubspace.mk' x (plane x) :
                Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
              ball x (scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x / δc)) ≤
            ENNReal.ofReal (δc * scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x)) →
        ∃ (I : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) (hI : I.Finite),
          I ⊆ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7 ∧
          ∀ x ∈ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7,
          ∀ z ∈ ball x (8 * bb * scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x),
            (∑ i ∈ hI.toFinset, ‖iteratedFDeriv ℝ 1
              (fun y => ballCutoff i
                  (40 * bb * scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg i)
                  (2 * (40 * bb * scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg i)) y /
                (∑ a ∈ hI.toFinset, ballCutoff a
                  (40 * bb * scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg a)
                  (2 * (40 * bb * scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg a)) y))
              z‖) ≤ cw / scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x := by
  obtain ⟨C, hC⟩ := cfs12_first_cloud_GAFS2 bb hbb
  refine ⟨C 1, (C 1).2, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hΛ hΔ hμ hτ hΔΛ he sg δc hsg hbsg plane hdim hδ hδc hcloud
  have h := hC X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
    P.toLocalChartPackets hΛ hΔ hμ hτ hΔΛ he sg δc hsg hbsg plane hdim hδ hδc hcloud
  obtain ⟨I, hI, hIS, -, -, -, hw, -⟩ := h
  refine ⟨I, hI, hIS, fun x hx z hz => ?_⟩
  have h1 := hw 1 x hx 1 le_rfl z hz
  rwa [pow_one] at h1

end DifferentialGeometry.Geometry.Collapse
